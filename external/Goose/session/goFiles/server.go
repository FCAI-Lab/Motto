package server

type Operation struct {
	VersionVector []uint64
	Data          uint64
}

type Message struct {
	MessageType uint64

	C2S_Client_Id            uint64
	C2S_Server_Id            uint64
	C2S_Client_OperationType uint64
	C2S_Client_Data          uint64
	C2S_Client_VersionVector []uint64

	S2S_Gossip_Sending_ServerId   uint64
	S2S_Gossip_Receiving_ServerId uint64
	S2S_Gossip_Operations         []Operation
	S2S_Gossip_Index              uint64

	S2S_Acknowledge_Gossip_Sending_ServerId   uint64
	S2S_Acknowledge_Gossip_Receiving_ServerId uint64
	S2S_Acknowledge_Gossip_Index              uint64

	S2C_Client_OperationType uint64
	S2C_Client_Data          uint64
	S2C_Client_VersionVector []uint64
	S2C_Server_Id            uint64
	S2C_Client_Number        uint64
}

type Server struct {
	Id                     uint64
	NumberOfServers        uint64
	UnsatisfiedRequests    []Message
	VectorClock            []uint64
	OperationsPerformed    []Operation
	MyOperations           []Operation
	PendingOperations      []Operation
	GossipAcknowledgements []uint64
}

func compareVersionVector(v1 []uint64, v2 []uint64) bool {
	var output = true
	var i = uint64(0)
	var l = uint64(len(v1))
	for i < l {
		if v1[i] < v2[i] {
			output = false
			break
		}
		i++
	}
	return output
}

func lexicographicCompare(v1 []uint64, v2 []uint64) bool {
	var output = false
	var i = uint64(0)
	var l = uint64(len(v1))
	for i < l {
		if v1[i] == v2[i] {
			i++
		} else {
			output = v1[i] > v2[i]
			break
		}
	}

	return output
}

func maxTwoInts(x uint64, y uint64) uint64 {
	if x > y {
		return x
	} else {
		return y
	}
}

func maxTS(t1 []uint64, t2 []uint64) []uint64 {
	var i = uint64(0)
	var length = uint64(len(t1))
	var output = make([]uint64, len(t1))
	for i < length {
		output[i] = maxTwoInts(t1[i], t2[i])
		i++
	}
	return output
}

func oneOffVersionVector(v1 []uint64, v2 []uint64) bool {
	var output = true
	var canApply = true
	var i = uint64(0)
	var l = uint64(len(v1))

	for i < l {
		if canApply && v1[i]+1 == v2[i] {
			canApply = false
			continue
		}
		if v1[i] < v2[i] {
			output = false
		}
		i++
	}

	return output && !canApply
}

func equalSlices(s1 []uint64, s2 []uint64) bool {
	var output = true
	var i = uint64(0)
	var l = uint64(len(s1))

	for i < l {
		if s1[i] != s2[i] {
			output = false
			break
		}
		i++
	}

	return output
}

func binarySearch(s []Operation, needle Operation) uint64 {
	var i = uint64(0)
	var j = uint64(len(s))
	for i < j {
		mid := i + (j - i)/2
		if lexicographicCompare(needle.VersionVector, s[mid].VersionVector) {
			i = mid + 1
		} else {
			j = mid
		}
	}

	return i
}

func sortedInsert(s []Operation, value Operation) []Operation {
	index := binarySearch(s, value)
	if uint64(len(s)) == index {
		return append(s, value)
	} else if equalSlices(s[index].VersionVector, value.VersionVector) {
		return s
	} else {
		right := append([]Operation{value}, s[index:]...)
		result := append(s[:index], right...)
		return result
	}
}

func deleteAtIndexOperation(l []Operation, index uint64) []Operation {
	var ret = make([]Operation, 0)
	ret = append(ret, l[:index]...)
	return append(ret, l[index+1:]...)
}

func deleteAtIndexMessage(l []Message, index uint64) []Message {
	var ret = make([]Message, 0)
	ret = append(ret, l[:index]...)
	return append(ret, l[index+1:]...)
}

func getDataFromOperationLog(l []Operation) uint64 {
	if len(l) > 0 {
		return l[len(l)-1].Data
	}
	return 0
}

func receiveGossip(server Server, request Message) Server {
	if len(request.S2S_Gossip_Operations) == 0 {
		return server
	}

	var s = server
	var i = uint64(0)

	for i < uint64(len(request.S2S_Gossip_Operations)) {
		if oneOffVersionVector(s.VectorClock, request.S2S_Gossip_Operations[i].VersionVector) {
			s.OperationsPerformed = sortedInsert(s.OperationsPerformed, request.S2S_Gossip_Operations[i])
			s.VectorClock = maxTS(s.VectorClock, request.S2S_Gossip_Operations[i].VersionVector)
		} else if !compareVersionVector(s.VectorClock, request.S2S_Gossip_Operations[i].VersionVector) {
			s.PendingOperations = sortedInsert(s.PendingOperations, request.S2S_Gossip_Operations[i])
		}
		i++
	}

	i = uint64(0)
	var seen = make([]uint64, 0)
	for i < uint64(len(s.PendingOperations)) {
		if oneOffVersionVector(s.VectorClock, s.PendingOperations[i].VersionVector) {
			s.OperationsPerformed = sortedInsert(s.OperationsPerformed, s.PendingOperations[i])
			s.VectorClock = maxTS(s.VectorClock, s.PendingOperations[i].VersionVector)
			seen = append(seen, i)
		}
		i++
	}

	i = uint64(0)
	var j = uint64(0)
	var output = make([]Operation, 0)
	for i < uint64(len(s.PendingOperations)) {
		if j < uint64(len(seen)) {
			if (i == seen[j]) {
				j++
			} else {
				output = append(output, s.PendingOperations[i])
			}
		} else {
			output = append(output, s.PendingOperations[i])
		}
		i++
	}

	s.PendingOperations = output
	return s
}

func acknowledgeGossip(server Server, request Message) Server {
	if request.S2S_Acknowledge_Gossip_Sending_ServerId >= uint64(len(server.GossipAcknowledgements)) {
		return server
	}
	server.GossipAcknowledgements[request.S2S_Acknowledge_Gossip_Sending_ServerId] = maxTwoInts(server.GossipAcknowledgements[request.S2S_Acknowledge_Gossip_Sending_ServerId], request.S2S_Acknowledge_Gossip_Index)
	return server
}

func getGossipOperations(server Server, serverId uint64) []Operation {
	var ret = make([]Operation, 0)
	if serverId >= uint64(len(server.GossipAcknowledgements)) || (server.GossipAcknowledgements[serverId] >= uint64(len(server.MyOperations))) {
		return ret
	}

	return append(ret, server.MyOperations[server.GossipAcknowledgements[serverId]:]...)
}

func processClientRequest(server Server, request Message) (bool, Server, Message) {
	var reply = Message{}

	if !compareVersionVector(server.VectorClock, request.C2S_Client_VersionVector) {
		return false, server, reply
	}
	
	if request.C2S_Client_OperationType == 0 {
		reply.MessageType = 4
		reply.S2C_Client_OperationType = 0
		reply.S2C_Client_Data = getDataFromOperationLog(server.OperationsPerformed)
		reply.S2C_Client_VersionVector = append(make([]uint64, 0), server.VectorClock...)
		reply.S2C_Server_Id = server.Id
		reply.S2C_Client_Number = request.C2S_Client_Id

		return true, server, reply
	} else {
	    var s = server

		var guard = uint64(18446744073709551613) // 2^64 - 3
		if !(uint64(s.VectorClock[s.Id]) <= guard) {
			return false, s, reply
		}
		if !(uint64(len(s.MyOperations)) <= guard) {
			return false, s, reply
		}

		s.VectorClock[s.Id] += 1

		s.OperationsPerformed = sortedInsert(s.OperationsPerformed, Operation{
			VersionVector: append(make([]uint64, 0), s.VectorClock...),
			Data:          request.C2S_Client_Data,
		})

		s.MyOperations = sortedInsert(s.MyOperations, Operation{
			VersionVector: append(make([]uint64, 0), s.VectorClock...),
			Data:          request.C2S_Client_Data,
		})

		reply.MessageType = 4
		reply.S2C_Client_OperationType = 1
		reply.S2C_Client_Data = 0
		reply.S2C_Client_VersionVector = append(make([]uint64, 0), s.VectorClock...)
		reply.S2C_Server_Id = s.Id
		reply.S2C_Client_Number = request.C2S_Client_Id

		return true, s, reply
	}
}

func processRequest(server Server, request Message) (Server, []Message) {
	var outGoingRequests = make([]Message, 0)
	var s = server
	if request.MessageType == 0 {
		var succeeded = false
		var reply = Message{}
		succeeded, s, reply = processClientRequest(s, request)
		if succeeded {
			outGoingRequests = append(outGoingRequests, reply)
		} else {
			s.UnsatisfiedRequests = append(s.UnsatisfiedRequests, request)
		}
	} else if request.MessageType == 1 {
		s = receiveGossip(s, request)

		var i = uint64(0)
		var reply = Message{}
		var succeeded = false

		for i < uint64(len(s.UnsatisfiedRequests)) {
			succeeded, s, reply = processClientRequest(s, s.UnsatisfiedRequests[i])
			if succeeded {
				outGoingRequests = append(outGoingRequests, reply)
				s.UnsatisfiedRequests = deleteAtIndexMessage(s.UnsatisfiedRequests, i)
				continue
			}
			i++
		}

	} else if request.MessageType == 2 {
		s = acknowledgeGossip(s, request)
	} else if request.MessageType == 3 {
		var i = uint64(0)
		for i < server.NumberOfServers {
			if uint64(i) != uint64(s.Id) {
				index := uint64(i)
				operations := getGossipOperations(s, index)
				if uint64(len(operations)) != uint64(0) {
					s.GossipAcknowledgements[index] = uint64(len(s.MyOperations))
					
					outGoingRequests = append(outGoingRequests,
						Message{MessageType: 1,
							S2S_Gossip_Sending_ServerId:   s.Id,
							S2S_Gossip_Receiving_ServerId: index,
							S2S_Gossip_Operations:         operations,
							S2S_Gossip_Index:              uint64(len(s.MyOperations)),
						})
				}
			}
			i++
		}
	}

	return s, outGoingRequests
}
