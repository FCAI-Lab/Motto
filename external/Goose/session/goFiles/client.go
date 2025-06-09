package client

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

type Client struct {
	Id                 uint64
	NumberOfServers    uint64
	WriteVersionVector []uint64
	ReadVersionVector  []uint64
	SessionSemantic    uint64
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
		i += 1
	}
	return output
}

func read(client Client, serverId uint64) Message {
	var reply = Message{}
	if client.SessionSemantic == 0 || client.SessionSemantic == 1 || client.SessionSemantic == 2 { // Eventual WFR MW
		reply.MessageType = 0
		reply.C2S_Client_Id = client.Id
		reply.C2S_Client_OperationType = 0
		reply.C2S_Client_Data = 0
		reply.C2S_Server_Id = serverId
		reply.C2S_Client_VersionVector = make([]uint64, client.NumberOfServers)
	} else if client.SessionSemantic == 3 { // MR
		reply.MessageType = 0
		reply.C2S_Client_Id = client.Id
		reply.C2S_Client_OperationType = 0
		reply.C2S_Client_Data = 0
		reply.C2S_Server_Id = serverId
		reply.C2S_Client_VersionVector = append(make([]uint64, 0), client.ReadVersionVector...)
	} else if client.SessionSemantic == 4 { // RYW
		reply.MessageType = 0
		reply.C2S_Client_Id = client.Id
		reply.C2S_Client_OperationType = 0
		reply.C2S_Client_Data = 0
		reply.C2S_Server_Id = serverId
		reply.C2S_Client_VersionVector = append(make([]uint64, 0), client.WriteVersionVector...)
	} else if client.SessionSemantic == 5 { // Causal
		reply.MessageType = 0
		reply.C2S_Client_Id = client.Id
		reply.C2S_Client_OperationType = 0
		reply.C2S_Client_Data = 0
		reply.C2S_Server_Id = serverId
		reply.C2S_Client_VersionVector = maxTS(client.WriteVersionVector, client.ReadVersionVector)
	}

	return reply
}

func write(client Client, serverId uint64, value uint64) Message {
	var reply = Message{}
	if client.SessionSemantic == 0 || client.SessionSemantic == 3 || client.SessionSemantic == 4 { // Eventual MR RYW
		reply.MessageType = 0
		reply.C2S_Client_Id = client.Id
		reply.C2S_Client_OperationType = 1
		reply.C2S_Client_Data = value
		reply.C2S_Server_Id = serverId
		reply.C2S_Client_VersionVector = make([]uint64, client.NumberOfServers)
	} else if client.SessionSemantic == 1 { // WFR
		reply.MessageType = 0
		reply.C2S_Client_Id = client.Id
		reply.C2S_Client_OperationType = 1
		reply.C2S_Client_Data = value
		reply.C2S_Server_Id = serverId
		reply.C2S_Client_VersionVector = append(make([]uint64, 0), client.ReadVersionVector...)
	} else if client.SessionSemantic == 2 { // MW
		reply.MessageType = 0
		reply.C2S_Client_Id = client.Id
		reply.C2S_Client_OperationType = 1
		reply.C2S_Client_Data = value
		reply.C2S_Server_Id = serverId
		reply.C2S_Client_VersionVector =  append(make([]uint64, 0), client.WriteVersionVector...)
	} else if client.SessionSemantic == 5 { // Causal
		reply.MessageType = 0
		reply.C2S_Client_Id = client.Id
		reply.C2S_Client_OperationType = 1
		reply.C2S_Client_Data = value
		reply.C2S_Server_Id = serverId
		reply.C2S_Client_VersionVector = maxTS(client.WriteVersionVector, client.ReadVersionVector)
	}

	return reply
}

func processRequest(client Client, requestType uint64, serverId uint64, value uint64, ackMessage Message) (Client, Message) {
	var nc Client = Client{Id: client.Id,
		NumberOfServers:    client.NumberOfServers,
		WriteVersionVector: client.WriteVersionVector,
		ReadVersionVector:  client.ReadVersionVector,
		SessionSemantic:    client.SessionSemantic}
	var msg = Message{}
	if requestType == 0 {
		msg = read(client, serverId)
	} else if requestType == 1 {
		msg = write(client, serverId, value)
	} else if requestType == 2 {
		if ackMessage.S2C_Client_OperationType == 0 {
			nc.ReadVersionVector = append(make([]uint64, 0), ackMessage.S2C_Client_VersionVector...)
		}
		if ackMessage.S2C_Client_OperationType == 1 {
			nc.WriteVersionVector = append(make([]uint64, 0), ackMessage.S2C_Client_VersionVector...)
		}
	}

	return nc, msg
}
