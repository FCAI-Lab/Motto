From Perennial.program_proof.session Require Export session_prelude.

#[local] Tactic Notation "tac_val_t" :=
  let val := lazymatch goal with [ |- val_ty (?val _) _ ] => val end in
  lazymatch goal with [ v : tuple_of ?tv |- _ ] =>
    unfold tuple_of in v; unfold tv in v; simpl in v; unfold val; simpl SessionPrelude.value_of; repeat constructor; auto
  end.

#[local] Tactic Notation "tac_IntoVal" integer( n ) :=
  intros;
  lazymatch goal with [ v : tuple_of ?tv |- _ ] =>
    unfold tuple_of in v; unfold tv in v; simpl in v; simpl SessionPrelude.value_of;
    do n destruct v as [v ?]; simpl
  end;
  repeat lazymatch goal with [ t : Slice.t |- _ ] => destruct t end; auto.

Definition value_bound (a: Z) : u64 -> Prop :=
  fun u: u64 => a >= 1 /\ uint.Z u ≤ 2 ^ 64 - a.

Module Operation.

  Definition tv : TypeVector.t 2 :=
    [Slice.t,u64].

  Definition from_val (v: val) : option (tuple_of tv) :=
    match v with
    | (slice_v, (#(LitInt d), #()))%V =>
      match slice_IntoVal.(from_val) slice_v with
      | Some s => Some (s, d)
      | None => None
      end
    | _ => None
    end.

  Definition val (v: tuple_of tv) : val :=
    SessionPrelude.value_of v.

  #[projections(primitive)]
  Record t : Type := mk
    { VersionVector: list u64
    ; Data:          u64
    }.

  Definition size_of (object: t) : nat :=
    length object.(VersionVector).

  Definition value_bound (a: Z) (object: t) : Prop :=
    Forall (value_bound a) object.(VersionVector).

End Operation.

Module Message.

  Definition tv : TypeVector.t 18 :=
    [u64,u64,u64,u64,u64,Slice.t,u64,u64,Slice.t,u64,u64,u64,u64,u64,u64,Slice.t,u64,u64].

  Definition from_val (v: val) : option (tuple_of tv) :=
    match v with
    | (#(LitInt MessageType), (#(LitInt C2S_Client_Id), (#(LitInt C2S_Server_Id), (#(LitInt C2S_Client_OperationType), (#(LitInt C2S_Client_Data), (C2S_Client_VersionVector, (#(LitInt S2S_Gossip_Sending_ServerId), (#(LitInt S2S_Gossip_Receiving_ServerId), (S2S_Gossip_Operations, (#(LitInt S2S_Gossip_Index), (#(LitInt S2S_Acknowledge_Gossip_Sending_ServerId), (#(LitInt S2S_Acknowledge_Gossip_Receiving_ServerId), (#(LitInt S2S_Acknowledge_Gossip_Index), (#(LitInt S2C_Client_OperationType), (#(LitInt S2C_Client_Data), (S2C_Client_VersionVector, (#(LitInt S2C_Server_Id), (#(LitInt S2C_Client_Number), #()))))))))))))))))))%V =>
      match slice_IntoVal.(from_val) C2S_Client_VersionVector, slice_IntoVal.(from_val) S2S_Gossip_Operations, slice_IntoVal.(from_val) S2C_Client_VersionVector with
      | Some s1, Some s2, Some s3 => Some (MessageType, C2S_Client_Id, C2S_Server_Id, C2S_Client_OperationType, C2S_Client_Data, s1, S2S_Gossip_Sending_ServerId, S2S_Gossip_Receiving_ServerId, s2, S2S_Gossip_Index, S2S_Acknowledge_Gossip_Sending_ServerId, S2S_Acknowledge_Gossip_Receiving_ServerId, S2S_Acknowledge_Gossip_Index, S2C_Client_OperationType, S2C_Client_Data, s3, S2C_Server_Id, S2C_Client_Number)
      | _, _, _ => None
      end
    | _ => None
    end.

  Definition val (v: tuple_of tv) : val :=
    SessionPrelude.value_of v.

  #[projections(primitive)]
  Record t : Type := mk
    { MessageType:  u64

    ; C2S_Client_Id:            u64
    ; C2S_Server_Id:            u64
    ; C2S_Client_OperationType: u64
    ; C2S_Client_Data:          u64
    ; C2S_Client_VersionVector: list u64

    ; S2S_Gossip_Sending_ServerId:   u64
    ; S2S_Gossip_Receiving_ServerId: u64
    ; S2S_Gossip_Operations:         list Operation.t
    ; S2S_Gossip_Index:              u64

    ; S2S_Acknowledge_Gossip_Sending_ServerId:   u64
    ; S2S_Acknowledge_Gossip_Receiving_ServerId: u64
    ; S2S_Acknowledge_Gossip_Index:              u64

    ; S2C_Client_OperationType: u64
    ; S2C_Client_Data:          u64
    ; S2C_Client_VersionVector: list u64
    ; S2C_Server_Id:            u64
    ; S2C_Client_Number:        u64
    }.

  Definition size_of (object: t) : nat * nat :=
    (length object.(C2S_Client_VersionVector), length object.(S2C_Client_VersionVector)).

  Definition value_bound (a: Z) (object: t) : Prop.
    (* TODO *)
  Admitted.

End Message.

Module Server.

  Definition tv : TypeVector.t 8 :=
    [u64,u64,Slice.t,Slice.t,Slice.t,Slice.t,Slice.t,Slice.t].

  Definition from_val (v: val) : option (tuple_of tv) :=
    match v with
    | (#(LitInt Id), (#(LitInt NumberOfServers), (UnsatisfiedRequests, (VectorClock, (OperationsPerformed, (MyOperations, (PendingOperations, (GossipAcknowledgements, #()))))))))%V =>
      match slice_IntoVal.(from_val) UnsatisfiedRequests, slice_IntoVal.(from_val) VectorClock, slice_IntoVal.(from_val) OperationsPerformed, slice_IntoVal.(from_val) MyOperations, slice_IntoVal.(from_val) PendingOperations, slice_IntoVal.(from_val) GossipAcknowledgements with
      | Some s1, Some s2, Some s3, Some s4, Some s5, Some s6 => Some (Id, NumberOfServers, s1, s2, s3, s4, s5, s6)
      | _, _, _, _, _, _ => None
      end
    | _ => None
    end.

  Definition val (v: tuple_of tv) : val :=
    SessionPrelude.value_of v.

  #[projections(primitive)]
  Record t : Type := mk
    { Id:                     u64
    ; NumberOfServers:        u64
    ; UnsatisfiedRequests:    list Message.t
    ; VectorClock:            list u64
    ; OperationsPerformed:    list Operation.t
    ; MyOperations:           list Operation.t
    ; PendingOperations:      list Operation.t
    ; GossipAcknowledgements: list u64
    }.

  Definition size_of (object: t) : nat * nat * nat * nat * nat :=
    (length object.(VectorClock), length object.(OperationsPerformed), length object.(MyOperations), length object.(PendingOperations), length object.(GossipAcknowledgements)).

  Definition value_bound (a: Z) (object: t) : Prop.
    (* TODO *)
  Admitted.

End Server.

Module Client.

  Definition tv : TypeVector.t 5 :=
    [u64,u64,Slice.t,Slice.t,u64].

  Definition from_val (v: val) : option (tuple_of tv) :=
    match v with
    | (#(LitInt Id), (#(LitInt NumberOfServers), (WriteVersionVector, (ReadVersionVector, (#(LitInt SessionSemantic), #())))))%V =>
      match slice_IntoVal.(from_val) WriteVersionVector, slice_IntoVal.(from_val) ReadVersionVector with
      | Some s1, Some s2 => Some (Id, NumberOfServers, s1, s2, SessionSemantic)
      | _, _ => None
      end
    | _ => None
    end.

  Definition val (v: tuple_of tv) : val :=
    SessionPrelude.value_of v.

  #[projections(primitive)]
  Record t : Type := mk
    { Id:                 u64
    ; NumberOfServers:    u64
    ; WriteVersionVector: list u64
    ; ReadVersionVector:  list u64
    ; SessionSemantic:    u64
    }.

  Definition size_of (object: t) : nat * nat :=
    (length object.(WriteVersionVector), length object.(ReadVersionVector)).

  Definition value_bound (a: Z) (object: t) : Prop.
    (* TODO *)
  Admitted.

End Client.

Module ServerSide.

  Include SessionServer.

  Theorem Operation_val_t v
    : val_ty (Operation.val v) (struct.t Operation).
  Proof.
    tac_val_t.
  Qed.

  #[global] Hint Resolve Operation_val_t : typeclasses_hints.

  #[global]
  Instance Operation_IntoVal
    : IntoVal (tuple_of Operation.tv).
  Proof.
    refine (
      {|
        to_val := Operation.val;
        from_val := Operation.from_val;
        IntoVal_def := (IntoVal_def Slice.t, W64 0);
      |}
    ).
    tac_IntoVal 1.
  Defined.

  Theorem Message_val_t v
    : val_ty (Message.val v) (struct.t Message).
  Proof.
    tac_val_t.
  Qed.

  #[global] Hint Resolve Message_val_t : typeclasses_hints.

  #[global]
  Instance Message_IntoVal
    : IntoVal (tuple_of Message.tv).
  Proof.
    refine (
      {|
        to_val := Message.val;
        from_val := Message.from_val;
        IntoVal_def := (W64 0, W64 0, W64 0, W64 0, W64 0, IntoVal_def Slice.t, W64 0, W64 0, IntoVal_def Slice.t, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, IntoVal_def Slice.t, W64 0, W64 0);
      |}
    ).
    tac_IntoVal 17.
  Defined.

  Theorem Server_val_t v
    : val_ty (Server.val v) (struct.t Server).
  Proof.
    tac_val_t.
  Qed.

  #[global] Hint Resolve Server_val_t : typeclasses_hints.

  #[global]
  Instance Server_IntoVal
    : IntoVal (tuple_of Server.tv).
  Proof.
    refine (
      {|
        to_val := Server.val;
        from_val := Server.from_val;
        IntoVal_def := (W64 0, W64 0, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t);
      |}
    ).
    tac_IntoVal 8.
  Defined.

  Section heap.

    Context `{hG: !heapGS Σ}.

    Definition is_good_operation (v: tuple_of Operation.tv) (object: Operation.t) (n: nat) : iProp Σ :=
      own_slice_small v!(0) uint64T DfracDiscarded object.(Operation.VersionVector) ∗
      ⌜v!(1) = object.(Operation.Data)⌝ ∗
      ⌜Operation.size_of object = n⌝.

    Definition is_good_slice_of_operations (s: Slice.t) (objects: list Operation.t) (n: nat) : iProp Σ :=
      ∃ vs, own_slice s (struct.t Operation) (DfracOwn 1) vs ∗ [∗ list] v;o ∈ vs;objects, is_good_operation v o n.

    Definition is_good_message (v: tuple_of Message.tv) (object: Message.t) (n: nat) (len_c2s: nat) (len_s2c: nat) : iProp Σ :=
      ⌜v!(0) = object.(Message.MessageType)⌝ ∗
      ⌜v!(1) = object.(Message.C2S_Client_Id)⌝ ∗
      ⌜v!(2) = object.(Message.C2S_Server_Id)⌝ ∗
      ⌜v!(3) = object.(Message.C2S_Client_OperationType)⌝ ∗
      ⌜v!(4) = object.(Message.C2S_Client_Data)⌝ ∗
      own_slice_small v!(5) uint64T (DfracOwn 1) object.(Message.C2S_Client_VersionVector) ∗
      ⌜len_c2s = length object.(Message.C2S_Client_VersionVector)⌝ ∗
      ⌜v!(6) = object.(Message.S2S_Gossip_Sending_ServerId)⌝ ∗
      ⌜v!(7) = object.(Message.S2S_Gossip_Receiving_ServerId)⌝ ∗
      is_good_slice_of_operations v!(8) object.(Message.S2S_Gossip_Operations) n ∗
      ⌜v!(9) = object.(Message.S2S_Gossip_Index)⌝ ∗
      ⌜v!(10) = object.(Message.S2S_Acknowledge_Gossip_Sending_ServerId)⌝ ∗
      ⌜v!(11) = object.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId)⌝ ∗
      ⌜v!(12) = object.(Message.S2S_Acknowledge_Gossip_Index)⌝ ∗
      ⌜v!(13) = object.(Message.S2C_Client_OperationType)⌝ ∗
      ⌜v!(14) = object.(Message.S2C_Client_Data)⌝ ∗
      own_slice_small v!(15) uint64T (DfracOwn 1) object.(Message.S2C_Client_VersionVector) ∗
      ⌜v!(16) = object.(Message.S2C_Server_Id)⌝ ∗
      ⌜v!(17) = object.(Message.S2C_Client_Number)⌝ ∗
      ⌜Message.size_of object = (len_c2s, len_s2c)⌝.

    Definition is_good_slice_of_messages (s: Slice.t) (objects: list Message.t) (n: nat) (len_c2s: nat) : iProp Σ :=
      ∃ vs, own_slice s (struct.t Message) (DfracOwn 1) vs ∗ [∗ list] v;o ∈ vs;objects, ∃ len_s2c : nat, is_good_message v o n len_c2s len_s2c.

    Definition is_good_server' {OWN_UnsatisfiedRequests: bool} (v: tuple_of Server.tv) (object: Server.t) (n: nat) (len_vc: nat) (len_op: nat) (len_mo: nat) (len_po: nat) (len_ga: nat) : iProp Σ :=
      ⌜v!(0) = object.(Server.Id)⌝ ∗
      ⌜v!(1) = object.(Server.NumberOfServers)⌝ ∗
      (if OWN_UnsatisfiedRequests then is_good_slice_of_messages v!(2) object.(Server.UnsatisfiedRequests) n len_vc else emp)%I ∗
      own_slice_small v!(3) uint64T (DfracOwn 1) object.(Server.VectorClock) ∗
      is_good_slice_of_operations v!(4) object.(Server.OperationsPerformed) len_op ∗
      is_good_slice_of_operations v!(5) object.(Server.MyOperations) len_mo ∗
      is_good_slice_of_operations v!(6) object.(Server.PendingOperations) len_po ∗
      own_slice_small v!(7) uint64T (DfracOwn 1) object.(Server.GossipAcknowledgements) ∗
      ⌜Server.size_of object = (len_vc, len_op, len_mo, len_po, len_ga)⌝.

    Definition is_good_server :=
      is_good_server' (OWN_UnsatisfiedRequests := true).

  End heap.

  Section Coq_nat.

    (* TODO *)

  End Coq_nat.

End ServerSide.

Module ClientSide.

  Include SessionClient.

  Theorem Operation_val_t v
    : val_ty (Operation.val v) (struct.t Operation).
  Proof.
    exact (ServerSide.Operation_val_t v).
  Defined.

  #[global] Hint Resolve Operation_val_t : typeclasses_hints.

  #[global]
  Instance Operation_IntoVal
    : IntoVal (tuple_of Operation.tv).
  Proof.
    exact (ServerSide.Operation_IntoVal).
  Defined.

  Theorem Message_val_t v
    : val_ty (Message.val v) (struct.t Message).
  Proof.
    exact (ServerSide.Message_val_t v).
  Defined.

  #[global] Hint Resolve Message_val_t : typeclasses_hints.

  #[global]
  Instance Message_IntoVal
    : IntoVal (tuple_of Message.tv).
  Proof.
    exact (ServerSide.Message_IntoVal).
  Defined.

  Theorem Client_val_t v
    : val_ty (Client.val v) (struct.t Client).
  Proof.
    tac_val_t.
  Defined.

  #[global] Hint Resolve Client_val_t : typeclasses_hints.

  #[global]
  Instance Client_IntoVal
    : IntoVal (tuple_of Client.tv).
  Proof.
    refine (
      {|
        to_val := Client.val;
        from_val := Client.from_val;
        IntoVal_def := (W64 0, W64 0, IntoVal_def Slice.t, IntoVal_def Slice.t, W64 0);
      |}
    ).
    tac_IntoVal 4.
  Defined.

  Section heap.

    Context `{hG: !heapGS Σ}.

    Definition is_good_operation :=
      ServerSide.is_good_operation.

    Definition is_good_slice_of_operations :=
      ServerSide.is_good_slice_of_operations.

    Definition is_good_message :=
      ServerSide.is_good_message.

    Definition is_good_slice_of_messages :=
      ServerSide.is_good_slice_of_messages.

    Definition is_good_client (v: tuple_of Client.tv) (object: Client.t) (n: nat) : iProp Σ :=
      ⌜v!(0) = object.(Client.Id)⌝ ∗
      ⌜v!(1) = object.(Client.NumberOfServers)⌝ ∗
      own_slice_small v!(2) uint64T (DfracOwn 1) object.(Client.WriteVersionVector) ∗
      own_slice_small v!(3) uint64T (DfracOwn 1) object.(Client.ReadVersionVector) ∗
      ⌜v!(4) = object.(Client.SessionSemantic)⌝ ∗
      ⌜(Client.size_of object, uint.nat object.(Client.NumberOfServers)) = (n, n, n)⌝.

  End heap.

  Section Coq_nat.

    (* TODO *)

  End Coq_nat.

End ClientSide.

Section heap.

  Import ServerSide.

  Context `{hG: !heapGS Σ}.

  (* TODO *)

End heap.
