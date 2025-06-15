From Perennial.program_proof.session Require Export session_prelude.
From Goose.session Require server client.

Module SessionServer := Goose.session.server.

Module SessionClient := Goose.session.client.

Definition CONSTANT : Z :=
  2 ^ 64 - 2.

Lemma CONSTANT_unfold
  : CONSTANT = 2 ^ 64 - 2.
Proof.
  reflexivity.
Qed.

Lemma CONSTANT_minus_1
  : CONSTANT - 1 = 18446744073709551613.
Proof.
  reflexivity.
Qed.

Definition nat_le_CONSTANT (n : nat) : Prop :=
  Z.of_nat n <= CONSTANT.

Definition u64_le_CONSTANT (u : u64) : Prop :=
  uint.Z u <= CONSTANT.

Lemma CONSTANT_ge_0
  : u64_le_CONSTANT (W64 0).
Proof.
  red; unfold CONSTANT. word.
Qed.

#[global] Opaque CONSTANT.

#[global] Tactic Notation "word" :=
  lazymatch goal with
  | [ hG : heapGS ?Σ |- _ ] => let con := fresh "_c" in Tac.revert_until hG; unfold u64_le_CONSTANT; generalize CONSTANT as con; intros; word
  | _ => word
  end.

Module _Data.

  Definition w : Type :=
    u64.

  #[global] Instance has_value_of_Data : SessionPrelude.has_value_of w :=
    SessionPrelude.u64_has_value_of.

  Definition ty : ty :=
    uint64T.

  Theorem val_ty v
    : val_ty (SessionPrelude.u64_has_value_of v) _Data.ty.
  Proof.
    econstructor; auto.
  Qed.

  #[global] Hint Resolve _Data.val_ty : typeclasses_hints.

  #[global]
  Instance IntoVal : IntoVal _Data.w :=
    u64_IntoVal.

End _Data.

#[global] Tactic Notation "tac_val_ty" :=
  let val := lazymatch goal with [ |- val_ty (?val _) _ ] => val end in
  lazymatch goal with [ v : tuple_of ?tv |- _ ] => unfold tuple_of in v; unfold tv in v; simpl in v; unfold val; simpl end;
  repeat constructor; ss!.

#[global] Tactic Notation "tac_IntoVal" integer( n ) :=
  intros;
  lazymatch goal with [ v : tuple_of ?tv |- _ ] => unfold tuple_of in v; unfold tv in v; simpl in v; simpl SessionPrelude.value_of; do n destruct v as [v ?]; simpl end;
  repeat lazymatch goal with [ t : Slice.t |- _ ] => destruct t end; auto.

#[global] Tactic Notation "tac_IntoValForType" :=
  let tv := lazymatch goal with [ |- IntoValForType (tuple_of ?tv) _ ] => tv end in
  unfold tuple_of, tv, _Data.w; simpl; repeat split; ss!.

Module Operation.

  Definition tv : TypeVector.t 2 :=
    [Slice.t,_Data.w].

  Definition from_val (v: val) : option (tuple_of tv) :=
    match v with
    | (VersionVector, (Data, #()))%V =>
      match slice_IntoVal.(from_val) VersionVector, _Data.IntoVal.(from_val) Data with
      | Some s1, Some d1 => Some (s1, d1)
      | _, _ => None
      end
    | _ => None
    end.

  Definition val (v: tuple_of tv) : val :=
    SessionPrelude.value_of v.

  Record t : Type := mk
    { VersionVector: list u64
    ; Data:          _Data.w
    }.

  #[global, program]
  Instance IntoVal : IntoVal (tuple_of tv) :=
    { to_val := val
    ; from_val := from_val
    ; IntoVal_def := (IntoVal_def Slice.t, IntoVal_def _Data.w)
    }.
  Next Obligation.
    tac_IntoVal 1.
  Defined.

  Theorem val_t v
    : val_ty (Operation.val v) (struct.t SessionServer.Operation).
  Proof.
    tac_val_ty.
  Qed.

  #[global] Hint Resolve val_t : session_hints.

  #[global] Instance Session_IntoValForType
    : IntoValForType (tuple_of tv) (struct.t SessionServer.Operation).
  Proof.
    tac_IntoValForType.
  Qed.

  #[global] Instance Client_IntoValForType
    : IntoValForType (tuple_of tv) (struct.t SessionClient.Operation).
  Proof.
    tac_IntoValForType.
  Qed.

  Section ADD_ON.

  Section HASKELLISH_INSTANCES.

  Definition getVersionVector (op: Operation.t) : list u64 :=
    op.(VersionVector).

  Definition well_formed (n: nat) (op: Operation.t) : Prop :=
    Forall (fun _ :  u64 => True) op.(VersionVector) /\ length op.(VersionVector) = n.

  #[global]
  Instance hsEq (n: nat) : SessionPrelude.hsEq (Operation.t) (well_formed := well_formed n) :=
    SessionPrelude.hsEq_preimage getVersionVector.

  #[global]
  Instance hsOrd (n: nat) : SessionPrelude.hsOrd (Operation.t) (well_formed := well_formed n) :=
    SessionPrelude.hsOrd_preimage getVersionVector.

  End HASKELLISH_INSTANCES.

  Definition size_of (op: Operation.t) : nat :=
    length op.(VersionVector).

  Definition value_bound (op: Operation.t) : Prop :=
    Forall u64_le_CONSTANT op.(Operation.VersionVector).

  End ADD_ON.

End Operation.

#[global] Hint Unfold Operation.size_of : session_hints.
#[global] Hint Unfold Operation.value_bound : session_hints.

Module Message.

  Definition tv : TypeVector.t 18 :=
    [u64,u64,u64,u64,_Data.w,Slice.t,u64,u64,Slice.t,u64,u64,u64,u64,u64,_Data.w,Slice.t,u64,u64].

  Definition from_val (v: val) : option (tuple_of tv) :=
    match v with
    | (#(LitInt MessageType), (#(LitInt C2S_Client_Id), (#(LitInt C2S_Server_Id), (#(LitInt C2S_Client_OperationType), (C2S_Client_Data, (C2S_Client_VersionVector, (#(LitInt S2S_Gossip_Sending_ServerId), (#(LitInt S2S_Gossip_Receiving_ServerId), (S2S_Gossip_Operations, (#(LitInt S2S_Gossip_Index), (#(LitInt S2S_Acknowledge_Gossip_Sending_ServerId), (#(LitInt S2S_Acknowledge_Gossip_Receiving_ServerId), (#(LitInt S2S_Acknowledge_Gossip_Index), (#(LitInt S2C_Client_OperationType), (S2C_Client_Data, (S2C_Client_VersionVector, (#(LitInt S2C_Server_Id), (#(LitInt S2C_Client_Number), #()))))))))))))))))))%V =>
      match slice_IntoVal.(from_val) C2S_Client_VersionVector, slice_IntoVal.(from_val) S2S_Gossip_Operations, slice_IntoVal.(from_val) S2C_Client_VersionVector, _Data.IntoVal.(from_val) C2S_Client_Data, _Data.IntoVal.(from_val) S2C_Client_Data with
      | Some s1, Some s2, Some s3, Some d1, Some d2 => Some (MessageType, C2S_Client_Id, C2S_Server_Id, C2S_Client_OperationType, d1, s1, S2S_Gossip_Sending_ServerId, S2S_Gossip_Receiving_ServerId, s2, S2S_Gossip_Index, S2S_Acknowledge_Gossip_Sending_ServerId, S2S_Acknowledge_Gossip_Receiving_ServerId, S2S_Acknowledge_Gossip_Index, S2C_Client_OperationType, d2, s3, S2C_Server_Id, S2C_Client_Number)
      | _, _, _, _, _ => None
      end
    | _ => None
    end.

  Definition val (v: tuple_of tv) : val :=
    tuple_of_has_value_of tv v.

  Record t : Type := mk
    { MessageType:  u64

    ; C2S_Client_Id:            u64
    ; C2S_Server_Id:            u64
    ; C2S_Client_OperationType: u64
    ; C2S_Client_Data:          _Data.w
    ; C2S_Client_VersionVector: list u64

    ; S2S_Gossip_Sending_ServerId:   u64
    ; S2S_Gossip_Receiving_ServerId: u64
    ; S2S_Gossip_Operations:         list Operation.t
    ; S2S_Gossip_Index:              u64

    ; S2S_Acknowledge_Gossip_Sending_ServerId:   u64
    ; S2S_Acknowledge_Gossip_Receiving_ServerId: u64
    ; S2S_Acknowledge_Gossip_Index:              u64

    ; S2C_Client_OperationType: u64
    ; S2C_Client_Data:          _Data.w
    ; S2C_Client_VersionVector: list u64
    ; S2C_Server_Id:            u64
    ; S2C_Client_Number:        u64
    }.

  #[global, program]
  Instance IntoVal : IntoVal (tuple_of tv) :=
    { to_val := val
    ; from_val := from_val
    ; IntoVal_def := (W64 0, W64 0, W64 0, W64 0, IntoVal_def _Data.w, IntoVal_def Slice.t, W64 0, W64 0, IntoVal_def Slice.t, W64 0, W64 0, W64 0, W64 0, W64 0, IntoVal_def _Data.w, IntoVal_def Slice.t, W64 0, W64 0);
    }.
  Next Obligation.
    tac_IntoVal 17.
  Defined.

  Theorem val_t v
    : val_ty (Message.val v) (struct.t SessionServer.Message).
  Proof.
    tac_val_ty.
  Qed.

  #[global] Hint Resolve val_t : session_hints.

  #[global] Instance Session_IntoValForType
    : IntoValForType (tuple_of tv) (struct.t SessionServer.Message).
  Proof.
    tac_IntoValForType.
  Qed.

  #[global] Instance Client_IntoValForType
    : IntoValForType (tuple_of tv) (struct.t SessionClient.Message).
  Proof.
    tac_IntoValForType.
  Qed.

  Section ADD_ON.

  Definition size_of (msg: Message.t) : nat * nat :=
    (length msg.(C2S_Client_VersionVector), length msg.(S2C_Client_VersionVector)).

  Definition value_bound (msg: Message.t) : Prop :=
    u64_le_CONSTANT msg.(Message.MessageType) /\ u64_le_CONSTANT msg.(Message.C2S_Client_Id) /\ u64_le_CONSTANT msg.(Message.C2S_Server_Id) /\ u64_le_CONSTANT msg.(Message.C2S_Client_OperationType) /\ Forall u64_le_CONSTANT msg.(Message.C2S_Client_VersionVector) /\ u64_le_CONSTANT msg.(Message.S2S_Gossip_Sending_ServerId) /\ u64_le_CONSTANT msg.(Message.S2S_Gossip_Index) /\ u64_le_CONSTANT msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) /\ u64_le_CONSTANT msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId) /\ u64_le_CONSTANT msg.(Message.S2S_Acknowledge_Gossip_Index) /\ u64_le_CONSTANT msg.(Message.S2C_Client_OperationType) /\ Forall u64_le_CONSTANT msg.(Message.S2C_Client_VersionVector) /\ u64_le_CONSTANT msg.(Message.S2C_Server_Id) /\ u64_le_CONSTANT msg.(Message.S2C_Server_Id).

  End ADD_ON.

End Message.

#[global] Hint Unfold Message.size_of : session_hints.
#[global] Hint Unfold Message.value_bound : session_hints.

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
    tuple_of_has_value_of tv v.

  Record t : Type := mk
    { Id:                     u64
    ; NumberOfServers:        u64
    ; UnsatisfiedRequests:    list (Message.t)
    ; VectorClock:            list u64
    ; OperationsPerformed:    list (Operation.t)
    ; MyOperations:           list (Operation.t)
    ; PendingOperations:      list (Operation.t)
    ; GossipAcknowledgements: list u64
    }.

  #[global, program]
  Instance IntoVal : IntoVal (tuple_of tv) :=
    { to_val := val
    ; from_val := from_val
    ; IntoVal_def := (W64 0, W64 0, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t)
    }.
  Next Obligation.
    tac_IntoVal 7.
  Defined.

  Theorem val_t v
    : val_ty (Server.val v) (struct.t SessionServer.Server).
  Proof.
    tac_val_ty.
  Qed.

  #[global] Hint Resolve val_t : session_hints.

  #[global] Instance Session_IntoValForType
    : IntoValForType (tuple_of tv) (struct.t SessionServer.Server).
  Proof.
    tac_IntoValForType.
  Qed.

  Section ADD_ON.

  Definition size_of (server: Server.t) : nat * nat :=
    (length server.(VectorClock), length server.(GossipAcknowledgements)).

  Definition value_bound (server: Server.t) : Prop :=
    u64_le_CONSTANT server.(Server.Id) /\ u64_le_CONSTANT server.(Server.NumberOfServers) /\ Forall u64_le_CONSTANT server.(Server.VectorClock) /\ Forall u64_le_CONSTANT server.(Server.GossipAcknowledgements).

  End ADD_ON.

End Server.

#[global] Hint Unfold Server.size_of : session_hints.
#[global] Hint Unfold Server.value_bound : session_hints.

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
    tuple_of_has_value_of tv v.

  #[projections(primitive)]
  Record t : Type := mk
    { Id:                 u64
    ; NumberOfServers:    u64
    ; WriteVersionVector: list u64
    ; ReadVersionVector:  list u64
    ; SessionSemantic:    u64
    }.

  #[global, program]
  Instance IntoVal : IntoVal (tuple_of tv) :=
    { to_val := val
    ; from_val := from_val
    ; IntoVal_def := (W64 0, W64 0, IntoVal_def Slice.t, IntoVal_def Slice.t, W64 0);
    }.
  Next Obligation.
    tac_IntoVal 4.
  Defined.

  Theorem val_t v
    : val_ty (Client.val v) (struct.t SessionClient.Client).
  Proof.
    tac_val_ty.
  Qed.

  #[global] Hint Resolve val_t : session_hints.

  #[global] Instance Client_IntoValForType
    : IntoValForType (tuple_of tv) (struct.t SessionClient.Client).
  Proof.
    tac_IntoValForType.
  Qed.

  Section ADD_ON.

  Definition size_of (client: Client.t) : nat * nat :=
    (length client.(WriteVersionVector), length client.(ReadVersionVector)).

  Definition value_bound (client: Client.t) : Prop :=
    u64_le_CONSTANT client.(Client.Id) /\ u64_le_CONSTANT client.(Client.NumberOfServers) /\ Forall u64_le_CONSTANT client.(Client.WriteVersionVector) /\ Forall u64_le_CONSTANT client.(Client.ReadVersionVector).

  End ADD_ON.

End Client.

#[global] Hint Unfold Client.size_of : session_hints.
#[global] Hint Unfold Client.value_bound : session_hints.

Module ServerSide.

  Include SessionServer.

  Section heap.

  Context `{hG: !heapGS Σ}.

  Definition is_operation (v: tuple_of Operation.tv) (op: Operation.t) (n: nat) : iProp Σ :=
    own_slice_small v!(0) uint64T DfracDiscarded op.(Operation.VersionVector) ∗
    ⌜v!(1) = op.(Operation.Data)⌝ ∗
    ⌜Operation.size_of op = n /\ Operation.value_bound op⌝.

  Definition operation_slice (s: Slice.t) (ops: list Operation.t) (n: nat) : iProp Σ :=
    ∃ vs, own_slice s (struct.t Operation) (DfracOwn 1) vs ∗ [∗ list] v;op ∈ vs;ops, is_operation v op n.

  Definition is_message (v: tuple_of Message.tv) (msg: Message.t) (n: nat) (len_c2s: nat) (len_s2c: nat) : iProp Σ :=
    ⌜v!(0) = msg.(Message.MessageType)⌝ ∗
    ⌜v!(1) = msg.(Message.C2S_Client_Id)⌝ ∗
    ⌜v!(2) = msg.(Message.C2S_Server_Id)⌝ ∗
    ⌜v!(3) = msg.(Message.C2S_Client_OperationType)⌝ ∗
    ⌜v!(4) = msg.(Message.C2S_Client_Data)⌝ ∗
    own_slice_small v!(5) uint64T (DfracOwn 1) msg.(Message.C2S_Client_VersionVector) ∗
    ⌜v!(6) = msg.(Message.S2S_Gossip_Sending_ServerId)⌝ ∗
    ⌜v!(7) = msg.(Message.S2S_Gossip_Receiving_ServerId)⌝ ∗
    operation_slice v!(8) msg.(Message.S2S_Gossip_Operations) n ∗
    ⌜v!(9) = msg.(Message.S2S_Gossip_Index)⌝ ∗
    ⌜v!(10) = msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId)⌝ ∗
    ⌜v!(11) = msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId)⌝ ∗
    ⌜v!(12) = msg.(Message.S2S_Acknowledge_Gossip_Index)⌝ ∗
    ⌜v!(13) = msg.(Message.S2C_Client_OperationType)⌝ ∗
    ⌜v!(14) = msg.(Message.S2C_Client_Data)⌝ ∗
    own_slice_small v!(15) uint64T (DfracOwn 1) msg.(Message.S2C_Client_VersionVector) ∗
    ⌜v!(16) = msg.(Message.S2C_Server_Id)⌝ ∗
    ⌜v!(17) = msg.(Message.S2C_Client_Number)⌝ ∗
    ⌜Message.size_of msg = (len_c2s, len_s2c) /\ Message.value_bound msg⌝.

  Definition message_slice (s: Slice.t) (msgs: list Message.t) (n: nat) (len_c2s: nat) : iProp Σ :=
    ∃ vs, own_slice s (struct.t server.Message) (DfracOwn 1) vs ∗ [∗ list] v;msg ∈ vs;msgs, ∃ len_s2c : nat, is_message v msg n len_c2s len_s2c.

  Definition is_server' (v: tuple_of Server.tv) (server: Server.t) (n: nat) (len_vc: nat) (len_op: nat) (len_mo: nat) (len_po: nat) (len_ga: nat) (OWN_UnsatisfiedRequests: bool) : iProp Σ :=
    ⌜v!(0) = server.(Server.Id)⌝ ∗
    ⌜v!(1) = server.(Server.NumberOfServers)⌝ ∗
    (if OWN_UnsatisfiedRequests then message_slice v!(2) server.(Server.UnsatisfiedRequests) n len_vc else emp)%I ∗
    own_slice_small v!(3) uint64T (DfracOwn 1) server.(Server.VectorClock) ∗
    operation_slice v!(4) server.(Server.OperationsPerformed) len_op ∗
    operation_slice v!(5) server.(Server.MyOperations) len_mo ∗
    operation_slice v!(6) server.(Server.PendingOperations) len_po ∗
    own_slice_small v!(7) uint64T (DfracOwn 1) server.(Server.GossipAcknowledgements) ∗
    ⌜Server.size_of server = (len_vc, len_ga) /\ Server.value_bound server⌝.

  Definition is_server sv s n len_vc len_op len_mo len_po len_ga : iProp Σ :=
    is_server' sv s n len_vc len_op len_mo len_po len_ga true.

  End heap.

  Section Coq_u64.

  Fixpoint coq_compareVersionVector (v1: list u64) (v2: list u64) : bool :=
    match v1 with
    | [] => true
    | h1 :: t1 =>
      match v2 with
      | [] => true
      | h2 :: t2 => if uint.Z h1 <? uint.Z h2 then false else coq_compareVersionVector t1 t2
      end
    end.

  Fixpoint coq_lexicographicCompare (v1: list u64) (v2: list u64) : bool :=
    match v1, v2 with
    | [], [] => false
    | [], h2 :: t2 => false
    | h1 :: t1, [] => true
    | h1 :: t1, h2 :: t2 => if uint.Z h1 =? uint.Z h2 then coq_lexicographicCompare t1 t2 else uint.Z h1 >? uint.Z h2
    end.

  Definition coq_maxTwoInts (x: u64) (y: u64) : u64 :=
    if uint.Z x >? uint.Z y then x else y. 

  Fixpoint coq_maxTS (t1: list u64) (t2: list u64) : list u64 :=
    match t1 with
    | [] => []
    | hd1 :: tl1 =>
      match t2 with
      | [] => []
      | hd2 :: tl2 => coq_maxTwoInts hd1 hd2 :: coq_maxTS tl1 tl2
      end
    end.

  Definition coq_oneOffVersionVector (v1: list u64) (v2: list u64) : bool :=
    let loop_step (acc: bool * bool) (element: u64 * u64) : bool * bool :=
      let '(e1, e2) := element in
      let '(output, canApply) := acc in
      if canApply && (uint.Z (w64_word_instance.(word.add) e1 (W64 1)) =? uint.Z e2) then
        (output, false)
      else if uint.Z e1 >=? uint.Z e2 then
        (output, canApply)
      else 
        (false, canApply)
    in
    let '(output, canApply) := fold_left loop_step (zip v1 v2) (true, true) in
    output && negb canApply.

  Fixpoint coq_equalSlices (s1: list u64) (s2: list u64) : bool :=
    match s1, s2 with
    | [], [] => true
    | [], h2 :: t2 => false
    | h1 :: t1, [] => false
    | h1 :: t1, h2 :: t2 => (uint.Z h1 =? uint.Z h2)%Z && coq_equalSlices t1 t2
    end.

  Variant binarySearch_spec (needle: Operation.t) (l: list Operation.t) (n: nat) (RESULT: nat) : Prop :=
    | binarySearch_spec_intro prefix suffix
      (LENGTH: RESULT = length prefix)
      (VECTOR: map Operation.getVersionVector l = if forallb (fun x => negb (coq_equalSlices x.(Operation.VersionVector) needle.(Operation.VersionVector))) l then prefix ++ suffix else prefix ++ [Operation.getVersionVector needle] ++ suffix)
      (PREFIX: ∀ op, In op prefix -> coq_lexicographicCompare needle.(Operation.VersionVector) op = true)
      (SUFFIX: ∀ op, In op suffix -> coq_lexicographicCompare op needle.(Operation.VersionVector) = true)
      : binarySearch_spec needle l n RESULT.

  Fixpoint coq_sortedInsert (l: list Operation.t) (i: Operation.t) : list Operation.t :=
    match l with
    | [] => [i]
    | h :: t =>
      if coq_lexicographicCompare h.(Operation.VersionVector) i.(Operation.VersionVector) then
        i :: h :: t
      else if coq_equalSlices h.(Operation.VersionVector) i.(Operation.VersionVector) then
        h :: t
      else
        h :: coq_sortedInsert t i
    end.

  Definition coq_deleteAtIndexOperation (o: list Operation.t) (index: nat) : list Operation.t :=
    take index o ++ drop (index + 1)%nat o.

  Definition coq_deleteAtIndexMessage (m: list Message.t) (index: nat) : list Message.t :=
    take index m ++ drop (index + 1)%nat m.

  Definition coq_getDataFromOperationLog (l: list Operation.t) : u64 :=
    match last l with
    | Some v => v.(Operation.Data)
    | None => W64 0
    end.

  Definition coq_receiveGossip (server: Server.t) (request: Message.t) : Server.t :=
    if (length request.(Message.S2S_Gossip_Operations) =? 0)%nat then
      server
    else
      let first_loop_output : Server.t :=
        let focus := request.(Message.S2S_Gossip_Operations) in
        let loop_step (acc: Server.t) (elem: Operation.t) : Server.t :=
          let server := acc in
          if coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then
            {|
              Server.Id := server.(Server.Id);
              Server.NumberOfServers := server.(Server.NumberOfServers);
              Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
              Server.VectorClock := coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector);
              Server.OperationsPerformed := coq_sortedInsert server.(Server.OperationsPerformed) elem;
              Server.MyOperations := server.(Server.MyOperations);
              Server.PendingOperations := server.(Server.PendingOperations);
              Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
            |}
          else if negb (coq_compareVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector)) then
            {|
              Server.Id := server.(Server.Id);
              Server.NumberOfServers := server.(Server.NumberOfServers);
              Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
              Server.VectorClock := server.(Server.VectorClock);
              Server.OperationsPerformed := server.(Server.OperationsPerformed);
              Server.MyOperations := server.(Server.MyOperations);
              Server.PendingOperations := coq_sortedInsert server.(Server.PendingOperations) elem;
              Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
            |}
          else
            server
        in
        fold_left loop_step focus server
      in
      let server := first_loop_output in
      let second_loop_output : Server.t * u64 * list u64 :=
        let focus := server.(Server.PendingOperations) in
        let loop_step (acc: Server.t * u64 * list u64) (elem: Operation.t) : Server.t * u64 * list u64 :=
          let '(server, i, seen) := acc in
          if coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then
            (Server.mk server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) (coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector)) (coq_sortedInsert server.(Server.OperationsPerformed) elem) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements), W64 (uint.Z i + 1), seen ++ [i])
          else
            (server, W64 (uint.Z i + 1), seen)
        in
        fold_left loop_step focus (server, W64 0, [])
      in
      let '(server, _, seen) := second_loop_output in
      let third_loop_output : nat * nat * list Operation.t :=
        let focus := server.(Server.PendingOperations) in
        let loop_step (acc: nat * nat * list Operation.t) (elem: Operation.t) : nat * nat * list Operation.t :=
          let '(i, j, output) := acc in
          match seen !! j with
          | Some i' => if (i =? uint.nat i')%nat then ((i + 1)%nat, (j + 1)%nat, output) else ((i + 1)%nat, j, output ++ [elem])
          | None => ((i + 1)%nat, j, output ++ [elem])
          end
        in
        fold_left loop_step focus (0%nat, 0%nat, [])
      in
      let '(_, _, output) := third_loop_output in
      {|
        Server.Id := server.(Server.Id);
        Server.NumberOfServers := server.(Server.NumberOfServers);
        Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
        Server.VectorClock := server.(Server.VectorClock);
        Server.OperationsPerformed := server.(Server.OperationsPerformed);
        Server.MyOperations := server.(Server.MyOperations);
        Server.PendingOperations := output;
        Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
      |}.

  Definition coq_acknowledgeGossip (s: Server.t) (r: Message.t) : Server.t :=
    let i := uint.nat (r.(Message.S2S_Acknowledge_Gossip_Sending_ServerId)) in
    let l := s.(Server.GossipAcknowledgements) in
    if (i >=? length l)%nat then
      s
    else
      let prevGossipAcknowledgementsValue : u64 :=
        match s.(Server.GossipAcknowledgements) !! i with
        | Some x => x
        | None => W64 0
        end
      in
      let newGossipAcknowledgements := coq_maxTwoInts prevGossipAcknowledgementsValue r.(Message.S2S_Acknowledge_Gossip_Index) in
      let gossipAcknowledgements := <[i := newGossipAcknowledgements]> l in
      Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) gossipAcknowledgements.

  Definition coq_getGossipOperations (s: Server.t) (serverId: u64) : list Operation.t :=
    match s.(Server.GossipAcknowledgements) !! uint.nat serverId with
    | Some v => drop (uint.nat v) s.(Server.MyOperations)
    | None => []
    end.

  Definition coq_processClientRequest (s: Server.t) (r: Message.t) : bool * Server.t * Message.t :=
    if negb (coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector)) then
      (false, s, Message.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
    else
      if uint.Z r.(Message.C2S_Client_OperationType) =? 0 then
        let S2C_Client_Data := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
        let S2C_Client_VersionVector := s.(Server.VectorClock) in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server.Id) in
        (true, s, Message.mk 4 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)
      else
        let v := match s.(Server.VectorClock) !! uint.nat s.(Server.Id) with Some v => uint.Z v | None => 0 end in
        if (v <=? CONSTANT - 1)%Z && (length s.(Server.MyOperations) <=? CONSTANT - 1)%Z then
          let VectorClock := <[uint.nat s.(Server.Id) := W64 (v + 1)]> s.(Server.VectorClock) in
          let OperationsPerformed := coq_sortedInsert s.(Server.OperationsPerformed) (Operation.mk VectorClock r.(Message.C2S_Client_Data)) in
          let MyOperations := coq_sortedInsert s.(Server.MyOperations) (Operation.mk VectorClock r.(Message.C2S_Client_Data)) in
          let S2C_Client_OperationType := 1 in
          let S2C_Client_Data := (IntoVal_def _Data.w) in
          let S2C_Client_VersionVector := VectorClock in
          let S2C_Client_Number := r.(Message.C2S_Client_Id) in
          let S2C_Server_Id := s.(Server.Id) in
          (true, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), Message.mk 4 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)
        else
          (false, s, Message.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0).

  Definition coq_processRequest (server: Server.t) (request: Message.t) : Server.t * list Message.t :=
    match uint.nat request.(Message.MessageType) with
    | 0%nat =>
      let '(succeeded, server, reply) := coq_processClientRequest server request in
      if succeeded then
        (server, [reply])
      else
        let UnsatisfiedRequests := server.(Server.UnsatisfiedRequests) ++ [request] in 
        let server := Server.mk server.(Server.Id) server.(Server.NumberOfServers) UnsatisfiedRequests server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements) in
        (server, [])
    | 1%nat =>
      let server := coq_receiveGossip server request in
      let focus := server.(Server.UnsatisfiedRequests) in
      let loop_init : nat * Server.t * list Message.t :=
        (0%nat, server, [])
      in
      let loop_step (acc: nat * Server.t * list Message.t) (element: Message.t) : nat * Server.t * list Message.t :=
        let '(i, s, outGoingRequests) := acc in
        let '(succeeded, s, reply) := coq_processClientRequest s element in
        if succeeded then
          let UnsatisfiedRequests := coq_deleteAtIndexMessage s.(Server.UnsatisfiedRequests) i in
          (i, Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), outGoingRequests ++ [reply])
        else
          ((i + 1)%nat, s, outGoingRequests)
      in
      let '(_, server, outGoingRequests) := fold_left loop_step focus loop_init in
      (server, outGoingRequests)
    | 2%nat => (coq_acknowledgeGossip server request, [])
    | 3%nat =>
      let loop_step (acc: Server.t * list Message.t) (index: u64) : Server.t * list Message.t :=
        let '(server, outGoingRequests) := acc in
        let operations := coq_getGossipOperations server index in
        if negb (uint.nat index =? uint.nat server.(Server.Id))%nat && negb (length operations =? 0)%nat then
          let GossipAcknowledgements := <[uint.nat index := W64 (length server.(Server.MyOperations))]> server.(Server.GossipAcknowledgements) in
          let S2S_Gossip_Sending_ServerId := server.(Server.Id) in
          let S2S_Gossip_Receiving_ServerId := index in
          let S2S_Gossip_Operations := operations in
          let S2S_Gossip_Index := length (server.(Server.MyOperations)) in
          let message := Message.mk 1 0 0 0 (IntoVal_def _Data.w) [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 in
          (Server.mk server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) GossipAcknowledgements, outGoingRequests ++ [message])
        else
          (server, outGoingRequests)
      in
      let nat_to_u64 (i: nat) : u64 :=
        W64 i
      in
      let focus := map nat_to_u64 (seq 0%nat (uint.nat server.(Server.NumberOfServers))) in
      fold_left loop_step focus (server, [])
    | _ => (server, [])
    end.

  End Coq_u64.

End ServerSide.

Module ClientSide.

  Include SessionClient.

  Section heap.

  Context `{hG: !heapGS Σ}.

  Definition is_client (v: tuple_of Client.tv) (client: Client.t) (n: nat) : iProp Σ :=
    ⌜v!(0) = client.(Client.Id)⌝ ∗
    ⌜v!(1) = client.(Client.NumberOfServers)⌝ ∗
    own_slice_small v!(2) uint64T (DfracOwn 1) client.(Client.WriteVersionVector) ∗
    own_slice_small v!(3) uint64T (DfracOwn 1) client.(Client.ReadVersionVector) ∗
    ⌜v!(4) = client.(Client.SessionSemantic)⌝ ∗
    ⌜(Client.size_of client, uint.nat client.(Client.NumberOfServers)) = (n, n, n) /\ Client.value_bound client⌝.

  End heap.

  Section Coq_u64.

  Import ServerSide.

  Definition coq_read (c: Client.t) (serverId: u64) : Message.t :=
    match uint.nat c.(Client.SessionSemantic) with
    | 0%nat => Message.mk 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.w) (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 1%nat => Message.mk 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.w) (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 2%nat => Message.mk 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.w) (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 3%nat => Message.mk 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.w) c.(Client.ReadVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 4%nat => Message.mk 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.w) c.(Client.WriteVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 5%nat => Message.mk 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.w) (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | _ => Message.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    end.

  Definition coq_write (c: Client.t) (serverId: u64) (value: _Data.w) : Message.t :=
    match uint.nat c.(Client.SessionSemantic) with
    | 0%nat => Message.mk 0 c.(Client.Id) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 1%nat => Message.mk 0 c.(Client.Id) serverId 1 value c.(Client.ReadVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 2%nat => Message.mk 0 c.(Client.Id) serverId 1 value c.(Client.WriteVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 3%nat => Message.mk 0 c.(Client.Id) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 4%nat => Message.mk 0 c.(Client.Id) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 5%nat => Message.mk 0 c.(Client.Id) serverId 1 value (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | _ => Message.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    end.

  Definition coq_processRequest (c: Client.t) (requestType: u64) (serverId: u64) (value: _Data.w) (ackMessage: Message.t) : Client.t * Message.t :=
    match uint.nat requestType with
    | 0%nat => (c, coq_read c serverId)
    | 1%nat => (c, coq_write c serverId value)
    | 2%nat =>
      match uint.nat ackMessage.(Message.S2C_Client_OperationType) with
      | 0%nat => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) c.(Client.WriteVersionVector) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
      | 1%nat => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.ReadVersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
      | _ => (c, Message.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
      end
    | _ => (c, Message.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
    end.

  End Coq_u64.

End ClientSide.

Section properties.

Import ServerSide SessionPrelude.

Lemma Forall_CONSTANT_replicate n
  : Forall u64_le_CONSTANT (replicate n (W64 0)).
Proof.
  induction n as [ | n IH]; simpl; econstructor; eauto. eapply CONSTANT_ge_0.
Qed.

Lemma CONSTANT_coq_maxTs xs ys
  (H_xs : Forall u64_le_CONSTANT xs)
  (H_ys : Forall u64_le_CONSTANT ys)
  : Forall u64_le_CONSTANT (coq_maxTS xs ys).
Proof.
  revert ys H_ys; induction H_xs as [ | x xs H_x H_xs IH]; intros ys H_ys; destruct H_ys as [ | y ys H_y H_ys]; simpl in *; try congruence; econstructor; simpl; eauto.
  unfold coq_maxTwoInts. red in H_x, H_y |- *. rewrite -> CONSTANT_unfold in *. rewrite Z.gtb_ltb. destruct (_ <? _) as [ | ] eqn: H_OBS; [rewrite Z.ltb_lt in H_OBS | rewrite Z.ltb_nlt in H_OBS]; word.
Qed.

Lemma redefine_coq_lexicographicCompare :
  coq_lexicographicCompare = vectorGt.
Proof.
  reflexivity.
Defined.

Lemma redefine_coq_equalSlices :
  coq_equalSlices = vectorEq.
Proof.
  reflexivity.
Defined.

Lemma redefine_coq_sortedInsert (n : nat) :
  coq_sortedInsert = sortedInsert (hsOrd := Operation.hsOrd n).
Proof.
  reflexivity.
Defined.

#[local] Hint Resolve @Forall_True : session_hints.

Lemma aux0_equalSlices l1 l2 :
  length l1 = length l2 ->
  coq_equalSlices l1 l2 = true ->
  l1 = l2.
Proof.
  rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; ss!.
Qed.

Lemma aux1_equalSlices l1 l2 :
  length l1 = length l2 ->
  coq_equalSlices l1 l2 = false ->
  l1 ≠ l2.
Proof.
  rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; ss!.
Qed.

Lemma aux2_equalSlices l1 l2 b :
  length l1 = length l2 ->
  coq_equalSlices l1 l2 = b ->
  coq_equalSlices l2 l1 = b.
Proof.
  rewrite redefine_coq_equalSlices. intros. subst b. eapply (eqb_comm (hsEq_A := hsEq_vector (length l1))); ss!.
Qed.

Lemma aux3_equalSlices l :
  coq_equalSlices l l = true.
Proof.
  change (coq_equalSlices l l) with (eqb (hsEq := hsEq_vector (length l)) l l).
  rewrite eqb_eq; ss!.
Qed.

Lemma aux0_lexicographicCompare l1 l2 l3 :
  coq_lexicographicCompare l2 l1 = true ->
  coq_lexicographicCompare l3 l2 = true ->
  coq_lexicographicCompare l3 l1 = true.
Proof.
  rewrite redefine_coq_lexicographicCompare.
  intros. eapply vectorGt_transitive with (l2 := l2); ss!.
Qed.

Lemma aux1_lexicographicCompare l1 l2 :
  length l1 = length l2 -> 
  l1 ≠ l2 ->
  (coq_lexicographicCompare l2 l1 = false <-> coq_lexicographicCompare l1 l2 = true).
Proof with ss!.
  rewrite redefine_coq_lexicographicCompare. remember (length l1) as len eqn: len_eq.
  pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector len) l1 l2) as claim. simpl in claim.
  symmetry in len_eq. intros len_eq'. symmetry in len_eq'.
  specialize (claim (conj (Forall_True _) len_eq) (conj (Forall_True _) len_eq')).
  destruct claim as [H_lt | [H_eq | H_gt]].
  - rewrite H_lt. intros NE. split.
    { congruence. }
    intros l1_gt_l2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1)...
  - intros NE. contradiction NE. clear NE. rewrite <- vectorEq_true_iff...
    change (eqb (hsEq := hsEq_vector len) l1 l2 = true). rewrite eqb_eq...
  - rewrite H_gt. intros NE. split.
    { congruence. }
    intros _. change (ltb (hsOrd := hsOrd_vector len) l1 l2 = false).
    rewrite ltb_nlt... intros NLT. change (ltb (hsOrd := hsOrd_vector len) l2 l1 = true) in H_gt.
    rewrite ltb_lt in H_gt... contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1)...
Qed.

Lemma aux3_lexicographicCompare l1 l2 :
  length l1 = length l2 ->
  coq_lexicographicCompare l2 l1 = false ->
  coq_lexicographicCompare l1 l2 = false ->
  l1 = l2.
Proof.
  rewrite redefine_coq_lexicographicCompare. intros. rewrite <- vectorEq_true_iff; ss!.
  change (eqb (hsEq := hsEq_vector (length l1)) l1 l2 = true). rewrite eqb_eq; ss!.
  pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector (length l1)) l1 l2) as [H_lt | [H_eq | H_gt]]; ss!.
Qed.

Lemma aux4_lexicographicCompare l1 l2 :
  coq_lexicographicCompare l1 l2 = true ->
  coq_equalSlices l1 l2 = false.
Proof.
  rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
  intros. eapply vectorGt_implies_not_vectorEq; ss!.
Qed.

Lemma aux5_lexicographicCompare l1 l2 :
  coq_equalSlices l1 l2 = true ->
  coq_lexicographicCompare l1 l2 = false.
Proof.
  rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
  intros. eapply vectorEq_implies_not_vectorGt; ss!.
Qed.

Lemma aux6_lexicographicCompare l1 l2 :
  length l1 = length l2 ->
  coq_lexicographicCompare l1 l2 = false ->
  (coq_lexicographicCompare l2 l1 = true \/ l1 = l2).
Proof.
  rewrite redefine_coq_lexicographicCompare. intros.
  pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector (length l2)) l1 l2) as [H_lt | [H_eq | H_gt]]; ss!.
  rewrite <- eqb_eq in H_eq; ss!. simpl in *. right; eapply aux0_equalSlices; trivial.
Qed.

Definition is_sorted (l: list Operation.t) : Prop :=
  ∀ i, ∀ j, (i < j)%nat -> ∀ o1, ∀ o2, l !! i = Some o1 -> l !! j = Some o2 ->
  coq_lexicographicCompare o2.(Operation.VersionVector) o1.(Operation.VersionVector) = true.

Lemma redefine_is_sorted (n: nat) (l: list Operation.t)
  : is_sorted l = SessionPrelude.isSorted (hsOrd := Operation.hsOrd n) l.
Proof.
  reflexivity.
Defined.

Lemma coq_maxTS_length n xs ys
  (LEN1: length xs = n)
  (LEN2: length ys = n)
  : length (coq_maxTS xs ys) = n.
Proof.
  revert xs ys LEN1 LEN2; induction n as [ | n IH], xs as [ | x xs], ys as [ | y ys]; simpl in *; intros; try congruence; f_equal; eapply IH; word.
Qed.

Lemma coq_sortedInsert_length l i
  : (length (coq_sortedInsert l i) <= length l + 1)%nat.
Proof.
  induction l as [ | x l IH]; simpl; try word.
  destruct (coq_lexicographicCompare _ _) as [ | ]; simpl; try word.
  destruct (coq_equalSlices _ _) as [ | ]; simpl; try word.
Qed.

End properties.

Module INVARIANT.

  Variant WEAK_SERVER_INVARIANT (EXTRA: Server.t -> Prop) (s: Server.t) : Prop :=
    | WEAK_SERVER_INVARIANT_INTRO
      (PendingOperations_is_sorted: is_sorted s.(Server.PendingOperations))
      (OperationsPerformed_is_sorted: is_sorted s.(Server.OperationsPerformed))
      (EXTRA_SERVER_INVARIANT: EXTRA s)
      : WEAK_SERVER_INVARIANT EXTRA s.

  Record SERVER_INVARIANT (EXTRA: Server.t -> Prop) (s: Server.t) : Prop :=
    SERVER_INVARIANT_INTRO
    { PendingOperations_is_sorted: is_sorted s.(Server.PendingOperations)
    ; OperationsPerformed_is_sorted: is_sorted s.(Server.OperationsPerformed)
    ; MyOperations_is_sorted: is_sorted s.(Server.MyOperations)
    ; Id_in_range: (uint.Z s.(Server.Id) >= 0)%Z /\ (uint.nat s.(Server.Id) < length s.(Server.VectorClock))%nat
    ; EXTRA_SERVER_INVARIANT: EXTRA s
    }.

  Record CLIENT_INVARIANT (EXTRA: Client.t -> Prop) (c: Client.t) : Prop :=
    CLIENT_INVARIANT_INTRO
    { SessionSemantic_ge_0: (uint.Z c.(Client.SessionSemantic) >= 0)%Z
    ; SessionSemantic_le_5: (uint.Z c.(Client.SessionSemantic) <= 5)%Z
    ; EXTRA_CLIENT_INVARIANT: EXTRA c
    }.

End INVARIANT.

Notation WEAK_SERVER_INVARIANT := INVARIANT.WEAK_SERVER_INVARIANT.
Notation SERVER_INVARIANT := INVARIANT.SERVER_INVARIANT.
Notation CLIENT_INVARIANT := INVARIANT.CLIENT_INVARIANT.

Definition FINAL_SERVER_INVARIANT {n: nat} : Server.t -> Prop :=
  let EXTRA_SERVER_INVARIANT (s: Server.t) : Prop :=
    uint.nat s.(Server.NumberOfServers) = n /\ length s.(Server.GossipAcknowledgements) = n /\ (Z.of_nat (length s.(Server.MyOperations)) <= CONSTANT)%Z
  in
  SERVER_INVARIANT EXTRA_SERVER_INVARIANT.

Section heap.

Import ServerSide.

Context `{hG: !heapGS Σ}.

Lemma Operation_well_formed op v (n : nat)
  : (is_operation v op n)%I ⊢@{iProp Σ} (⌜Operation.well_formed n op⌝)%I.
Proof.
  iIntros "H_hd". iDestruct "H_hd" as "(H3 & %H2 & %H1 & %H1')"; iClear "H3".
  iPureIntro; split; [eapply SessionPrelude.Forall_True | eauto].
Qed.

Lemma Forall_Operation_wf ops vs (n: nat)
  : ([∗ list] v;op ∈ vs;ops, is_operation v op n)%I ⊢@{iProp Σ} (⌜Forall (Operation.well_formed n) ops⌝)%I.
Proof.
  revert vs; induction ops as [ | hd tl IH]; intros vs.
  - iIntros "H_big_sepL2"; iPureIntro; eauto.
  - iIntros "H_big_sepL2".
    iPoseProof (big_sepL2_cons_inv_r with "H_big_sepL2") as "(%hd' & %tl' & -> & H_hd & H_tl)".
    iAssert (⌜Operation.well_formed n hd⌝)%I as "%YES1".
    { iApply Operation_well_formed. iExact "H_hd". }
    iAssert (⌜Forall (Operation.well_formed n) tl⌝)%I as "%YES2".
    { iApply IH; iExact "H_tl". }
    iPureIntro; econstructor; trivial.
Qed.

Lemma VersionVector_len (s: Slice.t) (ops: list Operation.t) (n: nat)
  : (operation_slice s ops n)%I ⊢@{iProp Σ} (⌜∀ i : nat, ∀ e, ops !! i = Some e -> length e.(Operation.VersionVector) = n⌝)%I.
Proof.
  iIntros "(%vs & H_vs & H)".
  iPoseProof (Forall_Operation_wf with "H") as "%H_well_formed".
  pose proof (List.Forall_forall (Operation.well_formed n) ops) as claim.
  rewrite claim in H_well_formed; iPureIntro; intros i x H_x.
  enough (WTS : Operation.well_formed n x) by now red in WTS.
  eapply H_well_formed; eapply SessionPrelude.lookup_In; eauto.
Qed.

Lemma pers_is_operation v op (n: nat)
  : (is_operation v op n)%I ⊢@{iProp Σ} (<pers> (is_operation v op n))%I.
Proof.
  iIntros "#H"; done.
Qed.

Lemma pers_big_sepL2_is_operation ops vs (n: nat)
  : ([∗ list] v;op ∈ vs;ops, is_operation v op n)%I ⊢@{iProp Σ} (<pers> ([∗ list] v;op ∈ vs;ops, is_operation v op n))%I.
Proof.
  iIntros "H_big_sepL2"; iApply (big_sepL2_persistently).
  iApply (big_sepL2_mono (λ k, λ y1, λ y2, is_operation y1 y2 n)%I with "[$H_big_sepL2]").
  intros; iIntros "#H"; done.
Qed.

Lemma pers_emp
  : (emp)%I ⊢@{iProp Σ} (<pers> emp)%I.
Proof.
  iIntros "#H"; done.
Qed.

Lemma big_sepL2_is_operation_elim ops vs (n: nat) (i: nat) op v
  (H_op: ops !! i = Some op)
  (H_v: vs !! i = Some v)
  : ([∗ list] v;op ∈ vs;ops, is_operation v op n)%I ⊢@{iProp Σ} (is_operation v op n)%I.
Proof.
  rewrite <- take_drop with (l := ops) (i := i); rewrite <- take_drop with (l := vs) (i := i); iIntros "H". 
  assert (i < length ops)%nat as H1_i by now eapply lookup_lt_is_Some_1.
  assert (i < length vs)%nat as H2_i by now eapply lookup_lt_is_Some_1.  
  iAssert (([∗ list] v;op ∈ take i vs;take i ops, is_operation v op n) ∗ ([∗ list] v;op ∈ drop i vs;drop i ops, is_operation v op n))%I with "[H]" as "[H1 H2]".
  { iApply (big_sepL2_app_equiv with "H"); do 2 rewrite length_take; word. }
  destruct (drop i vs) as [ | v' vs_suffix] eqn: H_vs_suffix.
  { apply f_equal with (f := length) in H_vs_suffix; simpl in *; rewrite length_drop in H_vs_suffix. word. }
  iPoseProof (big_sepL2_cons_inv_l with "[$H2]") as "(%op' & %ops_suffix & %H_ops_suffix & H3 & H4)".
  rewrite <- take_drop with (l := ops) (i := i) in H_op; rewrite <- take_drop with (l := vs) (i := i) in H_v.
  rewrite H_ops_suffix in H_op; rewrite H_vs_suffix in H_v.
  assert (i = length (take i ops)) as H3_i.
  { rewrite length_take; word. }
  assert (i = length (take i vs)) as H4_i.
  { rewrite length_take; word. }
  pose proof (list_lookup_middle (take i ops) ops_suffix op' i H3_i) as EQ_l_i.
  pose proof (list_lookup_middle (take i vs) vs_suffix v' i H4_i) as EQ_ops_i.
  assert (op = op' /\ v = v') as [<- <-] by now split; congruence.
  iExact "H3".
Qed.

Lemma big_sepL2_is_operation_intro ops vs (n: nat)
  (LENGTH: length ops = length vs)
  : (∀ i : nat, ∀ op, ∀ v, ⌜(ops !! i = Some op) /\ (vs !! i = Some v)⌝ -∗ is_operation op v n)%I ⊢@{iProp Σ} ([∗ list] v;op ∈ vs;ops, is_operation op v n)%I.
Proof.
  revert vs n LENGTH; induction ops as [ | ops_hd ops_tl IH], vs as [ | v_hd v_tl]; intros; simpl in *; try congruence.
  - iIntros "#H"; iClear "H"; done.
  - iIntros "#H"; iSplit.
    + iApply "H"; instantiate (1 := 0%nat); done.
    + iApply IH. { word. }
      iIntros "%i %op %v [%H_op %H_v]"; iApply "H"; instantiate (1 := S i); done.
Qed.

Lemma big_sepL2_middle_split {A: Type} {B: Type} {Φ: A -> B -> iProp Σ} {xs: list A} {i: nat} {x0: A} (ys: list B)
  (LOOKUP: xs !! i = Some x0)
  : ([∗ list] x;y ∈ xs;ys, Φ x y)%I ⊢@{iProp Σ} (∃ y0, ∃ ys1, ∃ ys2, ⌜ys = (ys1 ++ y0 :: ys2)%list /\ length ys1 = i⌝ ∗ Φ x0 y0 ∗ ([∗ list] x;y ∈ take i xs;ys1, Φ x y) ∗ ([∗ list] x;y ∈ drop (i + 1)%nat xs;ys2, Φ x y))%I.
Proof.
  pose proof (take_drop_middle xs i x0 LOOKUP) as claim1.
  assert (i < length xs)%nat as claim2.
  { now eapply lookup_lt_is_Some_1. }
  iIntros "H_big_sepL2".
  iPoseProof (big_sepL2_length with "[$H_big_sepL2]") as "%LENGTH".
  rewrite <- take_drop with (l := xs) (i := i).
  rewrite <- take_drop with (l := ys) (i := i).
  iPoseProof (big_sepL2_app_equiv with "H_big_sepL2") as "[H_prefix H_suffix]".
  { (do 2 rewrite length_take); word. }
  assert (is_Some (ys !! i)) as [y0 H_y0].
  { eapply lookup_lt_is_Some_2; word. }
  iExists y0; iExists (take i ys); iExists (drop (S i) ys).
  pose proof (take_drop_middle ys i y0 H_y0) as claim3.
  iSplitL "".
  { iPureIntro; split; [rewrite claim3; eapply take_drop | rewrite length_take; word]. }
  rewrite <- take_drop with (l := ys) (i := i) in claim3 at -1.
  apply SessionPrelude.app_cancel_l in claim3; rewrite take_drop in claim3; rewrite <- claim3.
  iPoseProof (big_sepL2_cons_inv_r with "[$H_suffix]") as "(%x0' & %xs2 & %EQ & H_middle & H_suffix)".
  rewrite <- take_drop with (l := xs) (i := i) in claim1 at -1.
  apply SessionPrelude.app_cancel_l in claim1; rewrite take_drop in claim1.
  assert (x0' = x0) as -> by congruence.
  iFrame; rewrite take_drop; iFrame.
  rewrite <- drop_drop with (l := xs) (n1 := 1%nat) (n2 := i); rewrite -> EQ; iExact "H_suffix".
Qed.

Lemma big_sepL2_middle_merge {A: Type} {B: Type} {Φ: A -> B -> iProp Σ} {xs: list A} {i: nat} {x0: A} (y0: B) (ys1: list B) (ys2: list B)
  (LOOKUP: xs !! i = Some x0)
  : (Φ x0 y0 ∗ ([∗ list] x;y ∈ take i xs;ys1, Φ x y) ∗ ([∗ list] x;y ∈ drop (i + 1)%nat xs;ys2, Φ x y))%I ⊢@{iProp Σ} ([∗ list] x;y ∈ xs;(ys1 ++ y0 :: ys2)%list, Φ x y)%I.
Proof.
  pose proof (take_drop_middle xs i x0 LOOKUP) as claim1.
  assert (i < length xs)%nat as claim2.
  { now eapply lookup_lt_is_Some_1. }
  iIntros "(H_middle & H_prefix & H_suffix)".
  replace ([∗ list] x;y ∈ xs;(ys1 ++ y0 :: ys2), Φ x y)%I with ([∗ list] x;y ∈ take i xs ++ x0 :: drop (S i) xs;(ys1 ++ y0 :: ys2), Φ x y)%I by now rewrite claim1.
  rewrite <- drop_drop with (l := xs) (n1 := 1%nat) (n2 := i).
  rewrite <- take_drop with (l := xs) (i := i) in claim1 at -1.
  apply SessionPrelude.app_cancel_l in claim1; rewrite take_drop in claim1.
  rewrite <- claim1; simpl; replace (drop 0 (drop (S i) xs)) with (drop (S i) xs) by reflexivity.
  iApply (big_sepL2_app with "[$H_prefix] [H_middle H_suffix]"); simpl; iFrame.
Qed.

End heap.

Lemma aux_1_le_CONSTANT
  : uint.Z (W64 1) ≤ CONSTANT.
Proof.
  rewrite CONSTANT_unfold. word.
Qed.

#[global] Hint Extern 5 (val_ty (Operation.val _)) => unfold Operation.val; simpl; repeat constructor; auto : session_hints.
#[global] Hint Extern 5 (val_ty (Message.val _)) => unfold Message.val; simpl; repeat constructor; auto : session_hints.
#[global] Hint Extern 5 (val_ty (Server.val _)) => unfold Server.val; simpl; repeat constructor; auto : session_hints.
#[global] Hint Extern 5 (val_ty (Client.val _)) => unfold Client.val; simpl; repeat constructor; auto : session_hints.

#[global] Hint Extern 5 (length (replicate _ _) = _) => rewrite length_replicate : session_hints.
#[global] Hint Resolve Forall_CONSTANT_replicate : session_hints.
#[global] Hint Resolve CONSTANT_coq_maxTs : session_hints.
#[global] Hint Resolve aux_1_le_CONSTANT : session_hints.
