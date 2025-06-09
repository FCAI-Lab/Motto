From Perennial.program_proof.session Require Export session_prelude.

#[local] Tactic Notation "tac_val_t" :=
  let val := lazymatch goal with [ |- val_ty (?val _) _ ] => val end in
  lazymatch goal with [ v : tuple_of ?tv |- _ ] => unfold tuple_of in v; unfold tv in v; simpl in v; unfold val; simpl SessionPrelude.value_of end;
  repeat constructor; auto.

#[local] Tactic Notation "tac_IntoVal" integer( n ) :=
  intros;
  lazymatch goal with [ v : tuple_of ?tv |- _ ] => unfold tuple_of in v; unfold tv in v; simpl in v; simpl SessionPrelude.value_of; do n destruct v as [v ?]; simpl end;
  repeat lazymatch goal with [ t : Slice.t |- _ ] => destruct t end; auto.

#[universes(template)]
Class has_value_boundary (t: Type) : Type :=
  value_bound (a: Z) (object: t) : Prop.

#[global] Hint Unfold value_bound : session_hints.

#[global]
Instance u64_has_value_boundary : has_value_boundary u64 :=
  fun a: Z => fun u: u64 => a >= 1 /\ uint.Z u <= 2 ^ 64 - a.

#[global]
Instance nat_has_value_boundary : has_value_boundary nat :=
  fun a: Z => fun n: nat => a >= 1 /\ Z.of_nat n <= 2 ^ 64 - a.
  
#[global]
Instance list_has_value_boundary {t: Type} (t_has_value_boundary: has_value_boundary t) : has_value_boundary (list t) :=
  fun a: Z => Forall ( @value_bound t t_has_value_boundary a).

Module _Data.

  Definition t : Type :=
    u64.

  #[global] Instance has_value_of_Data : SessionPrelude.has_value_of t :=
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
  Instance IntoVal : IntoVal _Data.t :=
    u64_IntoVal.

End _Data.

#[local] Opaque _Data.t.

Module Operation.

  Definition tv : TypeVector.t 2 :=
    [Slice.t,_Data.t].

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

  #[projections(primitive), universes(template)]
  Record t {u64: Type} : Type := mk
    { VersionVector: list u64
    ; Data:          _Data.t
    }.

  #[global] Arguments t : clear implicits. 

  #[global]
  Instance FMap
    : FMap t.
  Proof.
    intros A B A_to_B F_A. econstructor.
    - refine (fmap A_to_B _). refine (VersionVector _). exact F_A.
    - refine (_). refine (Data _). exact F_A.
  Defined.

  Definition size_of {u64: Type} (object: t u64) : nat :=
    length object.(VersionVector).

  #[global]
  Instance value_bound : has_value_boundary (t u64) :=
    fun a: Z => fun object: t u64 => value_bound a object.(VersionVector).

  Section ADD_ON.

    Context {u64: Type}.

    Definition getVersionVector (op: Operation.t u64) : list u64 :=
      op.(VersionVector).

    Context {u64_well_formed: u64 -> Prop}.

    Definition well_formed (n: nat) (op: Operation.t u64) : Prop :=
      Forall u64_well_formed op.(VersionVector) /\ length op.(VersionVector) = n.

    Context {u64_hsEq: SessionPrelude.hsEq u64 (well_formed := u64_well_formed)}.

    #[global]
    Instance hsEq_Operation (n: nat) : SessionPrelude.hsEq (Operation.t u64) (well_formed := well_formed n) :=
      SessionPrelude.hsEq_preimage getVersionVector.

    Context {u64_hsOrd: SessionPrelude.hsOrd u64 (well_formed := u64_well_formed)}.

    #[global]
    Instance hsOrd_Operation (n: nat) : SessionPrelude.hsOrd (Operation.t u64) (well_formed := well_formed n) :=
      SessionPrelude.hsOrd_preimage getVersionVector.

  End ADD_ON.

End Operation.

Module Message.

  Definition tv : TypeVector.t 18 :=
    [u64,u64,u64,u64,_Data.t,Slice.t,u64,u64,Slice.t,u64,u64,u64,u64,u64,_Data.t,Slice.t,u64,u64].

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
    SessionPrelude.value_of v.

  #[projections(primitive), universes(template)]
  Record t {u64: Type} : Type := mk
    { MessageType:  u64

    ; C2S_Client_Id:            u64
    ; C2S_Server_Id:            u64
    ; C2S_Client_OperationType: u64
    ; C2S_Client_Data:          _Data.t
    ; C2S_Client_VersionVector: list u64

    ; S2S_Gossip_Sending_ServerId:   u64
    ; S2S_Gossip_Receiving_ServerId: u64
    ; S2S_Gossip_Operations:         list (Operation.t u64)
    ; S2S_Gossip_Index:              u64

    ; S2S_Acknowledge_Gossip_Sending_ServerId:   u64
    ; S2S_Acknowledge_Gossip_Receiving_ServerId: u64
    ; S2S_Acknowledge_Gossip_Index:              u64

    ; S2C_Client_OperationType: u64
    ; S2C_Client_Data:          _Data.t
    ; S2C_Client_VersionVector: list u64
    ; S2C_Server_Id:            u64
    ; S2C_Client_Number:        u64
    }.

  #[global] Arguments t : clear implicits.

  #[global]
  Instance FMap
    : FMap t.
  Proof.
    intros A B A_to_B F_A. econstructor.
    - refine (A_to_B _). refine (MessageType _). exact F_A.
    - refine (A_to_B _). refine (C2S_Client_Id _). exact F_A.
    - refine (A_to_B _). refine (C2S_Server_Id _). exact F_A.
    - refine (A_to_B _). refine (C2S_Client_OperationType _). exact F_A.
    - refine (_). refine (C2S_Client_Data _). exact F_A.
    - refine (fmap A_to_B _). refine (C2S_Client_VersionVector _). exact F_A.
    - refine (A_to_B _). refine (S2S_Gossip_Sending_ServerId _). exact F_A.
    - refine (A_to_B _). refine (S2S_Gossip_Receiving_ServerId _). exact F_A.
    - refine (fmap (Operation.FMap A B A_to_B) _). refine (S2S_Gossip_Operations _). exact F_A.
    - refine (A_to_B _). refine (S2S_Gossip_Index _). exact F_A.
    - refine (A_to_B _). refine (S2S_Acknowledge_Gossip_Sending_ServerId _). exact F_A.
    - refine (A_to_B _). refine (S2S_Acknowledge_Gossip_Receiving_ServerId _). exact F_A.
    - refine (A_to_B _). refine (S2S_Acknowledge_Gossip_Index _). exact F_A.
    - refine (A_to_B _). refine (S2C_Client_OperationType _). exact F_A.
    - refine (_). refine (S2C_Client_Data _). exact F_A.
    - refine (fmap A_to_B _). refine (S2C_Client_VersionVector _). exact F_A.
    - refine (A_to_B _). refine (S2C_Server_Id _). exact F_A.
    - refine (A_to_B _). refine (S2C_Client_Number _). exact F_A.
  Defined.

  Definition size_of (object: t u64) : nat * nat :=
    (length object.(C2S_Client_VersionVector), length object.(S2C_Client_VersionVector)).

  Variant _value_bound {a: Z} (object: t u64) : Prop :=
    | _value_bound_intro
      (C2S_Client_Id_bound: value_bound a object.(C2S_Client_Id))
      (C2S_Server_Id_bound: value_bound a object.(C2S_Server_Id))
      (C2S_Client_VersionVector: value_bound a object.(C2S_Client_VersionVector))
      (S2S_Gossip_Sending_ServerId_bound: value_bound a object.(S2S_Gossip_Sending_ServerId))
      (S2S_Gossip_Receiving_ServerId_bound: value_bound a object.(S2S_Gossip_Receiving_ServerId))
      (S2S_Gossip_Operations_bound: value_bound a object.(S2S_Gossip_Operations))
      (S2S_Gossip_Index_bound: value_bound a object.(S2S_Gossip_Index))
      (S2S_Acknowledge_Gossip_Sending_ServerId_bound: value_bound a object.(S2S_Acknowledge_Gossip_Sending_ServerId))
      (S2S_Acknowledge_Gossip_Receiving_ServerId_bound: value_bound a object.(S2S_Acknowledge_Gossip_Receiving_ServerId))
      (S2S_Acknowledge_Gossip_Index_bound: value_bound a object.(S2S_Acknowledge_Gossip_Index))
      (S2C_Client_VersionVector_bound: value_bound a object.(S2C_Client_VersionVector))
      (S2C_Server_Id_bound: value_bound a object.(S2C_Server_Id))
      (S2C_Client_Number: value_bound a object.(S2C_Client_Number))
      : _value_bound object.

  #[global]
  Instance has_value_boundary : has_value_boundary (t u64) :=
    @_value_bound.

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

  #[projections(primitive), universes(template)]
  Record t {u64: Type} : Type := mk
    { Id:                     u64
    ; NumberOfServers:        u64
    ; UnsatisfiedRequests:    list (Message.t u64)
    ; VectorClock:            list u64
    ; OperationsPerformed:    list (Operation.t u64)
    ; MyOperations:           list (Operation.t u64)
    ; PendingOperations:      list (Operation.t u64)
    ; GossipAcknowledgements: list u64
    }.

  #[global] Arguments t : clear implicits.

  #[global]
  Instance FMap
    : FMap Server.t.
  Proof.
    intros A B A_to_B F_A. econstructor.
    - refine (A_to_B _). refine (Id _). exact F_A.
    - refine (A_to_B _). refine (NumberOfServers _). exact F_A.
    - refine (fmap (Message.FMap A B A_to_B) _). refine (UnsatisfiedRequests _). exact F_A.
    - refine (fmap A_to_B _). refine (VectorClock _). exact F_A.
    - refine (fmap (Operation.FMap A B A_to_B) _). refine (OperationsPerformed _). exact F_A.
    - refine (fmap (Operation.FMap A B A_to_B) _). refine (MyOperations _). exact F_A.
    - refine (fmap (Operation.FMap A B A_to_B) _). refine (PendingOperations _). exact F_A.
    - refine (fmap A_to_B _). refine (GossipAcknowledgements _). exact F_A.
  Qed.

  Definition size_of (object: t u64) : nat * nat * nat * nat * nat :=
    (length object.(VectorClock), length object.(OperationsPerformed), length object.(MyOperations), length object.(PendingOperations), length object.(GossipAcknowledgements)).

  Variant _value_bound {a: Z} (object: t u64) : Prop :=
    | _value_bound_intro
      (Id_bound: value_bound a object.(Id))
      (NumberOfServers_bound: value_bound a object.(NumberOfServers))
      (UnsatisfiedRequests_bound: value_bound a object.(UnsatisfiedRequests))
      (VectorClock_bound: value_bound a object.(VectorClock))
      (OperationsPerformed_bound: value_bound a object.(OperationsPerformed))
      (MyOperations_bound: value_bound a object.(MyOperations))
      (PendingOperations_bound: value_bound a object.(PendingOperations))
      (GossipAcknowledgements_bound: value_bound a object.(GossipAcknowledgements))
      : _value_bound object.

  #[global]
  Instance has_value_boundary : has_value_boundary (t u64) :=
    @_value_bound.

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

  #[projections(primitive), universes(template)]
  Record t {u64: Type} : Type := mk
    { Id:                 u64
    ; NumberOfServers:    u64
    ; WriteVersionVector: list u64
    ; ReadVersionVector:  list u64
    ; SessionSemantic:    u64
    }.

  #[global] Arguments t : clear implicits.

  #[global]
  Instance FMap
    : FMap Client.t.
  Proof.
    intros A B A_to_B F_A. econstructor.
    - refine (A_to_B _). refine (Id _). exact F_A.
    - refine (A_to_B _). refine (NumberOfServers _). exact F_A.
    - refine (fmap A_to_B _). refine (WriteVersionVector _). exact F_A.
    - refine (fmap A_to_B _). refine (ReadVersionVector _). exact F_A.
    - refine (A_to_B _). refine (SessionSemantic _). exact F_A.
  Defined.

  Definition size_of (object: t u64) : nat * nat :=
    (length object.(WriteVersionVector), length object.(ReadVersionVector)).

  Variant _value_bound {a: Z} (object: t u64) : Prop :=
    | _value_bound_intro
      (Id_bound: value_bound a object.(Id))
      (NumberOfServers_bound: value_bound a object.(NumberOfServers))
      (WriteVersionVector_bound: value_bound a object.(WriteVersionVector))
      (ReadVersionVector_bound: value_bound a object.(ReadVersionVector))
      : _value_bound object.

  #[global]
  Instance has_value_boundary : has_value_boundary (t u64) :=
    @_value_bound.

End Client.

Module ServerSide.

  Include SessionServer.

  Theorem Operation_val_t v
    : val_ty (Operation.val v) (struct.t SessionServer.Operation).
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
        IntoVal_def := (IntoVal_def Slice.t, IntoVal_def _Data.t);
      |}
    ).
    tac_IntoVal 1.
  Defined.

  Theorem Message_val_t v
    : val_ty (Message.val v) (struct.t SessionServer.Message).
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
        IntoVal_def := (W64 0, W64 0, W64 0, W64 0, IntoVal_def _Data.t, IntoVal_def Slice.t, W64 0, W64 0, IntoVal_def Slice.t, W64 0, W64 0, W64 0, W64 0, W64 0, IntoVal_def _Data.t, IntoVal_def Slice.t, W64 0, W64 0);
      |}
    ).
    tac_IntoVal 17.
  Defined.

  Theorem Server_val_t v
    : val_ty (Server.val v) (struct.t SessionServer.Server).
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
    tac_IntoVal 7.
  Defined.

  Section heap.

    Context `{hG: !heapGS Σ}.

    Definition is_good_operation (v: tuple_of Operation.tv) (object: Operation.t u64) (n: nat) : iProp Σ :=
      own_slice_small v!(0) uint64T DfracDiscarded object.(Operation.VersionVector) ∗
      ⌜v!(1) = object.(Operation.Data)⌝ ∗
      ⌜Operation.size_of object = n⌝.

    Definition is_good_slice_of_operations (s: Slice.t) (objects: list (Operation.t u64)) (n: nat) : iProp Σ :=
      ∃ vs, own_slice s (struct.t Operation) (DfracOwn 1) vs ∗ [∗ list] v;o ∈ vs;objects, is_good_operation v o n.

    Definition is_good_message (v: tuple_of Message.tv) (object: Message.t u64) (n: nat) (len_c2s: nat) (len_s2c: nat) : iProp Σ :=
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

    Definition is_good_slice_of_messages (s: Slice.t) (objects: list (Message.t u64)) (n: nat) (len_c2s: nat) : iProp Σ :=
      ∃ vs, own_slice s (struct.t Message) (DfracOwn 1) vs ∗ [∗ list] v;o ∈ vs;objects, ∃ len_s2c : nat, is_good_message v o n len_c2s len_s2c.

    Definition is_good_server' {OWN_UnsatisfiedRequests: bool} (v: tuple_of Server.tv) (object: Server.t u64) (n: nat) (len_vc: nat) (len_op: nat) (len_mo: nat) (len_po: nat) (len_ga: nat) : iProp Σ :=
      ⌜v!(0) = object.(Server.Id)⌝ ∗
      ⌜v!(1) = object.(Server.NumberOfServers)⌝ ∗
      (if OWN_UnsatisfiedRequests then is_good_slice_of_messages v!(2) object.(Server.UnsatisfiedRequests) n len_vc else emp)%I ∗
      own_slice_small v!(3) uint64T (DfracOwn 1) object.(Server.VectorClock) ∗
      is_good_slice_of_operations v!(4) object.(Server.OperationsPerformed) len_op ∗
      is_good_slice_of_operations v!(5) object.(Server.MyOperations) len_mo ∗
      is_good_slice_of_operations v!(6) object.(Server.PendingOperations) len_po ∗
      own_slice_small v!(7) uint64T (DfracOwn 1) object.(Server.GossipAcknowledgements) ∗
      ⌜Server.size_of object = (len_vc, len_op, len_mo, len_po, len_ga)⌝.

  End heap.

  Notation is_good_server := (is_good_server' (OWN_UnsatisfiedRequests := true)).

  Section Coq_nat.

    (* TODO *)

  End Coq_nat.

End ServerSide.

Module ClientSide.

  Include SessionClient.

  Theorem Operation_val_t v
    : val_ty (Operation.val v) (struct.t SessionClient.Operation).
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
    : val_ty (Message.val v) (struct.t SessionClient.Message).
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
    : val_ty (Client.val v) (struct.t SessionClient.Client).
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

  Notation is_good_operation := ServerSide.is_good_operation.

  Notation is_good_slice_of_operations := ServerSide.is_good_slice_of_operations.

  Notation is_good_message := ServerSide.is_good_message.

  Notation is_good_slice_of_messages := ServerSide.is_good_slice_of_messages.

  Section heap.

    Context `{hG: !heapGS Σ}.

    Definition is_good_client (v: tuple_of Client.tv) (object: Client.t u64) (n: nat) : iProp Σ :=
      ⌜v!(0) = object.(Client.Id)⌝ ∗
      ⌜v!(1) = object.(Client.NumberOfServers)⌝ ∗
      own_slice_small v!(2) uint64T (DfracOwn 1) object.(Client.WriteVersionVector) ∗
      own_slice_small v!(3) uint64T (DfracOwn 1) object.(Client.ReadVersionVector) ∗
      ⌜v!(4) = object.(Client.SessionSemantic)⌝ ∗
      ⌜(Client.size_of object, uint.nat object.(Client.NumberOfServers)) = (n, n, n)⌝.

  End heap.

  Section Coq_nat.

    Import ServerSide.

    (* TODO *)

  End Coq_nat.

End ClientSide.

Section heap.

  Import ServerSide.

  Context `{hG: !heapGS Σ}.

  Lemma Operation_well_formed (n: nat) v op
    : (is_good_operation v op n)%I ⊢@{iProp Σ} (⌜Operation.well_formed (u64_well_formed := fun _ : u64 => True) n op⌝)%I.
  Proof.
    iIntros "H_hd". iDestruct "H_hd" as "(H3 & %H2 & %H1)"; iClear "H3".
    iPureIntro; split; [eapply SessionPrelude.Forall_True | done].
  Qed.

  Lemma Forall_Operation_well_formed (n: nat) vs ops
    : ([∗ list] v;op ∈ vs;ops, is_good_operation v op n)%I ⊢@{iProp Σ} (⌜Forall (Operation.well_formed (u64_well_formed := fun _ : u64 => True) n) ops⌝)%I.
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

End heap.
