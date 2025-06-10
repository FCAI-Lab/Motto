From Perennial.program_proof.session Require Export session_prelude.
From Goose.session Require server client.

Module SessionServer := Goose.session.server.
Module SessionClient := Goose.session.client.

#[local] Tactic Notation "tac_val_t" :=
  let val := lazymatch goal with [ |- val_ty (?val _) _ ] => val end in
  lazymatch goal with [ v : tuple_of ?tv |- _ ] => unfold tuple_of in v; unfold tv in v; simpl in v; unfold val; simpl end;
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
  fun a: Z => fun n: nat => a >= 1 /\ uint.Z n <= 2 ^ 64 - a.

Lemma u64_has_value_boundary_dec a n
  : {u64_has_value_boundary a n} + {~ u64_has_value_boundary a n}.
Proof.
  unfold u64_has_value_boundary;
  pose proof (Z.ge_dec a 1) as [YES_ge | NO_ge];
  pose proof (Z.le_dec (uint.Z n) (2 ^ 64 - a)) as [YES_le | NO_le];
  first [now left; split | right; word].
Qed.

#[global]
Instance list_has_value_boundary {t: Type} (t_has_value_boundary: has_value_boundary t) : has_value_boundary (list t) :=
  let has_value_boundary : has_value_boundary t := t_has_value_boundary in
  fun a: Z => Forall (has_value_boundary a).

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

  #[global, program]
  Instance IntoVal : IntoVal (tuple_of tv) :=
    { to_val := val
    ; from_val := from_val
    ; IntoVal_def := (IntoVal_def Slice.t, IntoVal_def _Data.t)
    }.
  Next Obligation.
    tac_IntoVal 1.
  Defined.

  Section ADD_ON.

  Context {u64: Type}.

  Section HASKELLISH_INSTANCES.

  Definition getVersionVector (op: Operation.t u64) : list u64 :=
    op.(VersionVector).

  Context {u64_well_formed: u64 -> Prop}.

  Definition well_formed (n: nat) (op: Operation.t u64) : Prop :=
    Forall u64_well_formed op.(VersionVector) /\ length op.(VersionVector) = n.

  Context {u64_hsEq: SessionPrelude.hsEq u64 (well_formed := u64_well_formed)}.

  #[global]
  Instance hsEq (n: nat) : SessionPrelude.hsEq (Operation.t u64) (well_formed := well_formed n) :=
    SessionPrelude.hsEq_preimage getVersionVector.

  Context {u64_hsOrd: SessionPrelude.hsOrd u64 (well_formed := u64_well_formed)}.

  #[global]
  Instance hsOrd (n: nat) : SessionPrelude.hsOrd (Operation.t u64) (well_formed := well_formed n) :=
    SessionPrelude.hsOrd_preimage getVersionVector.

  End HASKELLISH_INSTANCES.

  Definition size_of (object: t u64) : nat :=
    length object.(VersionVector).

  Context `(has_value_boundary u64).

  #[global]
  Instance value_bound : has_value_boundary (t u64) :=
    fun a: Z => fun object: t u64 => value_bound a object.(VersionVector).

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

  #[global, program]
  Instance IntoVal : IntoVal (tuple_of tv) :=
    { to_val := val
    ; from_val := from_val
    ; IntoVal_def := (W64 0, W64 0, W64 0, W64 0, IntoVal_def _Data.t, IntoVal_def Slice.t, W64 0, W64 0, IntoVal_def Slice.t, W64 0, W64 0, W64 0, W64 0, W64 0, IntoVal_def _Data.t, IntoVal_def Slice.t, W64 0, W64 0);
    }.
  Next Obligation.
    tac_IntoVal 17.
  Defined.

  Section ADD_ON.

  Context {u64: Type}.

  Definition size_of (object: t u64) : nat * nat :=
    (length object.(C2S_Client_VersionVector), length object.(S2C_Client_VersionVector)).

  Context `(has_value_boundary u64).

  Variant _value_bound {a: Z} (object: t u64) : Prop :=
    | _value_bound_intro
      (MessageType_bound: value_bound 1 object.(MessageType))
      (C2S_Client_Id_bound: value_bound a object.(C2S_Client_Id))
      (C2S_Server_Id_bound: value_bound a object.(C2S_Server_Id))
      (C2S_Client_OperationType_bound: value_bound 1 object.(C2S_Client_OperationType))
      (C2S_Client_VersionVector: value_bound a object.(C2S_Client_VersionVector))
      (S2S_Gossip_Sending_ServerId_bound: value_bound a object.(S2S_Gossip_Sending_ServerId))
      (S2S_Gossip_Receiving_ServerId_bound: value_bound a object.(S2S_Gossip_Receiving_ServerId))
      (S2S_Gossip_Operations_bound: value_bound a object.(S2S_Gossip_Operations))
      (S2S_Gossip_Index_bound: value_bound a object.(S2S_Gossip_Index))
      (S2S_Acknowledge_Gossip_Sending_ServerId_bound: value_bound a object.(S2S_Acknowledge_Gossip_Sending_ServerId))
      (S2S_Acknowledge_Gossip_Receiving_ServerId_bound: value_bound a object.(S2S_Acknowledge_Gossip_Receiving_ServerId))
      (S2S_Acknowledge_Gossip_Index_bound: value_bound a object.(S2S_Acknowledge_Gossip_Index))
      (S2C_Client_OperationType_bound: value_bound 1 object.(S2C_Client_OperationType))
      (S2C_Client_VersionVector_bound: value_bound a object.(S2C_Client_VersionVector))
      (S2C_Server_Id_bound: value_bound a object.(S2C_Server_Id))
      (S2C_Client_Number: value_bound a object.(S2C_Client_Number))
      : _value_bound object.

  #[global]
  Instance has_value_boundary : has_value_boundary (t u64) :=
    @_value_bound.

  End ADD_ON.

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

  #[global, program]
  Instance IntoVal : IntoVal (tuple_of tv) :=
    { to_val := val
    ; from_val := from_val
    ; IntoVal_def := (W64 0, W64 0, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t, IntoVal_def Slice.t)
    }.
  Next Obligation.
    tac_IntoVal 7.
  Defined.

  Section ADD_ON.

  Context {u64: Type}.

  Definition size_of (object: t u64) : nat * nat * nat * nat * nat :=
    (length object.(VectorClock), length object.(OperationsPerformed), length object.(MyOperations), length object.(PendingOperations), length object.(GossipAcknowledgements)).

  Context `(has_value_boundary u64).

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

  End ADD_ON.

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

  #[global, program]
  Instance IntoVal : IntoVal (tuple_of tv) :=
    { to_val := val
    ; from_val := from_val
    ; IntoVal_def := (W64 0, W64 0, IntoVal_def Slice.t, IntoVal_def Slice.t, W64 0);
    }.
  Next Obligation.
    tac_IntoVal 4.
  Defined.

  Section ADD_ON.

  Context {u64: Type}.

  Definition size_of (object: t u64) : nat * nat :=
    (length object.(WriteVersionVector), length object.(ReadVersionVector)).

  Context `(has_value_boundary u64).

  Variant _value_bound {a: Z} (object: t nat) : Prop :=
    | _value_bound_intro
      (Id_bound: value_bound a object.(Id))
      (NumberOfServers_bound: value_bound a object.(NumberOfServers))
      (WriteVersionVector_bound: value_bound a object.(WriteVersionVector))
      (ReadVersionVector_bound: value_bound a object.(ReadVersionVector))
      (SessionSemantic_bound: value_bound 1 object.(SessionSemantic))
      : _value_bound object.

  #[global]
  Instance has_value_boundary : has_value_boundary (t nat) :=
    @_value_bound.

  End ADD_ON.

End Client.

Module ServerSide.

  Include SessionServer.

  Theorem Operation_val_t v
    : val_ty (Operation.val v) (struct.t SessionServer.Operation).
  Proof.
    tac_val_t.
  Qed.

  #[global] Hint Resolve Operation_val_t : typeclasses_hints.

  Theorem Message_val_t v
    : val_ty (Message.val v) (struct.t SessionServer.Message).
  Proof.
    tac_val_t.
  Qed.

  #[global] Hint Resolve Message_val_t : typeclasses_hints.

  Theorem Server_val_t v
    : val_ty (Server.val v) (struct.t SessionServer.Server).
  Proof.
    tac_val_t.
  Qed.

  #[global] Hint Resolve Server_val_t : typeclasses_hints.

  Section heap.

  Context `{hG: !heapGS Σ}.

  #[local] Notation operation := (Operation.t u64).
  #[local] Notation operationList := (list operation).
  #[local] Notation message := (Message.t u64).
  #[local] Notation messageList := (list message).
  #[local] Notation server := (Server.t u64).

  Definition isOperation (v: tuple_of Operation.tv) (op: operation) (n: nat) : iProp Σ :=
    own_slice_small v!(0) uint64T DfracDiscarded op.(Operation.VersionVector) ∗
    ⌜v!(1) = op.(Operation.Data)⌝ ∗
    ⌜Operation.size_of op = n⌝.

  Definition isOperationSlice (s: Slice.t) (ops: operationList) (n: nat) : iProp Σ :=
    ∃ vs, own_slice s (struct.t Operation) (DfracOwn 1) vs ∗ [∗ list] v;op ∈ vs;ops, isOperation v op n.

  Definition isMessage (v: tuple_of Message.tv) (msg: message) (n: nat) (len_c2s: nat) (len_s2c: nat) : iProp Σ :=
    ⌜v!(0) = msg.(Message.MessageType)⌝ ∗
    ⌜v!(1) = msg.(Message.C2S_Client_Id)⌝ ∗
    ⌜v!(2) = msg.(Message.C2S_Server_Id)⌝ ∗
    ⌜v!(3) = msg.(Message.C2S_Client_OperationType)⌝ ∗
    ⌜v!(4) = msg.(Message.C2S_Client_Data)⌝ ∗
    own_slice_small v!(5) uint64T (DfracOwn 1) msg.(Message.C2S_Client_VersionVector) ∗
    ⌜len_c2s = length msg.(Message.C2S_Client_VersionVector)⌝ ∗
    ⌜v!(6) = msg.(Message.S2S_Gossip_Sending_ServerId)⌝ ∗
    ⌜v!(7) = msg.(Message.S2S_Gossip_Receiving_ServerId)⌝ ∗
    isOperationSlice v!(8) msg.(Message.S2S_Gossip_Operations) n ∗
    ⌜v!(9) = msg.(Message.S2S_Gossip_Index)⌝ ∗
    ⌜v!(10) = msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId)⌝ ∗
    ⌜v!(11) = msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId)⌝ ∗
    ⌜v!(12) = msg.(Message.S2S_Acknowledge_Gossip_Index)⌝ ∗
    ⌜v!(13) = msg.(Message.S2C_Client_OperationType)⌝ ∗
    ⌜v!(14) = msg.(Message.S2C_Client_Data)⌝ ∗
    own_slice_small v!(15) uint64T (DfracOwn 1) msg.(Message.S2C_Client_VersionVector) ∗
    ⌜v!(16) = msg.(Message.S2C_Server_Id)⌝ ∗
    ⌜v!(17) = msg.(Message.S2C_Client_Number)⌝ ∗
    ⌜Message.size_of msg = (len_c2s, len_s2c)⌝.

  Definition isMessageSlice (s: Slice.t) (msgs: messageList) (n: nat) (len_c2s: nat) : iProp Σ :=
    ∃ vs, own_slice s (struct.t Message) (DfracOwn 1) vs ∗ [∗ list] v;msg ∈ vs;msgs, ∃ len_s2c : nat, isMessage v msg n len_c2s len_s2c.

  Definition isServer' {OWN_UnsatisfiedRequests: bool} (v: tuple_of Server.tv) (server: server) (n: nat) (len_vc: nat) (len_op: nat) (len_mo: nat) (len_po: nat) (len_ga: nat) : iProp Σ :=
    ⌜v!(0) = server.(Server.Id)⌝ ∗
    ⌜v!(1) = server.(Server.NumberOfServers)⌝ ∗
    (if OWN_UnsatisfiedRequests then isMessageSlice v!(2) server.(Server.UnsatisfiedRequests) n len_vc else emp)%I ∗
    own_slice_small v!(3) uint64T (DfracOwn 1) server.(Server.VectorClock) ∗
    isOperationSlice v!(4) server.(Server.OperationsPerformed) len_op ∗
    isOperationSlice v!(5) server.(Server.MyOperations) len_mo ∗
    isOperationSlice v!(6) server.(Server.PendingOperations) len_po ∗
    own_slice_small v!(7) uint64T (DfracOwn 1) server.(Server.GossipAcknowledgements) ∗
    ⌜Server.size_of server = (len_vc, len_op, len_mo, len_po, len_ga)⌝.

  End heap.

  Notation isServer := (isServer' (OWN_UnsatisfiedRequests := true)).

  Section Coq_nat.

  #[local] Notation Operation := (Operation.t u64).
  #[local] Notation Message := (Message.t u64).
  #[local] Notation Server := (Server.t u64).

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
    match v1 with
    | [] => false
    | h1 :: t1 =>
      match v2 with
      | [] => false
      | h2 :: t2 => if uint.Z h1 =? uint.Z h2 then coq_lexicographicCompare t1 t2 else uint.Z h1 >? uint.Z h2
      end
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
      let (e1, e2) := element in
      let (output, canApply) := acc in
      if canApply && (uint.Z (w64_word_instance.(word.add) e1 (W64 1)) =? uint.Z e2) then
        (output, false)
      else if uint.Z e1 >=? uint.Z e2 then
        (output, canApply)
      else 
        (false, canApply)
    in
    let (output, canApply) := fold_left loop_step (zip v1 v2) (true, true) in
    output && negb canApply.

  Fixpoint coq_equalSlices (s1: list u64) (s2: list u64) : bool :=
    match s1 with
    | [] => true
    | h1 :: t1 =>
      match s2 with
      | [] => true
      | h2 :: t2 => if negb (uint.Z h1 =? uint.Z h2) then false else coq_equalSlices t1 t2
      end
    end.

  Variant binarySearch_spec (needle: Operation) (l: list Operation) (n: nat) (RESULT: nat) : Prop :=
    | binarySearch_spec_intro (prefix: list (list u64)) (suffix: list (list u64))
      (LENGTH: RESULT = length prefix)
      (VECTOR: map Operation.getVersionVector l = if forallb (fun x => negb (coq_equalSlices x.(Operation.VersionVector) needle.(Operation.VersionVector))) l then prefix ++ suffix else prefix ++ [Operation.getVersionVector needle] ++ suffix)
      (PREFIX: ∀ op, In op prefix -> coq_lexicographicCompare needle.(Operation.VersionVector) op = true)
      (SUFFIX: ∀ op, In op suffix -> coq_lexicographicCompare op needle.(Operation.VersionVector) = true)
      : binarySearch_spec needle l n RESULT.

  Fixpoint coq_sortedInsert (l: list Operation) (i: Operation) : list Operation :=
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

  Definition coq_getDataFromOperationLog (l: list Operation) : u64 :=
    match last l with
    | Some v => v.(Operation.Data)
    | None => W64 0
    end.

  Definition coq_receiveGossip (server: Server) (request: Message) : Server :=
    if (length request.(Message.S2S_Gossip_Operations) =? 0)%nat then
      server
    else
      let first_loop_output : Server :=
        let focus := request.(Message.S2S_Gossip_Operations) in
        let loop_step (acc: Server) (elem: Operation) : Server :=
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
      let second_loop_output : Server * u64 * list u64 :=
        let focus := server.(Server.PendingOperations) in
        let loop_step (acc: Server * u64 * list u64) (elem: Operation) : Server * u64 * list u64 :=
          let '(server, i, seen) := acc in
            if coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then
              (Server.mk u64 server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) (coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector)) (coq_sortedInsert server.(Server.OperationsPerformed) elem) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements), W64 (uint.Z i + 1), seen ++ [i])
            else
              (server, W64 (uint.Z i + 1), seen)
        in
        fold_left loop_step focus (server, W64 0, [])
      in
      let '(server, _, seen) := second_loop_output in
      let third_loop_output : nat * nat * list Operation :=
        let focus := server.(Server.PendingOperations) in
        let loop_step (acc: nat * nat * list Operation) (elem: Operation) : nat * nat * list Operation :=
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

  Definition coq_acknowledgeGossip (s: Server) (r: Message) : Server :=
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
      Server.mk u64 s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) gossipAcknowledgements.

  Definition coq_getGossipOperations (s: Server) (serverId: u64) : list Operation :=
    match s.(Server.GossipAcknowledgements) !! uint.nat serverId with
    | Some v => drop (uint.nat v) s.(Server.MyOperations)
    | None => []
    end.

  Definition coq_processClientRequest (s: Server) (r: Message) : bool * Server * Message :=
    if negb (coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector)) then
      (false, s, Message.mk u64 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
    else
      if uint.Z r.(Message.C2S_Client_OperationType) =? 0 then
        let S2C_Client_Data := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
        let S2C_Client_VersionVector := s.(Server.VectorClock) in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server.Id) in
        (true, s, Message.mk u64 4 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)
      else
        let v := match s.(Server.VectorClock) !! uint.nat s.(Server.Id) with Some v => uint.Z v | None => 0 end in
        let VectorClock := <[uint.nat s.(Server.Id) := W64 (v + 1)]> s.(Server.VectorClock) in
        let OperationsPerformed := coq_sortedInsert s.(Server.OperationsPerformed) (Operation.mk u64 VectorClock r.(Message.C2S_Client_Data)) in
        let MyOperations := coq_sortedInsert s.(Server.MyOperations) (Operation.mk u64 VectorClock r.(Message.C2S_Client_Data)) in
        let S2C_Client_OperationType := 1 in
        let S2C_Client_Data := (IntoVal_def _Data.t) in
        let S2C_Client_VersionVector := VectorClock in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server.Id) in
        (true, Server.mk u64 s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), Message.mk u64 4 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number).

  Definition coq_processRequest (server: Server) (request: Message) : Server * list Message :=
    match uint.nat request.(Message.MessageType) with
    | 0%nat =>
      let '(succeeded, server, reply) := coq_processClientRequest server request in
      if succeeded then
        (server, [reply])
      else
        let UnsatisfiedRequests := server.(Server.UnsatisfiedRequests) ++ [request] in 
        let server := Server.mk u64 server.(Server.Id) server.(Server.NumberOfServers) UnsatisfiedRequests server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements) in
        (server, [])
    | 1%nat =>
      let server := coq_receiveGossip server request in
      let focus := server.(Server.UnsatisfiedRequests) in
      let loop_init : nat * Server * list Message :=
        (0%nat, server, [])
      in
      let loop_step (acc: nat * Server * list Message) (element: Message) : nat * Server * list Message :=
        let '(i, s, outGoingRequests) := acc in
        let '(succeeded, s, reply) := coq_processClientRequest s element in
        if succeeded then
          let UnsatisfiedRequests := SessionPrelude.deleteAt s.(Server.UnsatisfiedRequests) i in
          (i, Server.mk u64 s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), outGoingRequests ++ [reply])
        else
          ((i + 1)%nat, s, outGoingRequests)
      in
      let '(_, server, outGoingRequests) := fold_left loop_step focus loop_init in
      (server, outGoingRequests)
    | 2%nat => (coq_acknowledgeGossip server request, [])
    | 3%nat =>
      let loop_step (acc: Server * list Message) (index: u64) : Server * list Message :=
        let '(server, outGoingRequests) := acc in
        let operations := coq_getGossipOperations server index in
        if negb (uint.nat index =? uint.nat server.(Server.Id))%nat && negb (length operations =? 0)%nat then
          let GossipAcknowledgements := <[uint.nat index := W64 (length server.(Server.MyOperations))]> server.(Server.GossipAcknowledgements) in
          let S2S_Gossip_Sending_ServerId := server.(Server.Id) in
          let S2S_Gossip_Receiving_ServerId := index in
          let S2S_Gossip_Operations := operations in
          let S2S_Gossip_Index := length (server.(Server.MyOperations)) in
          let message := Message.mk u64 1 0 0 0 (IntoVal_def _Data.t) [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 in
          (Server.mk u64 server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) GossipAcknowledgements, outGoingRequests ++ [message])
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

  Theorem Message_val_t v
    : val_ty (Message.val v) (struct.t SessionClient.Message).
  Proof.
    exact (ServerSide.Message_val_t v).
  Defined.

  #[global] Hint Resolve Message_val_t : typeclasses_hints.

  Theorem Client_val_t v
    : val_ty (Client.val v) (struct.t SessionClient.Client).
  Proof.
    tac_val_t.
  Defined.

  #[global] Hint Resolve Client_val_t : typeclasses_hints.

  Notation isOperation := ServerSide.isOperation.

  Notation isOperationSlice := ServerSide.isOperationSlice.

  Notation isMessage := ServerSide.isMessage.

  Notation isMessageSlice := ServerSide.isMessageSlice.

  Section heap.

  Context `{hG: !heapGS Σ}.

  #[local] Notation operation := (Operation.t u64).
  #[local] Notation operationList := (list operation).
  #[local] Notation message := (Message.t u64).
  #[local] Notation messageList := (list message).
  #[local] Notation client := (Client.t u64).

  Definition Client_u64 (v: tuple_of Client.tv) (client: client) (n: nat) : iProp Σ :=
    ⌜v!(0) = client.(Client.Id)⌝ ∗
    ⌜v!(1) = client.(Client.NumberOfServers)⌝ ∗
    own_slice_small v!(2) uint64T (DfracOwn 1) client.(Client.WriteVersionVector) ∗
    own_slice_small v!(3) uint64T (DfracOwn 1) client.(Client.ReadVersionVector) ∗
    ⌜v!(4) = client.(Client.SessionSemantic)⌝ ∗
    ⌜(Client.size_of client, uint.nat client.(Client.NumberOfServers)) = (n, n, n)⌝.

  End heap.

  Section Coq_nat.

  Import ServerSide.

  #[local] Notation Operation := (Operation.t u64).
  #[local] Notation Message := (Message.t u64).
  #[local] Notation Client := (Client.t u64).

  Definition coq_read (c: Client) (serverId: u64) : Message :=
    match uint.nat c.(Client.SessionSemantic) with
    | 0%nat => Message.mk u64 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 1%nat => Message.mk u64 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 2%nat => Message.mk u64 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 3%nat => Message.mk u64 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) c.(Client.ReadVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 4%nat => Message.mk u64 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) c.(Client.WriteVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 5%nat => Message.mk u64 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | _ => Message.mk u64 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    end.

  Definition coq_write (c: Client) (serverId: u64) (value: u64) : Message :=
    match uint.nat c.(Client.SessionSemantic) with
    | 0%nat => Message.mk u64 0 c.(Client.Id) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 1%nat => Message.mk u64 0 c.(Client.Id) serverId 1 value c.(Client.ReadVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 2%nat => Message.mk u64 0 c.(Client.Id) serverId 1 value c.(Client.WriteVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 3%nat => Message.mk u64 0 c.(Client.Id) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 4%nat => Message.mk u64 0 c.(Client.Id) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 5%nat => Message.mk u64 0 c.(Client.Id) serverId 1 value (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | _ => Message.mk u64 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    end.

  Definition coq_processRequest (c: Client) (requestType: u64) (serverId: u64) (value: u64) (ackMessage: Message) : Client * Message :=
    match uint.nat requestType with
    | 0%nat => (c, coq_read c serverId)
    | 1%nat => (c, coq_write c serverId value)
    | 2%nat =>
      match uint.nat ackMessage.(Message.S2C_Client_OperationType) with
      | 0%nat => (Client.mk u64 c.(Client.Id) c.(Client.NumberOfServers) c.(Client.WriteVersionVector) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.SessionSemantic), Message.mk u64 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
      | 1%nat => (Client.mk u64 c.(Client.Id) c.(Client.NumberOfServers) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.ReadVersionVector) c.(Client.SessionSemantic), Message.mk u64 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
      | _ => (c, Message.mk u64 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
      end
    | _ => (c, Message.mk u64 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
    end.

  End Coq_nat.

End ClientSide.

Section properties.

Import ServerSide SessionPrelude.

Lemma redefine_coq_lexicographicCompare
  : coq_lexicographicCompare = vectorGt.
Proof.
  reflexivity.
Defined.

Lemma redefine_coq_equalSlices
  : coq_equalSlices = vectorEq.
Proof.
  reflexivity.
Defined.

Lemma redefine_coq_sortedInsert (n: nat)
  : coq_sortedInsert = sortedInsert (hsOrd := Operation.hsOrd n).
Proof.
  reflexivity.
Defined.

#[local] Hint Resolve @Forall_True : core.

Lemma aux0_equalSlices l1 l2 :
  length l1 = length l2 ->
  coq_equalSlices l1 l2 = true ->
  l1 = l2.
Proof.
  rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; eauto 2.
Qed.

Lemma aux1_equalSlices l1 l2 :
  length l1 = length l2 ->
  coq_equalSlices l1 l2 = false ->
  l1 ≠ l2.
Proof.
  rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; eauto 2.
  rewrite H0; congruence.
Qed.

Lemma aux2_equalSlices l1 l2 b :
  length l1 = length l2 ->
  coq_equalSlices l1 l2 = b ->
  coq_equalSlices l2 l1 = b.
Proof.
  rewrite redefine_coq_equalSlices. intros. subst b. eapply (eqb_comm (hsEq_A := hsEq_vector (length l1))); eauto.
Qed.

Lemma aux3_equalSlices l :
  coq_equalSlices l l = true.
Proof.
  change (coq_equalSlices l l) with (eqb (hsEq := hsEq_vector (length l)) l l).
  rewrite eqb_eq; eauto 2. eapply eqProp_reflexivity; eauto 2.
Qed.

Lemma aux0_lexicographicCompare l1 l2 l3 :
  coq_lexicographicCompare l2 l1 = true ->
  coq_lexicographicCompare l3 l2 = true ->
  coq_lexicographicCompare l3 l1 = true.
Proof.
  rewrite redefine_coq_lexicographicCompare.
  intros. eapply vectorGt_transitive; eauto.
Qed.

Lemma aux1_lexicographicCompare l1 l2 :
  length l1 = length l2 -> 
  l1 ≠ l2 ->
  (coq_lexicographicCompare l2 l1 = false <-> coq_lexicographicCompare l1 l2 = true).
Proof.
  rewrite redefine_coq_lexicographicCompare. remember (length l1) as len eqn: len_eq.
  pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector len) l1 l2) as claim. simpl in claim.
  symmetry in len_eq. intros len_eq'. symmetry in len_eq'.
  specialize (claim (conj (Forall_True _) len_eq) (conj (Forall_True _) len_eq')).
  destruct claim as [H_lt | [H_eq | H_gt]].
  - rewrite H_lt. intros NE. split.
    { congruence. }
    intros l1_gt_l2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1); eauto.
    + eapply eqProp_reflexivity; eauto.
    + eapply ltProp_transitivity with (y := l2); eauto.
  - intros NE. contradiction NE. clear NE. rewrite <- vectorEq_true_iff; eauto 2.
    change (eqb (hsEq := hsEq_vector len) l1 l2 = true). rewrite eqb_eq; eauto 2.
  - rewrite H_gt. intros NE. split.
    { congruence. }
    intros _. change (ltb (hsOrd := hsOrd_vector len) l1 l2 = false).
    rewrite ltb_nlt; eauto 2. intros NLT. change (ltb (hsOrd := hsOrd_vector len) l2 l1 = true) in H_gt.
    rewrite ltb_lt in H_gt; eauto 2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1); eauto.
    + eapply eqProp_reflexivity; eauto.
    + eapply ltProp_transitivity with (y := l2); eauto.
Qed.

Lemma aux3_lexicographicCompare l1 l2 :
  length l1 = length l2 ->
  coq_lexicographicCompare l2 l1 = false ->
  coq_lexicographicCompare l1 l2 = false ->
  l1 = l2.
Proof.
  rewrite redefine_coq_lexicographicCompare. intros. rewrite <- vectorEq_true_iff; eauto 2.
  change (eqb (hsEq := hsEq_vector (length l1)) l1 l2 = true). rewrite eqb_eq; eauto 2.
  pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector (length l1)) l1 l2) as [H_lt | [H_eq | H_gt]]; eauto.
  - rewrite <- ltb_lt in H_lt; eauto 2. simpl in *. congruence.
  - rewrite <- ltb_lt in H_gt; eauto 2. simpl in *. congruence.
Qed.

Lemma aux4_lexicographicCompare l1 l2 :
  coq_lexicographicCompare l1 l2 = true ->
  coq_equalSlices l1 l2 = false.
Proof.
  rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
  intros. eapply vectorGt_implies_not_vectorEq; eauto 2.
Qed.

Lemma aux5_lexicographicCompare l1 l2 :
  coq_equalSlices l1 l2 = true ->
  coq_lexicographicCompare l1 l2 = false.
Proof.
  rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
  intros. eapply vectorEq_implies_not_vectorGt; eauto 2.
Qed.

Lemma aux6_lexicographicCompare l1 l2 :
  length l1 = length l2 ->
  coq_lexicographicCompare l1 l2 = false ->
  (coq_lexicographicCompare l2 l1 = true \/ l1 = l2).
Proof.
  rewrite redefine_coq_lexicographicCompare. intros.
  pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector (length l2)) l1 l2) as [H_lt | [H_eq | H_gt]]; eauto.
  - rewrite <- eqb_eq in H_eq; eauto 2. simpl in *. right; eapply aux0_equalSlices; trivial.
  - rewrite <- ltb_lt in H_gt; eauto 2. simpl in *. congruence.
Qed.

Definition is_sorted (l: list (Operation.t u64)) : Prop :=
  ∀ i, ∀ j, (i < j)%nat -> ∀ o1, ∀ o2, l !! i = Some o1 -> l !! j = Some o2 ->
  coq_lexicographicCompare o2.(Operation.VersionVector) o1.(Operation.VersionVector) = true.

Lemma redefine_is_sorted n l
  : is_sorted l = isSorted (hsOrd := Operation.hsOrd n) l.
Proof.
  reflexivity.
Defined.

Lemma length_coq_maxTS n xs ys
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

Lemma BOUND_replicate a x n
  (BOUND_x : u64_has_value_boundary a x)
  : Forall (u64_has_value_boundary a) (replicate n x).
Proof.
  induction n as [ | n IH]; simpl in *; eauto.
Qed.

Lemma BOUND_coq_maxTwoInts a x y
  (BOUND_x : u64_has_value_boundary a x)
  (BOUND_y : u64_has_value_boundary a y)
  : u64_has_value_boundary a (coq_maxTwoInts x y).
Proof.
  unfold coq_maxTwoInts. red in BOUND_x, BOUND_y |- *. destruct (_ >? _)%Z as [ | ]; word.
Qed.

Lemma BOUND_coq_maxTS a xs ys
  (BOUND_xs : Forall (u64_has_value_boundary a) xs)
  (BOUND_ys : Forall (u64_has_value_boundary a) ys)
  : Forall (u64_has_value_boundary a) (coq_maxTS xs ys).
Proof.
  revert ys BOUND_ys. induction BOUND_xs as [ | x x_wf xs xs_wf IH]; intros; destruct BOUND_ys as [ | y y_wf ys ys_wf]; simpl; eauto.
  econstructor; eauto. eapply BOUND_coq_maxTwoInts; eauto.
Qed.

End properties.

Module INVARIANT.

  Variant WEAK_SERVER_INVARIANT (EXTRA: Server.t u64 -> Prop) (server: Server.t u64) : Prop :=
    | WEAK_SERVER_INVARIANT_INTRO
      (PendingOperations_is_sorted: is_sorted server.(Server.PendingOperations))
      (OperationsPerformed_is_sorted: is_sorted server.(Server.OperationsPerformed))
      (EXTRA_SERVER_INVARIANT: EXTRA server)
      : WEAK_SERVER_INVARIANT EXTRA server.

  Record SERVER_INVARIANT (EXTRA: Server.t u64 -> Prop) (server: Server.t u64) : Prop :=
    SERVER_INVARIANT_INTRO
    { PendingOperations_is_sorted: is_sorted server.(Server.PendingOperations)
    ; OperationsPerformed_is_sorted: is_sorted server.(Server.OperationsPerformed)
    ; MyOperations_is_sorted: is_sorted server.(Server.MyOperations)
    ; Id_in_range: (uint.Z server.(Server.Id) >= 0)%Z /\ (uint.nat server.(Server.Id) < length server.(Server.VectorClock))%nat
    ; EXTRA_SERVER_INVARIANT: EXTRA server
    }.

  Record CLIENT_INVARIANT (EXTRA: Client.t u64 -> Prop) (client: Client.t u64) : Prop :=
    CLIENT_INVARIANT_INTRO
    { SessionSemantic_le_5: (uint.nat client.(Client.SessionSemantic) <= 5)%nat
    ; EXTRA_CLIENT_INVARIANT: EXTRA client
    }.

End INVARIANT.

Notation WEAK_SERVER_INVARIANT := INVARIANT.WEAK_SERVER_INVARIANT.
Notation SERVER_INVARIANT := INVARIANT.SERVER_INVARIANT.
Notation CLIENT_INVARIANT := INVARIANT.CLIENT_INVARIANT.

Section heap.

Import ServerSide.

Context `{hG: !heapGS Σ}.

Lemma Operation_well_formed (n: nat) v op
  : (isOperation v op n)%I ⊢@{iProp Σ} (⌜Operation.well_formed (u64_well_formed := fun _ => True) n op⌝)%I.
Proof.
  iIntros "H_hd". iDestruct "H_hd" as "(H3 & %H2 & %H1)"; iClear "H3".
  iPureIntro; split; [eapply SessionPrelude.Forall_True | done].
Qed.

Lemma Forall_Operation_well_formed (n: nat) vs ops
  : ([∗ list] v;op ∈ vs;ops, isOperation v op n)%I ⊢@{iProp Σ} (⌜Forall (Operation.well_formed (u64_well_formed := fun _ => True) n) ops⌝)%I.
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

Lemma VersionVector_length s ops n
  : (isOperationSlice s ops n)%I ⊢@{iProp Σ} (⌜∀ i : nat, ∀ e, ops !! i = Some e -> length e.(Operation.VersionVector) = n⌝)%I.
Proof.
  iIntros "(%vs & H_vs & H)".
  iPoseProof (Forall_Operation_well_formed with "H") as "%H_well_formed".
  pose proof (List.Forall_forall (Operation.well_formed (u64_well_formed := fun _ => True) n) ops) as claim.
  rewrite claim in H_well_formed; iPureIntro; intros i x H_x.
  enough (WTS: Operation.well_formed (u64_well_formed := fun _ => True) n x) by now red in WTS.
  eapply H_well_formed; eapply SessionPrelude.lookup_In; eauto.
Qed.

Lemma pers_isOperation v op (n: nat)
  : (isOperation v op n)%I ⊢@{iProp Σ} (<pers> (isOperation v op n))%I.
Proof.
  iIntros "#H"; done.
Qed.

Lemma pers_big_sepL2_isOperation vs ops (n: nat)
  : ([∗ list] v;op ∈ vs;ops, isOperation v op n)%I ⊢@{iProp Σ} (<pers> ([∗ list] v;op ∈ vs;ops, isOperation v op n))%I.
Proof.
  iIntros "H_big_sepL2"; iApply (big_sepL2_persistently).
  iApply (big_sepL2_mono (λ k, λ y1, λ y2, isOperation y1 y2 n)%I with "[$H_big_sepL2]").
  intros; iIntros "#H"; done.
Qed.

Lemma pers_emp
  : (emp)%I ⊢@{iProp Σ} (<pers> emp)%I.
Proof.
  iIntros "#H"; done.
Qed.

Lemma big_sepL2_isOperation_elim l ops (n: nat) (i: nat) l_i ops_i
  (H_l_i: l !! i = Some l_i)
  (H_ops_i: ops !! i = Some ops_i)
  : ([∗ list] opv;o ∈ ops;l, isOperation opv o n)%I ⊢@{iProp Σ} (isOperation ops_i l_i n)%I.
Proof.
  rewrite <- take_drop with (l := l) (i := i); rewrite <- take_drop with (l := ops) (i := i); iIntros "H". 
  assert (i < length l)%nat as H1_i by now eapply lookup_lt_is_Some_1.
  assert (i < length ops)%nat as H2_i by now eapply lookup_lt_is_Some_1.  
  iAssert (([∗ list] opv;o ∈ take i ops;take i l, isOperation opv o n) ∗ ([∗ list] opv;o ∈ drop i ops;drop i l, isOperation opv o n))%I with "[H]" as "[H1 H2]".
  { iApply (big_sepL2_app_equiv with "H"); do 2 rewrite length_take; word. }
  destruct (drop i ops) as [ | ops_i' ops_suffix] eqn: H_ops_suffix.
  { apply f_equal with (f := length) in H_ops_suffix; simpl in *; rewrite length_drop in H_ops_suffix. word. }
  iPoseProof (big_sepL2_cons_inv_l with "[$H2]") as "(%l_i' & %l_suffix & %H_l_suffix & H3 & H4)".
  rewrite <- take_drop with (l := l) (i := i) in H_l_i; rewrite <- take_drop with (l := ops) (i := i) in H_ops_i.
  rewrite H_l_suffix in H_l_i; rewrite H_ops_suffix in H_ops_i.
  assert (i = length (take i l)) as H3_i.
  { rewrite length_take; word. }
  assert (i = length (take i ops)) as H4_i.
  { rewrite length_take; word. }
  pose proof (list_lookup_middle (take i l) l_suffix l_i' i H3_i) as EQ_l_i.
  pose proof (list_lookup_middle (take i ops) ops_suffix ops_i' i H4_i) as EQ_ops_i.
  assert (l_i = l_i' /\ ops_i = ops_i') as [<- <-] by now split; congruence.
  iExact "H3".
Qed.

Lemma big_sepL2_isOperation_intro l ops n
  (LENGTH: length l = length ops)
  : (∀ i : nat, ∀ l_i, ∀ ops_i, ⌜(l !! i = Some l_i) /\ (ops !! i = Some ops_i)⌝ -∗ isOperation ops_i l_i n)%I ⊢@{iProp Σ} ([∗ list] opv;o ∈ ops;l, isOperation opv o n)%I.
Proof.
  revert ops n LENGTH; induction l as [ | l_hd l_tl IH], ops as [ | ops_hd ops_tl]; intros; simpl in *; try congruence.
  - iIntros "#H"; iClear "H"; done.
  - iIntros "#H"; iSplit.
    + iApply "H"; instantiate (1 := 0%nat); done.
    + iApply IH. { word. }
      iIntros "%i %l_i %ops_i [%H_l_i %H_ops_i]"; iApply "H"; instantiate (1 := S i); done.
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
  iSplitL "H_middle".
  { iExact "H_middle". }
  rewrite take_drop; iSplitL "H_prefix".
  { iExact "H_prefix". }
  { rewrite <- drop_drop with (l := xs) (n1 := 1%nat) (n2 := i); rewrite -> EQ; iExact "H_suffix". }
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
