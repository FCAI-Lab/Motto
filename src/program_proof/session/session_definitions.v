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

Definition BOUND (a: Z) (n: nat) : Prop :=
  a >= 1 /\ Z.of_nat n <= 2 ^ 64 - a.

#[universes(template)]
Class has_value_boundary (t: Type) : Type :=
  value_bound (a: Z) (object: t) : Prop.

#[global] Hint Unfold value_bound : session_hints.

#[global]
Instance u64_has_value_boundary : has_value_boundary u64 :=
  fun a: Z => fun u: u64 => a >= 1 /\ uint.Z u <= 2 ^ 64 - a.

#[global]
Instance nat_has_value_boundary : has_value_boundary nat :=
  BOUND.

Lemma BOUND_dec a n
  : {BOUND a n} + {~ BOUND a n}.
Proof.
  unfold BOUND;
  pose proof (Z.ge_dec a 1) as [YES_ge | NO_ge];
  pose proof (Z.le_dec (Z.of_nat n) (2 ^ 64 - a)) as [YES_le | NO_le];
  first [now left; split | right; word].
Qed.

Lemma maybe_u64 (a: Z) (n: nat)
  : { RET : option u64 | match RET with Some v => value_bound a n /\ uint.nat v = n | None => ~ value_bound a n end }.
Proof.
  pose proof (BOUND_dec a n) as [YES | NO].
  - red in YES; exists (Some (W64 n)); split; trivial; word.
  - exists None; trivial.
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

    Definition isOperation (v: tuple_of Operation.tv) (op: Operation.t nat) (n: nat) : iProp Σ :=
      ∃ object, ⌜Operation.FMap u64 nat (fun u : u64 => uint.nat u) object = op⌝ ∗
      own_slice_small v!(0) uint64T DfracDiscarded object.(Operation.VersionVector) ∗
      ⌜v!(1) = object.(Operation.Data)⌝ ∗
      ⌜Operation.size_of op = n⌝.

    Definition isOperationSlice (s: Slice.t) (ops: list (Operation.t nat)) (n: nat) : iProp Σ :=
      ∃ vs, own_slice s (struct.t Operation) (DfracOwn 1) vs ∗ [∗ list] v;op ∈ vs;ops, isOperation v op n.

    Definition isMessage (v: tuple_of Message.tv) (msg: Message.t nat) (n: nat) (len_c2s: nat) (len_s2c: nat) : iProp Σ :=
      ∃ object, ⌜Message.FMap u64 nat (fun u : u64 => uint.nat u) object = msg⌝ ∗
      ⌜v!(0) = object.(Message.MessageType)⌝ ∗
      ⌜v!(1) = object.(Message.C2S_Client_Id)⌝ ∗
      ⌜v!(2) = object.(Message.C2S_Server_Id)⌝ ∗
      ⌜v!(3) = object.(Message.C2S_Client_OperationType)⌝ ∗
      ⌜v!(4) = object.(Message.C2S_Client_Data)⌝ ∗
      own_slice_small v!(5) uint64T (DfracOwn 1) object.(Message.C2S_Client_VersionVector) ∗
      ⌜len_c2s = length object.(Message.C2S_Client_VersionVector)⌝ ∗
      ⌜v!(6) = object.(Message.S2S_Gossip_Sending_ServerId)⌝ ∗
      ⌜v!(7) = object.(Message.S2S_Gossip_Receiving_ServerId)⌝ ∗
      isOperationSlice v!(8) msg.(Message.S2S_Gossip_Operations) n ∗
      ⌜v!(9) = object.(Message.S2S_Gossip_Index)⌝ ∗
      ⌜v!(10) = object.(Message.S2S_Acknowledge_Gossip_Sending_ServerId)⌝ ∗
      ⌜v!(11) = object.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId)⌝ ∗
      ⌜v!(12) = object.(Message.S2S_Acknowledge_Gossip_Index)⌝ ∗
      ⌜v!(13) = object.(Message.S2C_Client_OperationType)⌝ ∗
      ⌜v!(14) = object.(Message.S2C_Client_Data)⌝ ∗
      own_slice_small v!(15) uint64T (DfracOwn 1) object.(Message.S2C_Client_VersionVector) ∗
      ⌜v!(16) = object.(Message.S2C_Server_Id)⌝ ∗
      ⌜v!(17) = object.(Message.S2C_Client_Number)⌝ ∗
      ⌜Message.size_of msg = (len_c2s, len_s2c)⌝.

    Definition isMessageSlice (s: Slice.t) (msgs: list (Message.t nat)) (n: nat) (len_c2s: nat) : iProp Σ :=
      ∃ vs, own_slice s (struct.t Message) (DfracOwn 1) vs ∗ [∗ list] v;msg ∈ vs;msgs, ∃ len_s2c : nat, isMessage v msg n len_c2s len_s2c.

    Definition isServer' {OWN_UnsatisfiedRequests: bool} (v: tuple_of Server.tv) (server: Server.t nat) (n: nat) (len_vc: nat) (len_op: nat) (len_mo: nat) (len_po: nat) (len_ga: nat) : iProp Σ :=
      ∃ object, ⌜Server.FMap u64 nat (fun u : u64 => uint.nat u) object = server⌝ ∗
      ⌜v!(0) = object.(Server.Id)⌝ ∗
      ⌜v!(1) = object.(Server.NumberOfServers)⌝ ∗
      (if OWN_UnsatisfiedRequests then isMessageSlice v!(2) server.(Server.UnsatisfiedRequests) n len_vc else emp)%I ∗
      own_slice_small v!(3) uint64T (DfracOwn 1) object.(Server.VectorClock) ∗
      isOperationSlice v!(4) server.(Server.OperationsPerformed) len_op ∗
      isOperationSlice v!(5) server.(Server.MyOperations) len_mo ∗
      isOperationSlice v!(6) server.(Server.PendingOperations) len_po ∗
      own_slice_small v!(7) uint64T (DfracOwn 1) object.(Server.GossipAcknowledgements) ∗
      ⌜Server.size_of server = (len_vc, len_op, len_mo, len_po, len_ga)⌝.

  End heap.

  Notation isServer := (isServer' (OWN_UnsatisfiedRequests := true)).

  Section Coq_nat.

  #[local] Open Scope nat_scope.

  Fixpoint coq_compareVersionVector (v1: list nat) (v2: list nat) : bool :=
    match v1 with
    | [] => true
    | h1 :: t1 =>
      match v2 with
      | [] => true
      | h2 :: t2 => (h2 <=? h1)%nat && (coq_compareVersionVector t1 t2)
      end
    end.

  Fixpoint coq_lexicographicCompare (v1: list nat) (v2: list nat) : bool :=
    match v1 with
    | [] => false
    | h1 :: t1 =>
      match v2 with
      | [] => false
      | h2 :: t2 => if (h1 =? h2)%nat then coq_lexicographicCompare t1 t2 else (h2 <? h1)%nat
      end
    end.

  Definition coq_maxTwoInts (x: nat) (y: nat) : nat :=
    Nat.max x y.

  Fixpoint coq_maxTS (v1: list nat) (v2: list nat) : list nat :=
    match v1 with
    | [] => []
    | hd1 :: tl1 =>
      match v2 with
      | [] => []
      | hd2 :: tl2 => coq_maxTwoInts hd1 hd2 :: coq_maxTS tl1 tl2
      end
    end.

  Definition coq_oneOffVersionVector (v1: list nat) (v2: list nat) : bool :=
    let loop_step (acc: bool * bool) (elem: nat * nat) : bool * bool :=
      let (e1, e2) := elem in
      let (output, canApply) := acc in
      if canApply && (e1 + 1 =? e2)%nat then
        (output, false)
      else if (e2 <=? e1)%nat then
        (output, canApply)
      else 
        (false, canApply)
    in
    let (output, canApply) := fold_left loop_step (zip v1 v2) (true, true) in
    output && negb canApply.

  Fixpoint coq_equalSlices (s1: list nat) (s2: list nat) : bool :=
    match s1 with
    | [] => true
    | h1 :: t1 =>
      match s2 with
      | [] => true
      | h2 :: t2 => (h1 =? h2)%nat && coq_equalSlices t1 t2
      end
    end.

  Variant binarySearch_spec (needle: Operation.t nat) (l: list (Operation.t nat)) (n: nat) (RESULT: nat) : Prop :=
    | binarySearch_spec_intro (prefix: list (list nat)) (suffix: list (list nat))
      (LENGTH: RESULT = length prefix)
      (VECTOR: map Operation.getVersionVector l = if forallb (fun x => negb (coq_equalSlices x.(Operation.VersionVector) needle.(Operation.VersionVector))) l then prefix ++ suffix else prefix ++ [Operation.getVersionVector needle] ++ suffix)
      (PREFIX: ∀ op, In op prefix -> coq_lexicographicCompare needle.(Operation.VersionVector) op = true)
      (SUFFIX: ∀ op, In op suffix -> coq_lexicographicCompare op needle.(Operation.VersionVector) = true)
      : binarySearch_spec needle l n RESULT.

  Fixpoint coq_sortedInsert (l: list (Operation.t nat)) (i: Operation.t nat) : list (Operation.t nat) :=
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

  Definition coq_deleteAtIndexOperation (ops: list (Operation.t nat)) (index: nat) : list (Operation.t nat) :=
    take index ops ++ drop (index + 1)%nat ops.

  Definition coq_deleteAtIndexMessage (msgs: list (Message.t nat)) (index: nat) : list (Message.t nat) :=
    take index msgs ++ drop (index + 1)%nat msgs.

  Definition coq_getDataFromOperationLog (l: list (Operation.t nat)) : _Data.t :=
    match last l with
    | Some v => v.(Operation.Data)
    | None => IntoVal_def _Data.t
    end.

  Definition coq_receiveGossip (server: Server.t nat) (request: Message.t nat) : Server.t nat :=
    if (length request.(Message.S2S_Gossip_Operations) =? 0)%nat then
      server
    else
      let first_loop_output : Server.t nat :=
        let focus := request.(Message.S2S_Gossip_Operations) in
        let loop_step (acc: Server.t nat) (elem: Operation.t nat) : Server.t nat :=
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
      let second_loop_output : Server.t nat * nat * list nat :=
        let focus := server.(Server.PendingOperations) in
        let loop_step (acc: Server.t nat * nat * list nat) (elem: Operation.t nat) : Server.t nat * nat * list nat :=
          let '(server, i, seen) := acc in
            if coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then
              (Server.mk _ server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) (coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector)) (coq_sortedInsert server.(Server.OperationsPerformed) elem) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements), (i + 1)%nat, seen ++ [i])
            else
              (server, (i + 1)%nat, seen)
        in
        fold_left loop_step focus (server, 0%nat, [])
      in
      let '(server, _, seen) := second_loop_output in
      let third_loop_output : nat * nat * list (Operation.t nat) :=
        let focus := server.(Server.PendingOperations) in
        let loop_step (acc: nat * nat * list (Operation.t nat)) (elem: Operation.t nat) : nat * nat * list (Operation.t nat) :=
          let '(i, j, output) := acc in
          match seen !! j with
          | Some i' => if (i =? i')%nat then ((i + 1)%nat, (j + 1)%nat, output) else ((i + 1)%nat, j, output ++ [elem])
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

  Definition coq_acknowledgeGossip (s: Server.t nat) (r: Message.t nat) : Server.t nat :=
    let i := r.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) in
    let l := s.(Server.GossipAcknowledgements) in
    if (i <? length l)%nat then
      let prevGossipAcknowledgementsValue : nat :=
        match s.(Server.GossipAcknowledgements) !! i with
        | Some x => x
        | None => 0%nat
        end
      in
      let newGossipAcknowledgements := coq_maxTwoInts prevGossipAcknowledgementsValue r.(Message.S2S_Acknowledge_Gossip_Index) in
      let gossipAcknowledgements := <[i := newGossipAcknowledgements]> l in
      Server.mk _ s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) gossipAcknowledgements
    else
      s.

  Definition coq_getGossipOperations (s: Server.t nat) (serverId: nat) : list (Operation.t nat) :=
    match s.(Server.GossipAcknowledgements) !! serverId with
    | Some v => drop v s.(Server.MyOperations)
    | None => []
    end.

  Definition coq_processClientRequest (s: Server.t nat) (r: Message.t nat) : bool * Server.t nat * Message.t nat :=
    if coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector) then
      if (r.(Message.C2S_Client_OperationType) =? 0)%nat then
        let S2C_Client_Data := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
        let S2C_Client_VersionVector := s.(Server.VectorClock) in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server.Id) in
        (true, s, Message.mk nat 4 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)
      else
        let v := match s.(Server.VectorClock) !! s.(Server.Id) with Some v => v | None => 0 end in
        let VectorClock := <[s.(Server.Id) := (v + 1)%nat]> s.(Server.VectorClock) in
        let OperationsPerformed := coq_sortedInsert s.(Server.OperationsPerformed) (Operation.mk nat VectorClock r.(Message.C2S_Client_Data)) in
        let MyOperations := coq_sortedInsert s.(Server.MyOperations) (Operation.mk nat VectorClock r.(Message.C2S_Client_Data)) in
        let S2C_Client_OperationType := 1 in
        let S2C_Client_Data := IntoVal_def _Data.t in
        let S2C_Client_VersionVector := VectorClock in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server.Id) in
        (true, Server.mk nat s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), Message.mk nat 4 0 0 0 (W64 0) [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)
    else
      (false, s, Message.mk nat 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0).

  Definition coq_processRequest (server: Server.t nat) (request: Message.t nat) : Server.t nat * list (Message.t nat) :=
    match request.(Message.MessageType) with
    | 0%nat =>
      let '(succeeded, server, reply) := coq_processClientRequest server request in
      if succeeded then
        (server, [reply])
      else
        let UnsatisfiedRequests := server.(Server.UnsatisfiedRequests) ++ [request] in 
        let server := Server.mk nat server.(Server.Id) server.(Server.NumberOfServers) UnsatisfiedRequests server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements) in
        (server, [])
    | 1%nat =>
      let server := coq_receiveGossip server request in
      let focus := server.(Server.UnsatisfiedRequests) in
      let loop_init : nat * Server.t nat * list (Message.t nat) :=
        (0%nat, server, [])
      in
      let loop_step (acc: nat * Server.t nat * list (Message.t nat)) (element: Message.t nat) : nat * Server.t nat * list (Message.t nat) :=
        let '(i, s, outGoingRequests) := acc in
        let '(succeeded, s, reply) := coq_processClientRequest s element in
        if succeeded then
          let UnsatisfiedRequests := coq_deleteAtIndexMessage s.(Server.UnsatisfiedRequests) i in
          (i, Server.mk nat s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), outGoingRequests ++ [reply])
        else
          ((i + 1)%nat, s, outGoingRequests)
      in
      let '(_, server, outGoingRequests) := fold_left loop_step focus loop_init in
      (server, outGoingRequests)
    | 2%nat => (coq_acknowledgeGossip server request, [])
    | 3%nat =>
      let loop_step (acc: Server.t nat * list (Message.t nat)) (index: nat) : Server.t nat * list (Message.t nat) :=
        let '(server, outGoingRequests) := acc in
        let operations := coq_getGossipOperations server index in
        if negb (index =? server.(Server.Id))%nat && negb (length operations =? 0)%nat then
          let GossipAcknowledgements := <[index := length server.(Server.MyOperations)]> server.(Server.GossipAcknowledgements) in
          let S2S_Gossip_Sending_ServerId := server.(Server.Id) in
          let S2S_Gossip_Receiving_ServerId := index in
          let S2S_Gossip_Operations := operations in
          let S2S_Gossip_Index := length (server.(Server.MyOperations)) in
          let message := Message.mk nat 1 0 0 0 (IntoVal_def _Data.t) [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 in
          (Server.mk nat server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) GossipAcknowledgements, outGoingRequests ++ [message])
        else
          (server, outGoingRequests)
      in
      let focus := seq 0%nat server.(Server.NumberOfServers) in
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

  Definition Client_u64 (v: tuple_of Client.tv) (client: Client.t nat) (n: nat) : iProp Σ :=
    ∃ object, ⌜Client.FMap u64 nat (fun u : u64 => uint.nat u) object = client⌝ ∗
    ⌜v!(0) = object.(Client.Id)⌝ ∗
    ⌜v!(1) = object.(Client.NumberOfServers)⌝ ∗
    own_slice_small v!(2) uint64T (DfracOwn 1) object.(Client.WriteVersionVector) ∗
    own_slice_small v!(3) uint64T (DfracOwn 1) object.(Client.ReadVersionVector) ∗
    ⌜v!(4) = object.(Client.SessionSemantic)⌝ ∗
    ⌜(Client.size_of client, uint.nat client.(Client.NumberOfServers)) = (n, n, n)⌝.

  End heap.

  Section Coq_nat.

  #[local] Open Scope nat_scope.

  Import ServerSide.

  Definition coq_read (c: Client.t nat) (serverId: nat) : Message.t nat :=
    match c.(Client.SessionSemantic) with
    | 0%nat => Message.mk nat 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) (replicate c.(Client.NumberOfServers) 0) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 1%nat => Message.mk nat 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) (replicate c.(Client.NumberOfServers) 0) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 2%nat => Message.mk nat 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) (replicate c.(Client.NumberOfServers) 0) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 3%nat => Message.mk nat 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) c.(Client.ReadVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 4%nat => Message.mk nat 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) c.(Client.WriteVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 5%nat => Message.mk nat 0 c.(Client.Id) serverId 0 (IntoVal_def _Data.t) (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | _ => Message.mk nat 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    end.

  Definition coq_write (c: Client.t nat) (serverId: nat) (value: _Data.t) : Message.t nat :=
    match c.(Client.SessionSemantic) with
    | 0%nat => Message.mk nat 0 c.(Client.Id) serverId 1 value (replicate c.(Client.NumberOfServers) 0) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 1%nat => Message.mk nat 0 c.(Client.Id) serverId 1 value (replicate c.(Client.NumberOfServers) 0) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 2%nat => Message.mk nat 0 c.(Client.Id) serverId 1 value (replicate c.(Client.NumberOfServers) 0) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 3%nat => Message.mk nat 0 c.(Client.Id) serverId 1 value c.(Client.ReadVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 4%nat => Message.mk nat 0 c.(Client.Id) serverId 1 value c.(Client.WriteVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | 5%nat => Message.mk nat 0 c.(Client.Id) serverId 1 value (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    | _ => Message.mk nat 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0
    end.

  Definition coq_processRequest (c: Client.t nat) (requestType: nat) (serverId: nat) (value: _Data.t) (ackMessage: Message.t nat) : Client.t nat * Message.t nat :=
    match requestType with
    | 0%nat => (c, coq_read c serverId)
    | 1%nat => (c, coq_write c serverId value)
    | 2%nat =>
      match ackMessage.(Message.S2C_Client_OperationType) with
      | 0%nat => (Client.mk nat c.(Client.Id) c.(Client.NumberOfServers) c.(Client.WriteVersionVector) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.SessionSemantic), Message.mk nat 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
      | 1%nat => (Client.mk nat c.(Client.Id) c.(Client.NumberOfServers) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.ReadVersionVector) c.(Client.SessionSemantic), Message.mk nat 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
      | _ => (c, Message.mk nat 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
      end
    | _ => (c, Message.mk nat 0 0 0 0 (IntoVal_def _Data.t) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.t) [] 0 0)
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

Definition is_sorted (l: list (Operation.t nat)) : Prop :=
  ∀ i, ∀ j, (i < j)%nat -> ∀ o1, ∀ o2, l !! i = Some o1 -> l !! j = Some o2 ->
  coq_lexicographicCompare o2.(Operation.VersionVector) o1.(Operation.VersionVector) = true.

Lemma redefine_is_sorted n l
  : is_sorted l = isSorted (hsOrd := Operation.hsOrd n) l.
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

Section heap.

Import ServerSide.

Context `{hG: !heapGS Σ}.

Lemma Operation_well_formed (n: nat) v op
  : (isOperation v op n)%I ⊢@{iProp Σ} (⌜Operation.well_formed (u64_well_formed := fun _ => True) n op⌝)%I.
Proof.
  iIntros "H_hd". iDestruct "H_hd" as "(%object & H_object & H3 & %H2 & %H1)"; iClear "H3".
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

End heap.
