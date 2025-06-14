Require Import Perennial.program_proof.session.session_definitions.

Reserved Infix ">>=" (left associativity, at level 90).
Reserved Infix "=~=" (at level 70, no associativity).

(** Section SIMILARITY. *)

#[universes(template)]
Class Similarity (A : Type) (A' : Type) : Type :=
  is_similar_to (x : A) (x' : A') : Prop.

Infix "=~=" := is_similar_to.

#[global]
Instance Similarity_forall {D : Type} {D' : Type} {C : D -> Type} {C' : D' -> Type} (DOM_SIM : Similarity D D') (COD_SIM : forall x : D, forall x' : D', x =~= x' -> Similarity (C x) (C' x')) : Similarity (forall x : D, C x) (forall x' : D', C' x') :=
  fun f => fun f' => forall x : D, forall x' : D', forall x_corres : x =~= x', @is_similar_to (C x) (C' x') (COD_SIM x x' x_corres) (f x) (f' x').

#[global]
Instance Similarity_prod {A : Type} {A' : Type} {B : Type} {B' : Type} (FST_SIM : Similarity A A') (SND_SIM : Similarity B B') : Similarity (A * B) (A' * B') :=
  fun p => fun p' => fst p =~= fst p' /\ snd p =~= snd p'.

Inductive list_corres {A : Type} {A' : Type} `{Similarity A A'} : Similarity (list A) (list A') :=
  | nil_corres
    : [] =~= []
  | cons_corres (x : A) (x' : A') (xs : list A) (xs' : list A')
    (x_corres : x =~= x')
    (xs_corres : xs =~= xs')
    : x :: xs =~= x' :: xs'.

#[local] Hint Constructors list_corres : core.

#[global]
Instance Similarity_list {A : Type} {A' : Type} (A_SIM : Similarity A A') : Similarity (list A) (list A') :=
  @list_corres A A' A_SIM.

Inductive option_corres {A : Type} {A' : Type} {SIM : Similarity A A'} : Similarity (option A) (option A') :=
  | None_corres
    : None =~= None
  | Some_corres (x : A) (x' : A')
    (x_corres : x =~= x')
    : Some x =~= Some x'.

#[local] Hint Constructors option_corres : core.

#[global]
Instance Similarity_option {A : Type} {A' : Type} (SIM : Similarity A A') : Similarity (option A) (option A') :=
  @option_corres A A' SIM.

#[global]
Instance Similarity_bool : Similarity bool bool :=
  @eq bool.

#[global]
Instance Similarity_nat : Similarity nat nat :=
  @eq nat.

#[global]
Instance Similarity_Data : Similarity _Data.w _Data.w :=
  @eq u64.

(** End SIMILARITY. *)

(** Section MONAD. *)

#[universes(polymorphic=yes), projections(primitive)]
Class isMonad@{d c} (M : Type@{d} -> Type@{c}) : Type@{max(d + 1, c + 1)} :=
  { bind {A : Type@{d}} {B : Type@{d}} (m : M A) (k : A -> M B) : M B
  ; pure {A : Type@{d}} : A -> M A
  ; bind_cong2 {A : Type@{d}} {B : Type@{d}} (m1 : M A) (m2 : M A) (k1 : A -> M B) (k2 : A -> M B)
    (m1_eq_m2 : m1 = m2)
    (k1_eq_k2 : forall x : A, k1 x = k2 x)
    : bind m1 k1 = bind m2 k2
  ; bind_assoc {A : Type@{d}} {B : Type@{d}} {C : Type@{d}} (m : M A) (k : A -> M B) (k' : B -> M C)
    : bind m (fun x => bind (k x) k') = bind (bind m k) k'
  ; bind_pure_l {A : Type@{d}} {B : Type@{d}} (k : A -> M B) (x : A)
    : bind (pure x) k = k x
  ; bind_pure_r {A : Type@{d}} (m : M A)
    : bind m pure = m
  }.

Infix ">>=" := bind.

#[universes(polymorphic=yes)]
Definition monad@{u v} {M : Type@{u} -> Type@{v}} {MONAD : isMonad@{u v} M} {A : Type@{u}} : Type@{v} :=
  M A.

Declare Scope monad_scope.
Declare Custom Entry do_notation.

Delimit Scope monad_scope with monad.
Bind Scope monad_scope with monad.

Reserved Notation "'do' m" (m custom do_notation at level 10, at level 0, format "'do'  '//' m").
Notation "'do' m" := m : monad_scope.
Notation "'do' m" := (m : monad).

Notation "x '<-' m1 ';' m2" := (m1 >>= fun x => m2) (in custom do_notation at level 0, x ident, m1 constr, m2 custom do_notation at level 10, format "x  '<-'  m1 ';' '//' m2").
Notation "''' x '<-' m1 ';' m2" := (m1 >>= fun 'x => m2) (in custom do_notation at level 0, x pattern, m1 constr, m2 custom do_notation at level 10, format "''' x  '<-'  m1 ';' '//' m2").
Notation "m1 ';' m2" := (m1 >>= fun _ => m2) (in custom do_notation at level 0, m1 constr, m2 custom do_notation at level 10, format "m1 ';' '//' m2").
Notation "'ret' t" := (pure t) (in custom do_notation at level 10, t constr, format "'ret'  t").
Notation "t" := t (in custom do_notation at level 0, t constr).

#[local] Open Scope monad_scope.

#[universes(polymorphic=yes)]
Definition identity@{u} (A : Type@{u}) : Type@{u} :=
  A.

#[global, program]
Instance identity_isMonad : isMonad identity :=
  { pure {A} (x : A) := x
  ; bind {A} {B} (m : A) (k : A -> B) := k m
  }.
Next Obligation.
  intros; cbn in *. congruence.
Qed.
Next Obligation.
  intros; cbn in *. congruence.
Qed.
Next Obligation.
  intros; cbn in *. congruence.
Qed.
Next Obligation.
  intros; cbn in *. congruence.
Qed.

#[universes(polymorphic=yes)]
Definition Err@{u} (A : Type@{u}) : Type@{u} :=
  (bool * A)%type.

#[global, program]
Instance Err_isMonad : isMonad Err :=
  { pure {A} (x : A) := (true, x)
  ; bind {A} {B} (m : Err A) (k : A -> Err B) :=
    let (b, y) := k m.2 in
    (m.1 && b, y)
  }.
Next Obligation.
  intros; cbn in *. destruct m1, m2; cbn in *.
  destruct (k1 a) as [? ?] eqn: H_OBS;
  destruct (k2 a0) as [? ?] eqn: H_OBS';
  cbn in *; congruence.
Qed.
Next Obligation.
  intros; cbn in *. destruct m as [? ?]; cbn in *.
  destruct (k a) as [? ?] eqn: H_OBS; cbn in *.
  destruct (k' b1) as [? ?] eqn: H_OBS'; cbn in *.
  rewrite andb_assoc; congruence.
Qed.
Next Obligation.
  intros; cbn in *. destruct (k x) as [? ?]; trivial.
Qed.
Next Obligation.
  intros; cbn in *. destruct m as [? ?]; simpl. rewrite andb_true_r. trivial.
Qed.

#[global, program]
Instance option_isMonad : isMonad option :=
  { pure {A} := @Some A
  ; bind {A} {B} (m : option A) (k : A -> option B) :=
    match m with
    | Some x => k x
    | None => None
    end
  }.
Next Obligation.
  intros; cbn in *. destruct m1, m2; cbn in *; try congruence.
Qed.
Next Obligation.
  intros; cbn in *. destruct m as [? | ]; cbn in *; try congruence.
Qed.
Next Obligation.
  intros; cbn in *. destruct (k x) as [? | ]; cbn in *; try congruence.
Qed.
Next Obligation.
  intros; cbn in *. destruct m as [? | ]; cbn in *; try congruence.
Qed.

Fixpoint fold_left' {M : Type -> Type} `{isMonad M} {A : Type} {B : Type} (f : A -> B -> M A) (xs : list B) (z : A) : M A :=
  match xs with
  | [] => do
    ret z
  | x :: xs' => do
    'y <- f z x;
    fold_left' f xs' y
  end.

Class isSuperMonad (M : Type -> Type) `{isMonad M} : Type :=
  { put_if {A : Type} (guard : bool) : A -> M A
  ; tryget {A : Type} : M A -> option A
  ; tryget_put_if_true {A : Type} (x : A)
    : tryget (put_if true x) = Some x
  ; tryget_put_if_false {A : Type} (x : A)
    : tryget (put_if false x) = None
  ; tryget_pure {A : Type} (x : A)
    : forall z : A, tryget (pure x) = Some z -> x = z
  ; tryget_bind {A : Type} {B : Type} (m : M A) (k : A -> M B)
    : forall z : B, tryget (bind m k) = Some z -> (exists x : A, tryget m = Some x /\ tryget (k x) = Some z)
  }.

#[global, program]
Instance Err_isSuperMonad : isSuperMonad Err :=
  { put_if {A} (guard : bool) (x : A) := (guard, x)
  ; tryget {A} (m : Err A) := if m.1 then Some m.2 else None
  }.
Next Obligation.
  intros. simpl in *. trivial.
Qed.
Next Obligation.
  intros. simpl in *. congruence.
Qed.
Next Obligation.
  intros. simpl in *. congruence.
Qed.
Next Obligation.
  intros. cbn in *. destruct m as [[ | ] x]; cbn in *.
  - exists x. split; trivial. destruct (k x) as [[ | ] y]; cbn in *; try congruence.
  - destruct (k x) as [[ | ] y]; cbn in *; try congruence.
Qed.

#[global, program]
Instance option_isSuperMonad : isSuperMonad option :=
  { put_if {A} (guard : bool) (x : A) := if guard then Some x else None
  ; tryget {A} (m : option A) := m
  }.
Next Obligation.
  intros. simpl in *. trivial.
Qed.
Next Obligation.
  intros. unfold pure in *. simpl in *. congruence.
Qed.
Next Obligation.
  intros. unfold pure in *. simpl in *. congruence.
Qed.
Next Obligation.
  intros. cbn in *. destruct m as [x | ]; simpl in *; try congruence.
  exists x. split; trivial.
Qed.

(** End MONAD. *)

(** Section BASIC_CORRES. *)

Definition param0func_corres `{isSuperMonad M} {A : Type} {A' : Type} `{Similarity A A'} (f : A) (f' : M A') : Prop :=
  forall a' : A', tryget f' = Some a' ->
  exists a : A, a =~= a' /\ f = a.

Definition param1func_corres `{isSuperMonad M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (f : A -> B) (f' : A' -> M B') : Prop :=
  forall a' : A', forall b' : B', tryget (f' a') = Some b' ->
  forall a : A, a =~= a' ->
  exists b : B, b =~= b' /\ f a = b.

Definition param2func_corres `{isSuperMonad M} {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} `{Similarity A A'} `{Similarity B B'} `{Similarity C C'} (f : A -> B -> C) (f' : A' -> B' -> M C') : Prop :=
  forall a' : A', forall b' : B', forall c' : C', tryget (f' a' b') = Some c' ->
  forall a : A, a =~= a' ->
  forall b : B, b =~= b' ->
  exists c : C, c =~= c' /\ f a b = c.

Definition param3func_corres `{isSuperMonad M} {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} {D : Type} {D' : Type} `{Similarity A A'} `{Similarity B B'} `{Similarity C C'} `{Similarity D D'} (f : A -> B -> C -> D) (f' : A' -> B' -> C' -> M D') : Prop :=
  forall a' : A', forall b' : B', forall c' : C', forall d' : D', tryget (f' a' b' c') = Some d' ->
  forall a : A, a =~= a' ->
  forall b : B, b =~= b' ->
  forall c : C, c =~= c' ->
  exists d : D, d =~= d' /\ f a b c = d.

#[global]
Instance Similarity_u64 : Similarity u64 nat :=
  fun u => fun n => uint.nat u = n /\ uint.Z u <= CONSTANT - 1.

Module Operation'.

  Record t : Type :=
    mk
    { VersionVector : list nat
    ; Data : nat
    }.

  Record corres (op : Operation.t) (op' : Operation'.t) : Prop :=
    Similarity_Operation_INTRO
    { VersionVector_corres : op.(Operation.VersionVector) =~= op'.(VersionVector)
    ; Data_corres : op.(Operation.Data) =~= op'.(Data)
    }.

End Operation'.

#[local] Hint Constructors Operation'.corres : core.

#[global]
Instance Similarity_Operation : Similarity Operation.t Operation'.t :=
  Operation'.corres.

Module Message'.

  Record t : Type :=
    mk
    { MessageType : nat
    ; C2S_Client_Id : nat
    ; C2S_Server_Id : nat
    ; C2S_Client_OperationType : nat
    ; C2S_Client_Data : _Data.w
    ; C2S_Client_VersionVector : list nat
    ; S2S_Gossip_Sending_ServerId : nat
    ; S2S_Gossip_Receiving_ServerId : nat
    ; S2S_Gossip_Operations : list Operation'.t
    ; S2S_Gossip_Index : nat
    ; S2S_Acknowledge_Gossip_Sending_ServerId : nat
    ; S2S_Acknowledge_Gossip_Receiving_ServerId : nat
    ; S2S_Acknowledge_Gossip_Index : nat
    ; S2C_Client_OperationType : nat
    ; S2C_Client_Data : _Data.w
    ; S2C_Client_VersionVector : list nat
    ; S2C_Server_Id : nat
    ; S2C_Client_Number : nat
    }.

  Record corres (msg : Message.t) (msg' : Message'.t) : Prop :=
    Similarity_Message_INTRO
    { MessageType_corres : msg.(Message.MessageType) =~= msg'.(MessageType)
    ; C2S_Client_Id_corres : msg.(Message.C2S_Client_Id) =~= msg'.(C2S_Client_Id)
    ; C2S_Server_Id_corres : msg.(Message.C2S_Server_Id) =~= msg'.(C2S_Server_Id)
    ; C2S_Client_OperationType_corres : msg.(Message.C2S_Client_OperationType) =~= msg'.(C2S_Client_OperationType)
    ; C2S_Client_Data_corres_corres : msg.(Message.C2S_Client_Data) =~= msg'.(C2S_Client_Data)
    ; C2S_Client_VersionVector_corres : msg.(Message.C2S_Client_VersionVector) =~= msg'.(C2S_Client_VersionVector)
    ; S2S_Gossip_Sending_ServerId_corres : msg.(Message.S2S_Gossip_Sending_ServerId) =~= msg'.(S2S_Gossip_Sending_ServerId)
    ; S2S_Gossip_Receiving_ServerId_corres : msg.(Message.S2S_Gossip_Receiving_ServerId) =~= msg'.(S2S_Gossip_Receiving_ServerId)
    ; S2S_Gossip_Operations_corres : msg.(Message.S2S_Gossip_Operations) =~= msg'.(S2S_Gossip_Operations)
    ; S2S_Gossip_Index_corres : msg.(Message.S2S_Gossip_Index) =~= msg'.(S2S_Gossip_Index)
    ; S2S_Acknowledge_Gossip_Sending_ServerId_corres : msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) =~= msg'.(S2S_Acknowledge_Gossip_Sending_ServerId)
    ; S2S_Acknowledge_Gossip_Receiving_ServerId_corres : msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId) =~= msg'.(S2S_Acknowledge_Gossip_Receiving_ServerId)
    ; S2S_Acknowledge_Gossip_Index_corres : msg.(Message.S2S_Acknowledge_Gossip_Index) =~= msg'.(S2S_Acknowledge_Gossip_Index)
    ; S2C_Client_OperationType_corres : msg.(Message.S2C_Client_OperationType) =~= msg'.(S2C_Client_OperationType)
    ; S2C_Client_Data_corres : msg.(Message.S2C_Client_Data) =~= msg'.(S2C_Client_Data)
    ; S2C_Client_VersionVector_corres : msg.(Message.S2C_Client_VersionVector) =~= msg'.(S2C_Client_VersionVector)
    ; S2C_Server_Id_corres : msg.(Message.S2C_Server_Id) =~= msg'.(S2C_Server_Id)
    ; S2C_Client_Number_corres : msg.(Message.S2C_Client_Number) =~= msg'.(S2C_Client_Number)
    }.

End Message'.

#[local] Hint Constructors Message'.corres : core.

#[global]
Instance Similarity_Message : Similarity Message.t Message'.t :=
  Message'.corres.

Module Server'.

  Record t : Type :=
    mk
    { Id : nat
    ; NumberOfServers : nat
    ; UnsatisfiedRequests : list Message'.t
    ; VectorClock : list nat
    ; OperationsPerformed : list Operation'.t
    ; MyOperations : list Operation'.t
    ; PendingOperations : list Operation'.t
    ; GossipAcknowledgements : list nat
    }.

  Record corres (s : Server.t) (s' : Server'.t) : Prop :=
    Similarity_Server_INTRO
    { Id_corres : s.(Server.Id) =~= s'.(Id)
    ; NumberOfServers_corres : s.(Server.NumberOfServers) =~= s'.(NumberOfServers)
    ; UnsatisfiedRequests_corres : s.(Server.UnsatisfiedRequests) =~= s'.(UnsatisfiedRequests)
    ; VectorClock_corres : s.(Server.VectorClock) =~= s'.(VectorClock)
    ; OperationsPerformed_corres : s.(Server.OperationsPerformed) =~= s'.(OperationsPerformed)
    ; MyOperations_corres : s.(Server.MyOperations) =~= s'.(MyOperations)
    ; PendingOperations_corres : s.(Server.PendingOperations) =~= s'.(PendingOperations)
    ; GossipAcknowledgements_corres : s.(Server.GossipAcknowledgements) =~= s'.(GossipAcknowledgements)
    }.

End Server'.

#[local] Hint Constructors Server'.corres : core.

#[global]
Instance Similarity_Server : Similarity Server.t Server'.t :=
  Server'.corres.

Module Client'.

  Record t : Type :=
    mk
    { Id : nat
    ; NumberOfServers : nat
    ; WriteVersionVector : list nat
    ; ReadVersionVector : list nat
    ; SessionSemantic : nat
    }.

  Record corres (c : Client.t) (c' : Client'.t) : Prop :=
    Similarity_Client_INTRO
    { Id_corres : c.(Client.Id) =~= c'.(Id)
    ; NumberOfServers_corres : c.(Client.NumberOfServers) =~= c'.(NumberOfServers)
    ; WriteVersionVector_corres : c.(Client.WriteVersionVector) =~= c'.(WriteVersionVector)
    ; ReadVersionVector_corres : c.(Client.ReadVersionVector) =~= c'.(ReadVersionVector)
    ; SessionSemantic_corres : c.(Client.SessionSemantic) =~= c'.(SessionSemantic)
    }.

End Client'.

#[local] Hint Constructors Client'.corres : core.

#[global]
Instance Similarity_Client : Similarity Client.t Client'.t :=
  Client'.corres.

Lemma fold_left_corres `{isSuperMonad M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (f : A -> B -> A) (f' : A' -> B' -> M A')
  (f_corres : param2func_corres f f')
  : param2func_corres (fold_left f) (fold_left' f').
Proof.
  red. intros xs' z' y' H_OBS xs xs_corres z z_corres. revert z z' y' z_corres H_OBS.
  induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; simpl; intros.
  - exists z. split; trivial. apply tryget_pure in H_OBS. congruence.
  - apply tryget_bind in H_OBS. destruct H_OBS as (_y' & H_OBS & H_y'). eapply IH with (z' := _y'); trivial.
    pose proof (f_corres z' x' _y' H_OBS z z_corres x x_corres) as (y & H_y & <-); trivial.
Qed.

Lemma zip_corres {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (xs : list A) (xs' : list A') (ys : list B) (ys' : list B')
  (xs_corres : xs =~= xs')
  (ys_corres : ys =~= ys')
  : zip xs ys =~= zip xs' ys'.
Proof.
  revert ys ys' ys_corres.
  induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; simpl in *; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; eauto.
  econstructor; [split; trivial | ss!].
Qed.

(** End BASIC_CORRES. *)

Definition downward `{isSuperMonad M} {R : Type} {R' : Type} `{Similarity R R'} (m : identity R) (m' : M R') : Prop :=
  forall r' : R',
  tryget m' = Some r' ->
  exists r : R, r =~= r' /\ m = r.

Notation "'DOWNWARD' tgt '====================' src" := (downward tgt src) (at level 100, no associativity, format "'//' 'DOWNWARD' '//' tgt  '//' '====================' '//' src").

Lemma downward_bind `{isSuperMonad M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (m : identity A) (m' : M A') (k : A -> identity B) (k' : A' -> M B')
  (m_corres : downward m m')
  (k_corres : forall x : A, forall x' : A', x =~= x' -> downward (k x) (k' x'))
  : downward (bind m k) (bind m' k').
Proof.
  unfold downward in *. intros r' H_r'.
  apply tryget_bind in H_r'. destruct H_r' as (x' & H_r' & H_x').
  eapply k_corres with (x' := x'); trivial.
  pose proof (m_corres x' H_r') as (x & H_x & H_m); congruence. 
Qed.

Lemma downward_pure `{isSuperMonad M} {R : Type} {R' : Type} `{Similarity R R'} (x : R) (x' : R')
  (x_corres : x =~= x')
  : downward (pure (M := identity) x) (pure (M := M) x').
Proof.
  red. intros r' H_r'. apply tryget_pure in H_r'. exists x. split; ss!.
Qed.

Lemma downward_fold_left `{isSuperMonad M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (f : A -> B -> identity A) (f' : A' -> B' -> M A') (xs : list B) (xs' : list B') (z : A) (z' : A')
  (f_corres : param2func_corres f f')
  (xs_corres : xs =~= xs')
  (z_corres : z =~= z')
  : downward (fold_left f xs z) (fold_left' f' xs' z').
Proof.
  revert z z' z_corres. induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; simpl; intros.
  - eapply downward_pure; trivial.
  - change (fold_left f xs (f z x)) with (bind (M := identity) (isMonad := identity_isMonad) (f z x) (fun y : A => pure (fold_left f xs y))).
    eapply downward_bind; eauto. intros r' H_r'. pose proof (f_corres z' x' r' H_r' z z_corres x x_corres) as (r & H_r & H_c). subst r.
    exists (f z x). split; ss!.
Qed.

Ltac des :=
  autounfold with session_hints in *;
  repeat (
    match goal with
    | [ |- context C[ (?X =? ?Y)%Z ] ] =>
      let H_OBS := fresh "H_OBS" in destruct (X =? Y) as [ | ] eqn: H_OBS; [rewrite Z.eqb_eq in H_OBS | rewrite Z.eqb_neq in H_OBS]
    | [ |- context C[ (?X <? ?Y)%Z ] ] =>
      let H_OBS := fresh "H_OBS" in destruct (X <? Y) as [ | ] eqn: H_OBS; [rewrite Z.ltb_lt in H_OBS | rewrite Z.ltb_nlt in H_OBS]
    | [ |- context C[ (?X <=? ?Y)%Z ] ] =>
      let H_OBS := fresh "H_OBS" in destruct (X <=? Y) as [ | ] eqn: H_OBS; [rewrite Z.leb_le in H_OBS | rewrite Z.leb_nle in H_OBS]
    | [ |- context C[ (?X >=? ?Y)%Z ] ] => rewrite Z.geb_leb;
      let H_OBS := fresh "H_OBS" in destruct (Y <=? X) as [ | ] eqn: H_OBS; [rewrite Z.leb_le in H_OBS | rewrite Z.leb_nle in H_OBS]
    | [ |- context C[ (?X >? ?Y)%Z ] ] => rewrite Z.gtb_ltb;
      let H_OBS := fresh "H_OBS" in destruct (Y <? X) as [ | ] eqn: H_OBS; [rewrite Z.ltb_lt in H_OBS | rewrite Z.ltb_nlt in H_OBS]
    | [ |- context C[ (?X =? ?Y)%nat ] ] =>
      let H_OBS := fresh "H_OBS" in destruct (X =? Y)%nat as [ | ] eqn: H_OBS; [rewrite Nat.eqb_eq in H_OBS | rewrite Nat.eqb_neq in H_OBS]
    | [ |- context C[ (?X <? ?Y)%nat ] ] =>
      let H_OBS := fresh "H_OBS" in destruct (X <? Y)%nat as [ | ] eqn: H_OBS; [rewrite Nat.ltb_lt in H_OBS | rewrite Nat.ltb_nlt in H_OBS]
    | [ |- context C[ (?X <=? ?Y)%nat ] ] =>
      let H_OBS := fresh "H_OBS" in destruct (X <=? Y)%nat as [ | ] eqn: H_OBS; [rewrite Nat.leb_le in H_OBS | rewrite Nat.leb_nle in H_OBS]
    | [ H : context C[ (?X =? ?Y)%nat ] |- _ ] =>
      let H_OBS := fresh "H_OBS" in destruct (X =? Y)%nat as [ | ] eqn: H_OBS in H; [rewrite Nat.eqb_eq in H_OBS | rewrite Nat.eqb_neq in H_OBS]
    | [ H : context C[ (?X <? ?Y)%nat ] |- _ ] =>
      let H_OBS := fresh "H_OBS" in destruct (X <? Y)%nat as [ | ] eqn: H_OBS in H; [rewrite Nat.ltb_lt in H_OBS | rewrite Nat.ltb_nlt in H_OBS]
    | [ H : context C[ (?X <=? ?Y)%nat ] |- _ ] =>
      let H_OBS := fresh "H_OBS" in destruct (X <=? Y)%nat as [ | ] eqn: H_OBS in H; [rewrite Nat.leb_le in H_OBS | rewrite Nat.leb_nle in H_OBS]
    | [ H : _ /\ _ |- _ ] => let H' := fresh H in destruct H as [H H']
    | [ H : (_, _)%core = (_, _)%core |- _ ] => rewrite -> Tac.pair_inv in H
    | [ |- (_, _)%core = (_, _)%core ] => rewrite -> Tac.pair_inv
    | [ H : exists x, _ |- _ ] => destruct H as [x H]
    | [ H : is_similar_to _ _ |- _ ] => do 2 red in H
    | [ |- is_similar_to _ _ ] => do 2 red
    end
  ).

Tactic Notation "xintros0" ident( a ) :=
  let r' := fresh "res'" in
  let H_r' := fresh "H_res'" in
  intros r' H_r';
  revert r' H_r';
  lazymatch goal with
  | [ |- forall r', tryget ?m' = Some r' -> exists r, r =~= r' /\ ?m = r ] => change (downward m m')
  end.

Tactic Notation "xintros1" ident( a ) :=
  let x := fresh a in
  let x' := fresh a "'" in
  let x_corres := fresh a "_corres" in
  let r' := fresh "res'" in
  let H_r' := fresh "H_res'" in
  intros x' r' H_r' x x_corres;
  revert r' H_r';
  lazymatch goal with
  | [ |- forall r', tryget ?m' = Some r' -> exists r, r =~= r' /\ ?m = r ] => change (downward m m')
  end.

Tactic Notation "xintros2" ident( a ) ident( b ) :=
  let x := fresh a in
  let x' := fresh a "'" in
  let x_corres := fresh a "_corres" in
  let y := fresh b in
  let y' := fresh b "'" in
  let y_corres := fresh b "_corres" in
  let r' := fresh "res'" in
  let H_r' := fresh "H_res'" in
  intros x' y' r' H_r' x x_corres y y_corres;
  revert r' H_r';
  lazymatch goal with
  | [ |- forall r', tryget ?m' = Some r' -> exists r, r =~= r' /\ ?m = r ] => change (downward m m')
  end.

Tactic Notation "xintros3" ident( a ) ident( b ) ident( c ) :=
  let x := fresh a in
  let x' := fresh a "'" in
  let x_corres := fresh a "_corres" in
  let y := fresh b in
  let y' := fresh b "'" in
  let y_corres := fresh b "_corres" in
  let z := fresh c in
  let z' := fresh c "'" in
  let z_corres := fresh c "_corres" in
  let r' := fresh "res'" in
  let H_r' := fresh "H_res'" in
  intros x' y' z' r' H_r' x x_corres y y_corres z z_corres;
  revert r' H_r';
  lazymatch goal with
  | [ |- forall r', tryget ?m' = Some r' -> exists r, r =~= r' /\ ?m = r ] => change (downward m m')
  end.

Module Server_nat.

  Section refine_coq_compareVersionVector.

  Fixpoint coq_compareVersionVector (v1 : list nat) (v2 : list nat) : bool :=
    match v1 with
    | [] => true
    | h1 :: t1 =>
      match v2 with
      | [] => true
      | h2 :: t2 => (h2 <=? h1)%nat && coq_compareVersionVector t1 t2
      end
    end.

  Lemma coq_compareVersionVector_corres
    : ServerSide.coq_compareVersionVector =~= coq_compareVersionVector.
  Proof.
    intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; try (do 2 red; reflexivity).
    des; try word. simpl. eapply IH; trivial.
  Qed.

  End refine_coq_compareVersionVector.

  Section refine_coq_lexicographicCompare.

  Fixpoint coq_lexicographicCompare (v1 : list nat) (v2 : list nat) : bool :=
    match v1 with
    | [] => false
    | h1 :: t1 =>
      match v2 with
      | [] => false
      | h2 :: t2 =>
        if (h1 =? h2)%nat then
          coq_lexicographicCompare t1 t2
        else
          (h2 <? h1)%nat
      end
    end.

  Lemma coq_lexicographicCompare_corres
    : ServerSide.coq_lexicographicCompare =~= coq_lexicographicCompare.
  Proof.
    intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; try (do 2 red; reflexivity).
    des; try word. simpl. eapply IH; trivial.
  Qed.

  End refine_coq_lexicographicCompare.

  Section refine_coq_maxTS.

  Fixpoint coq_maxTS (xs : list nat) (ys : list nat) : list nat :=
    match xs with
    | [] => []
    | x' :: xs' =>
      match ys with
      | [] => []
      | y' :: ys' => Nat.max x' y' :: coq_maxTS xs' ys'
      end
    end.

  Lemma coq_maxTS_corres
    : ServerSide.coq_maxTS =~= coq_maxTS.
  Proof.
    intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; eauto.
    unfold ServerSide.coq_maxTwoInts. des; econstructor 2; eauto; do 2 red; word.
  Qed.

  End refine_coq_maxTS.

  Section refine_coq_oneOffVersionVector.

  Let coq_oneOffVersionVector_u64 :
    ServerSide.coq_oneOffVersionVector =
    fun v1 : list u64 => fun v2 : list u64 => do
    let loop_step (acc : bool * bool) (elem : u64 * u64) : identity (bool * bool) :=
      let '(e1, e2) := elem in
      let '(output, canApply) := acc in
      if canApply && (uint.Z (w64_word_instance.(word.add) e1 (W64 1)) =? uint.Z e2) then do
        ret (output, false)
      else if uint.Z e1 >=? uint.Z e2 then do
        ret (output, canApply)
      else do
        ret (false, canApply)
    in
    do
    '(output, canApply) <- fold_left loop_step (zip v1 v2) (true, true);
    ret (output && negb canApply).
  Proof.
    reflexivity.
  Defined.

  Context `{isSuperMonad M}.

  Definition coq_oneOffVersionVector (v1 : list nat) (v2 : list nat) : M bool :=
    let loop_step (acc : bool * bool) (elem : nat * nat) : M (bool * bool)%type :=
      let '(e1, e2) := elem in
      let '(output, canApply) := acc in
      if canApply && (e1 + 1 =? e2)%nat then do
        ret (output, false)
      else do
        ret ((e2 <=? e1)%nat && output, canApply)
    in
    do
    '(output, canApply) <- fold_left' loop_step (zip v1 v2) (true, true);
    ret (output && negb canApply).

  Lemma coq_oneOffVersionVector_corres
    : param2func_corres (M := M) ServerSide.coq_oneOffVersionVector coq_oneOffVersionVector.
  Proof.
    rewrite coq_oneOffVersionVector_u64. unfold coq_oneOffVersionVector.
    xintros2 v1 v2. eapply downward_bind.
    { eapply downward_fold_left.
      - clear. xintros2 acc elem. destruct acc as [output canApply], acc' as [output' canApply']; simpl in *. destruct elem as [e1 e2], elem' as [e1' e2']; simpl in *.
        destruct acc_corres as [output_corres canApply_corres]; simpl in *. destruct elem_corres as [e1_corres e2_corres]; simpl in *.
        do 2 red in output_corres, canApply_corres, e1_corres, e2_corres. red; Tac.des; intros.
        + destruct canApply' as [ | ]; simpl in *; (destruct (e1' + 1 =? e2')%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']); apply tryget_pure in H1; try word; subst.
          * exists (output', true). split; simpl.
            { split; simpl; do 2 red; trivial. symmetry. replace (uint.nat e2 <=? uint.nat e1)%nat with true by now symmetry; rewrite Nat.leb_le; word. eapply andb_true_l. }
            { rewrite -> CONSTANT_unfold in *. word. }
          * exists (output', false). split; simpl.
            { split; simpl; do 2 red; trivial. symmetry. replace (uint.nat e2 <=? uint.nat e1)%nat with true by now symmetry; rewrite Nat.leb_le; word. eapply andb_true_l. }
            { rewrite -> CONSTANT_unfold in *. word. }
        + destruct canApply' as [ | ]; simpl in *; (destruct (e1' + 1 =? e2')%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']); apply tryget_pure in H1; try word; subst.
          * exists (output', false). split; simpl.
            { split; simpl; do 2 red; trivial. }
            { trivial. }
          * exists (false, false). split; simpl.
            { split; simpl; do 2 red; trivial. replace (uint.nat e2 <=? uint.nat e1)%nat with false by now symmetry; rewrite Nat.leb_nle; word. reflexivity. }
            { trivial. }
        + destruct canApply' as [ | ]; simpl in *; (destruct (e1' + 1 =? e2')%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']); apply tryget_pure in H1; try word; subst.
          * exists (output', true). split; simpl.
            { split; simpl; do 2 red; trivial. symmetry. replace (uint.nat e2 <=? uint.nat e1)%nat with true by now symmetry; rewrite Nat.leb_le; word. eapply andb_true_l. }
            { rewrite -> CONSTANT_unfold in *. trivial. }
          * exists (output', false). split; simpl.
            { split; simpl; do 2 red; trivial. symmetry. replace (uint.nat e2 <=? uint.nat e1)%nat with true by now symmetry; rewrite Nat.leb_le; word. eapply andb_true_l. }
            { rewrite -> CONSTANT_unfold in *. trivial. }
        + destruct canApply' as [ | ]; simpl in *; (destruct (e1' + 1 =? e2')%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']); apply tryget_pure in H1; try word; subst.
          * exists (false, true). split; simpl.
            { split; simpl; do 2 red; trivial. symmetry. replace (uint.nat e2 <=? uint.nat e1)%nat with false by now symmetry; rewrite Nat.leb_nle; word. eapply andb_true_l. }
            { rewrite -> CONSTANT_unfold in *. trivial. }
          * exists (false, false). split; simpl.
            { split; simpl; do 2 red; trivial. symmetry. replace (uint.nat e2 <=? uint.nat e1)%nat with false by now symmetry; rewrite Nat.leb_nle; word. eapply andb_true_l. }
            { rewrite -> CONSTANT_unfold in *. trivial. }
      - eapply zip_corres; trivial.
      - split; simpl; do 2 red; trivial.
    }
    intros [output canApply] [output' canApply']; simpl in *.
    intros [output_corres canApply_corres]; simpl in *.
    eapply downward_pure. do 2 red in output_corres, canApply_corres |- *.
    subst output' canApply'; destruct output, canApply; reflexivity.
  Qed.

  End refine_coq_oneOffVersionVector.

  Section refine_coq_equalSlices.

  Fixpoint coq_equalSlices (s1 : list nat) (s2: list nat) : bool :=
    match s1 with
    | [] => true
    | h1 :: t1 =>
      match s2 with
      | [] => true
      | h2 :: t2 => (h1 =? h2)%nat && coq_equalSlices t1 t2
      end
    end.

  Lemma coq_equalSlices_corres
    : ServerSide.coq_equalSlices =~= coq_equalSlices.
  Proof.
    intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; try (do 2 red; reflexivity).
    des; try word; simpl; trivial; eapply IH; trivial.
  Qed.

  End refine_coq_equalSlices.

  (* Use SessionPrelude.deleteAt instead of coq_deleteAtIndexOperation, coq_deleteAtIndexMessage. *)

End Server_nat.

Module Client_nat.

  (* TODO: implement Client as nat with SuperMonad *)

End Client_nat.
