Require Import Perennial.program_proof.session.session_definitions.

Reserved Infix ">>=" (left associativity, at level 90).
Reserved Infix "=~=" (at level 70, no associativity).

(** Section SIMILARITY. *)

#[universes(template)]
Class Similarity (A : Type) (A' : Type) : Type :=
  is_similar_to (x : A) (x' : A') : Prop.

Infix "=~=" := is_similar_to.

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

#[universes(polymorphic=yes)]
Class isMonad@{d c} (M : Type@{d} -> Type@{c}) : Type :=
  { bind {A : Type@{d}} {B : Type@{d}} (m : M A) (k : A -> M B) : M B
  ; pure {A : Type@{d}} : A -> M A
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
Notation "'let' x ':=' t ';' m" := (let x := t in m) (in custom do_notation at level 0, x pattern, t constr, m custom do_notation at level 10, format "'let'  x  ':='  t ';' '//' m").
Notation "''' x '<-' m1 ';' m2" := (m1 >>= fun 'x => m2) (in custom do_notation at level 0, x pattern, m1 constr, m2 custom do_notation at level 10, format "''' x  '<-'  m1 ';' '//' m2").
Notation "m1 ';' m2" := (m1 >>= fun _ => m2) (in custom do_notation at level 0, m1 constr, m2 custom do_notation at level 10, format "m1 ';' '//' m2").
Notation "'ret' t" := (pure t) (in custom do_notation at level 10, t constr, format "'ret'  t").
Notation "t" := t (in custom do_notation at level 0, t constr).

#[local] Open Scope monad_scope.

#[universes(polymorphic=yes)]
Definition identity@{u} (A : Type@{u}) : Type@{u} :=
  A.

#[global]
Instance identity_isMonad : isMonad identity :=
  { pure {A} (x : A) := x
  ; bind {A} {B} (m : A) (k : A -> B) := k m
  }.

#[universes(polymorphic=yes)]
Definition Err@{u} (A : Type@{u}) : Type@{u} :=
  (bool * A)%type.

#[global]
Instance Err_isMonad : isMonad Err :=
  { pure {A} (x : A) := (true, x)
  ; bind {A} {B} (m : Err A) (k : A -> Err B) :=
    let (b, y) := k m.2 in
    (m.1 && b, y)
  }.

#[global]
Instance option_isMonad : isMonad option :=
  { pure {A} := @Some A
  ; bind {A} {B} (m : option A) (k : A -> option B) :=
    match m with
    | Some x => k x
    | None => None
    end
  }.

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
  ; tryget_pure {A : Type} (x : A)
    : forall z : A, tryget (pure x) = Some z -> x = z
  ; tryget_bind {A : Type} {B : Type} (m : M A) (k : A -> M B)
    : forall z : B, tryget (bind m k) = Some z -> (exists x : A, tryget m = Some x /\ tryget (k x) = Some z)
  }.

#[global, program]
Instance identity_isSuperMonad : isSuperMonad identity :=
  { put_if {A} (guard : bool) (x : A) := x
  ; tryget {A} (m : A) := Some m
  }.
Next Obligation.
  intros. simpl in *. trivial.
Qed.
Next Obligation.
  intros. simpl in *. congruence.
Qed.
Next Obligation.
  intros. cbn in *. exists m. split; trivial.
Qed.

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

(** End BASIC_CORRES. *)

Module Server_nat.

  Lemma coq_compareVersionVector_unfold (v1 : list u64) (v2 : list u64) :
    ServerSide.coq_compareVersionVector v1 v2 =
    match v1 with
    | [] => do
      ret true
    | h1 :: t1 =>
      match v2 with
      | [] => do
        ret true
      | h2 :: t2 =>
        if uint.Z h1 <? uint.Z h2 then do
          ret false
        else do
          ServerSide.coq_compareVersionVector t1 t2
      end
    end.
  Proof.
    destruct v1; trivial.
  Qed.

  Fixpoint coq_compareVersionVector `{isSuperMonad M} (v1 : list nat) (v2 : list nat) : M bool :=
    match v1 with
    | [] => do
      ret true
    | h1 :: t1 =>
      match v2 with
      | [] => do
        ret true
      | h2 :: t2 => do
        'b <- coq_compareVersionVector t1 t2;
        ret ((h2 <=? h1)%nat && b)
      end
    end.

  Lemma coq_compareVersionVector_corres `{isSuperMonad M}
    : param2func_corres (M := M) ServerSide.coq_compareVersionVector coq_compareVersionVector.
  Proof.
    intros xs' ys' z' H_OBS xs xs_corres ys ys_corres. revert ys ys' ys_corres z' H_OBS.
    induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; simpl; intros ys ys' ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl; intros.
    - exists true; split; s!. apply tryget_pure in H_OBS. ss!.
    - exists true; split; s!. apply tryget_pure in H_OBS. ss!.
    - exists true; split; s!. apply tryget_pure in H_OBS. ss!.
    - specialize (IH ys ys' ys_corres z'). apply tryget_bind in H_OBS. Tac.des.
      + destruct H_OBS as (b & H_OBS & H_b). apply tryget_pure in H_b. subst z'.
        exists false; split; trivial. destruct (_ <=? _)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.leb_le in H_OBS' | rewrite Nat.leb_nle in H_OBS'].
        * do 2 red in x_corres, y_corres. word.
        * rewrite andb_false_l. reflexivity.
      + destruct H_OBS as (b & H_OBS & H_b). apply tryget_pure in H_b. subst z'.
        destruct (_ <=? _)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.leb_le in H_OBS' | rewrite Nat.leb_nle in H_OBS'].
        * eapply IH. rewrite andb_true_l. exact H_OBS.
        * do 2 red in x_corres, y_corres. word.
  Qed.

  Lemma coq_lexicographicCompare_unfold (v1 : list u64) (v2 : list u64) :
    ServerSide.coq_lexicographicCompare v1 v2 =
    match v1 with
    | [] => do
      ret false
    | h1 :: t1 =>
      match v2 with
      | [] => do
        ret false
      | h2 :: t2 =>
        if uint.Z h1 =? uint.Z h2 then do
          ServerSide.coq_lexicographicCompare t1 t2
        else do
          ret (uint.Z h1 >? uint.Z h2)
      end
    end.
  Proof.
    destruct v1; trivial.
  Qed.

  Fixpoint coq_lexicographicCompare `{isSuperMonad M} (v1 : list nat) (v2 : list nat) : M bool :=
    match v1 with
    | [] => do
      ret false
    | h1 :: t1 =>
      match v2 with
      | [] => do
        ret false
      | h2 :: t2 =>
        if uint.Z h1 =? uint.Z h2 then do
          coq_lexicographicCompare t1 t2
        else do
          ret (uint.Z h1 >? uint.Z h2)
      end
    end.

  Lemma coq_lexicographicCompare_corres `{isSuperMonad M}
    : param2func_corres (M := M) ServerSide.coq_lexicographicCompare coq_lexicographicCompare.
  Proof.
    intros xs' ys' z' H_OBS xs xs_corres ys ys_corres. revert ys ys' ys_corres z' H_OBS.
    induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; simpl; intros ys ys' ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl; intros.
    - exists false; split; s!. apply tryget_pure in H_OBS. ss!.
    - exists false; split; s!. apply tryget_pure in H_OBS. ss!.
    - exists false; split; s!. apply tryget_pure in H_OBS. ss!.
    - specialize (IH ys ys' ys_corres z'). do 2 red in x_corres, y_corres. revert H_OBS; Tac.des; intros; try word.
      + eapply IH; trivial.
      + exists true; split; trivial. apply tryget_pure in H_OBS3. do 2 red; trivial.
      + exists false; split; trivial. apply tryget_pure in H_OBS3. do 2 red; trivial.
  Qed.

(* Use SessionPrelude.deleteAt instead of coq_deleteAtIndexOperation, coq_deleteAtIndexMessage. *)

End Server_nat.

Module Client_nat.

(* TODO: implement Client as nat with SuperMonad *)

End Client_nat.
