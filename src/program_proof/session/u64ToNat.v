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
  ; tryget_put_if {A : Type} (x : A)
    : tryget (put_if true x) = Some x
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

#[global, program]
Instance identity_isSuperMonad : isSuperMonad identity :=
  { put_if {A} (guard : bool) (x : A) := x 
  ; tryget {A} (m : identity A) := Some m
  }.
Next Obligation.
  intros. simpl in *. trivial.
Qed.
Next Obligation.
  intros. unfold pure in *. simpl in *. congruence.
Qed.
Next Obligation.
  intros. cbn in *.
  exists m. split; trivial.
Qed.

(** End MONAD. *)

#[global] Arguments bind {M} {isMonad} {A} {B} : simpl never.
#[global] Arguments pure {M} {isMonad} {A} : simpl never.

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

Module Server_u64.

(* TODO *)

(* Use deleteAt instead of coq_deleteAtIndexOperation, coq_deleteAtIndexMessage. *)

End Server_u64.

Module Server_nat.

(* TODO *)

(* Use deleteAt instead of coq_deleteAtIndexOperation, coq_deleteAtIndexMessage. *)

End Server_nat.

Module Client_u64.

(* TODO *)

End Client_u64.

Module Client_nat.

(* TODO *)

End Client_nat.
