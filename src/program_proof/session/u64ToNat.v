Require Import Perennial.program_proof.session.session_definitions.

Reserved Infix ">>=" (left associativity, at level 90).
Reserved Infix "=~=" (at level 70, no associativity).

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
Open Scope monad_scope.

Reserved Notation "'do' m" (m custom do_notation at level 10, at level 0, format "'do'  '//' m").
Notation "'do' m" := m : monad_scope.
Notation "'do' m" := (m : monad).

Notation "x '<-' m1 ';' m2" := (m1 >>= fun x => m2) (in custom do_notation at level 0, x ident, m1 constr, m2 custom do_notation at level 10, format "x  '<-'  m1 ';' '//' m2").
Notation "'let' x ':=' t ';' m" := (let x := t in m) (in custom do_notation at level 0, x pattern, t constr, m custom do_notation at level 10, format "'let'  x  ':='  t ';' '//' m").
Notation "''' x '<-' m1 ';' m2" := (m1 >>= fun 'x => m2) (in custom do_notation at level 0, x pattern, m1 constr, m2 custom do_notation at level 10, format "''' x  '<-'  m1 ';' '//' m2").
Notation "m1 ';' m2" := (m1 >>= fun _ => m2) (in custom do_notation at level 0, m1 constr, m2 custom do_notation at level 10, format "m1 ';' '//' m2").
Notation "'ret' t" := (pure t) (in custom do_notation at level 10, t constr, format "'ret'  t").
Notation "t" := t (in custom do_notation at level 0, t constr).

#[global]
Instance option_isMonad : isMonad option :=
  { pure {A} := @Some A
  ; bind {A} {B} (m : option A) (k : A -> option B) :=
    match m with
    | Some x => k x
    | None => None
    end
  }.

Notation "'fail'" := (None) (in custom do_notation at level 10, format "'fail'").

(** End MONAD. *)

(** Section OPTION. *)

Fixpoint fold_left_option {A : Type} {B : Type} (f : A -> B -> option A) (xs : list B) (z : A) : option A :=
  match xs with
  | [] => do
    ret z
  | x :: xs' => do
    'y <- f z x;
    fold_left_option f xs' y
  end.

(** End OPTION. *)

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

(** End SIMILARITY. *)

(** Section BASIC_CORRES. *)

Definition param2func_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} `{Similarity A A'} `{Similarity B B'} `{Similarity C C'} (f : A -> B -> C) (f' : A' -> B' -> option C') : Prop :=
  forall a' : A', forall b' : B', forall c' : C', f' a' b' = Some c' ->
  forall a : A, a =~= a' ->
  forall b : B, b =~= b' ->
  exists c : C, c =~= c' /\ f a b = c.

Lemma fold_left_corres {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (f : A -> B -> A) (f' : A' -> B' -> option A')
  (f_corres : param2func_corres f f')
  : param2func_corres (fold_left f) (fold_left_option f').
Proof.
  red. intros xs' z' y' H_OBS xs xs_corres z z_corres. revert z z' y' z_corres H_OBS.
  induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; simpl; intros.
  - exists z. split; trivial. congruence.
  - destruct (f' z' x') as [_y' | ] eqn: H_y'; try congruence. eapply IH with (z' := _y'); trivial.
    pose proof (f_corres z' x' _y' H_y' z z_corres x x_corres) as (? & H_y & <-); trivial.
Qed.

(** End BASIC_CORRES. *)
