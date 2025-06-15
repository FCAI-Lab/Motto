Require Import Perennial.program_proof.session.session_definitions.

#[local] Opaque _Data.w.

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
Instance Similarity_list {A : Type} {A' : Type} (SIM : Similarity A A') : Similarity (list A) (list A') :=
  @list_corres A A' SIM.

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

(** Section CORRES_LEMMAS. *)

  Lemma list_corres_length {A : Type} {A' : Type} {SIM : Similarity A A'} (xs : list A) (xs' : list A')
  (xs_corres : xs =~= xs')
  : @length A xs = @length A' xs'.
Proof.
  induction xs_corres; simpl; congruence.
Qed.

Lemma last_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (xs : list A) (xs' : list A')
  (xs_corres : xs =~= xs')
  : @last A xs =~= @last A' xs'.
Proof.
  induction xs_corres as [ | ? ? ? ? ? [ | ? ? ? ? ? ?] ?]; simpl; eauto.
Qed.

Lemma app_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (xs : list A) (xs' : list A') (ys : list A) (ys' : list A')
  (xs_corres : xs =~= xs')
  (ys_corres : ys =~= ys')
  : @app A xs ys =~= @app A' xs' ys'.
Proof.
  revert ys ys' ys_corres; induction xs_corres; simpl; eauto.
Qed.

Lemma ite_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (b : bool) (b' : bool) (x : A) (x' : A') (y : A) (y' : A')
  (b_corres : b =~= b')
  (x_corres : x =~= x')
  (y_corres : y =~= y')
  : (if b then x else y) =~= (if b' then x' else y').
Proof.
  do 2 red in b_corres; destruct b as [ | ]; subst b'; simpl; eauto.
Qed.

Lemma take_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (n : nat) (n' : nat) (xs : list A) (xs' : list A')
  (n_corres : n =~= n')
  (xs_corres : xs =~= xs')
  : @take A n xs =~= @take A' n' xs'.
Proof.
  do 2 red in n_corres; subst n'; revert xs xs' xs_corres; induction n as [ | n IH]; intros ? ? xs_corres; destruct xs_corres as [ | x x' x_corres xs xs' xs_corres]; simpl in *; eauto.
Qed.

Lemma drop_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (n : nat) (n' : nat) (xs : list A) (xs' : list A')
  (n_corres : n =~= n')
  (xs_corres : xs =~= xs')
  : @drop A n xs =~= @drop A' n' xs'.
Proof.
  do 2 red in n_corres; subst n'; revert xs xs' xs_corres; induction n as [ | n IH]; intros ? ? xs_corres; destruct xs_corres as [ | x x' x_corres xs xs' xs_corres]; simpl in *; eauto.
Qed.

Lemma andb_corres (b1 : bool) (b1' : bool) (b2 : bool) (b2' : bool)
  (b1_corres : b1 =~= b1')
  (b2_corres : b2 =~= b2')
  : b1 && b2 =~= b1' && b2'.
Proof.
  do 2 red in b1_corres, b2_corres |- *; congruence.
Qed.

Lemma orb_corres (b1 : bool) (b1' : bool) (b2 : bool) (b2' : bool)
  (b1_corres : b1 =~= b1')
  (b2_corres : b2 =~= b2')
  : b1 || b2 =~= b1' || b2'.
Proof.
  do 2 red in b1_corres, b2_corres |- *; congruence.
Qed.

Lemma negb_corres (b1 : bool) (b1' : bool)
  (b1_corres : b1 =~= b1')
  : negb b1 =~= negb b1'.
Proof.
  do 2 red in b1_corres |- *; congruence.
Qed.

Lemma ite_corres_negb {A : Type} {A' : Type} {A_SIM : Similarity A A'} (b : bool) (b' : bool) (x : A) (x' : A') (y : A) (y' : A')
  (b_corres : negb b =~= b')
  (x_corres : x =~= x')
  (y_corres : y =~= y')
  : (if b then x else y) =~= (if b' then y' else x').
Proof.
  do 2 red in b_corres; destruct b as [ | ]; subst b'; simpl in *; eauto.
Qed.

Lemma match_option_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} (x : option A) (x' : option A') (f : A -> B) (f' : A' -> B') (z : B) (z' : B')
  (x_corres : x =~= x')
  (f_corres : f =~= f')
  (z_corres : z =~= z')
  : (match x with Some y => f y | None => z end) =~= (match x' with Some y' => f' y' | None => z' end).
Proof.
  destruct x_corres; eauto.
Qed.

Lemma let2_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} {C_SIM : Similarity C C'} (f : A -> B -> C) (f' : A' -> B' -> C') (t : A * B) (t' : A' * B')
  (t_corres : t =~= t')
  (f_corres : f =~= f')
  : (let '(x, y) := t in f x y) =~= (let '(x', y') := t' in f' x' y').
Proof.
  destruct t as [x y], t' as [x' y']; simpl in *.
  inversion t_corres; subst; simpl in *.
  eapply f_corres; trivial.
Qed.

Lemma let3_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} {D : Type} {D' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} {C_SIM : Similarity C C'} {D_SIM : Similarity D D'} (f : A -> B -> C -> D) (f' : A' -> B' -> C' -> D') (t : A * B * C) (t' : A' * B' * C')
  (t_corres : t =~= t')
  (f_corres : f =~= f')
  : (let '(x, y, z) := t in f x y z) =~= (let '(x', y', z') := t' in f' x' y' z').
Proof.
  destruct t as [[x y] z], t' as [[x' y'] z']; simpl in *.
  inversion t_corres; subst; simpl in *. inversion H; subst; simpl in *.
  eapply f_corres; trivial.
Qed.

Lemma fold_left_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} (f : A -> B -> A) (xs : list B) (z : A) (f' : A' -> B' -> A') (xs' : list B') (z' : A')
  (f_corres : f =~= f')
  (xs_corres : xs =~= xs')
  (z_corres : z =~= z')
  : @fold_left A B f xs z =~= @fold_left A' B' f' xs' z'.
Proof.
  do 4 red in f_corres; revert z z' z_corres; induction xs_corres; simpl; eauto.
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

Lemma match_nat_2_corres {A : Type} {A' : Type} `{Similarity A A'} (n : nat) (n' : nat) (t0 : A) (t0' : A') (t1 : A) (t1' : A') (t2 : A) (t2' : A')
  (n_corres : n =~= n')
  (t0_corres : t0 =~= t0')
  (t1_corres : t1 =~= t1')
  (t2_corres : t2 =~= t2')
  : (match n with 0%nat => t0 | 1%nat => t1 | _ => t2 end) =~= (match n' with 0%nat => t0' | 1%nat => t1' | _ => t2' end).
Proof.
  do 2 red in n_corres; subst n'. destruct n as [ | [ | n]]; simpl; eauto.
Qed.

Lemma match_nat_3_corres {A : Type} {A' : Type} `{Similarity A A'} (n : nat) (n' : nat) (t0 : A) (t0' : A') (t1 : A) (t1' : A') (t2 : A) (t2' : A') (t3 : A) (t3' : A')
  (n_corres : n =~= n')
  (t0_corres : t0 =~= t0')
  (t1_corres : t1 =~= t1')
  (t2_corres : t2 =~= t2')
  (t3_corres : t3 =~= t3')
  : (match n with 0%nat => t0 | 1%nat => t1 | 2%nat => t2 | _ => t3 end) =~= (match n' with 0%nat => t0' | 1%nat => t1' | 2%nat => t2' | _ => t3' end).
Proof.
  do 2 red in n_corres; subst n'. destruct n as [ | [ | [ | [ | n]]]]; simpl; eauto.
Qed.

Lemma match_nat_6_corres {A : Type} {A' : Type} `{Similarity A A'} (n : nat) (n' : nat) (t0 : A) (t0' : A') (t1 : A) (t1' : A') (t2 : A) (t2' : A') (t3 : A) (t3' : A') (t4 : A) (t4' : A') (t5 : A) (t5' : A') (t6 : A) (t6' : A')
  (n_corres : n =~= n')
  (t0_corres : t0 =~= t0')
  (t1_corres : t1 =~= t1')
  (t2_corres : t2 =~= t2')
  (t3_corres : t3 =~= t3')
  (t4_corres : t4 =~= t4')
  (t5_corres : t5 =~= t5')
  (t6_corres : t6 =~= t6')
  : (match n with 0%nat => t0 | 1%nat => t1 | 2%nat => t2 | 3%nat => t3 | 4%nat => t4 | 5%nat => t5 | _ => t6 end) =~= (match n' with 0%nat => t0' | 1%nat => t1' | 2%nat => t2' | 3%nat => t3' | 4%nat => t4' | 5%nat => t5' | _ => t6' end).
Proof.
  do 2 red in n_corres; subst n'. destruct n as [ | [ | [ | [ | [ | [ | n]]]]]]; simpl; eauto.
Qed.

Lemma replicate_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (n : nat) (n' : nat) (x : A) (x' : A')
  (n_corres : n = n')
  (x_corres : x =~= x')
  : replicate n x =~= replicate n' x'.
Proof.
  subst n'; induction n as [ | n IH]; simpl; eauto.
Qed.

#[global]
Instance Similarity_u64 : Similarity u64 nat :=
  fun u => fun n => uint.nat u = n /\ uint.Z u <= CONSTANT - 1.

(** End CORRES_LEMMAS. *)

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

Class MonadError (M : Type -> Type) `{isMonad M} : Type :=
  { put_if {A : Type} (guard : bool) : A -> M A
  ; tryget {A : Type} : M A -> option A
  ; tryget_put_if_true {A : Type} (x : A) (r : option A)
    : tryget (put_if true x) = r <-> Some x = r
  ; tryget_put_if_false {A : Type} (x : A) (r : option A)
    : tryget (put_if false x) = r <-> None = r
  ; tryget_pure {A : Type} (x : A)
    : forall z : A, tryget (pure x) = Some z -> x = z
  ; tryget_bind {A : Type} {B : Type} (m : M A) (k : A -> M B)
    : forall z : B, tryget (bind m k) = Some z -> (exists x : A, tryget m = Some x /\ tryget (k x) = Some z)
  }.

#[global, program]
Instance Err_MonadError : MonadError Err :=
  { put_if {A} (guard : bool) (x : A) := (guard, x)
  ; tryget {A} (m : Err A) := if m.1 then Some m.2 else None
  }.
Next Obligation.
  intros. simpl in *. eauto.
Qed.
Next Obligation.
  intros. simpl in *. eauto.
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
Instance option_MonadError : MonadError option :=
  { put_if {A} (guard : bool) (x : A) := if guard then Some x else None
  ; tryget {A} (m : option A) := m
  }.
Next Obligation.
  intros. simpl in *. eauto.
Qed.
Next Obligation.
  intros. unfold pure in *. eauto.
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

Definition param0func_corres `{MonadError M} {A : Type} {A' : Type} `{Similarity A A'} (f : A) (f' : M A') : Prop :=
  forall a' : A', tryget f' = Some a' ->
  exists a : A, a =~= a' /\ f = a.

Definition param1func_corres `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (f : A -> B) (f' : A' -> M B') : Prop :=
  forall a' : A', forall b' : B', tryget (f' a') = Some b' ->
  forall a : A, a =~= a' ->
  exists b : B, b =~= b' /\ f a = b.

Definition param2func_corres `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} `{Similarity A A'} `{Similarity B B'} `{Similarity C C'} (f : A -> B -> C) (f' : A' -> B' -> M C') : Prop :=
  forall a' : A', forall b' : B', forall c' : C', tryget (f' a' b') = Some c' ->
  forall a : A, a =~= a' ->
  forall b : B, b =~= b' ->
  exists c : C, c =~= c' /\ f a b = c.

Definition param3func_corres `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} {D : Type} {D' : Type} `{Similarity A A'} `{Similarity B B'} `{Similarity C C'} `{Similarity D D'} (f : A -> B -> C -> D) (f' : A' -> B' -> C' -> M D') : Prop :=
  forall a' : A', forall b' : B', forall c' : C', forall d' : D', tryget (f' a' b' c') = Some d' ->
  forall a : A, a =~= a' ->
  forall b : B, b =~= b' ->
  forall c : C, c =~= c' ->
  exists d : D, d =~= d' /\ f a b c = d.

  Definition downward `{MonadError M} {R : Type} {R' : Type} `{Similarity R R'} (m : identity R) (m' : M R') : Prop :=
  forall r' : R',
  tryget m' = Some r' ->
  exists r : R, r =~= r' /\ m = r.

Notation "'REFINEMENT' src '====================' tgt" := (downward tgt src) (at level 100, no associativity, format "'//' 'REFINEMENT' '//' src  '//' '====================' '//' tgt").

Lemma downward_bind `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (m : identity A) (m' : M A') (k : A -> identity B) (k' : A' -> M B')
  (m_corres : downward m m')
  (k_corres : param1func_corres k k')
  : downward (M := M) (bind m k) (bind m' k').
Proof.
  unfold downward in *. intros r' H_r'.
  apply tryget_bind in H_r'. destruct H_r' as (x' & H_r' & H_x').
  eapply k_corres with (a' := x'); trivial.
  pose proof (m_corres x' H_r') as (x & H_x & H_m); congruence. 
Qed.

Lemma downward_pure `{MonadError M} {R : Type} {R' : Type} `{Similarity R R'} (x : R) (x' : R')
  (x_corres : x =~= x')
  : downward (M := M) (pure x) (pure x').
Proof.
  red. intros r' H_r'. apply tryget_pure in H_r'. exists x. split; ss!.
Qed.

Lemma downward_put_if_false `{MonadError M} {R : Type} {R' : Type} `{Similarity R R'} (x : R) (x' : R')
  : downward (M := M) x (put_if false x').
Proof.
  intros r' H_r'. rewrite tryget_put_if_false in H_r'. congruence.
Qed.

Lemma downward_put_if_true `{MonadError M} {R : Type} {R' : Type} `{Similarity R R'} (x : R) (x' : R')
  (x_corres : x =~= x')
  : downward (M := M) x (put_if true x').
Proof.
  intros r' H_r'. rewrite tryget_put_if_true in H_r'. exists x; split; ss!.
Qed.

Lemma downward_app0 `{MonadError M} {A : Type} {A' : Type} `{Similarity A A'} (f : identity A) (f' : M A')
  (f_corres : param0func_corres f f')
  : downward (M := M) f f'.
Proof.
  trivial.
Qed.

Lemma downward_app1 `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (f : A -> identity B) (f' : A' -> M B') (x : A) (x' : A')
  (f_corres : param1func_corres f f')
  (x_corres : x =~= x')
  : downward (M := M) (f x) (f' x').
Proof.
  intros r' H_r'. exact (f_corres x' r' H_r' x x_corres).
Qed.

Lemma downward_app2 `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} `{Similarity A A'} `{Similarity B B'} `{Similarity C C'} (f : A -> B -> identity C) (f' : A' -> B' -> M C') (x : A) (x' : A') (y : B) (y' : B')
  (f_corres : param2func_corres f f')
  (x_corres : x =~= x')
  (y_corres : y =~= y')
  : downward (M := M) (f x y) (f' x' y').
Proof.
  intros r' H_r'. exact (f_corres x' y' r' H_r' x x_corres y y_corres).
Qed.

Lemma downward_app3 `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} {C : Type} {C' : Type} {D : Type} {D' : Type} `{Similarity A A'} `{Similarity B B'} `{Similarity C C'} `{Similarity D D'} (f : A -> B -> C -> identity D) (f' : A' -> B' -> C' -> M D') (x : A) (x' : A') (y : B) (y' : B') (z : C) (z' : C')
  (f_corres : param3func_corres f f')
  (x_corres : x =~= x')
  (y_corres : y =~= y')
  (z_corres : z =~= z')
  : downward (M := M) (f x y z) (f' x' y' z').
Proof.
  intros r' H_r'. exact (f_corres x' y' z' r' H_r' x x_corres y y_corres z z_corres).
Qed.

Tactic Notation "xintros" :=
  let r' := fresh "res'" in
  let H_r' := fresh "H_res'" in
  intros r' H_r';
  revert r' H_r';
  lazymatch goal with
  | [ |- forall r', tryget ?m' = Some r' -> exists r, r =~= r' /\ ?m = r ] => change (downward m m')
  end.

Tactic Notation "xintros" ident( a ) :=
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

Tactic Notation "xintros" ident( a ) ident( b ) :=
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

Tactic Notation "xintros" ident( a ) ident( b ) ident( c ) :=
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

Ltac xapp_aux :=
  try ((repeat lazymatch goal with [ H : _ =~= _ |- _ ] => inversion H; subst end); (try do 2 red); trivial).

Ltac xapp0 :=
  eapply downward_app0; xapp_aux.

Ltac xapp1 :=
  eapply downward_app1; xapp_aux.

Ltac xapp2 :=
  eapply downward_app2; xapp_aux.

Ltac xapp3 :=
  eapply downward_app3; xapp_aux.

Ltac xapp :=
  first
  [ eapply downward_app3; [eassumption | xapp_aux | xapp_aux | xapp_aux]
  | eapply downward_app2; [eassumption | xapp_aux | xapp_aux]
  | eapply downward_app1; [eassumption | xapp_aux]
  | eapply downward_app0; eassumption
  ].

Lemma downward_match_option `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (m : identity B) (m' : M B') (k : A -> identity B) (k' : A' -> M B') (o : option A) (o' : option A')
  (m_corres : downward m m')
  (k_corres : param1func_corres k k')
  (o_corres : o =~= o')
  : downward (match o with Some x => k x | None => m end) (match o' with Some x' => k' x' | None => m' end).
Proof.
  destruct o_corres; eauto. xapp.
Qed.

Lemma downward_fold_left `{MonadError M} {A : Type} {A' : Type} {B : Type} {B' : Type} `{Similarity A A'} `{Similarity B B'} (f : A -> B -> identity A) (f' : A' -> B' -> M A') (xs : list B) (xs' : list B') (z : A) (z' : A')
  (f_corres : param2func_corres f f')
  (xs_corres : xs =~= xs')
  (z_corres : z =~= z')
  : downward (fold_left f xs z) (fold_left' f' xs' z').
Proof.
  revert z z' z_corres. induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; simpl; intros.
  - eapply downward_pure; trivial.
  - change (fold_left f xs (f z x)) with (bind (M := identity) (isMonad := identity_isMonad) (f z x) (fun y : A => pure (fold_left f xs y))).
    eapply downward_bind; [xapp | clear z z' z_corres]. xintros z; eauto.
Qed.

(** End BASIC_CORRES. *)

Module Operation'.

  #[projections(primitive)]
  Record t : Type :=
    mk
    { VersionVector : list nat
    ; Data : _Data.w
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

  #[projections(primitive)]
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

  #[projections(primitive)]
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

  #[projections(primitive)]
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
    | [ |- context C[ bool_decide ?P ] ] =>
      let H_OBS := fresh "H_OBS" in destruct (bool_decide P)%nat as [ | ] eqn: H_OBS; [rewrite bool_decide_eq_true in H_OBS | rewrite bool_decide_eq_false in H_OBS]
    | [ H : context C[ bool_decide ?P ] |- _ ] =>
      let H_OBS := fresh "H_OBS" in destruct (bool_decide P)%nat as [ | ] eqn: H_OBS in H; [rewrite bool_decide_eq_true in H_OBS | rewrite bool_decide_eq_false in H_OBS]
    | [ H : _ /\ _ |- _ ] => let H' := fresh H in destruct H as [H H']
    | [ H : (_, _)%core = (_, _)%core |- _ ] => rewrite -> Tac.pair_inv in H
    | [ |- (_, _)%core = (_, _)%core ] => rewrite -> Tac.pair_inv
    | [ H : exists x, _ |- _ ] => let x' := fresh x in destruct H as [x' H]
    | [ H : is_similar_to _ _ |- _ ] => do 2 red in H
    | [ |- is_similar_to _ _ ] => do 2 red
    end
  ).

Module Server_nat.

  Import SessionPrelude.

  Section refine_coq_compareVersionVector.

  Definition coq_compareVersionVector (v1 : list nat) (v2 : list nat) : bool :=
    bool_decide (Forall2 (fun h2 => fun h1 => h1 <= h2)%nat v1 v2).

  Lemma coq_compareVersionVector_corres
    : ServerSide.coq_compareVersionVector =~= coq_compareVersionVector.
  Proof.
    unfold coq_compareVersionVector. intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; try (do 2 red; reflexivity). do 2 red in IH.
    specialize (IH ys ys' ys_corres). do 2 red in IH |- *. do 2 red in x_corres, y_corres. des; simpl; try congruence.
    - inversion H_OBS0; subst; contradiction.
    - contradiction H_OBS0. econstructor; eauto 2. subst x' y'. rewrite -> CONSTANT_unfold in *. word.
    - inversion H_OBS0; subst. word.
    - inversion H_OBS0; subst. word.
  Qed.

  End refine_coq_compareVersionVector.

  Section refine_coq_lexicographicCompare.

  Fixpoint coq_lexicographicCompare (v1: list nat) (v2: list nat) : bool :=
    match v1, v2 with
    | [], [] => false
    | [], h2 :: t2 => false
    | h1 :: t1, [] => true
    | h1 :: t1, h2 :: t2 => if (h1 =? h2)%nat then coq_lexicographicCompare t1 t2 else uint.Z h1 >? uint.Z h2
    end.

  Lemma coq_lexicographicCompare_corres
    : ServerSide.coq_lexicographicCompare =~= coq_lexicographicCompare.
  Proof.
    intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; try (do 2 red; reflexivity).
    des; try word. simpl. eapply IH; trivial.
  Qed.

  End refine_coq_lexicographicCompare.

  Section refine_coq_maxTS.

  Definition coq_maxTS (xs : list nat) (ys : list nat) : list nat :=
    map (fun '(x, y) => Nat.max x y) (zip xs ys).

  Lemma coq_maxTS_corres
    : ServerSide.coq_maxTS =~= coq_maxTS.
  Proof.
    intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; eauto.
    unfold ServerSide.coq_maxTwoInts. des; econstructor 2; eauto; do 2 red; word.
  Qed.

  End refine_coq_maxTS.

  Section refine_coq_oneOffVersionVector.

  Context `{MonadError M}.

  Definition coq_oneOffVersionVector (v1 : list nat) (v2 : list nat) : M bool :=
    put_if (length v1 =? length v2)%nat (
      let loop_step (acc : bool * bool) (elem : nat * nat) : bool * bool :=
        let '(e1, e2) := elem in
        let '(output, canApply) := acc in
        if canApply && (e1 + 1 =? e2)%nat then
          (output, false)
        else
          ((e2 <=? e1)%nat && output, canApply)
      in
      let (output, canApply) := fold_left loop_step (zip v1 v2) (true, true) in
      output && negb canApply
    ).

  Lemma coq_oneOffVersionVector_corres
    : param2func_corres (M := M) ServerSide.coq_oneOffVersionVector coq_oneOffVersionVector.
  Proof.
    xintros v1 v2. unfold ServerSide.coq_oneOffVersionVector, coq_oneOffVersionVector. des.
    - eapply downward_put_if_true. 
      eapply let2_corres.
      { eapply fold_left_corres.
        - intros [output canApply] [output' canApply']; simpl in *.
          intros [output_corres canApply_corres]; simpl in *.
          intros [e1 e2] [e1' e2']; simpl in *.
          intros [e1_corres e2_corres]; simpl in *.
          eapply ite_corres.
          + eapply andb_corres; trivial.
            do 2 red in e1_corres, e2_corres |- *. rewrite -> CONSTANT_unfold in *. des; try word.
          + split; trivial; simpl. do 2 red; reflexivity.
          + des; simpl; split; trivial; try word. do 2 red; reflexivity.
        - eapply zip_corres; trivial.
        - split; simpl; do 2 red; reflexivity.
      }
      intros output output' output_corres canApply canApply' canApply_corres.
      do 2 red in output_corres, canApply_corres |- *; congruence.
    - eapply downward_put_if_false.
  Qed.

  End refine_coq_oneOffVersionVector.

  Section refine_coq_equalSlices.

  Definition coq_equalSlices (s1 : list nat) (s2: list nat) : bool :=
    bool_decide (s1 = s2).

  Lemma coq_equalSlices_corres
    : ServerSide.coq_equalSlices =~= coq_equalSlices.
  Proof.
    unfold coq_equalSlices. intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; try (do 2 red; reflexivity).
    specialize (IH ys ys' ys_corres). des; try word; simpl; try congruence. contradiction H_OBS. enough (x' = y') by word. congruence.
  Qed.

  End refine_coq_equalSlices.

  Section refine_coq_sortedInsert.

  Fixpoint coq_sortedInsert (ops : list Operation'.t) (op : Operation'.t) : list Operation'.t :=
    match ops with
    | [] => [op]
    | op' :: ops' =>
      if coq_lexicographicCompare op'.(Operation'.VersionVector) op.(Operation'.VersionVector) then
        op :: op' :: ops'
      else if coq_equalSlices op'.(Operation'.VersionVector) op.(Operation'.VersionVector) then
        op' :: ops'
      else
        op' :: coq_sortedInsert ops' op
    end.

  Lemma coq_sortedInsert_corres
    : ServerSide.coq_sortedInsert =~= coq_sortedInsert.
  Proof.
    intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros y y' y_corres; simpl in *; eauto.
    inversion x_corres; subst. inversion y_corres; subst. eapply ite_corres; eauto.
    - eapply coq_lexicographicCompare_corres; trivial.
    - eapply ite_corres; eauto. eapply coq_equalSlices_corres; trivial.
  Qed.

  End refine_coq_sortedInsert.

  Section refine_coq_deleteAtIndexOperation.

  Context `{MonadError M}.

  Definition coq_deleteAtIndexOperation (l : list Operation'.t) (index : nat) : M (list Operation'.t) :=
    put_if (index + 1 <? length l)%nat (deleteAt l index).

  Lemma coq_deleteAtIndexOperation_corres
    : param2func_corres (M := M) ServerSide.coq_deleteAtIndexOperation coq_deleteAtIndexOperation.
  Proof.
    xintros l index. unfold ServerSide.coq_deleteAtIndexOperation, coq_deleteAtIndexOperation.
    red; intros; des.
    - rewrite -> (tryget_put_if_true (deleteAt l' index')) in H1.
      assert (r' = deleteAt l' index') as -> by congruence. clear H1.
      exists (deleteAt l index). split; trivial.
      unfold deleteAt; eapply app_corres; [eapply take_corres | eapply drop_corres]; trivial.
      do 2 red; congruence.
    - rewrite -> tryget_put_if_false in H1. congruence.
  Qed.

  End refine_coq_deleteAtIndexOperation.

  Section refine_coq_deleteAtIndexMessage.

  Context `{MonadError M}.

  Definition coq_deleteAtIndexMessage (l : list Message'.t) (index : nat) : M (list Message'.t) :=
    put_if (index + 1 <? length l)%nat (deleteAt l index).

  Lemma coq_deleteAtIndexMessage_corres
    : param2func_corres (M := M) ServerSide.coq_deleteAtIndexMessage coq_deleteAtIndexMessage.
  Proof.
    xintros l index. unfold ServerSide.coq_deleteAtIndexMessage, coq_deleteAtIndexMessage.
    red; intros; des.
    - rewrite -> (tryget_put_if_true (deleteAt l' index')) in H1.
      assert (r' = deleteAt l' index') as -> by congruence. clear H1.
      exists (deleteAt l index). split; trivial.
      unfold deleteAt; eapply app_corres; [eapply take_corres | eapply drop_corres]; trivial.
      do 2 red; congruence.
    - rewrite -> tryget_put_if_false in H1. congruence.
  Qed.

  End refine_coq_deleteAtIndexMessage.

  Section refine_coq_getDataFromOperationLog.

  Context `{MonadError M}.

  Definition coq_getDataFromOperationLog (ops : list Operation'.t) : M _Data.w :=
    match last ops with
    | Some op => put_if true op.(Operation'.Data)
    | None => put_if false (IntoVal_def _Data.w)
    end.

  Lemma coq_getDataFromOperationLog_corres
    : param1func_corres (M := M) ServerSide.coq_getDataFromOperationLog coq_getDataFromOperationLog.
  Proof.
    xintros ops. unfold ServerSide.coq_getDataFromOperationLog, coq_getDataFromOperationLog.
    eapply downward_match_option.
    - eapply downward_put_if_false.
    - xintros op. eapply downward_put_if_true. inversion op_corres; subst. trivial.
    - eapply last_corres; trivial.
  Qed.

  End refine_coq_getDataFromOperationLog.

  Section refine_coq_receiveGossip.

  Lemma ServerSide_coq_receiveGossip :
    ServerSide.coq_receiveGossip =
    fun server : Server.t => fun request : Message.t =>
    if (length request.(Message.S2S_Gossip_Operations) =? 0)%nat then do
      ret server
    else do
      'TMP <- fold_left
        ( fun acc : Server.t => fun elem : Operation.t =>
          let server := acc in do
          if ServerSide.coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then do
            ret
              {|
                Server.Id := server.(Server.Id);
                Server.NumberOfServers := server.(Server.NumberOfServers);
                Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
                Server.VectorClock := ServerSide.coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector);
                Server.OperationsPerformed := ServerSide.coq_sortedInsert server.(Server.OperationsPerformed) elem;
                Server.MyOperations := server.(Server.MyOperations);
                Server.PendingOperations := server.(Server.PendingOperations);
                Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
              |}
          else if negb (ServerSide.coq_compareVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector)) then do
            ret
              {|
                Server.Id := server.(Server.Id);
                Server.NumberOfServers := server.(Server.NumberOfServers);
                Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
                Server.VectorClock := server.(Server.VectorClock);
                Server.OperationsPerformed := server.(Server.OperationsPerformed);
                Server.MyOperations := server.(Server.MyOperations);
                Server.PendingOperations := ServerSide.coq_sortedInsert server.(Server.PendingOperations) elem;
                Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
              |}
          else do
            ret server
        )
        request.(Message.S2S_Gossip_Operations)
        server;
      let server := TMP in do
      'TMP <- fold_left
        ( fun acc : Server.t * u64 * list u64 => fun elem : Operation.t =>
          let '(server, i, seen) := acc in do
          if ServerSide.coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then do
            ret (Server.mk server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) (ServerSide.coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector)) (ServerSide.coq_sortedInsert server.(Server.OperationsPerformed) elem) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements), W64 (uint.Z i + 1), seen ++ [i])
          else do
            ret (server, W64 (uint.Z i + 1), seen)
        )
        server.(Server.PendingOperations)
        (server, W64 0, []);
      let '(server, _, seen) := TMP in do
      ret (
        let '(_, _, output) := fold_left (fun acc : nat * nat * list Operation.t => fun elem : Operation.t => let '(i, j, output) := acc in match seen !! j with Some i' => if (i =? uint.nat i')%nat then ((i + 1)%nat, (j + 1)%nat, output) else ((i + 1)%nat, j, output ++ [elem]) | None => ((i + 1)%nat, j, output ++ [elem]) end) server.(Server.PendingOperations) (0%nat, 0%nat, []) in do
        {|
          Server.Id := server.(Server.Id);
          Server.NumberOfServers := server.(Server.NumberOfServers);
          Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
          Server.VectorClock := server.(Server.VectorClock);
          Server.OperationsPerformed := server.(Server.OperationsPerformed);
          Server.MyOperations := server.(Server.MyOperations);
          Server.PendingOperations := output;
          Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
        |}
      ).
  Proof.
    reflexivity.
  Defined.

  Context `{MonadError M}.

  (* TODO *)

  End refine_coq_receiveGossip.

  Section refine_coq_acknowledgeGossip.

  (* TODO *)

  End refine_coq_acknowledgeGossip.

  Section refine_coq_getGossipOperations.

  (* TODO *)

  End refine_coq_getGossipOperations.

  Section refine_coq_processClientRequest.

  (* TODO *)

  End refine_coq_processClientRequest.

  Section refine_coq_processRequest.

  (* TODO *)

  End refine_coq_processRequest.

End Server_nat.

Module Client_nat.

  Import SessionPrelude.

  Section refine_coq_maxTS.

  Definition coq_maxTS (xs : list nat) (ys : list nat) : list nat :=
    map (fun '(x, y) => Nat.max x y) (zip xs ys).

  Lemma coq_maxTS_corres
    : ServerSide.coq_maxTS =~= coq_maxTS.
  Proof.
    intros xs xs' xs_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; eauto.
    unfold ServerSide.coq_maxTwoInts. des; econstructor 2; eauto; do 2 red; word.
  Qed.

  End refine_coq_maxTS.

  Section refine_coq_read.

  Definition coq_read (c : Client'.t) (serverId : nat) : Message'.t :=
    match c.(Client'.SessionSemantic) with
    | 0%nat => Message'.mk 0 c.(Client'.Id) serverId 0 (IntoVal_def _Data.w) (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 1%nat => Message'.mk 0 c.(Client'.Id) serverId 0 (IntoVal_def _Data.w) (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 2%nat => Message'.mk 0 c.(Client'.Id) serverId 0 (IntoVal_def _Data.w) (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 3%nat => Message'.mk 0 c.(Client'.Id) serverId 0 (IntoVal_def _Data.w) c.(Client'.ReadVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 4%nat => Message'.mk 0 c.(Client'.Id) serverId 0 (IntoVal_def _Data.w) c.(Client'.WriteVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 5%nat => Message'.mk 0 c.(Client'.Id) serverId 0 (IntoVal_def _Data.w) (coq_maxTS c.(Client'.WriteVersionVector) c.(Client'.ReadVersionVector)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | _ => Message'.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    end.

  Lemma coq_read_corres
    : ClientSide.coq_read =~= coq_read.
  Proof.
    intros c c' c_corres serverId serverId' serverId_corres. unfold ClientSide.coq_read, coq_read.
    inversion c_corres; subst. eapply match_nat_6_corres.
    - do 2 red in SessionSemantic_corres |- *. word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor.
      eapply replicate_corres; trivial. do 2 red; word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor.
      eapply replicate_corres; trivial. do 2 red; word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor.
      eapply replicate_corres; trivial. do 2 red; word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor.
      eapply coq_maxTS_corres; trivial.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor.
  Qed.

  End refine_coq_read.

  Section refine_coq_write.

  Definition coq_write (c : Client'.t) (serverId : nat) (value: _Data.w) : Message'.t :=
    match c.(Client'.SessionSemantic) with
    | 0%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 1%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value c.(Client'.ReadVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 2%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value c.(Client'.WriteVersionVector) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 3%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 4%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | 5%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value (coq_maxTS c.(Client'.WriteVersionVector) c.(Client'.ReadVersionVector)) 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    | _ => Message'.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0
    end.

  Lemma coq_write_corres
    : ClientSide.coq_write =~= coq_write.
  Proof.
    intros c c' c_corres serverId serverId' serverId_corres value value' value_corres. unfold ClientSide.coq_write, coq_write.
    inversion c_corres; subst. eapply match_nat_6_corres.
    - do 2 red in SessionSemantic_corres |- *. word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor; rewrite -> CONSTANT_unfold in *; try word.
      eapply replicate_corres; trivial. do 2 red; rewrite -> CONSTANT_unfold; word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor; rewrite -> CONSTANT_unfold in *; try word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor; rewrite -> CONSTANT_unfold in *; try word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor; rewrite -> CONSTANT_unfold in *; try word.
      eapply replicate_corres; trivial. do 2 red; rewrite -> CONSTANT_unfold; word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor; rewrite -> CONSTANT_unfold in *; try word.
      eapply replicate_corres; trivial. do 2 red; rewrite -> CONSTANT_unfold; word.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor; rewrite -> CONSTANT_unfold in *; try word.
      eapply coq_maxTS_corres; trivial.
    - des. split; simpl; (try do 2 red; word || (repeat split); reflexivity || eauto 2); try econstructor; rewrite -> CONSTANT_unfold in *; try word.
  Qed.

  End refine_coq_write.

  Section refine_coq_processRequest.

  Definition coq_processRequest (c : Client'.t) (requestType : nat) (serverId : nat) (value: _Data.w) (ackMessage : Message'.t) : Client'.t * Message'.t :=
    match requestType with
    | 0%nat => (c, coq_read c serverId)
    | 1%nat => (c, coq_write c serverId value)
    | 2%nat =>
      match ackMessage.(Message'.S2C_Client_OperationType) with
      | 0%nat => (Client'.mk c.(Client'.Id) c.(Client'.NumberOfServers) c.(Client'.WriteVersionVector) ackMessage.(Message'.S2C_Client_VersionVector) c.(Client'.SessionSemantic), Message'.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
      | 1%nat => (Client'.mk c.(Client'.Id) c.(Client'.NumberOfServers) ackMessage.(Message'.S2C_Client_VersionVector) c.(Client'.ReadVersionVector) c.(Client'.SessionSemantic), Message'.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
      | _ => (c, Message'.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
      end
    | _ => (c, Message'.mk 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 [] 0 0 0 0 0 (IntoVal_def _Data.w) [] 0 0)
    end.

  Lemma coq_processRequest_corres
    : ClientSide.coq_processRequest =~= coq_processRequest.
  Proof.
    intros c c' c_corres requestType requestType' requestType_corres serverId serverId' serverId_corres value value' value_corres ackMessage ackMessage' ackMessage_corres. unfold ClientSide.coq_processRequest, coq_processRequest.
    inversion c_corres; subst. eapply match_nat_3_corres.
    - do 2 red in requestType_corres |- *; try word.
    - split; simpl; trivial. eapply coq_read_corres; trivial.
    - split; simpl; trivial. eapply coq_write_corres; trivial.
    - inversion ackMessage_corres; subst. eapply match_nat_2_corres; trivial.
      + do 2 red in S2C_Client_OperationType_corres |- *; try word.
      + split; simpl; trivial.
        * econstructor; simpl; trivial.
        * econstructor; simpl; trivial; do 2 red; try rewrite -> CONSTANT_unfold; try word.
      + split; simpl; trivial.
        * econstructor; simpl; trivial.
        * econstructor; simpl; trivial; do 2 red; try rewrite -> CONSTANT_unfold; try word.
      + split; simpl; trivial.
        econstructor; simpl; trivial; do 2 red; try rewrite -> CONSTANT_unfold; try word.
    - inversion ackMessage_corres; subst. split; simpl; trivial.
      econstructor; simpl; trivial; do 2 red; try rewrite -> CONSTANT_unfold; try word.
  Qed.

  End refine_coq_processRequest.

End Client_nat.
