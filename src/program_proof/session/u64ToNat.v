Require Import Perennial.program_proof.session.session_definitions.

Reserved Infix "=~=" (at level 70, no associativity).

#[universes(template)]
Class Similarity (A : Type) (A' : Type) : Type :=
  is_similar_to (x : A) (x' : A') : Prop.

Infix "=~=" := is_similar_to.
