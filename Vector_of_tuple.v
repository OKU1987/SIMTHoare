(* This file is originated from
  https://gist.github.com/qnighy/bad737efac4b1bc9b9fc *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset.
Require Import Coq.Vectors.Vector.

Lemma beheadE n T (x : T) (t : n.-tuple T) :
    behead_tuple [tuple of x :: t] = t.
Proof.
  by apply val_inj.
Qed.

Section tuple_Vector_correspondence.
  Variable T : Type.

  Fixpoint tuple_of_Vector (n:nat) : Vector.t T n -> tuple_of n T :=
    match n return Vector.t T n -> tuple_of n T with
    | 0 => fun _ => [tuple]
    | n'.+1 => fun v =>
        [tuple of Vector.hd v :: tuple_of_Vector n' (Vector.tl v)]
    end.

  Fixpoint Vector_of_tuple(n:nat) :=
    match n return tuple_of n T -> Vector.t T n with
    | 0 => fun _ => Vector.nil T
    | n'.+1 => fun t =>
        Vector.cons T (thead t) n' (Vector_of_tuple n' (behead_tuple t))
    end.

  Lemma tuple_of_VectorK n :
      cancel (@tuple_of_Vector n) (@Vector_of_tuple n).
  Proof.
    elim: n; first by move=> /=; apply case0.
    move=> n /= H v.
    move: n v H.
    refine (@caseS T _ _).
    move => vh n vt H /=.
    congr 2 (fun vh => cons T vh n).
    by rewrite beheadE H.
  Qed.

  Lemma VectorK_of_tuple n :
      cancel (@Vector_of_tuple n) (@tuple_of_Vector n).
  Proof.
    elim: n; first by move=> x; symmetry; apply tuple0.
    move=> n /= H t.
    by rewrite H -tuple_eta.
  Qed.
End tuple_Vector_correspondence.


(* Explanation of a problem *)

Parameter Sg : nat -> eqType.

Fail Inductive Term :=
  | Tvar : nat -> Term
  | Tope n : Sg n -> n.-tuple Term -> Term.
(* Error: Non strictly positive occurrence of "Term" in
    "forall n : nat, Sg n -> n.-tuple Term -> Term". *)

Inductive Term :=
  | Tvar : nat -> Term
  | Tope n : Sg n -> Vector.t Term n -> Term.
(* success *)
