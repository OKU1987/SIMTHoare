Require Import Vectors.VectorDef.
Require Import ZArith.
Import VectorNotations.
Require Import JMeq.
Require Import FunctionalExtensionality.
Require Import Vector_of_tuple.

Ltac existT_eq' :=
  match goal with
    | [ H : existT ?f ?t ?a = existT ?f ?t ?b,
            H' : JMeq ?a ?b |- _ ] =>
      subst; clear H
    | [ H : existT ?f ?t ?a = existT ?f ?t ?b |- JMeq ?a ?b] =>
      change (match existT f t a with
                | existT t c => JMeq c b
              end); rewrite H; constructor
    | [ H : existT ?f ?t ?a = existT ?f ?t ?b |- _] =>
      assert (JMeq a b)

    | [ H : JMeq (existT ?f ?t ?a) (existT ?f ?t ?b),
            H' : JMeq ?a ?b |- _ ] =>
      subst; clear H
    | [ H : JMeq (existT ?f ?t ?a) (existT ?f ?t ?b) |- JMeq ?a0 ?b0] =>
      change (match existT f t a with
                | existT t c => JMeq c b0
              end); rewrite H; constructor
    | [ H : JMeq (existT ?f ?t ?a) (existT ?f ?t ?b) |- _ ] =>
      assert (JMeq a b)

    | _ => fail
  end.

Ltac existT_eq := repeat existT_eq'.

Ltac functional_extensionality_pair_l :=
  match goal with
    | [ |- context[(?f, ?b) = (?g, ?b)]] =>
      rewrite (functional_extensionality f g ); reflexivity
    | [ |- context[(?a, ?f) = (?a, ?g)]] =>
      rewrite (functional_extensionality f g ); reflexivity
    | _ => idtac
  end.
Ltac functional_extensionality_pair_r :=
  match goal with
    | [ |- context[(?f, ?b) = (?g, ?b)]] =>
      rewrite <- (functional_extensionality f g); try reflexivity
    | [ |- context[(?a, ?f) = (?a, ?g)]] =>
      rewrite <- (functional_extensionality f g); try reflexivity
    | _ => idtac
  end.
Ltac functional_extensionality_dep_pair_l :=
  match goal with
    | [ |- context[(?f, ?b) = (?g, ?b)]] =>
      rewrite (functional_extensionality_dep f g ); reflexivity
    | [ |- context[(?a, ?f) = (?a, ?g)]] =>
      rewrite (functional_extensionality_dep f g ); reflexivity
    | _ => idtac
  end.
Ltac functional_extensionality_dep_pair_r :=
  match goal with
    | [ |- context[(?f, ?b) = (?g, ?b)]] =>
      rewrite <- (functional_extensionality_dep f g); try reflexivity
    | [ |- context[(?a, ?f) = (?a, ?g)]] =>
      rewrite <- (functional_extensionality_dep f g); try reflexivity
    | _ => idtac
  end.

Definition Vector_of_tuple := Vector_of_tuple.Vector_of_tuple.
Definition tuple_of_Vector := Vector_of_tuple.tuple_of_Vector.
