Require Import FunctionalExtensionality.
Require Import Vector_of_tuple.

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
