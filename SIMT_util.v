Require Import Vectors.VectorDef.
Require Import ZArith.
Import VectorNotations.
Require Import JMeq.

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


Ltac zero_lt_pos :=
  match goal with
    | [ H : (?z > 0)%Z,
            H0 : context[match ?z with
                    | 0%Z => Eq
                    | Z.pos _ => Lt
                    | Z.neg _ => Gt
                  end]
 |- _ ] =>
       simpl in H; unfold Zgt in H; apply Zcompare_Gt_spec in H;
       destruct H; simpl in H; rewrite <- Zplus_0_r_reverse in H;
       simpl in H0; rewrite H in H0; simpl in H0
    | _ => idtac
  end.
