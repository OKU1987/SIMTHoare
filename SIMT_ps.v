Require Import SIMT_util.
Require Import Vector_of_tuple.
Require Import SIMT.
Close Scope nat_scope.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat fintype.
Require Import tuple div bigop finset ssralg ssrint intdiv.
Require Import FunctionalExtensionality.
Implicit Arguments var [n].
Implicit Arguments Vector_of_tuple [T n].
Implicit Arguments tuple_of_Vector [T n].
Coercion Vector_of_tuple : tuple_of >-> Vector.t.
Coercion tuple_of_Vector : Vector.t >-> tuple_of.

Definition funcT := fun n op tpl => @func n op (Vector_of_tuple tpl).
Definition varT := fun n op tpl => @var n op (Vector_of_tuple tpl).
Implicit Arguments funcT [n].
Implicit Arguments varT [n].

Notation "a '+E' b" := (@funcT 2 e_plus [tuple a; b]) (at level 60).
Notation "a '*E' b" := (@funcT 2 e_mult [tuple a; b]) (at level 60).
Notation "a '/E' b" := (@funcT 2 e_div [tuple a; b]) (at level 60).
Notation "a '&&' b" := (@funcT 2 e_and [tuple a; b]).
Notation "a '<E' b" := (@funcT 2 e_lt [tuple a; b]) (at level 90).
Notation "'!' a" := (@funcT 1 e_neg [tuple a]) (at level 35, right associativity).
Notation "'c' z" := (@funcT 0 (const z) [tuple]) (at level 20).

Notation "x '::=' e" := (@asgn 0%nat x [tuple] e) (at level 110, right associativity).
Notation "x '@' i ':::=' e" := (@asgn _ x i e) (at level 110, right associativity).

Notation "'`' x" := (@varT _ x [tuple]) (at level 30).
Notation "P ;; Q" := (seq P Q) (at level 150).
Notation "'IFB' e 'THEN' P 'ELSE' Q" := (P_if e P Q) (at level 135).
Notation "'WHILE' e 'DO' P" := (P_while e P) (at level 140).

Notation "s '[[' e ']](' i ')'" := (@E_under_state _ s e i) (at level 50).


Ltac unfold_update_state :=
  match goal with
    | [ H : context[update_state]|-_] => rewrite/update_state in H
    | [ |- context[update_state]] => rewrite/update_state
    | _ => fail
  end.
Ltac simplify_update_state' :=
  match goal with
    | [ H : context[eq_rect_r] |- _] => rewrite/eq_rect_r in H
    | [ H : context[eq_rec_r] |- _] => rewrite/eq_rec_r in H
    | [ H : context[eq_rect ?x _ _ _ _ _ _] |- _] =>
      destruct (@eqnP x x); rewrite // in H;
      rewrite (eq_irrelevance (Logic.eq_sym _) erefl)
    | [ H : context[eq_rec ?x _ _ _ _ _ _] |- _] =>
      destruct (@eqnP x x); rewrite // in H;
      rewrite (eq_irrelevance (Logic.eq_sym _) erefl)
    | [ |- context[eq_rect_r]] => rewrite/eq_rect_r
    | [ |- context[eq_rec_r]] => rewrite/eq_rec_r
    | [ |-context[eq_rect ?x _ _ _ _ _ _]] =>
      destruct (@eqnP x x); rewrite //;
      rewrite (eq_irrelevance (Logic.eq_sym _) erefl)
    | [ |-context[eq_rec ?x _ _ _ _ _ _]] =>
      destruct (@eqnP x x); rewrite // ;
      rewrite (eq_irrelevance (Logic.eq_sym _) erefl)
    | [ |-context[@eq_op]] =>
      case: eqP => // => _
    | [ H : context[eqnP] |- _] =>
      move: H; case: eqnP => //= _ H
    | [ |-context[eqnP]] =>
      case: eqnP => //= _
    | _ => fail
  end.
Ltac simplify_update_state :=
  repeat unfold_update_state; simpl; repeat simplify_update_state';
  rewrite ?eq_refl/= .

Ltac rename_for_newvar' H x :=
  let asgn_x := fresh "asgn_to_"x in
  rename H into asgn_x;
    apply (elimT eqP) in asgn_x.
Ltac rename_for_newvar :=
  match goal with
    | [ H : context[?x _==_] |- _ ] =>
      rename_for_newvar' H x
    | _ => idtac
  end.
