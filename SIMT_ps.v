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
