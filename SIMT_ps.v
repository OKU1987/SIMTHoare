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

Ltac simplify_mask' :=
  match goal with
    | [ H : SIMT.all _ _ |- _] => apply lem_5_1 in H
    | [ H : context[e_and] |- _] => rewrite -?setD_e_and_neg-?setI_e_and in H
    | [ |- context[e_and] ] => rewrite -?setD_e_and_neg-?setI_e_and
    | _ => fail
  end.
Ltac simplify_mask'' :=
  match goal with
    | [ H : mask_of _ ?z = _, H0 : context[?z] |- _] => rewrite H in H0
    | [ H : context[setI] |- _] =>
      rewrite ?/T_mask?/empty?setTI?setIT?setI0?set0I in H
    | [ H : context[setD] |- _] =>
      rewrite ?/T_mask?/empty?setTD?setDT?setD0?set0D in H
    | [ |- context[setI]] =>
      rewrite ?/T_mask?/empty?setTI?setIT?setI0?set0I
    | [ |- context[setD]] =>
      rewrite ?/T_mask?/empty?setTD?setDT?setD0?set0D
    | _ => fail
  end.
Ltac simplify_mask := repeat simplify_mask'; repeat simplify_mask''.

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

Lemma exprzn : forall n m : nat, (exprz n%:Z m) = (expn n m).
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  elim.
  { intro. rewrite expr0z expn0. done. }
  { intros. rewrite exprSz. rewrite H. rewrite expnS. done. }
Qed.

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
Ltac destruct_by_andP H :=
  let H' := fresh H"'" in
  try (move: H;
       case/andP => H H'; destruct_by_andP H').
Ltac eliminate_forallP' i :=
  match goal with
    | [ H : context[ FiniteQuant.quant0b] |- _ ] =>
      try (move: (elimT forallP H) => {H} H;
           try (move: (H i) => {H} H);
           try (rewrite /mask_of/bool_of_int ?in_set//= in H));
        destruct_by_andP H
    | _ => idtac
  end.
Ltac eliminate_forallP i := eliminate_forallP' i; rename_for_newvar.
Ltac eliminate_existsP' i' :=
  match goal with
    | [ H : context[FiniteQuant.quant0b] |- _ ] =>
      try (move: (elimT existsP H) => {H} H;
           try (rewrite in_set/mask_of in H);
           case H => i' {H} H
          );
        destruct_by_andP H
    | _ => idtac
  end.
Ltac eliminate_existsP := let i' := fresh "i" in
                        eliminate_existsP' i'; rename_for_newvar.

Ltac apply_hoare_rules' loopinv :=
  try
    (match goal with
       | [|-Hoare_proof _ _ _ sync _] => eapply H_Sync
       | [|-Hoare_proof _ (fun _ => forall _, assign _ _ _ _ _ _ _ _ -> _ _) _
                        (?x @ ?es :::= ?e) _] =>
         eapply H_Assign
       | [|-Hoare_proof _ _ _ (?x @ ?es :::= ?e) _] =>
         (try eapply H_Assign; try (eapply H_Conseq_pre; [eapply H_Assign|]))
       | [|-Hoare_proof _ _ _ (?P;; sync) _] =>
         eapply H_Seq; try eapply H_Sync
       | [|-Hoare_proof _ _ _ (?P;; (WHILE _ DO _)) _] =>
         eapply H_Seq with (psi:=loopinv)
       | [|-Hoare_proof _ _ _ (?P;; ?Q) _] =>
         eapply H_Seq
       | [|-Hoare_proof _ _ _ (IFB _ THEN _ ELSE _) _] =>
         let z' := fresh "z" in eapply H_If; move => z'
       | [|-Hoare_proof _ _ ?m (WHILE ?e DO ?P)
                        (fun _ => loopinv _ /\ none _ _)] =>
         let z' := fresh "z" in eapply H_While; move => z'
       | [|-Hoare_proof _ _ ?m (WHILE ?e DO ?P) _ ] =>
         let z' := fresh "z" in
         eapply H_Conseq_post; [eapply H_While; move => z'|]
       | [|-Hoare_proof _ _ _ skip _] => eapply H_Skip
       | _ => fail
     end;
     apply_hoare_rules' loopinv).

Ltac apply_hoare_rules := repeat (apply_hoare_rules' False).
Ltac apply_hoare_rules_with loopinv := repeat (apply_hoare_rules' loopinv).

Require Import seq.
Require Import bigop ssralg.
Open Scope ring_scope.

Ltac apply_big_nat_widen m n1 n2 H :=
  match goal with
    | [|-context[\big[_/_]_(_ <= _ < _ | (_ <= ?n)%nat) _ _]]=>
      rewrite -2?(@big_nat_widen _ 0%:Z +%R m n1 n2 _ _ H);
      rewrite -(@big_nat_widen _ 0%:Z +%R m n1 n2 predT _ H)
    | [|-context[\big[_/_]_(_ <= _ < _ | ?P _) _ _]]=>
      rewrite (@big_nat_widen _ 0%:Z +%R m n1 n2 [eta P] _ H);
      rewrite (@big_nat_widen _ 0%:Z +%R m n1 n2 [eta xpredC P] _ H);
      rewrite (@big_nat_widen _ 0%:Z +%R m n1 n2 predT _ H)
    | _ => fail 1 "a"
  end.
