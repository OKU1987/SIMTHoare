Require Import SIMT_util.
Require Import Vector_of_tuple.
Require Import SIMT.
Require Import SIMT_verification_util.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat fintype.
From mathcomp Require Import tuple finfun div bigop finset ssralg ssrint intdiv.
Implicit Arguments var [n].
Implicit Arguments Vector_of_tuple [T n].
Implicit Arguments tuple_of_Vector [T n].
Close Scope nat_scope.
Open Scope int_scope.
Coercion Vector_of_tuple : tuple_of >-> Vector.t.
Coercion tuple_of_Vector : Vector.t >-> tuple_of.

Definition funcT := fun n op tpl => @func n op (Vector_of_tuple tpl).
Definition varT := fun n op tpl => @var n op (Vector_of_tuple tpl).
Implicit Arguments funcT [n].
Implicit Arguments varT [n].

Notation "z < z'" := (@intOrdered.ltz z z').
Notation "z <= z'" := (@intOrdered.lez z z').
Notation "z + z'" := (@intZmod.addz z z').
Notation "z - z'" := (z + (intZmod.oppz z')).
Notation "z * z'" := (@intRing.mulz z z').

Delimit Scope E_scope with E.
Notation "a + b" := (@funcT 2 e_plus [tuple (a : E); (b : E)]) : E_scope.
Notation "a - b" := (@funcT 2 e_minus [tuple (a : E); (b : E)]) : E_scope.
Notation "a * b" := (@funcT 2 e_mult [tuple (a : E); (b : E)]) : E_scope.
Notation "a / b" := (@funcT 2 e_div [tuple (a : E); (b : E)]) : E_scope.
Notation "a % b" := (@funcT 2 e_mod [tuple (a : E); (b : E)]) (at level 60) : E_scope.
Notation "a && b" := (@funcT 2 e_and [tuple (a : E); (b : E)]) : E_scope.
Notation "a < b" := (@funcT 2 e_lt [tuple (a : E); (b : E)]) : E_scope.
Notation "a '<=' b" := (@funcT 2 e_leq [tuple (a : E); (b : E)]) : E_scope.
Notation "a '=E' b" := (@funcT 2 e_eq [tuple (a : E); (b : E)]) (at level 90) : E_scope.
Notation "'!' a" := (@funcT 1 e_neg [tuple (a : E)]) (at level 35, right associativity) : E_scope.
Notation "x '@' i '::=' e" := (@asgn _ x i (e : E)) (at level 110, right associativity).
Notation "x ':::=' e" := (x @ [tuple] ::= (e : E)) (at level 110, right associativity).
Close Scope E.

Definition E_of_int z := @funcT 0 (const z) [tuple].
Coercion E_of_int : int >-> E.

Definition scalar : Set := V 0%nat.
Definition scalar_LV : Set := LV 0%nat.
Definition scalar_SV : Set := SV 0%nat.
Definition E_of_scalar (x : scalar) : E := @varT _ x [tuple].
Definition E_of_scalar_LV (x : scalar_LV) := @varT _ x [tuple].
Definition E_of_scalar_SV (x : scalar_SV) := @varT _ x [tuple].
Coercion E_of_scalar : scalar >-> E.
Coercion E_of_scalar_LV : scalar_LV >-> E.
Coercion E_of_scalar_SV : scalar_SV >-> E.
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
Ltac remove_ReflectF :=
  match goal with
  | [ |-context[@eq_op]] =>
      case: eqP => // => _
  | [ H : context[eqnP] |- _] =>
    move: H; case: eqnP => //= _ H
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
  repeat unfold_update_state; simpl;
  repeat simplify_update_state';
  rewrite ?ffunE/= ;
  rewrite ?eq_refl/= ;
  repeat remove_ReflectF.

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
           try (rewrite in_set/mask_of ?ffunE in H);
           case H => i' {H} H
          );
        destruct_by_andP H
    | _ => idtac
  end.
Ltac eliminate_existsP := let i' := fresh "i" in
                        eliminate_existsP' i'; rename_for_newvar.
Ltac asgn_to_scalar_never_fail H i :=
  match type of H with
    | context[FiniteQuant.quant0b] =>
      let H0 := fresh H"'" in
      try (destruct H as [ [H H0] | H];
           eliminate_forallP' i;
           try (move: (introT eqP H0) => {H0} H0; rename_for_newvar);
           try (move: H;
                match goal with
                  | [H' : SIMT.all _ _ |- _] =>
                    try (rewrite ?in_set/bool_of_int (H' i)// -(H' i) //)
                  | [H' : context[setT]|- _] =>
                    rewrite in_set// in H'
                  | _ => fail 1 "There may be inactivated threads"
                end;
                move => {H} H))
    | _ => let msg := (type of H) in
           fail 1 "This tactic cannot be applied terms of type: "msg
  end;
  eliminate_existsP.
Ltac certify_asgn_performed_by H i H' :=
  match type of H with
    | context[FiniteQuant.quant0b] =>
      let H0 := fresh H"'" in
      try (destruct H as [ [H H0] | H];
           eliminate_forallP' i;
           try (move: (introT eqP H0) => {H0} H0; rename_for_newvar);
           try (move: (H i);
                try (rewrite in_set ?ffunE/= /bool_of_int (H' i) //);
                try (rewrite -(H' i) //);
                move => {H} H))
    | _ => fail
  end.

Ltac no_active_threads_no_asgn_to H :=
  match goal with
    | [ H' : none _ _ |- _] =>
      match type of H with
        | context[FiniteQuant.quant0b] =>
          let H0 := fresh H"'" in
          let i' := fresh "i" in
          try (destruct H as [ [H H0] | H];
                try (eliminate_existsP' i'; rename_for_newvar;
                     move: (H' i'); rewrite ?ffunE=> {H'} H';
                       rewrite in_set ?ffunE (eqP H') // in H))
        | _ => let msg := (type of H) in
               fail 1 "This tactic cannot be applied terms of type: "msg
      end
    | _ => fail 1 "There may be activated threads"
  end.

Ltac asgn_not_occur_due_to H H' :=
  match type of H with
    | context[FiniteQuant.quant0b] =>
      let H0 := fresh H"'" in
      let i' := fresh "i" in
      try (destruct H as [ [H H0] | H];
           try (eliminate_existsP' i'; rename_for_newvar;
                rewrite in_set ?ffunE (eqP (H' i')) // in H))
    | _ => let msg := (type of H) in
           fail 1 "This tactic cannot be applied terms of type: "msg
  end.

Ltac apply_hoare_rules :=
  try
    (match goal with
       | [|-Hoare_proof _ _ _ sync _] => eapply H_Sync
       | [|-Hoare_proof _ (fun _ => forall _, assign _ _ _ _ _ _ _ _ -> _ _) _
                        (?x @ ?es ::= ?e) _] =>
         eapply H_Assign
       | [|-Hoare_proof _ _ _ (?x @ ?es ::= ?e) _] =>
         (try eapply H_Assign; try (eapply H_Conseq_pre; [eapply H_Assign|]))
       | [|-Hoare_proof _ _ _ (?P;; sync) _] =>
         eapply H_Seq; try eapply H_Sync
       | [|-Hoare_proof _ _ _ (?P;; ?Q) _] =>
         eapply H_Seq
       | [|-Hoare_proof _ _ _ (IFB _ THEN _ ELSE _) _] =>
         let z' := fresh "z" in eapply H_If; move => z'
       | [|-Hoare_proof _ _ ?m (WHILE ?e DO ?P) _ ] =>
         let z' := fresh "z" in
         eapply H_Conseq_post; [eapply H_While; move => z'|]
       | [|-Hoare_proof _ _ _ skip _] => eapply H_Skip
       | _ => fail
     end;
     apply_hoare_rules).

Ltac apply_hoare_rules_with_a_loopinv' loopinv :=
  try
    (match goal with
       | [|-Hoare_proof _ _ _ sync _] => eapply H_Sync
       | [|-Hoare_proof _ (fun _ => forall _, assign _ _ _ _ _ _ _ _ -> _ _) _
                        (?x @ ?es ::= ?e) _] =>
         eapply H_Assign
       | [|-Hoare_proof _ _ _ (?x @ ?es ::= ?e) _] =>
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
      apply_hoare_rules_with_a_loopinv' loopinv).

Ltac apply_hoare_rules_with_a_loopinv loopinv := repeat (apply_hoare_rules_with_a_loopinv' loopinv).

Unset Ltac Debug.

From mathcomp Require Import seq.
From mathcomp Require Import bigop ssralg.
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
(*
Module Kogge_Stone.
  Definition s : scalar_SV := shared _ 0%nat.

  (* The array length is N *)
  Lemma implements_prefixsum :
    forall (n : nat) (N : { n : nat | 0%nat < n}) (a : SV 1%nat) (a0 : 1.-tuple int -> int),
      (exists l : nat, sval N = expn 2 l) ->
      n = (sval N)%nat ->
      Hoare_proof N
                  (fun s : state _ =>
                     forall (e : int) i,
                       s[[varT a [tuple e:E]]](i) = a0 [tuple e])
                  (fun _ => 1%:Z)
                  (s :::= 1%nat
                     ;;
                     (WHILE (s < n) DO
                            (IFB (s <= tid) THEN
                                 (a @ [tuple tid] ::= varT a[tuple tid] + varT a[tuple tid - s])
                                 ELSE skip
                                 ;;
                                 s :::= s * 2%nat
                                 ;;
                                 sync
                            )
                     )
                  )%E
                  (fun s : state _ =>
                     forall (i : T N) (j : nat),
                       j < sval N ->
                       s[[varT a [tuple j:E] ]](i) =
                       (\sum_(0 <= m < j+1) a0 [tuple (Posz m)])).
  Proof.
    move=> n N a a0 N_2exp n_2N.
    remember
      (fun st =>
         exists l : nat,
           (forall i : T N, st[[`s]](i) = (2 ^ l)%:Z) /\
           (2 ^ l <= n)%nat /\
           (forall j,
             ((2 ^ l - 1 < j)%nat -> (j < n) ->
              (forall i, st[[varT a [tuple j:E]]](i) = (\sum_(j-2^l+1 <= k < j+1) (a0 [tuple k%:Z]))))) /\
           (forall j,
              ((j < 2 ^ l)%nat ->
               (forall i, st[[varT a [tuple j:E]]](i) = (\sum_(0 <= k < j+1) (a0 [tuple k%:Z])))))
      )%Z as loopinv.
    apply_hoare_rules_with_a_loopinv loopinv.
    { subst.
      move=> s0 pre_cond new_s.
      case new_s => // => {new_s} new_s.
      rewrite /sassign/= => asgn_to_new_s.
      destruct N_2exp as [l N_2exp].
      move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s.
      simplify_update_state.
      exists 0%nat.
      rewrite N_2exp leq_exp2l//= (leq0n l) //= expn0.
      move: (Ordinal (svalP N)) => th0.
      asgn_to_scalar_never_fail asgn_to_new_s th0.
      rewrite/const/= in pre_cond,asgn_to_new_s|-*.
      repeat split => //; move=> j.
      { rewrite -[(1 - 1)%nat]add0n addnBA // addnK => j_gt_0 _ i0.
        rewrite (pre_cond j i0) subnK // addn1 big_nat1 // . }
      { rewrite ltnS leqn0 => j_lt_1 i0.
        rewrite (pre_cond j i0) (elimT eqP j_lt_1) add0n big_nat1 // . }}
    { cbv beta.
      move=> s0 pre_cond new_a asgn_to_new_a new_s asgn_to_new_s H.
      destruct pre_cond as [ [loopinv_pre while_cond] if_cond].
      destruct new_a as [new_a|new_a]; destruct new_s as [new_s|new_s]; rewrite // .
      rewrite /s_es in asgn_to_new_a,asgn_to_new_s.
      destruct H; rewrite Heqloopinv in loopinv_pre|-*; last first.
      { destruct loopinv_pre as [l [H7 [H7' [H7'' H7''']]]].
        exists l.
        repeat split => // .
        { move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s i.
          no_active_threads_no_asgn_to asgn_to_new_s.
          simplify_update_state.
          move: (H7 i) => /= => {H7} H7.
          rewrite -H7//= . }
        { move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s j H8 H8' i.
          move: (asgn_to_new_a [tuple j%:Z]) => {asgn_to_new_a} asgn_to_new_a.
          no_active_threads_no_asgn_to asgn_to_new_a.
          simplify_update_state.
          rewrite -(H7'' _ H8 H8' i)// . }
        { move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s j H8 i.
          move: (asgn_to_new_a [tuple j%:Z]) => {asgn_to_new_a} asgn_to_new_a.
          no_active_threads_no_asgn_to asgn_to_new_a.
          simplify_update_state.
          move: (H7''' j).
          rewrite -(H7''' _ H8 i)//= . }
      }
      { subst.
        destruct loopinv_pre as [l [old_s [n_ge_2expl [old_a old_a']]]].
        move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s.
        simplify_update_state.
        destruct N_2exp as [l_N N_2exp].
        move: n_ge_2expl.
        rewrite leq_eqVlt.
        case/orP.
        { rewrite eq_sym => n_eq_2expl.
          apply (elimT eqP) in n_eq_2expl.
          rewrite ?exprzn?n_eq_2expl/const/= in old_s,while_cond.
          move: (Ordinal (svalP N)) => th0.
          move: (H th0).
          rewrite -(while_cond th0).
          rewrite intOrdered.ltz_def-(old_s th0)/const eq_refl /negb// . }
        { (* Case: 2 ^ l < n *)
          move => n_gt_2expl.
          exists (l.+1)%nat.
          repeat split => // .
          { move => i.
            asgn_to_scalar_never_fail asgn_to_new_s (Ordinal (svalP N)).
            rewrite /= in old_s.
            rewrite asgn_to_new_s0 (old_s i) ?exprzn/= -expnSr// . }
          { rewrite N_2exp in n_gt_2expl|-*.
            apply ltn_pexp2l in n_gt_2expl => // .
            apply leq_pexp2l => // . }
          { (* SCase: 2^l.+1 <= j (P(j), which is stronger than P_pre(j), holds) *)
            move => j j_gt_subn_2_expl1(* = P(j) *) j_lt_n i.
            (* lemma in order to prove Q(tid) *)
            assert (2 ^ l - 1 < 2 ^ l.+1 - 1)%nat.
            { apply ltn_sub2r.
              { clear.
                elim l => // n IH.
                apply (ltn_trans IH).
                rewrite ltn_exp2l// . }
              rewrite ltn_exp2l// . }
            rewrite eq_refl.
            move: (asgn_to_new_a [tuple j%:Z]) => {asgn_to_new_a} asgn_to_new_a.
            move: (svalP N) => /= => N_gt_0.
            simplify_mask.
            certify_asgn_performed_by asgn_to_new_a (Ordinal j_lt_n) H.
            { move: (old_s (Ordinal j_lt_n)) (if_cond (Ordinal j_lt_n)).
              rewrite /= => old_s_eq_2expl.
              rewrite old_s_eq_2expl ?exprzn/intOrdered.lez/= .
              rewrite -(leq_add2r 1) ?subn1 ?addn1 in H0.
              rewrite subn1 -(ltn_add2r 1) ?addn1 in j_gt_subn_2_expl1.
              rewrite ?prednK in H0,j_gt_subn_2_expl1; try by rewrite expn_gt0.
              rewrite -ltnS (ltn_trans H0 j_gt_subn_2_expl1)(* proof of Q(tid), which is equiv. to P_pre(j) *)/int_of_bool => z0_true.
              rewrite ?in_set -z0_true/= negbF// in asgn_to_new_a.
                by apply (introT eqP), val_inj. }
            { eliminate_existsP.
              move: (old_a j (ltn_trans H0 j_gt_subn_2_expl1)(* proof of P_pre(j) *) j_lt_n i0) => /= => old_a0.
              rewrite /const in old_a0.
              rewrite /= in asgn_to_new_a0,asgn_to_new_a'.
              apply (elimT eqP) in asgn_to_new_a'.
              inversion asgn_to_new_a' => {asgn_to_new_a'}.
              subst.
              rewrite old_a0 in asgn_to_new_a0.
              rewrite ?in_set/bool_of_int/= in asgn_to_new_a.
              move: (if_cond i0) asgn_to_new_a (old_s i0) => /= => {old_s}.
              rewrite /int_of_bool.
              case:ifP => old_s_leq_i0 z0_eq; rewrite -z0_eq // => _ old_s.
              rewrite old_s ?exprzn/= in old_s_leq_i0,asgn_to_new_a0.
              rewrite /intOrdered.lez in old_s_leq_i0.
              rewrite /intZmod.oppz/= in asgn_to_new_a0.
              rewrite expnS in j_gt_subn_2_expl1|-*.
              move: (asgn_to_new_a0) (expn_gt0 2 l) old_s_leq_i0 old_a old_a0 j_gt_subn_2_expl1.
              case:(expn 2 l) => // n {asgn_to_new_a0} asgn_to_new_a _ n_lt_i0 old_a old_a0 j_cond.
              rewrite n_lt_i0 in asgn_to_new_a.
              assert (j_cond' : (n.+1 - 1 < i0 - n.+1)%nat)
                by rewrite mul2n -addnn -(@subnK (succn n) i0) -?addnBA 1?addnC ?ltn_add2r in j_cond => // .
              move: (leq_sub (leqnn i0) (leq0n n.+1)).
              rewrite subn0 => i0_n1_lt_i0.
              move: (old_a _ j_cond' (leq_ltn_trans i0_n1_lt_i0 j_lt_n) i0).
              rewrite /const/= => old_a0'.
              move: asgn_to_new_a.
              rewrite old_a0' intZmod.addzC -subnDA addnn mul2n.
              remember (i0 - n.+1 + 1)%nat as mid.
              remember (i0 - (n.+1).*2 + 1)%nat as low.
              assert (low <= mid)
                by rewrite Heqlow Heqmid /= leq_add2r -addnn subnDA leq_sub2r// .
              remember (index_iota low mid) as lst.
              remember (index_iota mid (i0+ 1)) as lst'.
              move: (@big_cat _ 0%:Z (GRing.add_monoid int_ZmodType) nat lst lst' predT (fun k => a0 [tuple k%:Z])).
              rewrite /= => lst_lst'.
              rewrite -[intZmod.addz _  _]lst_lst' Heqlst Heqlst' /index_iota// .
              rewrite -{2}(@subnK low mid) => // .
              remember (mid - low)%nat as mid_low.
              rewrite addnC -seq.iota_add addnC.
              rewrite Heqmid_low {Heqmid_low} addnBA// .
              rewrite subnK // .
              rewrite Heqmid leq_add2r // . }}
          { (* SCase: j < 2^l.+1 (P(j) doesn't hold) *)
            move => j j_lt_2expl1 i.
            rewrite eq_refl.
            move: (asgn_to_new_a [tuple j%:Z]) => {asgn_to_new_a} asgn_to_new_a.
            simplify_mask.
            rewrite N_2exp ltn_exp2l// -(@leq_exp2l 2)// -N_2exp in n_gt_2expl.
            move: (leq_trans j_lt_2expl1 n_gt_2expl) => j_lt_N.
            case: (ltnP j (2 ^ l)) => j_cmp_2expl.
            { (* SSCase: j < 2^l (P_pre(j), which is equiv. to Q(tid), doesn't hold) *)
              asgn_not_occur_due_to asgn_to_new_a if_cond; last first.
              { eliminate_existsP.
                apply (elimT eqP) in asgn_to_new_a'.
                rewrite /s_es in asgn_to_new_a'.
                inversion asgn_to_new_a' => {asgn_to_new_a'}.
                subst.
                rename i0 into j.
                move: (old_s j) (if_cond j) asgn_to_new_a.
                rewrite /= => {old_s} old_s.
                rewrite ltnNge in j_cmp_2expl.
                apply negbTE in j_cmp_2expl.
                rewrite old_s ?exprzn/= j_cmp_2expl/= => z0_false.
                rewrite in_set -z0_false/bool_of_int// . }
              { move: {asgn_to_new_a} (old_a' _ j_cmp_2expl i).
                rewrite /const/= asgn_to_new_a'// . }}
            { (* SSCase: 2^l <= j (P_pre(j) holds) *)
              certify_asgn_performed_by asgn_to_new_a (Ordinal j_lt_N) H.
              { move: (old_s (Ordinal j_lt_N)) (if_cond (Ordinal j_lt_N)).
                rewrite /= => {old_s} old_s.
                rewrite old_s/const ?exprzn/= j_cmp_2expl => z0_true.
                rewrite ?in_set -z0_true/= negbF// in asgn_to_new_a.
                by apply (introT eqP), val_inj. }
              { eliminate_existsP.
                rewrite in_set in asgn_to_new_a.
                rewrite /= in asgn_to_new_a0.
                apply (elimT eqP) in asgn_to_new_a'.
                inversion asgn_to_new_a'.
                subst.
                rename i0 into j.
                rewrite -(@prednK (2^l)) ?expn_gt0// -subn1 in j_cmp_2expl.
                move: (old_a _ j_cmp_2expl j_lt_N j) => /= old_a0.
                rewrite old_a0 in asgn_to_new_a0.
                move: (if_cond j) asgn_to_new_a old_s => /= . (* => {old_s}. *)
                rewrite /int_of_bool.
                case:ifP => old_s_leq_i0 z0_eq; rewrite -z0_eq ?andbF// => _ old_s.
                rewrite (old_s i) ?exprzn/= in old_s_leq_i0,asgn_to_new_a0.
                rewrite /intOrdered.lez in old_s_leq_i0.
                rewrite /intZmod.oppz/= in asgn_to_new_a0.
                rewrite expnS in j_lt_2expl1.
                move: (asgn_to_new_a0) (expn_gt0 2 l) old_s_leq_i0 old_a' old_a0 j_lt_2expl1.
                case:(expn 2 l) => // n {asgn_to_new_a0} asgn_to_new_a _ n_lt_i0 old_a' old_a0 j_lt_2expl1.
                rewrite /const/= in old_a'.
                move: asgn_to_new_a.
                rewrite ?n_lt_i0 ?subnS ?addn1 ?prednK // ?ltn_subRL ?addn0// .
                rewrite -subnS (old_a' (j - n.+1)%nat)// .
                rewrite subnS ?addn1 prednK // ?ltn_subRL ?addn0// .
                rewrite intZmod.addzC.
                remember (j - n)%nat as mid.
                remember (index_iota 0 mid) as lst.
                remember (index_iota mid j.+1) as lst'.
                move: (@big_cat _ 0%:Z (GRing.add_monoid int_ZmodType) nat lst lst' predT (fun k => a0 [tuple k%:Z])).
                rewrite /= => lst_lst'.
                rewrite -[intZmod.addz _  _]lst_lst' Heqlst Heqlst' /index_iota// .
                move: (ltnW n_lt_i0) => n_leq_j.
                rewrite -{2}(@subnK 0 mid) // ?subn0 addn0 Heqmid subnBA// .
                rewrite -seq.iota_add addnC addnBA // .
                rewrite (@subnK j) // ?addnK // .
                apply (leq_trans (leqnSn j) (leq_addr n _)).
                rewrite -(ltn_add2r n.+1) subnK// ?addnn -mul2n// . }}}}}}
    { rewrite /none Heqloopinv => {Heqloopinv}  {loopinv} s0 loopinv_none i.
      case: loopinv_none.
      case => l loopinv.
      move: loopinv.
      case => loopinv.
      case => loopinv'.
      case => _ loopinv''' _none j j_cond.
      rewrite /const/= in loopinv,_none.
      rewrite (loopinv i) ?exprzn/= int_of_boolK/int_of_bool in _none.
      move: loopinv' (_none i).
      rewrite leq_eqVlt.
      case/orP => H; try rewrite H // .
      move=> _.
      rewrite -n_2N -(elimT eqP H)/= in j_cond.
      rewrite (loopinv''' _ j_cond) // .
    }
  Qed.
End Kogge_Stone.
*)
Ltac apply_hoare_rules_with_loopinv' :=
  try
    (match goal with
     | [|- Hoare_proof' _ _ _ (skip' _) ?phi] =>
       idtac "skip";
         let s' := fresh "s" in
         let H' := fresh "H" in
       try (eapply H_Skip'; fail);
       try (eapply H_Conseq_pre' with (phi':=phi);
             [eapply H_Skip'| try (move=> s' H'; repeat move=> _; eapply H')])
     | [|- Hoare_proof' _ _ ?m (sync' _) ?phi] =>
       idtac "sync";
         let s' := fresh "s" in
         let H' := fresh "H" in
       try (eapply H_Sync'; fail);
         try (eapply H_Conseq_pre' with
              (phi':=(fun s => SIMT.all _ m \/ none _ m -> phi s));
               [eapply H_Sync'| try (move=> s' H'; repeat move=> _; eapply H')])
     | [|- Hoare_proof' _ _ ?m (asgn' _ ?n ?x ?es ?e) ?phi] =>
       idtac "assign: "x"["es"] := "e;
         let s' := fresh "s" in
         let H' := fresh "H" in
         (try eapply H_Assign';
         try (eapply H_Conseq_pre';
               [eapply H_Assign'| try (move=> s' H'; repeat move=> _; eapply H')]))
     | [|- Hoare_proof' _ _ _ (seq' _ _ _) _] =>
       idtac "seq";
       eapply H_Seq'; last first
     | [|- Hoare_proof' _ _ _ (P_if' _ _ _ _) _] =>
       idtac "if";
         try (eapply H_If'; fail);
         let s' := fresh "s" in
         let H' := fresh "H" in
         let z' := fresh "z" in
         eapply H_Conseq_pre';
           [eapply H_If'; move=> z'|try (move=> s' H'; repeat move=> _; eapply H')]
     | [|-Hoare_proof' _ _ _ (P_while' _ _ _ ?loopinv)
                       (fun _ => ?loopinv _ /\ none _ _)] =>
       idtac "while_done"loopinv;
         let z' := fresh "z" in
         let s' := fresh "s" in
         let H' := fresh "H" in
         eapply H_Conseq_pre';
           [eapply H_While'; move => z'|try (move=> s' H'; repeat move=> _; eapply H')]
     | [|-Hoare_proof' _ _ ?m (P_while' _ ?e _ ?loopinv) _ ] =>
       idtac "while"loopinv;
       let z' := fresh "z" in
       let s' := fresh "s" in
       let H' := fresh "H" in
       eapply H_Conseq_post'
       with (psi':=(fun s : state _ =>
                      loopinv s /\
                      none _ [ffun i => e_and [tuple m i; s[[e]](i)]]));
       [eapply H_While'; move => z'| try (move=> s' H'; repeat move=> _; eapply H')]
     | _ => fail
     end;
      apply_hoare_rules_with_loopinv').

Ltac apply_hoare_rules_with_loopinv :=
  repeat apply_hoare_rules_with_loopinv'; try (move=> s H; eassumption).


Ltac apply_hoare_rules_with_loopinv_original' :=
  try
    (match goal with
     | [|-Hoare_proof' _ _ _ (sync' _) _] => idtac "sync"; eapply H_Sync'
     | [|-Hoare_proof' _ (fun _ => forall _, assign _ _ _ _ _ _ _ _ -> _ _) _
                       (asgn' _ _ ?x ?es ?e) _] =>
       idtac "assign_done"; eapply H_Assign'
     | [|-Hoare_proof' _ _ _ (asgn' _ _ ?x ?es ?e) _] =>
       idtac "assign";
       (try eapply H_Assign'; try (eapply H_Conseq_pre'; [eapply H_Assign'|]))
     | [|-Hoare_proof' _ _ _ (seq' _ _ (sync' _)) _] =>
       idtac "seq_sync";
       eapply H_Seq'; try eapply H_Sync'
     | [|-Hoare_proof' _ _ _ (seq' _ _ (P_while' _ _ _ ?loopinv)) _] =>
       idtac "seq_while";
         eapply H_Seq' with (psi:=loopinv)
     | [|-Hoare_proof' _ _ _ (seq' _ ?P ?Q) _] =>
       idtac "seq";
       eapply H_Seq'
     | [|-Hoare_proof' _ _ _ (P_if' _ _ _ _) _] =>
       idtac "if";
       let z' := fresh "z" in eapply H_If'; move => z'
     | [|-Hoare_proof' _ _ _ (P_while' _ _ _ ?loopinv)
                       (fun _ => ?loopinv _ /\ none _ _)] =>
       idtac "while_done";
       let z' := fresh "z" in eapply H_While'; move => z'
     | [|-Hoare_proof' _ _ _ (P_while' _ _ _ _) _ ] =>
       idtac "while";
       let z' := fresh "z" in
       eapply H_Conseq_post'; [eapply H_While'; move => z'|]
     | [|-Hoare_proof' _ _ _ (skip' _) _] => idtac "skip"; eapply H_Skip'
     | _ => fail
     end;
      apply_hoare_rules_with_loopinv_original').

Ltac apply_hoare_rules_with_loopinv_original := repeat apply_hoare_rules_with_loopinv_original'.


Module Blelloch.
  Variable N : { n : nat | (0 < n)%nat }.
  Definition s : scalar_SV := shared _ 0%nat.
  Definition temp : scalar_SV := shared _ 1%nat.
  Definition t : scalar_LV := local _ 2%nat.

  Notation "'SKIP'" := (skip' _).

  Notation "'SYNC'" := (sync' _).
  Notation "x '@' i '::=' e" := (@asgn' _ _ x i (e : E)) (at level 110, right associativity).
  Notation "x ':::=' e" := (x @ [tuple] ::= (e : E)) (at level 110, right associativity).
  Notation "P ;; Q" := (seq' _ P Q) (at level 150).
  Notation "'IFB' e 'THEN' P 'ELSE' Q" := (P_if' _ e P Q) (at level 135).
  Notation "'WHILE_inv' e 'DO' P 'WITH' PHI" := (P_while' _ e P PHI) (at level 135).

  Lemma implements_prefixsum :
    forall (n : nat) (a : SV 1%nat) (a0 : 1.-tuple int -> int)
           (e11 e12 e21 e22 : 1.-tuple E),
      (exists l : nat, sval N = expn 2 l) ->
      n = (sval N)%nat ->
      e11 = [tuple (s * (2%:Z * tid + 1%:Z) - 1%:Z)%E] ->
      e12 = [tuple (s * (2%:Z * tid + 2%:Z) - 1%:Z)%E] ->
      e21 = [tuple (s * tid + s/ 2%:Z - 1%:Z)%E] ->
      e22 = [tuple (s * tid + s - 1%:Z)%E] ->
      Hoare_proof' N
                   (fun s : state _ =>
                      forall (j : nat) i,
                        s[[varT a [tuple j:E]]](i) = a0 [tuple j%:Z])
                   [ffun _ => 1]
                   ((s :::= 1%:Z)
                      ;;
                      (WHILE_inv
                         (s < n) DO
                         (IFB (tid < n / (2%:Z * s)) THEN
                              (a @ e12 ::= varT a e12 + varT a e11)
                              ELSE SKIP
                              ;;
                              (s :::= s * 2%nat)
                              ;;
                              SYNC
                         )
                         WITH
                         (fun st : state _ =>
                            forall i,
                            exists l : nat,
                              st[[s]](i) = (2 ^ l)%:Z /\
                              (2 ^ l <= n)%nat /\
                              forall j : nat,
                                (j < sval N)%nat ->
                                if ((2 ^ l %| j + 1)%nat) then
                                  st[[varT a [tuple j:E] ]](i) =
                                  (\sum_(0 <= m < 2 ^ l) a0 [tuple (j - m)%:Z])
                                else
                                  exists l' : nat,
                                    (l' < l)%nat /\
                                    (2 ^ l' %| j + 1)%nat /\
                                    ~~(2 ^ l'.+1 %| j + 1)%nat /\
                                    st[[varT a [tuple j:E] ]](i) =
                                    (\sum_(0 <= m < 2 ^ l') a0 [tuple (j - m)%:Z])
                         )
                      );;
                      (temp :::= varT a[tuple n - 1%:Z]);;
                      (a @ [tuple n - 1 %:Z] ::= 0%:Z);;
                      (WHILE_inv
                         (1%:Z < s) DO
                         IFB (tid < n / s) THEN
                         (t :::= varT a e21;;
                            a @ e21 ::= varT a e22;;
                            a @ e22 ::= `t + varT a e22
                         )
                         ELSE SKIP
                         ;;
                         s :::= s / 2%nat
                         ;;
                         SYNC
                         WITH
                         (fun st : state _ =>
                            forall i,
                              (st[[temp]](i) = \sum_(0 <= m < n) a0 [tuple m%:Z]) /\
                              exists l : nat,
                                st[[s]](i) = (n %/ 2 ^ l)%:Z /\
                                (2 ^ l <= n)%nat /\
                                forall j,
                                  (j < sval N)%nat ->
                                  if ((n %/ 2^ l) %| (j + 1))%nat then
                                    st[[varT a [tuple j:E] ]](i) =
                                    (\sum_(0 <= m < j + 1 - (n %/ 2 ^ l)) a0 [tuple m%:Z])
                                  else
                                    exists l' : nat,
                                      (2 ^ l' < (n %/ 2 ^ l))%nat /\
                                      (2 ^ l' %| j + 1)%nat /\
                                      ~~(2 ^ l'.+1 %| j + 1)%nat /\
                                      st[[varT a [tuple j:E] ]](i) =
                                      (\sum_(0 <= m < 2 ^ l') a0 [tuple (j - m)%:Z])
                         )
                      );;
                      SYNC;;
                      (a @ [tuple 0%:Z:E] ::= `temp)
                   )%E
                   (fun s : state _ =>
                      forall (i : T N) (j : nat),
                        s[[varT a [tuple 0%:Z:E] ]](i) =
                        (\sum_(0 <= m < n) a0 [tuple m%:Z]) /\
                        (0 < j ->
                         j < sval N ->
                         s[[varT a [tuple j:E] ]](i) =
                         (\sum_(0 <= m < j) a0 [tuple  m%:Z]))).
  Proof.
    move=> n a a0 e11 e12 e21 e22 N_2exp n_N Heq_e11 Heq_e12 Heq_e21 Heq_e22.
    apply_hoare_rules_with_loopinv.
    { cbv beta.
      move=> {Heq_e11} {Heq_e12} {e11} {e12}.
      case=> l_map s_map loopinv.
      case=> // => new_t asgn_to_new_t.
      case=> // => new_a_e21 asgn_to_new_a_e21.
      case=> // => new_a_e22 asgn_to_new_a_e22.
      case=> // => new_s asgn_to_new_s sync_H i.
      destruct loopinv as [ if_cond [while_cond loopinv_pre] ].
      move: (loopinv_pre i) => {loopinv_pre}.
      case => old_temp.
      case => l.
      case => old_s.
      case => two_expl_leq_n old_a.
      rewrite /s_es in asgn_to_new_a_e21, asgn_to_new_a_e22, asgn_to_new_s.
      rewrite /= in old_s.
      split.
      { move=> {old_a} {asgn_to_new_a_e21} {asgn_to_new_a_e22} {asgn_to_new_s}.
        simplify_update_state. }
      { destruct sync_H as [sync_H|sync_H]; last first.
        { (* all threads are inactivated none *)
          exists l.
          repeat split => // .
          { move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s.
            no_active_threads_no_asgn_to asgn_to_new_s.
            move=> {asgn_to_new_a_e21} {asgn_to_new_a_e22} {asgn_to_new_s} {old_a} {while_cond} {if_cond} {Heq_e21} {Heq_e22} {two_expl_leq_n}.
            move=> {asgn_to_new_t}.
            simplify_update_state.
            move: asgn_to_new_s'.
            rewrite ffunE in old_s.
            rewrite old_s// . }
          { move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s j j_lt_N.
            move: (asgn_to_new_t [tuple]) => {asgn_to_new_t} asgn_to_new_t.
            move: (asgn_to_new_a_e21 [tuple j%:Z]) => {asgn_to_new_a_e21} asgn_to_new_a_e21.
            move: (asgn_to_new_a_e22 [tuple j%:Z]) => {asgn_to_new_a_e22} asgn_to_new_a_e22.
            no_active_threads_no_asgn_to asgn_to_new_a_e22.
            rewrite /eq_rect/eq_rect in asgn_to_new_a_e21.
            no_active_threads_no_asgn_to asgn_to_new_a_e21.
            move: (old_a j j_lt_N) => {old_a} old_a.
            case: ifP => index_mod.
            { rewrite index_mod in old_a.
              move => {asgn_to_new_s} {while_cond} {if_cond} {sync_H} {old_s} {asgn_to_new_a_e21} {asgn_to_new_a_e22}.
              simplify_update_state.
              rewrite /= in old_a, asgn_to_new_a_e21', asgn_to_new_a_e22'|-*.
              rewrite ?ffunE in old_a.
              rewrite asgn_to_new_a_e22'.
              simplify_update_state.
              rewrite asgn_to_new_a_e21'// . }
            { rewrite index_mod in old_a.
              destruct old_a as [l' [l'_leq_l [index_mod0 [index_mod1 old_a]]]].
              exists l'.
              repeat split => // .
              move=> {asgn_to_new_s} {while_cond} {if_cond} {sync_H} {old_s}.
              simplify_update_state.
              rewrite /= ?ffunE in old_a.
              rewrite asgn_to_new_a_e22'.
              simplify_update_state.
              rewrite asgn_to_new_a_e21'// . }}}
        { (* all threads are activated: all *)
          exists (l.+1)%nat.
          move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s.
          asgn_to_scalar_never_fail asgn_to_new_s i.
          repeat split.
          { move=> {asgn_to_new_a_e21} {asgn_to_new_a_e22} {old_a} {while_cond} {if_cond} {asgn_to_new_s'}.
            rewrite /s_es in asgn_to_new_s0.
            simplify_update_state.
            symmetry in asgn_to_new_s0.
            move: asgn_to_new_s0.
            rewrite ?ffunE in old_s|-*.
            rewrite old_s/const/= divz_nat -divnMA// .
            rewrite mulnC expnS// . }
          { destruct N_2exp as [log2_N N_2exp].
            (* while_cond is satisfied in the loop *)
            move: (Ordinal (svalP N)) => th0.
            move: (sync_H th0).
            move: (while_cond th0).
            rewrite ?ffunE/= => {while_cond} while_cond.
            rewrite -while_cond.
            rewrite /e_and/= int_of_boolK.
            move/int_of_bool_true => {while_cond} while_cond.
            (* end *)
            rewrite n_N N_2exp leq_exp2l// in two_expl_leq_n.
            rewrite ?ffunE in old_s.
            rewrite ?ffunE old_s/const/= n_N N_2exp ltn_divRL ?dvdn_Pexp2l// in while_cond.
            rewrite -N_2exp -n_N mul1n in while_cond.
            move: two_expl_leq_n.
            rewrite leq_eqVlt.
            case/orP => two_expl_cmp_n.
            { apply (elimT eqP) in two_expl_cmp_n.
              rewrite two_expl_cmp_n -N_2exp -n_N ltnn// in while_cond. }
            { rewrite n_N N_2exp leq_exp2l// . }}
          { move => j j_lt_N.
            destruct N_2exp as [log2_N N_2exp].
            (* while_cond is satisfied in the loop *)
            move: (Ordinal (svalP N)) => th0.
            move: (sync_H th0).
            move: (while_cond th0).
            rewrite ?ffunE/= => while_cond'.
            rewrite -while_cond'.
            rewrite /e_and/= int_of_boolK.
            move/int_of_bool_true => s_gt_1.
            rewrite ?ffunE in old_s.
            rewrite old_s in s_gt_1.
            move: {+}s_gt_1 => l_ltn_logN.
            rewrite n_N N_2exp in l_ltn_logN.
            (* end *)
            case:eqnP => // => p.
            case:eqnP => // => p'.
            rewrite /eq_rec_r/eq_rec/eq_rect.
            rewrite (eq_irrelevance (Logic.eq_sym _) erefl).
            rewrite eq_refl/= .
            rewrite n_N N_2exp leq_exp2l// in two_expl_leq_n.
            rewrite /const ?ffunE/= in l_ltn_logN.
            rewrite ltn_divRL ?dvdn_exp2l// mul1n in l_ltn_logN.
            move: (asgn_to_new_a_e22 [tuple j%:Z]) => {asgn_to_new_a_e22} asgn_to_new_a_e22.
            move: (svalP N) => /= => N_gt_0.
            assert (e22_inv_leq_j : ((j + 1)%/(n %/ 2^l) - 1 <= j)%nat).
            { clear.
              case: (@eqnP ((j + 1)%/(n %/ 2^l))%nat 0%nat) => index_cmp_0.
              { rewrite index_cmp_0// . }
              { apply (introF eqP), neq0_lt0n in index_cmp_0.
                rewrite -(leq_add2r 1) subnK// .
                rewrite leq_div// . }
            }
            assert (j_div_snew_odd : (n %/ 2^l.+1 %| j + 1)%nat ->
                                     ~(n %/ 2^l %| j + 1)%nat ->
                                     odd((j + 1)%/(n %/ 2 ^ l.+1))).
            { move: n_N N_2exp l_ltn_logN.
              clear.
              move=> n_N N_2exp l_ltn_logN index_mod index_mod'.
              rewrite -N_2exp-n_N in l_ltn_logN.
              case: (boolP (odd ((j + 1) %/ (n %/ 2^l.+1)))); last first => // .
              rewrite -dvdn2 dvdn_divRL// muln_divA ?expnS ?divnMl// .
              rewrite -expnS n_N N_2exp dvdn_exp2l// .
              rewrite -(@ltn_exp2l 2) -?N_2exp-?n_N// . }
            assert (e21_inv_leq_j : (n %/ 2^l.+1 %| j + 1)%nat ->
                                    ~(n %/ 2^l %| j + 1)%nat ->
                                    (((j + 1)%/(n %/ 2^l.+1) - 1)%/2 <= j)%nat).
            { move: j_div_snew_odd s_gt_1.
              clear.
              move=> j_div_snew_odd s_gt_1 index_mod index_mod'.
              move: (j_div_snew_odd index_mod index_mod').
              move=> {j_div_snew_odd} j_div_snew_odd.
              assert (~~ (odd ((j + 1) %/ (n %/ 2 ^ l.+1) - 1)))
                by rewrite odd_sub ?odd_gt0 ?negb_add/= ?j_div_snew_odd// .
              rewrite -dvdn2 in H.
              rewrite leq_divLR// .
              rewrite -(@leq_add2r 1) subnK.
              rewrite leq_divLR// .
              rewrite (@leq_trans (j * 2 + 1)%nat)// .
              rewrite leq_add2r leq_pmulr// .
              rewrite leq_pmulr// .
              rewrite expnS mulnC divnMA divn2 half_gt0// .
              rewrite /const ?ffunE//= in s_gt_1.
              apply odd_gt0=> // . }
            set (e21_inv :=
                   fun (H : (n %/ 2^l.+1 %| j + 1)%nat)
                       (H0 : ~(n %/ 2^l %| j + 1)%nat) =>
                     Ordinal (leq_ltn_trans (e21_inv_leq_j H H0) j_lt_N)).
            set (e22_inv := Ordinal (leq_ltn_trans e22_inv_leq_j j_lt_N)).
            assert (e22K : ((n %/ 2^l) %| (j + 1))%nat ->
                           (((n %/ 2^l) * e22_inv + (n %/ 2^l) - 1) = j)%nat).
            { move: n_N N_2exp two_expl_leq_n l_ltn_logN s_gt_1.
              clear.
              move=> n_N N_2exp two_expl_leq_n l_ltn_logN s_gt_1 index_mod.
              rewrite -N_2exp-n_N in l_ltn_logN.
              rewrite /= .
              rewrite mulnBr muln1 subnK.
              rewrite muln_divA// mulnC mulnK ?addnK// .
              rewrite ?ffunE in s_gt_1.
              apply (ltn_trans (ltn0Sn _) s_gt_1)=> // .
              rewrite leq_pmulr// divn_gt0// ?addn1 ?ltn0Sn// -?[j.+1%nat]addn1.
              apply dvdn_leq=> // .
              rewrite addn1 ltn0Sn// .
              rewrite ?ffunE in s_gt_1.
              apply (ltn_trans (ltn0Sn _) s_gt_1)=> // .
            }
            assert (e21K : forall (H : (n %/ 2^l.+1 %| j + 1)%nat)
                                  (H0 : ~(n %/ 2^l %| j + 1)%nat),
                       ((n %/ 2^l.+1) * (2 * (e21_inv H H0) + 1) - 1 = j)%nat).
            { move: j_div_snew_odd n_N N_2exp two_expl_leq_n l_ltn_logN s_gt_1.
              clear.
              move=> j_div_snew_odd n_N N_2exp two_expl_leq_n l_ltn_logN s_gt_1 index_mod index_mod'.
              rewrite -N_2exp-n_N in l_ltn_logN.
              assert (~~ (odd ((j + 1) %/ (n %/ 2 ^ l.+1) - 1)))
                by rewrite odd_sub ?odd_gt0 ?negb_add/= ?j_div_snew_odd// .
              rewrite /= .
              rewrite -dvdn2 in H.
              rewrite muln_divA// [(2 * _)%nat]mulnC ?mulnK// .
              rewrite subnK.
              rewrite muln_divA// mulnC mulnK// ?addnK// .
              rewrite ?ffunE/= in s_gt_1.
              rewrite expnS mulnC divnMA divn2 half_gt0// .
              apply (odd_gt0 (j_div_snew_odd index_mod index_mod')). }
            case:ifP => index_mod.
            { (* SCase: P_next is satisfied *)
              (* i.e., the case where the assignment to 'a' is performed *)
              rewrite Heq_e22 in asgn_to_new_a_e22.
              case: (boolP (n %/ 2 ^ l %| j + 1)%nat) => index_mod_pre.
              { (* SSCase: P_prev is satisfied *)
                case: asgn_to_new_a_e22 => asgn_to_new_a_e22.
                { destruct asgn_to_new_a_e22.
                  eliminate_forallP' H.
                  rename H into asgn_to_new_a_e22.
                  move: (asgn_to_new_a_e22 e22_inv).
                  rewrite /mask_of/bool_of_int ?in_set//= .
                  move=> {asgn_to_new_a_e22} {H0} asgn_to_new_a_e22.
                  move: (if_cond e22_inv).
                  move: (while_cond e22_inv).
                  rewrite /e22_inv/= .
                  rewrite ?ffunE/= in s_gt_1.
                  rewrite ?ffunE/= /const old_s/= divz_nat/= s_gt_1.
                  move=> {while_cond} {if_cond} while_cond if_cond.
                  rewrite ?ffunE/= -while_cond-if_cond in asgn_to_new_a_e22.
                  suff: ((j + 1) %/ (n %/ 2 ^ l) - 1 < n %/ (n %/ 2 ^ l))%nat.
                  move => if_cond_true.
                  rewrite if_cond_true in asgn_to_new_a_e22.
                  rewrite /int_of_bool/= in asgn_to_new_a_e22.
                  rewrite /= negbF// in asgn_to_new_a_e22.
                  apply (introT eqP), val_inj=> /= .
                  move=> {asgn_to_new_s'} {asgn_to_new_s0} {asgn_to_new_a_e21}.
                  simplify_update_state.
                  rewrite /const/= old_s/= .
                  rewrite addn_gt0 ?divn_gt0 ?expn_gt0// .
                  rewrite {3}n_N N_2exp leq_exp2l// two_expl_leq_n orbT// .
                  rewrite (e22K index_mod_pre)// .
                  rewrite -(@ltn_add2r 1).
                  rewrite subnK ?addn1 ?ltnS.
                  apply leq_div2r.
                  rewrite n_N j_lt_N// .
                  rewrite -[j.+1%nat]addn1.
                  rewrite (divn_gt0 _ (ltn_trans (ltn0Sn _) s_gt_1)).
                  rewrite dvdn_leq// addn1 ltn0Sn// . }
                { eliminate_existsP.
                  rewrite ltn_exp2l// in l_ltn_logN.
                  rewrite ?ffunE/= asgn_to_new_a_e0.
                  apply (elimT eqP) in asgn_to_new_a_e22'.
                  rewrite ?ffunE/s_es/= in asgn_to_new_a_e22' => {asgn_to_new_a_e0}.
                  simplify_update_state.
                  assert (a == a = true) by rewrite eq_refl// .
                  rewrite H/= /const old_s/= => {H}.
                  rewrite ?ffunE/= in asgn_to_new_a_e22'.
                  inversion asgn_to_new_a_e22'=> {asgn_to_new_a_e22'}.
                  rename H0 into asgn_to_new_a_e22'.
                  move: asgn_to_new_a_e22'.
                  rewrite /const old_s/= .
                  rewrite n_N N_2exp -?expnB// .
                  rewrite addn_gt0 expn_gt0 orTb orbT//= =>asgn_to_new_a_e22'.
                  inversion asgn_to_new_a_e22'.
                  move: H0=> {asgn_to_new_a_e22'} asgn_to_new_a_e22'.
                  rewrite asgn_to_new_a_e22'.
                  move=> {asgn_to_new_s'} {asgn_to_new_s0}.
                  move: (asgn_to_new_t [tuple] i1) => {asgn_to_new_t} asgn_to_new_t.
                  destruct asgn_to_new_t as [H asgn_to_new_t].
                  move: asgn_to_new_t=> {H}.
                  rewrite /s_es Heq_e21/= ?int_of_boolK.
                  rewrite /const old_s/= .
                  rewrite ?ffunE/= -divnMA -[(_ * 2)%nat]mulnC -expnS n_N N_2exp -?expnB// .
                  rewrite mul1n addn_gt0 expn_gt0 orTb orbT// .
                  move=> asgn_to_new_t.
                  rewrite asgn_to_new_t=> {asgn_to_new_t}.
                  move: (@leq_sub2l (j + 1) 1 (n%/2^l.+1 + 1)).
                  rewrite addn1 addnK ?ltn0Sn/= => j_snew_leq_j.
                  set (j_snew := Ordinal (leq_ltn_trans (j_snew_leq_j is_true_true) j_lt_N)).
                  assert (j_snew_eq : (2 ^ (log2_N - l) * i1 + 2 ^ (log2_N - l.+1) - 1 = j_snew)%nat).
                  { rewrite /= -asgn_to_new_a_e22'.
                    rewrite -(@ltn_exp2l 2)// in l_ltn_logN.
                    rewrite -[(n %/ _).+1%nat]addn1.
                    rewrite subnK.
                    rewrite n_N N_2exp -expnB -1?(@ltn_exp2l 2)// .
                    rewrite -{3}[(log2_N - l)%nat]subnSK -1?(@ltn_exp2l 2)// .
                    rewrite expnS -{3}[(2 ^ (log2_N - l.+1))%nat]mul1n.
                    rewrite 2?[(_ * 2 ^ _)%nat]mulnC.
                    rewrite subnDA.
                    rewrite -[(_ * i1 + 2 ^ _ * 2 - 2 ^ _ * 1)%nat]addnBA.
                    rewrite -mulnBr ?subn1 ?muln1//= .
                    rewrite leq_mul2l orbT// .
                    rewrite addn_gt0 expn_gt0 orbT// . }
                  rewrite j_snew_eq=> {j_snew_eq}.
                  move: (old_a j_snew (ltn_ord j_snew)).
                  assert (j_snew_mod : (n %/ 2 ^ l %| j_snew + 1)%nat = false).
                  { rewrite addn1/= .
                    rewrite -subSn// .
                    rewrite subSS addn1.
                    rewrite addn1 in index_mod,index_mod_pre.
                    rewrite (dvdn_subr (dvdn_leq (ltn0Sn _) index_mod) index_mod_pre)// .
                    rewrite n_N N_2exp -2?expnB// .
                    rewrite -[(log2_N - l)%nat]subnSK// .
                    rewrite expnS -{2}[(2 ^ (log2_N - l.+1))%nat]mul1n// .
                    rewrite dvdn_pmul2r//= .
                    rewrite expn_gt0// .
                    rewrite addn1 in index_mod_pre.
                    apply dvdn_leq in index_mod_pre=> // .
                    rewrite -[j.+1%nat]addn1 in index_mod_pre.
                    apply (@leq_trans (n %/ 2 ^ l)%nat)=> // .
                    rewrite n_N N_2exp -2?expnB// .
                    rewrite -[(log2_N - l)%nat]subnSK// .
                    rewrite ltn_exp2l ltnSn// . }
                  rewrite j_snew_mod.
                  rewrite /const/= ?addn1 ?subSS => old_a'.
                  destruct old_a' as [l' [l'_lt_s_old [index_mod_pre' [index_mod' old_a']]]].
                  rewrite ?ffunE/= in old_a'.
                  rewrite old_a'=> {old_a'}.
                  move: (negbT j_snew_mod) l'_lt_s_old.
                  rewrite /j_snew/= .
                  rewrite ?addn1 subSS.
                  rewrite {1}n_N {2}n_N N_2exp -?expnB// .
                  rewrite -[(log2_N - l)%nat]subnSK// .
                  rewrite ltn_exp2l ltnS// .
                  move=> index'_mod l'_leq_log2s.
                  move: (dvdn_sub index_mod (dvdnn _)).
                  rewrite addn1 subSn.
                  rewrite {1}n_N N_2exp -expnB// .
                  move=> index'_mod_pre.
                  move:l'_leq_log2s.
                  rewrite leq_eqVlt.
                  case/orP => l'_cmp_log2s; last first.
                  { apply (dvdn_exp2l 2) in l'_cmp_log2s.
                    rewrite (dvdn_trans l'_cmp_log2s index'_mod_pre)// in index_mod'. }
                  rewrite n_N N_2exp -expnB// -(elimT eqP l'_cmp_log2s).
                  rewrite {1}big_nat_rev add0n.
                  assert (F_eq : forall i,
                             (0 <= i < 2^l')%nat && true ->
                             (fun x => a0 [tuple (j - 2^l' - (2^l' - x.+1))%:Z]) i =
                             (fun x => a0 [tuple (x + (1 + j - 2^l'.+1))%:Z]) i).
                  { move: index_mod_pre.
                    rewrite n_N N_2exp -expnB// .
                    rewrite -[(log2_N - l)%nat]subSS subSn// .
                    rewrite -(elimT eqP l'_cmp_log2s) [(j + 1)%nat]addn1.
                    clear.
                    move=> index_mod i.
                    do 2 case/andP.
                    move => _ i_lt_2exp_l _.
                    rewrite subnAC subnBA// .
                    rewrite -subnDA addnn -mul2n -expnS addnC -[i.+1%nat]addn1.
                    rewrite addnBA ?addnA ?add1n// .
                    apply dvdn_leq=> // . }
                  rewrite {1}big_nat_cond.
                  rewrite (@eq_bigr _ _ _ nat (index_iota 0 (2 ^ l')) _ _ _ F_eq) => {F_eq}.
                  rewrite -big_nat_cond.
                  rewrite addnC.
                  assert (ub_eq : (j.+1 - 2^l' - (j + 1 - 2^l'.+1) = 2^l')%nat).
                  { move: index_mod_pre.
                    rewrite n_N N_2exp -expnB// .
                    rewrite -[(log2_N - l)%nat]subSS subSn// .
                    rewrite -(elimT eqP l'_cmp_log2s) addn1.
                    clear.
                    move/(@dvdn_leq _ _ (ltn0Sn _)).
                    move=> index_mod_pre.
                    rewrite subnAC subnBA// .
                    rewrite -subnDA subnDl.
                    rewrite expnS -{2}[(2 ^ l')%nat]mul1n -mulnBl subn1 mul1n// . }
                  rewrite -ub_eq => {ub_eq}.
                  rewrite -(@big_addn _ _ _ _ (j.+1 - 2^l')%nat (j + 1 - 2^l'.+1)%nat (fun _ => true) (fun x => a0 [tuple x%:Z])) add0n addn1.
                  move=> {index'_mod} {index'_mod_pre}.
                  move: (asgn_to_new_a_e21 [tuple j%:Z])
                  => {asgn_to_new_a_e21} asgn_to_new_a_e21.
                  case: asgn_to_new_a_e21 => asgn_to_new_a_e21; last first.
                  { eliminate_existsP.
                    rewrite asgn_to_new_a_e0=> {asgn_to_new_a_e0}.
                    rewrite Heq_e22/=/const old_s/= .
                    rewrite /s_es Heq_e21/=/const old_s ?ffunE/= mul1n in asgn_to_new_a_e21'.
                    rewrite ?ffunE/= in s_gt_1.
                    rewrite addn_gt0 divn_gt0// ?expn_gt0 ?s_gt_1 ?orbT ?orTb// in asgn_to_new_a_e21'.
                    move: {+}l_ltn_logN.
                    rewrite -{1}[l%nat]addn0 -ltn_subRL=> l_ltn_logN'.
                    rewrite ?ffunE/= in s_gt_1.
                    rewrite ?ffunE/= addn_gt0 (ltn_trans (ltn0Sn _) s_gt_1) orbT// .
                    apply (elimT eqP) in asgn_to_new_a_e21'.
                    inversion asgn_to_new_a_e21'.
                    move: H0=> {asgn_to_new_a_e21'} asgn_to_new_a_e21'.
                    move: index_mod_pre.
                    rewrite -asgn_to_new_a_e21' subnK.
                    rewrite dvdn_addr ?(dvdn_mulr i2)// .
                    move/dvdn_leq=> // .
                    rewrite dvdn_leq// .
                    rewrite -{3}[2%nat]expn1.
                    rewrite n_N N_2exp -2?expnB// -?subnDA ?addn1 ?leq_exp2l// .
                    move=> contr.
                    move: (contr is_true_true)=> {contr}.
                    rewrite -{1}[(log2_N - l)%nat]subnSK// .
                    rewrite ltnn// .
                    rewrite ltn_divRL ?(ltn_trans (ltn0Sn _) s_gt_1)// .
                    rewrite n_N N_2exp -expnB// -{1}[2%nat]expn1 dvdn_exp2l// .
                    rewrite addn_gt0 ?dvdn_gt0 ?expn_gt0.
                    rewrite ltn_divRL ?(ltn_trans (ltn0Sn _) s_gt_1) ?orbT// .
                    rewrite n_N N_2exp -expnB// -{1}[2%nat]expn1 dvdn_exp2l// . }
                  destruct asgn_to_new_a_e21 as [index_neq asgn_to_new_a_e21].
                  move=> {index_neq}.
                  rewrite asgn_to_new_a_e21/= => {asgn_to_new_a_e21}.
                  move: (old_a j j_lt_N).
                  rewrite index_mod_pre/= /const /= .
                  move: index_mod index_mod_pre.
                  rewrite addn1 n_N N_2exp -2?expnB// .
                  rewrite -[(log2_N - l)%nat]subnSK -?(elimT eqP l'_cmp_log2s)// .
                  move=> {old_a} index_mod index_mod_pre old_a.
                  apply (dvdn_leq (ltn0Sn _)) in index_mod.
                  apply (dvdn_leq (ltn0Sn _)) in index_mod_pre.
                  rewrite ?ffunE/= in old_a.
                  rewrite old_a=> {old_a}.
                  rewrite intZmod.addzC.
                  rewrite -[intZmod.addz _ _](@big_cat _ _ (GRing.add_monoid int_ZmodType) nat _ _).
                  rewrite /index_iota ?subn0/= .
                  rewrite -{2}[j.+1%nat]add0n -iota_add.
                  rewrite -subnDA subKn// .
                  rewrite subnDA subnAC subKn// .
                  rewrite expnS -{3}[(2^l')%nat]mul1n addnBA ?leq_mul2r ?orbT// .
                  rewrite expnS in index_mod_pre.
                  rewrite subnK// mul1n addnBA// addnC mul2n -addnn subnDr// .
                  rewrite addnC expnS mul2n -addnn subnDA subnK ?leq_subr// .
                  rewrite -(@leq_add2r (2^l')%nat) addnn -mul2n -expnS subnK// .
                  rewrite addn1 in index_mod_pre.
                  apply dvdn_leq in index_mod_pre.
                  rewrite -ltnS.
                  apply (@leq_trans (n %/ 2 ^ l)%nat)=> // .
                  rewrite n_N N_2exp -2?expnB// ltn_exp2l//-[(log2_N - l)%nat]subnSK// .
                  rewrite ltn0Sn// .
                  split => // .
                  rewrite /mask_of in_set ?ffunE/= ?int_of_boolK in asgn_to_new_a_e22.
                  rewrite ?int_of_boolK asgn_to_new_a_e22 int_of_bool_true// . }}
              { (* SSCase: P_prev is NOT satisfied *)
                rewrite ltn_exp2l// in l_ltn_logN.
                case: asgn_to_new_a_e22 => asgn_to_new_a_e22; last first.
                { eliminate_existsP.
                  rewrite ffunE asgn_to_new_a_e0=> {asgn_to_new_s'} {asgn_to_new_a_e0}.
                  apply (elimT eqP) in asgn_to_new_a_e22'.
                  rewrite /s_es/= in asgn_to_new_a_e22'.
                  inversion asgn_to_new_a_e22'.
                  move: H0=> {asgn_to_new_a_e22'}.
                  rewrite /eq_rec_r/eq_rec/eq_rect/= .
                  simplify_update_state.
                  assert (a == a = true) by rewrite eq_refl// .
                  (* rewrite H asgn_to_new_a_e22' => {H}. *)
                  rewrite H => {H}.
                  move: {+}l_ltn_logN.
                  rewrite -{1}[l%nat]addn0 -ltn_subRL=> l_ltn_logN'.
                  rewrite ?ffunE in s_gt_1.
                  rewrite /const old_s/= addn_gt0 (ltn_trans (ltn0Sn _) s_gt_1) orbT// .
                  move=> asgn_to_new_a_e22'.
                  inversion asgn_to_new_a_e22'.
                  move: H0=> {asgn_to_new_a_e22'} asgn_to_new_a_e22'.
                  move: index_mod_pre.
                  rewrite -asgn_to_new_a_e22' subnK.
                  rewrite dvdn_addr ?(dvdn_mulr i2)// .
                  rewrite dvdnn// .
                  rewrite (dvdn_mulr _ (dvdnn _))// .
                  rewrite n_N N_2exp -expnB// .
                  rewrite addn_gt0 ?dvdn_gt0 ?expn_gt0 ?orbT// . }
                destruct asgn_to_new_a_e22 as [index_neq asgn_to_new_a_e22].
                move=> {index_neq}.
                rewrite ffunE asgn_to_new_a_e22/= => {asgn_to_new_a_e22}.
                move=> {asgn_to_new_s'} {asgn_to_new_s0}.
                simplify_update_state.
                move: (asgn_to_new_a_e21 [tuple j%:Z]) => {asgn_to_new_a_e21} asgn_to_new_a_e21.
                set (e21_inv' := (e21_inv index_mod (elimT negP index_mod_pre))).
                case: asgn_to_new_a_e21 => asgn_to_new_a_e21.
                { destruct asgn_to_new_a_e21.
                  eliminate_forallP' H.
                  rename H into asgn_to_new_a_e21.
                  move: (e21K index_mod (elimT negP index_mod_pre)).
                  rewrite /= .
                  move: (asgn_to_new_a_e21 e21_inv').
                  rewrite /mask_of/bool_of_int ?in_set//= .
                  move=> {e21K} {asgn_to_new_a_e21} {H0} asgn_to_new_a_e21 e21K.
                  move: (if_cond e21_inv').
                  move: (while_cond e21_inv').
                  rewrite /e21_inv'/e21_inv/= .
                  rewrite ?ffunE/= in s_gt_1.
                  rewrite ?ffunE/= old_s/= divz_nat/= s_gt_1.
                  move=> {while_cond} {if_cond} while_cond if_cond.
                  rewrite ?ffunE/= -while_cond-if_cond in asgn_to_new_a_e21.
                  move: {+}l_ltn_logN.
                  rewrite -(@dvdn_Pexp2l 2)// -N_2exp -n_N=> n_dvdn.
                  suff: (((j + 1) %/ (n %/ 2 ^ l.+1) - 1)%/ 2 < n %/ (n %/ 2 ^ l))%nat.
                  move => if_cond_true.
                  rewrite if_cond_true in asgn_to_new_a_e21.
                  rewrite /int_of_bool/= in asgn_to_new_a_e21.
                  rewrite /= negbF// in asgn_to_new_a_e21.
                  apply (introT eqP), val_inj=> /= .
                  rewrite Heq_e21/= .
                  rewrite ?ffunE /const/= old_s/= .
                  rewrite mul1n addn_gt0 ?divn_gt0 ?expn_gt0// s_gt_1 orbT// .
                  move: e21K.
                  rewrite mulnDr mulnA {1}[(_ * 2)%nat]mulnC [(2 * (n %/ _))%nat]muln_divA// {1}expnS.
                  rewrite divnMl// -divnMA [(2 ^ l * 2)%nat]mulnC -expnS muln1 =>index_eq.
                  rewrite index_eq// .
                  rewrite ltn_divLR// .
                  rewrite mulnC.
                  rewrite -[(n %/ 2 ^l)%nat](@divnMl 2)// -expnS.
                  rewrite -muln_divA// .
                  rewrite {1}[(2 * _)%nat]muln_divA// ?divnMl// .
                  rewrite -(@ltn_add2r 1) subnK// ?addn1 ?ltnS/= .
                  apply leq_div2r.
                  rewrite n_N j_lt_N// .
                  rewrite divn_gt0.
                  apply dvdn_leq => // .
                  rewrite -[j.+1%nat]addn1// .
                  rewrite n_N N_2exp -expnB// expn_gt0 orTb// .
                  rewrite muln_divA// expnS divnMl// .
                  apply dvdn_div.
                  rewrite n_N N_2exp.
                  rewrite dvdn_Pexp2l// . }
                eliminate_existsP.
                rewrite asgn_to_new_a_e0=> {asgn_to_new_a_e0}.
                rewrite Heq_e22/const/= old_s ?ffunE/= .
                simplify_update_state.
                assert (snew_gt_0 : (0 < n %/ 2 ^l.+1)%nat)
                  by rewrite n_N N_2exp -expnB// expn_gt0 ?orTb// .
                move: {+}l_ltn_logN.
                move/(dvdn_exp2l 2).
                rewrite -N_2exp -n_N/= => snew_mod_n.
                rewrite /s_es/= Heq_e21/= ?ffunE old_s/= in asgn_to_new_a_e21'.
                apply (elimT eqP) in asgn_to_new_a_e21'.
                inversion asgn_to_new_a_e21'.
                move: H0.
                rewrite mul1n.
                rewrite ?ffunE/= in s_gt_1.
                rewrite 2?addn_gt0 ?divn_gt0 ?s_gt_1 ?expn_gt0 ?orTb ?orbT//= .
                rewrite -divnMA [(_ * 2)%nat]mulnC.
                move=> index_eq.
                rewrite n_N N_2exp leq_exp2l ?two_expl_leq_n ?orbT// .
                rewrite -N_2exp -n_N -[(n%/2^l)%nat](@divnMl 2)// in index_eq|-*.
                rewrite -muln_divA// [(2 * _)%nat]mulnC muln2 -addnn// in index_eq|-*.
                rewrite addnC -addnA [(_ + _ * i1)%nat]addnC.
                inversion index_eq.
                move: H0=> {index_eq} index_eq.
                rewrite -addnBA.
                rewrite index_eq addnC addn1=> {index_eq}.
                rewrite -expnS.
                move: (elimT dvdnP index_mod)=> index_modP.
                destruct index_modP as [k index_modP].
                move: (@mulnK n (2^l.+1)%nat).
                rewrite expn_gt0 orTb// mulnC => n_mulnK.
                move: (n_mulnK is_true_true)=> {n_mulnK} n_mulnK.
                rewrite -muln_divA// in n_mulnK.
                rewrite addn1 in index_modP.
                move: {+}j_lt_N.
                rewrite {1}index_modP -n_N -{2}n_mulnK leq_pmul2r// .
                rewrite leq_eqVlt.
                case/orP=> k_cmp_k'.
                { rewrite (elimT eqP k_cmp_k') n_mulnK in index_modP.
                  move=> {e21_inv'}.
                  rewrite addn1 index_modP dvdn_divLR in index_mod_pre.
                  rewrite -{1}[n%nat]muln1 dvdn_pmul2l ?dvd1n// in index_mod_pre.
                  rewrite n_N N_gt_0// .
                  rewrite expn_gt0 orTb// .
                  rewrite n_N N_2exp dvdn_Pexp2l ?two_expl_leq_n// . }
                move: k_cmp_k'.
                rewrite -(@leq_pmul2r (n%/2^l.+1))// .
                rewrite mulSnr -index_modP n_mulnK addSn {2}n_N=> j_snew_lt_n.
                move: (old_a _ j_snew_lt_n).
                rewrite addn1 -addSn.
                rewrite -{1}(@mulnK j.+1 (n %/ 2 ^ l.+1))// mulnC.
                rewrite -{1}[j.+1%nat]addn1.
                rewrite -muln_divA// .
                rewrite -mulnSr.
                assert (index_even : ~~(odd (j.+1 %/ (n %/ 2 ^l.+1)).+1)).
                { rewrite -2?addn1 odd_add.
                  rewrite (j_div_snew_odd index_mod (elimT negP index_mod_pre))// . }
                rewrite -dvdn2 in index_even.
                rewrite -{1}(@divnMl 2)// -expnS -muln_divA// 1?mulnC.
                rewrite dvdn_pmul2l// addn1 index_even/= /const/= => {old_a} old_a.
                rewrite ?ffunE in old_a.
                rewrite old_a=> {old_a}.
                rewrite -[(n %/ 2 ^ l)%nat](@divnMl 2)// -expnS mul2n -addnn.
                rewrite divnDl// subnDA addnK// .
                rewrite addn_gt0 ?expn_gt0 -expnS snew_gt_0 orbT// .
                rewrite addnn -mul2n -expnS// . }}
            { assert (index_mod_pre : ((n %/ 2 ^ l %| j + 1) = false)%nat).
              { move: index_mod.
                apply contraFF=> index_mod_pre.
                apply (@dvdn_trans (n %/ 2^l)%nat)=> // .
                rewrite expnS divnMA divnAC dvdn_div// n_N N_2exp -expnB// .
                rewrite -{1}[2%nat]expn1 dvdn_Pexp2l// -(@ltn_exp2l 2)// .
                rewrite ?ffunE/= in s_gt_1.
                rewrite expn0 expnB// -N_2exp -n_N s_gt_1// . }
              move: (old_a j j_lt_N).
              rewrite index_mod_pre/= => {old_a} old_a.
              destruct old_a as [l' [l'_lt_log2s [index_mod_pre' [index_mod' old_a]]]].
              move=> {asgn_to_new_s0} {asgn_to_new_s'}.
              case: asgn_to_new_a_e22=> asgn_to_new_a_e22; last first.
              { eliminate_existsP.
                move=> {asgn_to_new_a_e22} {asgn_to_new_a_e0} {asgn_to_new_a_e21}.
                rewrite /s_es Heq_e22/= in asgn_to_new_a_e22'.
                simplify_update_state.
                rewrite ?ffunE/= in s_gt_1.
                move: (ltn_trans (ltn0Sn _) s_gt_1)=> s_gt_0.
                move: asgn_to_new_a_e22'.
                rewrite ?ffunE/= old_s/= addn_gt0 ?s_gt_0 orbT// .
                move/(elimT eqP)=> index_eq.
                inversion index_eq.
                move: H0=> {index_eq} index_eq.
                move: index_mod_pre.
                rewrite -index_eq-mulnSr subnK ?muln_gt0 ?s_gt_0// .
                rewrite -{1}[(n %/ 2 ^ l)%nat]muln1 dvdn_pmul2l// dvd1n// . }
              destruct asgn_to_new_a_e22 as [index_eq asgn_to_new_a_e22].
              move=> {index_eq}.
              rewrite ffunE asgn_to_new_a_e22=> {asgn_to_new_a_e22}.
              simplify_update_state.
              move: (asgn_to_new_a_e21 [tuple j%:Z])=> {asgn_to_new_a_e21}.
              case=> asgn_to_new_a_e21; last first.
              { eliminate_existsP.
                move=> {asgn_to_new_a_e0}.
                rewrite /s_es Heq_e21/= in asgn_to_new_a_e21'.
                simplify_update_state.
                rewrite ?ffunE/= in s_gt_1.
                move: (ltn_trans (ltn0Sn _) s_gt_1)=> s_gt_0.
                move: asgn_to_new_a_e21'.
                rewrite ?ffunE/= old_s/= mul1n addn_gt0 ?divn_gt0// ?s_gt_1 orbT// .
                move/(elimT eqP)=> index_eq.
                inversion index_eq.
                move: H0=> {index_eq} index_eq.
                move: index_mod.
                rewrite -index_eq subnK ?addn_gt0 ?divn_gt0 ?s_gt_1 ?orbT// .
                rewrite -{1}[(n %/ 2 ^ l)%nat](@mulnK _ 2)// .
                rewrite [(_ * 2)%nat]mulnC.
                move: {+}l_ltn_logN.
                rewrite ltn_exp2l// => l_ltn_logN'.
                rewrite -muln_divA// .
                rewrite mulnC mulnA -mulSnr -divnMA [(2^l * _)%nat]mulnC -expnS.
                rewrite -{1}[(n %/ 2 ^ l.+1)%nat]mul1n.
                rewrite dvdn_pmul2r// ?dvd1n// .
                rewrite n_N N_2exp -expnB// expn_gt0 ?orTb// .
                rewrite n_N N_2exp -expnB// -{1}[2%nat]expn1 dvdn_Pexp2l// .
                rewrite -{1}[l%nat]addn0 -ltn_subRL// in l_ltn_logN'. }
              destruct asgn_to_new_a_e21 as [index_neq asgn_to_new_a_e21].
              eliminate_forallP asgn_to_new_a_e21.
              move=> {index_neq}.
              rewrite asgn_to_new_a_e21=> {asgn_to_new_a_e21}.
              simplify_update_state.
              rewrite ?ffunE in old_a.
              rewrite old_a=> {old_a}.
              exists l'.
              repeat split=> // .
              case: (ltnP (2 ^ l') (n %/ 2 ^ l.+1))=> // .
              move: {+}l_ltn_logN.
              rewrite ltn_exp2l// => l_ltn_logN'.
              rewrite n_N N_2exp -expnB// ?leq_exp2l// .
              move=> contr.
              apply (@dvdn_exp2l 2) in contr.
              rewrite expnB// -N_2exp -n_N in contr.
              rewrite -index_mod.
              apply (@dvdn_trans (2^l')%nat) => // . }}}}}
    { cbv beta.
      move=> {Heq_e11} {Heq_e12} {e11} {e12}.
      case=> l_map s_map.
      case=> loopinv loopinv_none sync_H.
      case=> // => new_a_0 asgn_to_new_a_0 i j.
      simplify_update_state.
      rewrite /const/= .
      split.
      { move: (loopinv i)=> {loopinv}.
        case=> /= => old_temp _.
        move: (asgn_to_new_a_0 [tuple 0%:Z])=> {asgn_to_new_a_0} asgn_to_new_a_0.
        destruct sync_H as [sync_H | sync_H]; move: (sync_H i);
        rewrite ?ffunE /none// => _.
        destruct asgn_to_new_a_0 as [ [asgn_to_new_a_0 asgn_to_new_a_1] | asgn_to_new_a_0];
          eliminate_forallP' i;
        try (move: (introT eqP asgn_to_new_a_1) => {asgn_to_new_a_1} asgn_to_new_a).
        move: asgn_to_new_a_0;
          rewrite (sync_H i) /s_es //= => {sync_H} sync_H.
        rewrite /= negbF// in sync_H.
        rewrite ?ffunE /const/= .
        apply (introT eqP), val_inj=> // .
        rewrite ?ffunE/= in asgn_to_new_a_0, old_temp.
        eliminate_existsP.
        rewrite asgn_to_new_a_1/= ?ffunE old_temp// . }
      { move=> j_gt_0 j_lt_N.
        move: (loopinv i)=> {loopinv}.
        case=> /= => old_temp old_a.
        destruct old_a as [l [old_s [two_expl_leq_n old_a]]].
        move: (old_a j j_lt_N)=> {old_a}.
        rewrite ?ffunE in old_s.
        rewrite /none/= old_s in loopinv_none.
        move: (loopinv_none i).
        rewrite ?ffunE int_of_boolK/= .
        move/int_of_bool_false.
        rewrite ltnNge/= negbK leq_eqVlt.
        destruct N_2exp as [log2_N N_2exp].
        rewrite n_N N_2exp leq_exp2l// in two_expl_leq_n.
        case/orP; last first.
        { rewrite ltnNge n_N N_2exp -expnB// expn_gt0// . }
        move/(elimT eqP)=> s_eq_1.
        rewrite s_eq_1 dvd1n addnK/= => old_a.
        move: (asgn_to_new_a_0 [tuple j%:Z])=> {asgn_to_new_a_0} asgn_to_new_a_0.
        asgn_to_scalar_never_fail asgn_to_new_a_0 i.
        { rewrite asgn_to_new_a_1/= .
          rewrite /const/= in old_a.
          rewrite old_a// . }
        { rewrite /s_es/= ?ffunE/= in asgn_to_new_a_0'.
          apply (elimT eqP) in asgn_to_new_a_0'.
          inversion asgn_to_new_a_0'.
          rewrite -H0// in j_gt_0. }}}
    { move=> {Heq_e21} {Heq_e22} {e21} {e22}.
      case=> l_map s_map pre_cond.
      case => // => new_a asgn_to_new_a.
      case => // => new_s asgn_to_new_s sync_H i.
      destruct pre_cond as [if_cond [while_cond loopinv_pre]].
      move: (loopinv_pre i) => {loopinv_pre}.
      case => l.
      case => old_s.
      case => two_expl_leq_n old_a.
      rewrite /s_es in asgn_to_new_a,asgn_to_new_s.
      rewrite ?ffunE/= in old_s.
      destruct sync_H as [sync_H|sync_H]; last first.
      { (* Case: all threads are inactivated (none) *)
        exists l.
        repeat split => // .
        { move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s.
          no_active_threads_no_asgn_to asgn_to_new_s.
          move=> {asgn_to_new_a} {asgn_to_new_s} {old_a} {while_cond} {if_cond}.
          simplify_update_state.
          rewrite asgn_to_new_s' // . }
        { move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s j j_lt_N.
          move: (asgn_to_new_a [tuple j%:Z]) => {asgn_to_new_a} asgn_to_new_a.
          no_active_threads_no_asgn_to asgn_to_new_a.
          move: (old_a j j_lt_N) => {old_a} old_a.
          case: ifP => index_mod.
          { rewrite index_mod in old_a.
            move => {asgn_to_new_s} {while_cond} {if_cond} {sync_H} {old_s}.
            simplify_update_state.
            rewrite /=?ffunE/=/const in old_a, asgn_to_new_a'|-*.
            rewrite asgn_to_new_a' old_a// . }
          { rewrite index_mod in old_a.
            destruct old_a as [l' [l'_leq_l [index_mod0 [index_mod1 old_a]]]].
            exists l'.
            repeat split => // .
            move=> {asgn_to_new_s} {while_cond} {if_cond} {sync_H} {old_s}.
            simplify_update_state.
            rewrite /= ?ffunE/=/const in old_a.
            rewrite /const asgn_to_new_a' //= . }}}
      { (* Case: all threads are activated (all) *)
        exists (l.+1)%nat.
        move: (asgn_to_new_s [tuple]) => {asgn_to_new_s} asgn_to_new_s.
        simplify_update_state.
        asgn_to_scalar_never_fail asgn_to_new_s i.
        rewrite ?ffunE/= in asgn_to_new_s0.
        repeat split.
        { rewrite asgn_to_new_s0 old_s/= expnS mulnC // . }
        { destruct N_2exp as [log2_N N_2exp].
          (* while_cond is satisfied in the loop *)
          move: (Ordinal (svalP N)) => th0.
          move: (sync_H th0).
          rewrite ?ffunE/= -(while_cond th0)/= ?ffunE/= .
          rewrite /e_and/= int_of_boolK.
          move/int_of_bool_true => {while_cond} while_cond.
          (* end *)
          rewrite old_s/const/= n_N N_2exp ltn_exp2l// in while_cond.
          rewrite n_N N_2exp leq_exp2l// . }
        { move => j j_lt_N.
          rewrite eq_refl.
          destruct N_2exp as [log2_N N_2exp].
          (* while_cond is satisfied in the loop *)
          move: (Ordinal (svalP N)) => th0.
          move: (sync_H th0).
          rewrite ?ffunE/= -(while_cond th0)/= ?ffunE/= .
          rewrite /e_and/= int_of_boolK.
          move/int_of_bool_true => {while_cond} while_cond.
          (* end *)
          rewrite n_N N_2exp in while_cond.
          rewrite old_s/= in while_cond.
          apply (@ltn_pexp2l 2%nat l log2_N) in while_cond => {N_2exp} // .
          move: (asgn_to_new_a [tuple j%:Z]) => {asgn_to_new_a} asgn_to_new_a.
          move: (svalP N) => /= => N_gt_0.
          rewrite in_set ?ffunE in asgn_to_new_s.
          simplify_mask.
          assert (mask_of_all : mask_of N [ffun=> 1] = [set : (T N)]).
          { apply setP => i1.
            rewrite ?in_set ?ffunE// . }
          rewrite mask_of_all setTI in sync_H.
          rewrite sync_H mask_of_all ?setTI in asgn_to_new_a.
          rewrite Heq_e12 /s_es/const/= old_s/= in asgn_to_new_a.
          move=> {Heq_e12} {e12} {e} {e0} {while_cond} {log2_N}.
          assert ((2^l.+1 %| j + 1)%nat -> (j + 1)%/ 2 ^ l.+1 - 1 < j)%nat.
          { clear.
            move=> two_exp2l'_mod_index.
            rewrite -(ltn_add2r 1).
            rewrite subnK ?divn_gt0 ?expn_gt0 ?addn_gt0// .
            apply ltn_Pdiv.
            rewrite -{1}(expn0 2) ltn_exp2l ?addn_gt0// .
            rewrite addn1 ltn0Sn// .
            apply dvdn_leq; rewrite //= ?addn1 ?ltn0Sn// . }
          case:ifP => index_mod.
          { (* SCase: if condition of loopinv is satisfied *)
            (* i.e., the case where the assignment to 'a' is performed *)
            certify_asgn_performed_by asgn_to_new_a (Ordinal (ltn_trans (H index_mod) j_lt_N)) sync_H.
            { rewrite ?ffunE/= in asgn_to_new_a.
              rewrite ?muln_gt0 ?expn_gt0 ?addn_gt0 ?orbT/= in asgn_to_new_a.
              (* required to prove that ~Q(f^{-1}(j)) *)
              move: (if_cond (Ordinal (ltn_trans (H index_mod) j_lt_N))).
              rewrite /= old_s ?ffunE/=/const divz_nat -expnS/= .
              rewrite -(ltn_add2r 1).
              rewrite subnK /= .
              rewrite [(n %/ 2 ^l.+1 + 1)%nat]addn1 ltnS.
              rewrite leq_div2r.
              move=> z0_true.
              rewrite -z0_true ?int_of_bool_true/= in asgn_to_new_a.
              rewrite negbF// in asgn_to_new_a.
              apply (introT eqP), val_inj => /= .
              rewrite -{4}[2%nat]muln1 -mulnDr.
              rewrite subnK.
              rewrite [(2 ^ l * (2 * _))%nat]mulnA [(_ * 2)%nat]mulnC -expnS.
              rewrite (muln_divA _ index_mod).
              rewrite mulKn ?expn_gt0// ?addnK// .
              rewrite divn_gt0 dvdn_leq ?addn_gt0 ?orbT ?expn_gt0// .
              rewrite addn1 n_N j_lt_N// .
              rewrite divn_gt0 dvdn_leq ?addn_gt0 ?orbT ?expn_gt0// . }
            { eliminate_existsP.
              (* get previous a[2 ^ l * (2 * i1 + 1) -1] *)
              move: (old_a ((2 ^ l * (2 * i1 + 1)) - 1)%nat).
              rewrite ?ffunE/= in asgn_to_new_a0.
              move: (if_cond i1).
              rewrite /= ?ffunE/= old_s/const/= divz_nat => z0_eq.
              move:{+}asgn_to_new_a => asgn_to_new_a2.
              rewrite ?in_set-z0_eq int_of_boolK in asgn_to_new_a.
              rename asgn_to_new_a into i1_lt_n_div_2s.
              rewrite leq_divRL -?expnS ?expn_gt0 ?addn_gt0 ?orTb // in i1_lt_n_div_2s.
              rewrite expnS in i1_lt_n_div_2s.
              rewrite -addn1 subnK ?muln_gt0 1?expn_gt0 1?addn_gt0 1?ltn0Sn 2?orbT 2?orTb // .
              rewrite -{1}[(2 ^ l * (2 * i1 + 1))%nat](addnK (2 ^ l )).
              rewrite subn1 addnC -subn1.
              rewrite -{1}[(2 ^ l)%nat]muln1.
              rewrite -mulnDr addnC.
              rewrite -[(2 * i1 + 1 + 1)%nat]addnA addnn -muln2 [(1 * 2)%nat]mulnC.
              rewrite -mulnDr addn1 mulnA [(2 ^ l * 2)%nat]mulnC.
              rewrite [(_ * i1.+1)%nat]mulnC -n_N.
              move: (leq_trans (leq_subr (2 ^ l)%nat _) i1_lt_n_div_2s).
              move=> {i1_lt_n_div_2s} i1_lt_n_div_2s prev_sum_i1.
              move: (prev_sum_i1 i1_lt_n_div_2s) =>
              {prev_sum_i1} {i1_lt_n_div_2s} prev_sum_i1.
              rewrite dvdn_mulr// in prev_sum_i1.
              (* end *)
              (* get previous a[2 ^ l * (2 * i1 + 2) -1] *)
              move: (old_a ((2 ^ l * (2 * i1 + 2)) - 1)%nat).
              rewrite /= in asgn_to_new_a0.
              rename asgn_to_new_a2 into asgn_to_new_a.
              move: (if_cond i1).
              rewrite /= ?ffunE/= old_s/const/= divz_nat => z0_eq'.
              rewrite ?in_set-z0_eq int_of_boolK in asgn_to_new_a.
              rename asgn_to_new_a into i1_lt_n_div_2s.
              rewrite leq_divRL -?expnS ?expn_gt0 ?addn_gt0 ?orTb // in i1_lt_n_div_2s.
              rewrite expnS in i1_lt_n_div_2s.
              rewrite -addn1 subnK ?muln_gt0 ?expn_gt0 ?addn_gt0 ?ltn0Sn ?orbT ?orTb // .
              rewrite -{3}[2%nat]muln1 -{1}mulnDr addn1.
              rewrite mulnA {1}mulnC {1}[(_ * 2)%nat]mulnC -n_N.
              move=> prev_sum_i1'.
              move: (prev_sum_i1' i1_lt_n_div_2s) =>
              {prev_sum_i1'} {i1_lt_n_div_2s} prev_sum_i1'.
              rewrite dvdn_mulr// in prev_sum_i1'.
              (* end *)
              rewrite asgn_to_new_a0 Heq_e11/= old_s/const ?ffunE/= .
              rewrite ?muln_gt0 ?expn_gt0 ?addn_gt0 ?ltn0Sn ?orbT ?orTb//= .
              rewrite prev_sum_i1 prev_sum_i1'.
              rewrite /s_es/= /const ?ffunE/= in asgn_to_new_a'.
              rewrite ?muln_gt0 ?expn_gt0 ?addn_gt0 ?ltn0Sn ?orbT ?orTb/= in asgn_to_new_a'.
              apply (elimT eqP) in asgn_to_new_a'.
              inversion asgn_to_new_a'.
              rewrite -{4}[2%nat]muln1 -mulnDr mulnA [(2 ^ l * 2)%nat]mulnC -expnS.
              assert (forall i,
                         (0 <= i < 2 ^ l)%nat && true ->
                         (fun x => a0 [tuple (2 ^ l * (2 * i1 + 1) - 1 - x)%:Z]) i =
                         (fun x => a0 [tuple (2 ^ l * (2 * i1 + 1) - 1 + 2 ^ l - (x + 2 ^ l))%:Z]) i).
              { clear.
                move => i.
                case/andP.
                case/andP => _ i_lt_2exp_l _.
                move: (leq_mul i_lt_2exp_l (leq_addl (2 * i1) 1)).
                rewrite muln1 ?addn1 => i_lt_2exp_l_mul.
                rewrite 2?subzn ?leq_add2r -{1}[i](addnK 1);
                  try apply leq_sub2r; rewrite ?addn1// .
                rewrite subnDA [(_ - i - 2 ^ l)%nat]subnAC addnK//= .
              }
              rewrite 2![\sum_(0 <= m < 2 ^ l | true) _]big_nat_cond.
              rewrite (@eq_bigr _ _ _ nat (index_iota 0 (2 ^ l)) _ _ _ H0) => {H0}.
              rewrite -2!big_nat_cond.
              suff : (2 ^ l.+1 - 2 ^ l = 2 ^ l)%nat.
              move => exp2l.
              rewrite -{2}exp2l => {exp2l}.
              rewrite -(@big_addn _ _ _ _ (2^l.+1)%nat (2^l)%nat (fun _ => true) (fun x => a0 [tuple (2 ^ l * (2 * i1 + 1) - 1 + 2 ^ l - x)%:Z])).
              rewrite add0n.
              assert (forall i,
                         true ->
                         (fun x => a0 [tuple (2 ^ l * (2 * i1 + 1) - 1 + 2 ^ l - x)%:Z]) i =
                         (fun x => a0 [tuple (2 ^ l.+1 * (i1 + 1) - 1 - x)%:Z]) i
                     ).
              { clear.
                move => i _.
                rewrite subn1 [(_ + 2 ^ l)%nat]addnC -subn1.
                rewrite addnBA ?muln_gt0 ?expn_gt0 ?addn_gt0 ?ltn0Sn ?orbT ?orTb // .
                rewrite mulnC -mulSn addn1 -addn2 expnS.
                rewrite [(2 * 2 ^ l)%nat]mulnC -mulnA mulnDr muln1 mulnC// .
              }
              rewrite (eq_bigr _ H0) => {H0}.
              remember (index_iota 0 (2^l)%nat) as lst.
              remember (index_iota (2^l)%nat (2^l.+1)%nat) as lst'.
              rewrite -[intZmod.addz _ _](@big_cat _ _ (GRing.add_monoid int_ZmodType) nat lst lst').
              rewrite Heqlst Heqlst'/index_iota/= 2!subn0 -{2}[(2^l)%nat]add0n.
              rewrite -iota_add.
              rewrite addnBA 1?addnC ?addnK// .
              apply leq_pexp2l => // .
              rewrite expnS -{2}[(2^l)%nat]mul1n.
              rewrite -[(2 * 2 ^ l - 1 * 2 ^ l)%nat]mulnBl.
              suff: (2 - 1 = 1)%nat => // .
              move=> two_1_1.
              rewrite two_1_1 mul1n// . }
          }
          { (* SCase: if condition of loopinv (P(j)) is NOT satisfied *)
            (* i.e., the case where the assignment to 'a' is NOT performed *)
            asgn_not_occur_due_to asgn_to_new_a if_cond; last first.
            { eliminate_existsP.
              (* Lead contradiction using ~P(f(tid)) and Q(tid) *)
              apply (elimT eqP) in asgn_to_new_a'.
              rewrite /s_es ?ffunE/= ?muln_gt0 ?expn_gt0 ?addn_gt0 ?ltn0Sn ?orbT /= in asgn_to_new_a'.
              inversion asgn_to_new_a' => {asgn_to_new_a'}.
              subst.
              rename i0 into j.
              rewrite subnK ?muln_gt0 ?expn_gt0 ?addn_gt0 ?ltn0Sn ?orbT // in index_mod.
              rewrite -{4}[2%nat]muln1 -mulnDr mulnA [(_ * 2)%nat]mulnC in index_mod.
              rewrite -expnS in index_mod.
              rewrite -{1}[(2^l.+1)%nat]muln1 dvdn_pmul2l ?expn_gt0// in index_mod.
              rewrite dvd1n// in index_mod. }
            { (* ~P(j) and ~Q(f^{-1}(j)) that is no execution of assignments *)
              case: (boolP (2 ^ l %| j + 1)%nat) => index_mod'.
              { move: (old_a _ j_lt_N).
                rewrite /=?ffunE index_mod' asgn_to_new_a'/= => {old_a} old_a.
                exists l.
                repeat split => // .
                rewrite (negbT index_mod)// . }
              { rewrite asgn_to_new_a'.
                move: (old_a _ j_lt_N).
                rewrite (negbTE index_mod')/= ?ffunE/= => {old_a} old_a.
                destruct old_a as [l' [l'_lt_l old_a]].
                exists l'.
                split => // .
                rewrite (ltn_trans l'_lt_l (ltnSn _))// . }}}}}}
    { move=> {Heq_e11} {Heq_e12} {Heq_e21} {Heq_e22} {e11} {e12} {e21} {e22}.
      cbv beta.
      case => l_map s_map loopinv.
      case => // => new_temp asgn_to_new_temp.
      case => // => new_a_n_1 asgn_to_new_a_n_1 i.
      destruct loopinv as [loopinv postcond_while].
      rewrite /assign/sassign in asgn_to_new_a_n_1.
      rewrite /s_es n_N/= (*(svalP N)/=*) in asgn_to_new_a_n_1.
      rewrite /const in asgn_to_new_a_n_1.
      simplify_update_state.
      (* after the while, while cond is not satisfied *)
      rewrite /none/const/= in postcond_while.
      move: (loopinv i) => /= => {loopinv} loopinv.
      destruct loopinv as [l [s_eq_2expl [two_expl_leq_n loopinv]]].
      move: (postcond_while i).
      rewrite ?ffunE int_of_boolK/const int_of_bool_false/= .
      rewrite ?ffunE in s_eq_2expl.
      rewrite s_eq_2expl/= ltnNge negbK => while_cond.
      (* end *)
      case N_2exp=> {N_2exp} log2_N N_2exp.
      split.
      { move: (asgn_to_new_temp [tuple])=> {asgn_to_new_temp} asgn_to_new_temp.
        asgn_to_scalar_never_fail asgn_to_new_temp i;
          try rewrite ffunE// in asgn_to_new_temp.
        rewrite /= ?ffunE/= in asgn_to_new_temp0.
        rewrite asgn_to_new_temp0/= n_N (svalP N)/= subn1.
        move: (loopinv ((sval N).-1)%nat).
        rewrite prednK ?(svalP N)// leqnn.
        rewrite -subn1 subnK ?(svalP N)// .
        assert (n == 2 ^ l)%nat by rewrite eqn_leq while_cond two_expl_leq_n// .
        rewrite -n_N (elimT eqP H) dvdnn ?ffunE/= => old_a.
        rewrite (old_a is_true_true).
        assert (F_eq : forall i,
                   (0 <= i < 2 ^ l)%nat && true ->
                   (fun x => a0 [tuple (2 ^ l - 1 - x)%:Z]) i =
                   (fun x => a0 [tuple (0 + 2 ^ l - x.+1)%:Z]) i).
        { clear.
          move=> i P.
          rewrite add0n -[i.+1%nat]add1n subnDA// . }
        rewrite [RHS]big_nat_rev.
        rewrite {1}big_nat_cond.
        rewrite (@eq_bigr _ _ _ nat (index_iota 0 (2 ^ l)) _ _ _ F_eq) => {F_eq}.
        rewrite -big_nat_cond// . }
      { move: (svalP N) => /= => N_gt_0.
        exists 0%nat.
        rewrite expn0 div.divn1 {2}[n]n_N {1}N_2exp expn_gt0 orTb.
        repeat split => // .
        { apply (elimT eqP).
          rewrite eqz_nat eqn_leq while_cond two_expl_leq_n// . }
        { move => j j_lt_N.
          rewrite eq_refl/= .
          move: (conj two_expl_leq_n while_cond).
          move/andP.
          rewrite -eqn_leq/= => two_expl_eq_n.
          apply (elimT eqnP) in two_expl_eq_n.
          rewrite /= two_expl_eq_n in loopinv.
          rewrite /= in asgn_to_new_a_n_1.
          move: (asgn_to_new_temp [tuple]) => {asgn_to_new_temp} asgn_to_new_temp.
          asgn_to_scalar_never_fail asgn_to_new_temp i;
            try rewrite ffunE// in asgn_to_new_temp.
          rewrite /= ?ffunE/= n_N/= N_gt_0 in asgn_to_new_temp0.
          move=> {asgn_to_new_temp} {asgn_to_new_temp'}.
          case:ifP => index_mod; last first.
          { move: (loopinv j j_lt_N).
            rewrite index_mod.
            case => l' {loopinv} loopinv.
            case (asgn_to_new_a_n_1 [tuple j%:Z]) => {asgn_to_new_a_n_1} asgn_to_new_a_n_1.
            { case asgn_to_new_a_n_1 => {asgn_to_new_a_n_1} _ asgn_to_new_a_n_1.
              rewrite ?ffunE/= asgn_to_new_a_n_1.
              rewrite ?ffunE/= in loopinv.
              exists l'%nat.
              rewrite -two_expl_eq_n ltn_exp2l// . }
            { eliminate_existsP.
              apply (elimT eqP) in asgn_to_new_a_n_1'.
              rewrite ?ffunE/= ?N_gt_0/= in asgn_to_new_a_n_1'.
              inversion asgn_to_new_a_n_1'.
              rewrite -H0 in index_mod.
              rewrite (subnK N_gt_0) -n_N dvdnn// in index_mod. }}
          { case: (leqP j (n - 1)%nat) => j_cmp_n_1; last first.
            { rewrite n_N -(ltn_add2r 1) subnK ?N_gt_0// in j_cmp_n_1.
              rewrite addn1 ltnS leqNgt j_lt_N// in j_cmp_n_1. }
            { rewrite leq_eqVlt in j_cmp_n_1.
              move:j_cmp_n_1.
              case/orP => j_cmp_n_1.
              { apply (elimT eqP) in j_cmp_n_1.
                rewrite ?ffunE/= j_cmp_n_1 subnK n_N ?N_gt_0// .
                rewrite -n_N -j_cmp_n_1 subnn/= .
                rewrite big_nil.
                case: (asgn_to_new_a_n_1 [tuple j%:Z])=> {asgn_to_new_a_n_1} asgn_to_new_a_n_1.
                { case: asgn_to_new_a_n_1=> index_chk _.
                  eliminate_forallP index_chk.
                  move: (index_chk i).
                  rewrite in_set ?ffunE/= N_gt_0 -n_N -j_cmp_n_1 negbF// .
                  apply (introT eqP), val_inj=> // . }
                { eliminate_existsP.
                  rewrite ?ffunE// in asgn_to_new_a_n_0. }}
              { rewrite ltn_subRL addnC in j_cmp_n_1.
                rewrite addn1 in index_mod.
                apply (dvdn_leq (ltn0Sn j)) in index_mod.
                rewrite -addn1 leqNgt j_cmp_n_1// in index_mod. }}}}}}
    { case=> l_map s_map a_init.
      case => // => s' s_1 i.
      move: (s_1 [tuple]) => {s_1} {Heq_e11} {Heq_e12} {Heq_e21} {Heq_e22} s_1.
      asgn_to_scalar_never_fail s_1 i; try rewrite ffunE// in s_1.
      simplify_update_state.
      rewrite in_set ffunE/= in s_1.
      rewrite /= ?ffunE/= in asgn_to_s'.
      exists 0%nat.
      repeat split => // .
      { case N_2exp => log2_N {N_2exp} N_2exp.
        rewrite expn0 n_N N_2exp expn_gt0 orTb// . }
      { move=> j j_lt_N.
        case: ifP => index_mod.
        { rewrite expn0 in index_mod|-*.
          rewrite ?big_cons big_nil/= [_ + 0]intZmod.addzC intZmod.add0z subn0.
          rewrite /= in a_init.
          rewrite (a_init j i)// . }
        { rewrite expn0 dvd1n//  in index_mod. }}}
  Qed.
End Blelloch.
