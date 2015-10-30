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
Notation "a '+E' b" := (@funcT 2 e_plus [tuple a; b]) (at level 60).
Notation "a '-E' b" := (@funcT 2 e_minus [tuple a; b]) (at level 60).
Notation "a '*E' b" := (@funcT 2 e_mult [tuple a; b]) (at level 60).
Notation "a '/E' b" := (@funcT 2 e_div [tuple a; b]) (at level 60).
Notation "a '&&' b" := (@funcT 2 e_and [tuple a; b]).
Notation "a '<E' b" := (@funcT 2 e_lt [tuple a; b]) (at level 90).
Notation "a '<=E' b" := (@funcT 2 e_leq [tuple a; b]) (at level 90).
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
                try (rewrite in_set/bool_of_int (H' i) //);
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
                    rewrite in_set (eqP (H' i')) // in H))
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
                rewrite in_set (eqP (H' i')) // in H))
    | _ => let msg := (type of H) in
           fail 1 "This tactic cannot be applied terms of type: "msg
  end.

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

Module Kogge_Stone.
  Definition s : SV 0%nat := shared _ 0%nat.

  (* The array length is N *)
  Lemma implements_prefixsum :
    forall (n : nat) (N : { n : nat | 0%nat < n}) (a : SV 1%nat) (a0 : 1.-tuple int -> int),
      (exists l : nat, sval N = expn 2 l) ->
      n = (sval N)%nat ->
      Hoare_proof N
                  (fun s : state _ =>
                     forall e i,
                       s[[varT a [tuple c e]]](i) = a0 [tuple e])
                  (fun _ => 1%:Z)
                  (s ::= c 1%nat
                     ;;
                     (WHILE (`s <E c n) DO
                            (IFB (`s <=E tid) THEN
                                 (a @ [tuple tid] :::= varT a[tuple tid] +E varT a[tuple tid -E `s])
                                 ELSE skip
                                 ;;
                                 s ::= (`s *E c 2%nat)
                                 ;;
                                 sync
                            )
                     )
                  )
                  (fun s : state _ =>
                     forall (i : T N) (j : nat),
                       j < sval N ->
                       s[[varT a [tuple c j%nat]]](i) =
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
              (forall i, st[[varT a [tuple c j]]](i) = (\sum_(j-2^l+1 <= k < j+1) (a0 [tuple k%:Z]))))) /\
           (forall j,
              ((j < 2 ^ l)%nat ->
               (forall i, st[[varT a [tuple c j]]](i) = (\sum_(0 <= k < j+1) (a0 [tuple k%:Z])))))
      ) as loopinv.
    apply_hoare_rules_with loopinv.
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
          rewrite intOrdered.ltz_def-(old_s th0)eq_refl/negb// . }
        { move => n_gt_2expl.
          exists (l.+1)%nat.
          repeat split => // .
          { move => i.
            asgn_to_scalar_never_fail asgn_to_new_s (Ordinal (svalP N)).
            rewrite /= in old_s.
            rewrite asgn_to_new_s0 (old_s i) ?exprzn/= -expnSr// . }
          { rewrite N_2exp in n_gt_2expl|-*.
            apply ltn_pexp2l in n_gt_2expl => // .
            apply leq_pexp2l => // . }
          { move => j j_gt_subn_2_expl1 j_lt_n i.
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
            { move: (old_a j (ltn_trans H0 j_gt_subn_2_expl1) j_lt_n i) => {old_a} old_a.
              move: (old_s (Ordinal j_lt_n)) (if_cond (Ordinal j_lt_n)).
              rewrite /= => old_s_eq_2expl.
              rewrite old_s_eq_2expl ?exprzn/intOrdered.lez/= .
              rewrite -(leq_add2r 1) ?subn1 ?addn1 in H0.
              rewrite subn1 -(ltn_add2r 1) ?addn1 in j_gt_subn_2_expl1.
              rewrite ?prednK in H0,j_gt_subn_2_expl1; try by rewrite expn_gt0.
              rewrite -ltnS (ltn_trans H0 j_gt_subn_2_expl1)/int_of_bool => z0_true.
              rewrite ?in_set -z0_true/= negbF// in asgn_to_new_a.
                by apply (introT eqP), val_inj. }
            { eliminate_existsP.
              move: (old_a j (ltn_trans H0 j_gt_subn_2_expl1) j_lt_n i0) => /= => old_a0.
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
          { move => j j_lt_2expl1 i.
            rewrite eq_refl.
            move: (asgn_to_new_a [tuple j%:Z]) => {asgn_to_new_a} asgn_to_new_a.
            simplify_mask.
            rewrite N_2exp ltn_exp2l// -(@leq_exp2l 2)// -N_2exp in n_gt_2expl.
            move: (leq_trans j_lt_2expl1 n_gt_2expl) => j_lt_N.
            case: (ltnP j (2 ^ l)) => j_cmp_2expl.
            { asgn_not_occur_due_to asgn_to_new_a if_cond; last first.
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
            { certify_asgn_performed_by asgn_to_new_a (Ordinal j_lt_N) H.
              { move: (old_s (Ordinal j_lt_N)) (if_cond (Ordinal j_lt_N)) (while_cond (Ordinal j_lt_N)).
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
