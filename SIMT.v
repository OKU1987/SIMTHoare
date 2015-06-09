Require Import SIMT_util.
Require Import Vectors.VectorDef.
Require Import ZArith.
Import VectorNotations.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Eqdep_dec.
Require Import EqdepFacts.

Section SIMT_Definition.
  Variable num_threads : { n : nat & (n > 0)%nat}. (* the number of threads *)
  Definition N := projT1 num_threads.

  Definition arity := nat.
  Definition variable_name := nat.

  Inductive LV (n:arity) : Set :=
  | local : variable_name -> LV n.

  Inductive SV (n:arity) : Set :=
  | shared : variable_name -> SV n.

  Definition V n := (LV n + SV n)%type.

  Lemma eq_lv_dec : forall n (lv lv' : LV n), {lv = lv'} + {lv <> lv'}.
    destruct n; destruct lv; destruct lv';
    destruct (eq_nat_dec v v0) as [H | H];
    try (subst; left; reflexivity);
    try (right; contradict H; inversion H; reflexivity).
  Qed.

  Lemma eq_sv_dec : forall n (sv sv' : SV n), {sv = sv'} + {sv <> sv'}.
    destruct n; destruct sv; destruct sv';
    destruct (eq_nat_dec v v0) as [H | H];
    try (subst; left; reflexivity);
    try (right; contradict H; inversion H; reflexivity).
  Qed.

  Definition Op n := t Z n -> Z.

  Definition const (z:Z) : Op 0 := fun _ : t Z 0 => z.
  Definition e_plus : Op 2 :=
    fun zs : t Z 2 => match zs return Z with
                        | [x; y] => (x + y)%Z
                        | _ => 0%Z
                      end.
  Definition e_neg : Op 1 :=
    fun z : t Z 1 => match z return Z with
                       | [0%Z] => 1%Z
                       | _ => 0%Z
                     end.
  Definition e_and : Op 2 :=
    fun zs : t Z 2 => match zs return Z with
                        | [0%Z; y] => 0%Z
                        | [x; 0%Z] => 0%Z
                        | [x; y] => (Z.abs x + Z.abs y)%Z
                        | _ => 0%Z
                      end.
  Definition e_lt : Op 2 :=
    fun zs : t Z 2 => match zs return Z with
                        | [x; y] => match (x ?= y)%Z with
                                      | Lt => 1%Z
                                      | _ => 0%Z
                                    end
                        | _ => 0%Z
                      end.

  Inductive E : Set :=
  | tid : E
  | ntid : E
  | var : forall n, V n -> t E n -> E
  | func : forall n, Op n -> t E n -> E.
  Implicit Arguments var [n].
  Implicit Arguments func [n].

  Notation "a '+' b" := (@func 2 e_plus [a; b]).
  Notation "a '&&' b" := (@func 2 e_and [a; b]).
  Notation "a '<' b" := (@func 2 e_lt [a; b]).
  Notation "'!' a" := (@func 1 e_neg [a]) (at level 35, right associativity).
  Notation "'c' z" := (@func 0 (const z) []) (at level 20).

  Inductive program : Set :=
  | asgn : forall n, V n -> t E n -> E -> program
  | skip : program
  | sync : program
  | seq : program -> program -> program
  | P_if : E -> program -> program -> program
  | P_while : E -> program -> program.
  Implicit Arguments asgn [n].

  Notation "x '::=' e" := (asgn x [] e) (at level 110, right associativity).
  Notation "x '$'" := (@var _ x []) (at level 30).
  Notation "P ;; Q" := (seq P Q) (at level 150).
  Notation "'IFB' e 'THEN' P 'ELSE' Q" := (P_if e P Q) (at level 135).
  Notation "'WHILE' e 'DO' P" := (P_while e P) (at level 140).
  
  Definition T := { n : nat & (n < N)%nat}.

  Definition T_S : forall n,
                   {n0 : nat & (n0 < n)%nat} ->
                   {n0 : nat & (n0 < S n)%nat}.
    intros. destruct H. exists x. abstract omega.
  Defined.

  Lemma T_dec : forall (P : T -> Prop),
                  (forall i, P i \/ ~ P i) ->
                  (forall i, ~ P i) \/ (exists i, P i).
    unfold T.
    induction N; intros.
    - left. intros. inversion i.
      induction x; inversion H0.
    - set (P' (u : {n0 : nat & (n0 < n)%nat}) := P (T_S _ u)).
      destruct (IHn P').
      + firstorder.
      + unfold P' in *.
        assert ((n < S n)%nat) by omega.
        destruct (H (exist _ n H1)).
        * right. eexists. eassumption.
        * left. intros.
          destruct i.
          inversion l; subst.
          { rewrite <- (proof_irrelevance _ H1 l). assumption. }
          { apply le_S_gt in H4.
            assert (exists i : {n0 : nat & (n0 < n)%nat},
                      T_S _ i = existT (fun n0 : nat => (n0 < S n)%nat) x l).
            exists (existT _ x H4).
            simpl.
            apply f_equal.
            apply proof_irrelevance.
            destruct H3.
            rewrite <- H3.
            apply H0.
          }
      + destruct H0.
        right. exists (T_S _ x). assumption.
  Qed.

  Definition L_map n := T -> t Z n -> Z.
  Definition S_map n := t Z n -> Z.
  Definition state := ((forall n, LV n -> L_map n) * (forall n, SV n -> S_map n))%type.

  Reserved Notation "s '[[' e ']](' i ')'" (at level 50).

  Fixpoint E_under_state (s:state) e : T -> Z :=
    match e with
      | tid => fun t => match t with existT i _ => Z.of_nat i end
      | ntid => fun _ => Z.of_nat N
      | var n (inl lv) es =>
        fun i => fst s n lv i (map (fun e => s[[e]](i)) es)
      | var n (inr sv) es =>
        fun i => snd s n sv (map (fun e => s[[e]](i)) es)
      | func n f es =>
        fun i => f (map (fun e => s[[e]](i)) es)
    end
      where "s '[[' e ']](' i ')'" := (E_under_state s e i).

  Definition Zeq_list_bool n (zs zs' : t Z n) :=
    fold_left (fun b b' => andb b b') true
              (map2 (fun z z' => Zeq_bool z z') zs zs').

  Definition update n (f : t Z n -> Z) (zs : t Z n) (z : Z) :=
    fun zs' : t Z n => if Zeq_list_bool n zs zs' then z else f zs'.

  Definition update_state (s : state) n (x : V n) (x' : (T -> t Z n -> Z) + (t Z n -> Z)) : state.
    refine (
        match x, x' with
          | inl lv, inl lv' =>
            ((fun n0 (lv0 : LV n0) =>
                match eq_nat_dec n n0 return L_map n0 with
                  | left e => _
                  | right _ => fst s n0 lv0
                end), snd s)
          | inr sv, inr sv' =>
            (fst s,
             fun n0 (sv0 : SV n0) =>
               match eq_nat_dec n n0 return S_map n0 with
                 | left e => _
                 | right _ => snd s n0 sv0
               end)
          | _, _ => s
        end
      ).
    - clear x x'. subst.
      refine (if eq_lv_dec _ lv lv0 then fun i => fun zs => lv' i zs else fst s _ lv0).
    - clear x x'. subst.
      refine (if eq_sv_dec _ sv sv0 then sv' else snd s _ sv0).
  Defined.

  Transparent update_state.

  Definition mask := T -> bool.
  Definition empty : mask := fun _ => false.
  Definition T_mask : mask := fun _ => true.

  Definition meet (mu mu' : mask) : mask := fun i => andb (mu i) (mu' i).
  Definition diff (mu mu' : mask) : mask := fun i => andb (mu i) (negb (mu' i)).

  Definition sub (mu mu' : mask) : Prop :=
    forall i : T, mu i = true -> mu' i = true.

  Lemma fold_meet : forall mu mu', (fun i => (mu i && mu' i))%bool = meet mu mu'.
  Proof.
    reflexivity.
  Qed.

  Lemma meet_empty_l : forall m, meet empty m = empty.
  Proof.
    intros; unfold meet, empty; apply functional_extensionality;
    intro;
    destruct (m x); try reflexivity.
  Qed.

  Lemma meet_empty_r : forall m, meet m empty = empty.
  Proof.
    intros; unfold meet, empty; apply functional_extensionality;
    intro;
    destruct (m x); try reflexivity.
  Qed.

  Lemma meet_comm : forall m m', meet m m' = meet m' m.
  Proof.
    intros; unfold meet, empty; apply functional_extensionality;
    intro;
    destruct (m x); destruct (m' x); try reflexivity.
  Qed.

  Lemma meet_assoc : forall m m' m'', meet (meet m m') m'' =
                                      meet m (meet m' m'').
  Proof.
    intros; unfold meet, empty; apply functional_extensionality;
    intro;
    destruct (m x); destruct (m' x); destruct (m'' x); try reflexivity.
  Qed.

  Lemma meet_double : forall m, meet m m = m.
  Proof.
    intros; unfold meet, empty; apply functional_extensionality;
    intro;
    destruct (m x); try reflexivity.
  Qed.

  Lemma sub_meet : forall m m', sub m m' -> meet m m' = m.
  Proof.
    intros.
    apply functional_extensionality; intro i.
    unfold sub in H.
    generalize (H i); clear H; intro.
    unfold meet.
    destruct (m i); destruct (m' i); try reflexivity.
    generalize (H (refl_equal _)); intro H'; inversion H'.
  Qed.

  Definition s_es n s := fun (es : t E n) i => map (fun e => s[[e]](i)) es.
  Notation "s '[[[' es ']]](' i ')'" := (s_es _ s es i) (at level 50).

  Inductive eval : program -> mask -> state -> state -> Prop :=
  | E_Inactive : forall P s, eval P empty s s
  | E_Skip : forall mu s, eval skip mu s s
  | E_Sync : forall s, eval sync T_mask s s
  | E_LAssign : forall n (x : LV n) es e mu (s s' : state),
                  snd s' = snd s ->
                  (forall n',
                     if eq_nat_dec n n' then
                       forall y : LV n,
                         if eq_lv_dec _ x y then
                           (forall i, mu i = false -> fst s' n x i = fst s n x i) /\
                           (forall i, mu i = true ->
                                      fst s' n x i =
                                      update n (fst s n x i) (s[[[es]]](i)) (s[[e]](i))
                           )
                         else fst s' n y = fst s n y
                     else (forall y : LV n', fst s' n' y = fst s n' y)) ->
                  eval (asgn (inl x) es e) mu s s'
  | E_SAssign : forall n (x : SV n) es e mu (s s' : state),
                  fst s' = fst s ->
                  (forall n',
                     if eq_nat_dec n n' then
                       forall y : SV n,
                         if eq_sv_dec _ x y then
                           (forall ns,
                              ((forall i, mu i = true ->
                                          Zeq_list_bool _ (s[[[es]]](i)) ns = false) ->
                               snd s' n x ns = snd s n x ns) /\
                              ((exists i, mu i = true /\
                                          Zeq_list_bool _ (s[[[es]]](i)) ns = true) ->
                               (exists j, mu j = true /\
                                          Zeq_list_bool _ (s[[[es]]](j)) ns = true /\
                                          snd s' n x ns = (s[[e]](j))))
                           )
                         else snd s' n y = snd s n y
                     else (forall y : SV n', snd s' _ y = snd s _ y)) ->
                  eval (asgn (inr x) es e) mu s s'
  | E_Seq : forall P Q mu s s' s'', eval P mu s s' ->
                                    eval Q mu s' s'' ->
                                    eval (seq P Q) mu s s''
  | E_If : forall P Q mu s e s_e s' s'',
             s_e = (fun i => negb (Zeq_bool (s[[e]](i)) 0)) ->
             eval P (meet mu s_e) s s' ->
             eval Q (diff mu s_e) s' s'' ->
             eval (IFB e THEN P ELSE Q) mu s s''
  | E_While : forall P mu s e mu' s' s'',
                mu' = meet mu (fun i => negb (Zeq_bool (s[[e]](i)) 0)) ->
                eval P mu' s s' ->
                eval (WHILE e DO P) mu' s' s'' ->
                eval (WHILE e DO P) mu s s''.

  Definition assertion := state -> Prop.

  Definition mask_of (m : T -> Z) i : bool := negb (Zeq_bool (m i) 0%Z).

  Lemma fold_mask_of : forall m, (fun i => negb (Zeq_bool (m i) 0%Z)) = mask_of m.
    reflexivity.
  Qed.

  Lemma meet_equiv :
    forall m z,
      meet (mask_of m) (mask_of z) = mask_of (fun i => e_and [m i; z i]).
  Proof.
    intros m z; apply functional_extensionality; intro i;
    unfold meet, mask_of; unfold negb;
    destruct (m i); simpl; destruct (z i); try reflexivity.
  Qed.

  Lemma diff_equiv :
    forall m z,
      diff (mask_of m) (mask_of z) = mask_of (fun i => e_and [m i; e_neg [z i]]).
  Proof.
    intros m z; apply functional_extensionality; intro i;
    unfold diff, mask_of; unfold negb.
    destruct (m i); simpl; destruct (z i); try reflexivity.
  Qed.

  Lemma lt_0_N : lt 0 N.
    unfold N.
    destruct num_threads.
    simpl.
    assumption.
  Qed.

  Definition zero_T : T := existT _ 0 (lt_0_N).

  Ltac simplify_mask' :=
    match goal with
      | [ H : context[mask_of] |- _] => unfold mask_of in H
      | [ H : context[meet] |- _] => unfold meet in H
      | [ H : context[diff] |- _] => unfold diff in H
      | [ H : context[negb] |- _] => unfold negb in H
      | _ => fail
    end.

  Ltac simplify_mask := repeat simplify_mask'; simpl in *|-*.

  Ltac inactive_is_not_active :=
    simplify_mask; zero_lt_pos;
    match goal with
      | [ H' : context[empty = _] |- _] =>
        assert (devil : false = true) by apply (equal_f H' zero_T);
          inversion devil
      | _ => idtac
    end.
  Unset Ltac Debug.

  Definition hoare_quadruple (phi : assertion) m (P : program) (psi : assertion) : Prop :=
    forall s s' : state,
      phi s ->
      eval P (mask_of m) s s' ->
      psi s'.

  Definition all e := forall i : T, e i <> 0%Z.
  Definition none e := forall i : T, e i = 0%Z.
  Definition forall_in_mask (s : state) m (P : T -> Prop) :=
    forall i : T, m i <> 0%Z -> P i.
  Definition exists_in_mask (s : state) m (P : T -> Prop) :=
    exists i : T, m i <> 0%Z /\ P i.

  Definition lassign (s : state) n (x' : T -> t Z n -> Z) m (x : LV n) (es : t E n) (e : E) : Prop :=
    forall (ns : t Z n) (i : T),
      (m i = 0%Z \/ Zeq_list_bool _ (s[[[es]]](i)) ns = false ->
       (x' i ns = fst s n x i ns)) /\
      (m i <> 0%Z /\ Zeq_list_bool _ (s[[[es]]](i)) ns = true ->
       (x' i ns = s[[e]](i))).

  Definition sassign s n (x' : t Z n -> Z) m (x : SV n) (es : t E n) (e : E) : Prop :=
    (forall ns : t Z n,
       (forall_in_mask s m (fun i => Zeq_list_bool _ (s[[[es]]](i)) ns = false) /\
       x' ns = snd s n x ns) \/
       (exists_in_mask s m (fun i => Zeq_list_bool _ (s[[[es]]](i)) ns = true /\
                                    x' ns = s[[e]](i)))).

  Definition assign rho n x' m (x : V n) (es : t _ n) (e : _) :=
    match x, x' return Prop with
      | inl lv, inl lv' => lassign rho n lv' m lv es e
      | inr sv, inr sv' => sassign rho n sv' m sv es e
      | _, _ => False
    end.
  Implicit Arguments assign [n].

  Inductive Hoare_proof : assertion -> (T -> Z) -> program -> assertion -> Prop :=
  | H_Skip : forall phi m, Hoare_proof phi m skip phi
  | H_Sync : forall (phi : assertion) m,
               Hoare_proof (fun s => (all m \/ none m) -> phi s)
                           m sync phi
  | H_Conseq : forall (phi phi' psi psi' : assertion) m P,
                 (forall s, phi' s -> phi s) ->
                 Hoare_proof phi m P psi ->
                 (forall s, psi s -> psi' s) ->
                 Hoare_proof phi' m P psi'
  | H_Seq : forall phi m P psi Q chi,
              Hoare_proof phi m P psi ->
              Hoare_proof psi m Q chi ->
              Hoare_proof phi m (P ;; Q) chi
  | H_Assign : forall n (x : V n) (es : t E n) e m (phi : assertion),
                 Hoare_proof (fun s =>
                                forall x', assign s x' m x es e ->
                                           phi (update_state s n x x'))
                             m (asgn x es e) (fun s => phi s)
  | H_If : forall (phi : assertion) psi chi e (m : T -> Z) P Q,
             (forall z : T -> Z,
                Hoare_proof
                  (fun s =>
                     phi s /\
                     (forall i, s[[e]](i) = z i))
                  (fun i => e_and [m i; z i]) P (psi z)) ->
             (forall z, Hoare_proof (psi z) (fun i => e_and [m i; e_neg [z i]]) Q chi) ->
             Hoare_proof phi m (IFB e THEN P ELSE Q) chi
  | H_While : forall (phi : assertion) m e P,
                (forall z : T -> Z,
                   Hoare_proof (fun s => phi s /\ (forall i, s[[e]](i) = z i)) (fun i => e_and [m i; z i]) P phi) ->
                Hoare_proof phi m (WHILE e DO P) (fun s => phi s /\ none (fun i : T => e_and [m i; s[[e]](i)])).

  Lemma lem_1 : forall s s' n (x : V n) es e (m : T -> Z),
                   eval (asgn x es e) (mask_of m) s s' <->
                   exists a,
                       s' = update_state s _ x a /\
                       assign s a m x es e.
  Proof.
    split; intros.
    - (* => *)
      inversion H; subst; clear H.
      + destruct x as [lv | sv].
        * destruct s'.
          exists (inl (fun i => fun zs => l n lv i zs)).
          simpl.
          split.
          { functional_extensionality_dep_pair_r; intro n'.
            destruct (eq_nat_dec n n'); try reflexivity; subst.
            unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
            subst.
            simpl.
            rewrite <- functional_extensionality with (f:=l n');
              try reflexivity; intro lv'.
            destruct (eq_lv_dec _ lv lv'); try reflexivity.
            subst.
            reflexivity. }
          { unfold lassign. intros. split.
            - inactive_is_not_active.
              apply equal_f with (x:=i) in H2.
              destruct (m i); reflexivity.
            - intros. destruct H.
              apply equal_f with (x:=i) in H2.
              inactive_is_not_active.
              destruct (m i); try (inactive_is_not_active; contradict H2;
                                  discriminate);
              contradict H; reflexivity. }
        * destruct s'.
          exists (inr (fun zs => s n sv zs)).
          simpl.
          split.
          { functional_extensionality_dep_pair_r; intro n'.
            destruct (eq_nat_dec n n'); try reflexivity; subst.
            unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
            subst.
            simpl.
            rewrite <- functional_extensionality with (f:=s n');
              try reflexivity; intro sv'.
            destruct (eq_sv_dec _ sv sv'); try reflexivity.
            subst.
            reflexivity. }
          { unfold sassign. intros.
            inactive_is_not_active.
            unfold forall_in_mask. unfold exists_in_mask.
            left.
            split; intros.
            apply equal_f with (x:=i) in H2;
            destruct (m i); try (contradict H; reflexivity);
            try (contradict H2; discriminate). reflexivity. }
      + existT_eq.
        destruct s. destruct s' as [l' s'].
        simpl in H8.
        unfold update_state.
        unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
        simpl in H7. subst.
        simpl.
        eexists (inl _).
        split.
        * functional_extensionality_dep_pair_r; try reflexivity.
          intro n'.
          generalize (H8 n'); intro H8'; clear H8.
          destruct (eq_nat_dec n n'); subst; try reflexivity.
          rewrite <- functional_extensionality with (f:=l' n');
            try reflexivity.
          subst. intro lv'.
          simpl.
          generalize (H8' lv'); intro H8; clear H8'.
          destruct (eq_lv_dec _ x1 lv'); subst; try reflexivity; assumption.
          apply functional_extensionality. intros. apply H8'.
        * unfold lassign.
          intros.
          generalize (H8 n); intro H8'; clear H8.
          destruct (eq_nat_dec n n) as [H|H]; [|contradict H; reflexivity].
          generalize (H8' x1); intro H8; clear H8'.
          destruct (eq_lv_dec _ x1 x1); [|contradict n0; reflexivity].
          simplify_mask.
          destruct H8 as [H0 H1].
          generalize (H0 i); intro H0'; clear H0.
          generalize (H1 i); intro H1'; clear H1.
          simpl. split.
          { intros.
            destruct (m i); try (simpl in H0'; rewrite H0'; reflexivity);
            simpl in H1';
            destruct H0; try discriminate;
            rewrite H1'; try reflexivity;
            unfold update; rewrite H0; reflexivity. }
          { intros. destruct H0.
            destruct (m i);
              try (rewrite H1'; try reflexivity;
                   unfold update; rewrite H1; reflexivity);
              contradict H0; reflexivity. }
      + existT_eq.
        destruct s. destruct s' as [l' s'].
        simpl in H8.
        unfold update_state.
        unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
        simpl in H7. subst.
        simpl.
        eexists (inr _).
        split.
        functional_extensionality_dep_pair_r; try reflexivity.
          intro n'.
          generalize (H8 n'); intro H8'; clear H8.
          destruct (eq_nat_dec n n'); subst; try reflexivity.
          rewrite <- functional_extensionality with (f:=s' n'); try reflexivity.
          subst. intro sv'.
          simpl.
          generalize (H8' sv'); intro H8; clear H8'.
          destruct (eq_sv_dec _ x1 sv'); subst; try reflexivity; assumption.
          apply functional_extensionality. intro. apply H8'.
        * unfold sassign.
          intros.
          generalize (H8 n); intro H8'; clear H8.
          destruct (eq_nat_dec n n) as [H|H]; [|contradict H; reflexivity].
          generalize (H8' x1); intro H8; clear H8'.
          destruct (eq_sv_dec _ x1 x1); [|contradict n0; reflexivity].
          simplify_mask.
          unfold forall_in_mask.
          unfold exists_in_mask.
          destruct (H8 ns) as [H0 H1]; clear H8.
          destruct T_dec
          with (P:=(fun i =>
                      negb (Zeq_bool (m i) 0) = true /\
                      Zeq_list_bool _ ((l,s)[[[es]]](i)) ns = true)).
          { unfold not. intros.
            destruct (m i); simpl;
            try (right; intros; destruct H2; inversion H2; fail);
            destruct (Zeq_list_bool n ((l,s)[[[es]]](i)));
            try (left; split; reflexivity);
            right; intros; destruct H2; discriminate.
          }
          { left.
            split.
            - intros. generalize (H2 i); intro H2'.
              destruct (m i); try (contradict H3; reflexivity);
              destruct (Zeq_list_bool n ((l,s)[[[es]]](i)));
                try (destruct H2'; split; reflexivity); reflexivity.
            - apply H0. intros.
              generalize (H2 i); intro H2'.
              destruct (m i); try discriminate;
              destruct (Zeq_list_bool n ((l,s)[[[es]]](i)));
                try (simpl in H2'; destruct H2'; split; reflexivity);
                reflexivity.
          }
          {
            right.
            destruct (H1 H2).
            exists x.
            destruct H3 as [H3 [H3' H3'']].
            repeat split; try assumption.
            destruct (m x); try (contradict H3; discriminate); try reflexivity.
          }
    - (* <= *)
      destruct x as [lv | sv]; constructor.
      + destruct H. destruct x as [la | sa].
        * destruct H. simpl in H0. subst. reflexivity.
        * destruct H. inversion H0.
      + destruct H. destruct x as [la | sa].
        * intros.
          destruct (eq_nat_dec n n'); subst; try intros y.
          { destruct (eq_lv_dec _ lv y).
            - split; intros.
              + destruct H. subst. simpl.
                simpl in H1.
                unfold lassign in H1.
                simplify_mask.
                destruct (eq_nat_dec n' n'); try (contradict n; reflexivity).
                unfold eq_rec_r; unfold eq_rec.
                rewrite <- (eq_rect_eq_dec eq_nat_dec).
                destruct (eq_lv_dec _ y y); try (contradict n; reflexivity).
                destruct s. simpl.
                apply functional_extensionality. intro zs.
                destruct (H1 zs i); clear H1. simpl in *.
                destruct (m i); try inversion H0.
                apply H. left. reflexivity.
              + destruct H. subst. simpl.
                simpl in H1.
                unfold lassign in H1.
                simplify_mask.
                destruct (eq_nat_dec n' n'); try (contradict n; reflexivity).
                unfold eq_rec_r; unfold eq_rec.
                rewrite <- (eq_rect_eq_dec eq_nat_dec).
                destruct (eq_lv_dec _ y y); try (contradict n; reflexivity).
                destruct s. simpl.
                apply functional_extensionality. intro zs.
                destruct (H1 zs i); clear H1. simpl in *.
                unfold update.
                destruct (m i); try inversion H0;
                destruct (Zeq_list_bool _ ((l, s)[[[es]]](i)) zs);
                  try (apply H2; split; try discriminate; reflexivity);
                  apply H; right; reflexivity.
            - destruct H. subst.
              simpl in H0.
              destruct s.
              simpl.
              unfold eq_rec_r; unfold eq_rec.
              apply functional_extensionality_dep. intro n''.
              apply functional_extensionality. intro lv''.
              destruct (eq_nat_dec n' n'); try reflexivity.
              rewrite <- eq_rect_eq.
              destruct (eq_lv_dec _ lv y); try reflexivity. subst.
              contradict n. reflexivity.
          }
          { destruct H. subst. destruct s.
            simpl.
            destruct (eq_nat_dec n n'); subst;
            try (contradict n0; reflexivity).
            reflexivity.
          }
        * intros. simpl in H. destruct H. inversion H0.
      + destruct H. destruct x as [la | sa].
        * destruct H. inversion H0.
        * destruct H. simpl in H0. subst. reflexivity.
      + destruct H. destruct x as [la | sa].
        * intros. simpl in H. destruct H. inversion H0.
        * intros.
          destruct (eq_nat_dec n n'); subst; try intros y.
          { destruct (eq_sv_dec _ sv y).
            - intros.
              destruct H. subst.
              simpl in H0. unfold sassign in H0.
              destruct (H0 ns); clear H0.
              + destruct H. split.
                * simpl. intros.
                  destruct (eq_nat_dec n' n'); try (contradict n; reflexivity).
                  unfold eq_rec_r; unfold eq_rec.
                  rewrite <- eq_rect_eq.
                  destruct (eq_sv_dec _ y y); try (contradict n; reflexivity).
                  assumption.
                * intros.
                  destruct H1.
                  simplify_mask.
                  exists x.
                  destruct H1.
                  repeat split; try assumption.
                  unfold forall_in_mask in H.
                  generalize (H x); intros. clear H.
                  destruct (m x); try (contradict H1; discriminate; fail);
                  destruct (Zeq_list_bool _ (s[[[es]]](x)) ns);
                  try (assert (H' : true = false) by (apply H3; discriminate));
                  try (assert (H' : false = true) by (apply H2; reflexivity));
                  try inversion H'.
              + split.
                * intros.
                  destruct H as [i [H [H' H'']]].
                  generalize (H0 i); clear H0; intro H0.
                  simplify_mask.
                  destruct (m i); try (contradict H; reflexivity);
                  simpl in H0;
                  generalize (H0 (refl_equal _)); intro;
                  rewrite H' in H1; discriminate.
                * intros.
                  simpl.
                  destruct (eq_nat_dec n' n'); subst;
                  try (contradict n; reflexivity);
                  try (unfold eq_rec_r; unfold eq_rec; rewrite <- eq_rect_eq);
                  destruct (eq_sv_dec _ y y); try (apply H; discriminate);
                  try contradict n; try reflexivity.
                  destruct H.
                  exists x.
                  destruct H as [H [H' H'']].
                  unfold mask_of in *.
                  repeat split; try assumption.
                  destruct (m x); try (contradict H; reflexivity); reflexivity.
            - destruct H. subst.
              simpl in H0.
              destruct s.
              simpl.
              unfold eq_rec_r; unfold eq_rec.
              apply functional_extensionality_dep. intro n''.
              destruct (eq_nat_dec n' n'); try reflexivity.
              rewrite <- eq_rect_eq.
              destruct (eq_sv_dec _ sv y); try reflexivity. subst.
              contradict n. reflexivity.
          }
          { destruct H. subst. destruct s.
            simpl.
            destruct (eq_nat_dec n n'); subst;
            try (contradict n0; reflexivity).
            reflexivity.
          }
  Qed.

  Definition stable :=
    fun e P =>
      forall (mu : mask) (s s' : state),
        eval P mu s s' ->
        forall i : T, mu i = false -> s[[e]](i) = s'[[e]](i).

  Lemma lem_2 : forall e P,
                  stable e P ->
                  forall mu s s',
                    eval P (meet mu (mask_of (E_under_state s e))) s s' ->
                    sub (meet mu (mask_of (E_under_state s' e)))
                        (meet mu (mask_of (E_under_state s e))).
  Proof.
    unfold sub, stable, meet, negb, mask_of.
    intros.
    generalize (H _ _ _ H0 i); intros.
    destruct (mu i); destruct (s[[e]](i)); simpl in *;
    try reflexivity;
    try inversion H1.
    rewrite <- H2 in H1; inversion H1; reflexivity.
  Qed.

  Inductive regular : program -> Prop :=
  | R_Assign : forall n x es e, regular (@asgn n x es e)
  | R_Skip : regular skip
  | R_Sync : regular sync
  | R_Seq : forall P Q, regular P -> regular Q -> regular (P;; Q)
  | R_If : forall e P Q, regular P -> regular Q ->
                         regular (IFB e THEN P ELSE Q)
  | R_While : forall e P, stable e P ->
                          regular P ->
                          regular (WHILE e DO P).

  Lemma lem_5_1 : forall e, all e <-> mask_of e = T_mask.
  Proof.
    split; intros; unfold all in *; unfold mask_of in *; unfold T_mask in *.
    - apply functional_extensionality; intro i.
      generalize (H i); intro H'.
      destruct (e i); try (contradict H'; reflexivity); reflexivity.
    - intro. apply equal_f with (x:=i) in H.
      destruct (e i); discriminate.
  Qed.

  Lemma lem_5_2 : forall e, none e <-> mask_of e = empty.
  Proof.
    split; intros; unfold none in *; unfold mask_of in *; unfold empty in *.
    - apply functional_extensionality; intro i.
      generalize (H i); intro H'.
      destruct (e i); try discriminate; try reflexivity.
    - intro. apply equal_f with (x:=i) in H.
      destruct (e i); try discriminate; try reflexivity.
  Qed.

  Lemma while_stable :
    forall e P,
      stable e P ->
      stable e (WHILE e DO P).
  Proof.
    intros. unfold stable; intros.
    remember (WHILE e DO P) as W.
    induction H0; inversion HeqW; subst.
    - reflexivity.
    - unfold stable in H.
      assert (forall mu', meet mu mu' i = false) by
          (intros; unfold meet; rewrite H1; reflexivity).
      generalize (H _ _ _ H0_ i (H0 (mask_of (E_under_state s e)))).
      intros.
      generalize (IHeval2 (refl_equal _) (H0 (mask_of (E_under_state s e)))).
      intros.
      rewrite H2, H3.
      reflexivity.
  Qed.

  Lemma lem_2_while :
    forall e P,
      stable e P ->
      forall mu s s',
        eval (WHILE e DO P) mu s s' ->
        sub (mask_of (E_under_state s' e)) (mask_of (E_under_state s e)).
  Proof.
    unfold sub.
    intros.
    remember (WHILE e DO P) as W.
    induction H0; inversion HeqW; subst; try assumption.
    clear IHeval1.
    generalize (H _ _ _ H0_); intro.
    rewrite fold_mask_of in *.
    generalize (while_stable _ _ H _ _ _ H0_0 i); intro.
    generalize (H0 i); intro.
    generalize H1 H2 H3; clear; intros.
    unfold meet in *.
    remember (mask_of (E_under_state s e) i) as b.
    destruct b; try reflexivity.
    unfold mask_of in H1, Heqb.
    rewrite <- H2, <- H3, <- Heqb in H1;
      try assumption; try (destruct (mu i); reflexivity).
  Qed.
End SIMT_Definition.
