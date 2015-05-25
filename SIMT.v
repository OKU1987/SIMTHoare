Require Import SIMT_util.
Require Import Vectors.VectorDef.
Require Import ZArith.
Import VectorNotations.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

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
End SIMT_Definition.
