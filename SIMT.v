Require Import SIMT_util.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import tuple finfun finset ssrint intdiv.
Require Import FunctionalExtensionality.
Open Scope list_scope.
Import List.ListNotations.

Section SIMT_Definition.
  Local Notation "z < z'" := (intOrdered.ltz z z').
  Local Notation "z <= z'" := (intOrdered.lez z z').
  Local Notation "z + z'" := (intZmod.addz z z').
  Local Notation "z - z'" := (intZmod.addz z (intZmod.oppz z')).
  Local Notation "z * z'" := (intRing.mulz z z').
  Implicit Arguments Vector_of_tuple [T n].
  Implicit Arguments tuple_of_Vector [T n].

  Variable num_threads : {n : nat | 0 < n}.
  Definition N := sval num_threads.

  Definition arity := nat.
  Definition arity_eqType := nat_eqType.
  Definition variable_name := nat.

  Inductive LV (n:arity) : Set := local of variable_name.
  Inductive SV (n:arity) : Set := shared of variable_name.

  Inductive V n : Set :=
  | local_variable : LV n -> V n
  | shared_variable : SV n -> V n.
  Coercion local_variable : LV >-> V.
  Coercion shared_variable : SV >-> V.

  Definition eq_lv n (lv lv' : LV n) : bool :=
    match lv, lv' with
      | local l, local l' => l == l'
    end.

  Definition eq_sv n (sv sv' : SV n) : bool :=
    match sv, sv' with
      | shared l, shared l' => l == l'
    end.

  Lemma lv_eqP : forall n, Equality.axiom (eq_lv n).
  Proof.
    move => n.
    case.
    move => v y.
    case: y => v'.
    move H : (eq_lv _ _ _) => [];
      rewrite/eq_lv in H; constructor; move: H;
      repeat move/eqP => ?; congruence.
  Qed.

  Lemma sv_eqP : forall n, Equality.axiom (eq_sv n).
    move => n.
    case.
    move => v y.
    case: y => v'.
    move H : (eq_sv _ _ _) => [];
      rewrite/eq_lv in H; constructor; move: H;
      repeat move/eqP => ?; congruence.
  Qed.

  Canonical lv_eqMixin n := EqMixin (lv_eqP n).
  Canonical sv_eqMixin n := EqMixin (sv_eqP n).
  Canonical lv_eqType n := Eval hnf in EqType _ (lv_eqMixin n).
  Canonical sv_eqType n := Eval hnf in EqType _ (sv_eqMixin n).


  Definition Op n := n.-tuple int -> int.

  Open Scope int_scope.
  Definition const (z:int) : Op 0 := fun _ : 0.-tuple int => z.
  Definition e_plus : Op 2 :=
    fun zs => match zs return int with
                | Tuple [x; y] _ => x + y
                | _ => 0
              end.
  Definition e_minus : Op 2 :=
    fun zs => match zs return int with
                | Tuple [x; y] _ => x - y
                | _ => 0
              end.
  Definition e_mult : Op 2 :=
    fun zs => match zs return int with
                | Tuple [x; y] _  => x * y
                | _ => 0
              end.
  Definition e_div : Op 2 :=
    fun zs => match zs with
                | Tuple [x; y] _ => x %/ y
                | _ => 0
              end.
  Definition e_mod : Op 2 :=
    fun zs => match zs with
                | Tuple [x; y] _ => x %% y
                | _ => 0
              end.
  Definition int_of_bool := fun b => if b then 1%:Z else 0.
  Definition bool_of_int := fun z : int => z != 0.
  Lemma int_of_boolK : cancel int_of_bool bool_of_int.
  Proof.
    rewrite /cancel/int_of_bool/bool_of_int.
    elim; done.
  Qed.
  Definition e_neg : Op 1 :=
    fun z => match z with
               | Tuple [x] _ => int_of_bool (~~ (bool_of_int x))
               | _ => 0
             end.
  Definition e_and : Op 2 :=
    fun zs => match zs with
                | Tuple [x; y] _ =>
                  int_of_bool (andb (bool_of_int x)
                                    (bool_of_int y))
                | _ => 0
              end.
  Definition e_lt : Op 2 :=
    fun zs => match zs with
                | Tuple [x; y] _ =>
                  int_of_bool (intOrdered.ltz x y)
                | _ => 0
              end.
  Definition e_leq : Op 2 :=
    fun zs => match zs with
                | Tuple [x; y] _ =>
                  int_of_bool (intOrdered.lez x y)
                | _ => 0
              end.

  Definition zero_tuple := tuple_of 0.
  Record hoge : Type := { foo (A : Set) (B : Set) : A * B }.

  Inductive E : Set :=
  | tid : E
  | ntid : E
  | var : forall n, V n -> Vector.t E n -> E
  | func : forall n, Op n -> Vector.t E n -> E.
  Implicit Arguments var [n].
  Implicit Arguments func [n].

  Lemma eqType_eq_rect_eq : forall (U : eqType) P (p : U) (x : P p) (H : p = p),
                       x = eq_rect p P x p H.
  Proof.
    move=> U P p x H.
      by rewrite (eq_irrelevance H erefl).
  Qed.

  Lemma eqType_eq_dep_eq :
    forall (U : eqType) P (p : U) (x y : P p),
      EqdepFacts.eq_dep U P p x p y -> x = y.
  Proof.
    move => U P p x y H.
    case: (EqdepFacts.eq_dep_dep1 _ _ _ _ _ _ H) => H0 H1.
    apply (eq_ind y (fun p0 : P p => x = p0 -> x = y) (fun H0 : x = y => H0)
                  (eq_rect p P y p H0) (eqType_eq_rect_eq U P p y H0) H1
          ).
  Qed.
  Lemma eq_existT : forall (U : eqType) P (p : U) (x y : P p),
                      existT P p x = existT P p y -> x = y.
  Proof.
    move=> U P p x y H.
    move: (eq_ind (existT P p y) (fun s : sigT P => EqdepFacts.eq_dep U P (projT1 s) (projT2 s) p y) (EqdepFacts.eq_dep_intro U P p y) (existT P p x) (Logic.eq_sym H)).
    rewrite /= .
    move=> H0.
    apply (eqType_eq_dep_eq _ _ _ _ _ H0).
  Qed.


  Notation "'!' a" := (@func 1 e_neg [a]) (at level 35, right associativity).
  Notation "'c' z" := (@func 0 (const z) []) (at level 20).

  Inductive program : Set :=
  | asgn : forall n, V n -> n.-tuple E -> E -> program
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

  Definition T := 'I_N. (* The set of threads *)
  Definition T_eqType := ordinal_eqType N.
  Definition T_finType := ordinal_finType N.

  Definition L_map n := T -> n.-tuple int -> int.
  Definition S_map n := n.-tuple int -> int.
  Definition state := ((forall n, LV n -> L_map n) * (forall n, SV n -> S_map n))%type.

  Reserved Notation "s '[[' e ']](' i ')'" (at level 50).

  Fixpoint E_under_state (s:state) e : T -> int :=
    match e with
      | tid => id
      | ntid => fun _ => N
      | var n (local_variable lv) es =>
        fun i => s.1 n lv i (tuple_of_Vector (Vector.map (fun e => s[[e]](i)) es))
      | var n (shared_variable sv) es =>
        fun i => s.2 n sv (tuple_of_Vector (Vector.map (fun e => s[[e]](i)) es))
      | func n f es =>
        fun i => f (tuple_of_Vector (Vector.map (fun e => s[[e]](i)) es))
    end
      where "s '[[' e ']](' i ')'" := (E_under_state s e i).

  Definition update_state (s : state) n (x : V n) (x' : (T -> n.-tuple int -> int) + (n.-tuple int -> int)) : state.
    destruct x; destruct x'; [|exact s|exact s|].
    {
      refine ((fun n0 (lv0 : LV n0) => _, s.2)).
      case: (@eqnP n n0) => H.
      { subst. exact (if l == lv0 then i else s.1 _ lv0). }
      { exact (s.1 n0 lv0). }
    }
    {
      refine (s.1, (fun n0 (sv0 : SV n0) => _)).
      case: (@eqnP n n0) => H.
      { subst. exact (if s0 == sv0 then i else s.2 _ sv0). }
      { exact (s.2 n0 sv0). }
    }
  Defined.
  Transparent update_state.

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
        destruct (@eqnP x x); rewrite //;
                                      rewrite (eq_irrelevance (Logic.eq_sym _) erefl)
      | [ |-context[eqnP]] =>
        case: eqnP => //=
      | _ => fail
    end.
  Ltac simplify_update_state :=
    repeat unfold_update_state; simpl; repeat simplify_update_state'; simpl.

  Definition mask := {set T}.
  Definition empty : mask := set0.
  Definition T_mask : mask := [set: T].
  Definition T_pred := set_predType T_finType.

  Definition s_es n s := fun (es : n.-tuple E) i =>
                           [tuple of [seq s[[e]](i) | e <- es]].
  Notation "s '[[[' es ']]](' i ')'" := (s_es _ s es i) (at level 50).

  Inductive eval : program -> mask -> state -> state -> Prop :=
  | E_Inactive : forall P s, eval P empty s s
  | E_Skip : forall mu s, eval skip mu s s
  | E_Sync : forall s, eval sync T_mask s s
  | E_LAssign : forall n (x : LV n) es e (mu : mask) (s s' : state),
                  (forall n, s'.2 n =2 s.2 n) ->
                  (forall n',
                     if n == n' then
                       forall y : LV n,
                         if x == y then
                           forall i : T,
                             s'.1 n x i =1
                             if i \in mu then
                               [eta s.1 n x i with s[[[es]]](i) |-> s[[e]](i)]
                             else
                               s.1 n x i
                         else s'.1 n y =2 s.1 n y
                     else (forall y : LV n', s'.1 n' y =2 s.1 n' y)) ->
                  eval (asgn x es e) mu s s'
  | E_SAssign : forall n (x : SV n) es e (mu : mask) (s s' : state),
                  (forall n (lv : LV n), s'.1 n lv =2 s.1 n lv) ->
                  (forall n',
                     if n == n' then
                       forall y : SV n,
                         if x == y then
                           (forall ns,
                              if [forall (i | i \in mu), s[[[es]]](i) != ns] then
                                s'.2 n x ns = s.2 n x ns
                              else
                                [exists (i | i \in mu),
                                   (s[[[es]]](i) == ns)
                                     && (s'.2 n x ns == s[[e]](i))]
                           )
                         else s'.2 n y =1 s.2 n y
                     else (forall y : SV n', s'.2 _ y =1 s.2 _ y)) ->
                  eval (asgn x es e) mu s s'
  | E_Seq : forall P Q mu s s' s'', eval P mu s s' ->
                                    eval Q mu s' s'' ->
                                    eval (seq P Q) mu s s''
  | E_If : forall P Q (mu : mask) s e (s_e : mask) s' s'',
             s_e = [set i | bool_of_int (s[[e]](i))] ->
             eval P (mu :&: s_e) s s' ->
             eval Q (mu :\: s_e) s' s'' ->
             eval (IFB e THEN P ELSE Q) mu s s''
  | E_While : forall P (mu : mask) s e mu' s' s'',
                mu' = mu :&: [set i | bool_of_int (s[[e]](i))] ->
                eval P mu' s s' ->
                eval (WHILE e DO P) mu' s' s'' ->
                eval (WHILE e DO P) mu s s''.

  Definition assertion := state -> Prop.

  Definition mask_of (m : T -> int) : mask := [set i | bool_of_int (m i)].

  Lemma setI_e_and :
    forall m z,
       (mask_of m) :&: (mask_of z) = mask_of (fun i => e_and [tuple m i; z i]).
  Proof.
    move => m z.
    apply setP => i.
    rewrite /mask_of/e_and -setIdE 3!in_set int_of_boolK // .
  Qed.

  Lemma setD_e_and_neg :
    forall m z,
      (mask_of m) :\: (mask_of z) = mask_of (fun i => e_and [tuple m i; e_neg [tuple z i]]).
  Proof.
    move => m z.
    apply setP => i.
    rewrite /mask_of/e_and/e_neg/= setDE -setIdE 4!in_set 2!int_of_boolK // .
  Qed.
  Definition hoare_quadruple (phi : assertion) m (P : program) (psi : assertion) : Prop :=
    forall s s' : state,
      phi s ->
      eval P (mask_of m) s s' ->
      psi s'.

  Definition all (e : T -> int) := forall i : T, e i != 0.
  Definition none (e : T -> int) := forall i : T, e i == 0.

  Definition lassign (s : state) n (x' : T -> n.-tuple int -> int) (m : T -> int) (x : LV n) (es : n.-tuple E) (e : E) : Prop :=
    forall (ns : n.-tuple int) (i : T),
      (m i == 0 \/ s[[[es]]](i) != ns ->
       (x' i ns = fst s n x i ns)) /\
      (m i != 0 /\ s[[[es]]](i) == ns ->
       (x' i ns = s[[e]](i))).

  Definition sassign s n (x' : n.-tuple int -> int) (m : T -> int) (x : SV n) (es : n.-tuple E) (e : E) : Prop :=
    (forall ns : n.-tuple int,
       ([forall (i | i \in mask_of m), s[[[es]]](i) != ns] /\
        x' ns = snd s n x ns) \/
       ([exists (i | i \in mask_of m),
           (s[[[es]]](i) == ns) && (x' ns == s[[e]](i))])).

  Definition assign rho n x' (m : T -> int) (x : V n) (es : n.-tuple _) (e : _) :=
    match x, x' return Prop with
      | local_variable lv, inl lv' => lassign rho n lv' m lv es e
      | shared_variable sv, inr sv' => sassign rho n sv' m sv es e
      | _, _ => False
    end.
  Implicit Arguments assign [n].

  Inductive Hoare_proof : assertion -> (T -> int) -> program -> assertion -> Prop :=
  | H_Skip : forall phi m, Hoare_proof phi m skip phi
  | H_Sync : forall (phi : assertion) m,
               Hoare_proof (fun s => (all m \/ none m) -> phi s)
                           m sync phi
  | H_Conseq : forall (phi phi' psi psi' : assertion) m P,
                 Hoare_proof phi m P psi ->
                 (forall s, phi' s -> phi s) ->
                 (forall s, psi s -> psi' s) ->
                 Hoare_proof phi' m P psi'
  | H_Seq : forall phi m P psi Q chi,
              Hoare_proof phi m P psi ->
              Hoare_proof psi m Q chi ->
              Hoare_proof phi m (P ;; Q) chi
  | H_Assign : forall n (x : V n) (es : n.-tuple E) e m (phi : assertion),
                 Hoare_proof (fun s =>
                                forall x', assign s x' m x es e ->
                                           phi (update_state s n x x'))
                             m (asgn x es e) (fun s => phi s)
  | H_If : forall (phi : assertion) psi chi e (m : T -> int) P Q,
             (forall z : T -> int,
                Hoare_proof
                  (fun s =>
                     phi s /\
                     (forall i, s[[e]](i) = z i))
                  (fun i => e_and [tuple m i; z i]) P (psi z)) ->
             (forall z, Hoare_proof (psi z) (fun i => e_and [tuple m i; e_neg [tuple z i]]) Q chi) ->
             Hoare_proof phi m (IFB e THEN P ELSE Q) chi
  | H_While : forall (phi : assertion) m e P,
                (forall z : T -> int,
                   Hoare_proof (fun s => phi s /\ (forall i, s[[e]](i) = z i)) (fun i => e_and [tuple m i; z i]) P phi) ->
                Hoare_proof phi m (WHILE e DO P) (fun s => phi s /\ none (fun i : T => e_and [tuple m i; s[[e]](i)])).

  Lemma lem_1 : forall s s' n (x : V n) es e (m : T -> int),
                   eval (asgn x es e) (mask_of m) s s' <->
                   exists a,
                       s' = update_state s _ x a /\
                       assign s a m x es e.
  Proof.
    split; intros.
    { inversion H; subst; clear H.
      {
        destruct x as [lv | sv].
        {
          destruct s'.
          exists (inl (l n lv)).
          simplify_update_state.
          split.
          { functional_extensionality_dep_pair_r => n'.
            simplify_update_state => p.
            subst.
            simplify_update_state.
            apply functional_extensionality => lv'.
            case:ifP => H // .
            rewrite (elimT eqP H) //= . }
          { rewrite/lassign => ns i.
            split => //= .
            (do 2!case/andP) => H _.
            apply setP in H2.
            rewrite /empty/mask_of/bool_of_int in H2.
            move: (H2 i).
            rewrite in_set0 in_set H// . }}
        { destruct s'.
          exists (inr (fun zs => s n sv zs)).
          split.
          { simplify_update_state.
            functional_extensionality_dep_pair_r => n'.
            simplify_update_state => p.
            subst.
            apply functional_extensionality => sv'.
            simplify_update_state.
            case:ifP => H // .
            rewrite (elimT eqP H) //= . }
          { rewrite/sassign => ns.
            left.
            split => //= .
            apply setP in H2.
            rewrite /empty/mask_of/bool_of_int in H2.
            apply (introT forall_inP) => i.
            move: (H2 i).
            rewrite in_set0 in_set.
            move => H.
              by rewrite -H. }
        }
      }
      { move: (eq_existT _ _ _ _ _ H1) => {H1} H1.
        move: (eq_existT _ _ _ _ _ H3) => {H3} H3.
        destruct s. destruct s' as [l' s'].
        rewrite /= in H7,H8|-*.
        subst.
        eexists (inl (l' n _)).
        split.
        { simplify_update_state.
          rewrite /eqrel in H7.
          assert ((l', s') = (l', s)).
          { functional_extensionality_dep_pair_r => n'.
            apply functional_extensionality => sv.
            apply functional_extensionality => y.
            rewrite (H7 _ sv y) => // . }
          rewrite H.
          functional_extensionality_dep_pair_r => n'.
          simplify_update_state => p.
          { subst.
            move: (H8 n') => {H8}.
            case: (@eqnP n' n') => p.
            { rewrite (introT eqP p).
              move => H8.
              apply functional_extensionality => lv.
              move: (H8 lv) => {H8}.
              case: (lv_eqP _ x1 lv) => H0.
              { rewrite (introT eqP H0) /= .
                subst.
                case: ifP => // H1.
                  by apply (elimF eqP) in H1. }
              { apply (introF eqP) in H0.
                simplify_update_state.
                rewrite H0 => H1.
                apply functional_extensionality => i.
                apply functional_extensionality => // . }}
            { rewrite (introF eqP p).
              simplify_update_state => // . }}
          { move: (H8 n').
            rewrite (introF eqP p) => H0.
            apply functional_extensionality => lv // .
            apply functional_extensionality => i.
            apply functional_extensionality => x.
            rewrite (H0 lv i x) => // . }}
        { rewrite /=/lassign.
          intros.
          move: (H8 n) => {H8} H8.
          rewrite (introT eqP erefl) in H8.
          move: (H8 x1) => {H8} H8.
          rewrite (introT eqP erefl) in H8.
          rewrite /= .
          rewrite (H8 i) => {H8}.
          rewrite /mask_of/bool_of_int in_set.
          case:ifP => /= H; split => // => H0.
          { rewrite (negbTE H) in H0.
            case: H0 => // H0.
            case:ifP => // H1.
            rewrite eq_sym (negbTE H0) // in H1. }
          { case: H0 => H0 H1.
            case:ifP => // .
            rewrite eq_sym H1 // . }
          { case H0 => // . }
        }
      }
      { move: (eq_existT _ _ _ _ _ H1).
        move: (eq_existT _ _ _ _ _ H3).
        move => {H1} {H3} H1 H3.
        destruct s. destruct s' as [l' s'].
        rewrite /= in H7,H8|-*.
        simplify_update_state.
        rewrite /= .
        subst.
        eexists (inr _).
        split.
        { rewrite /eqrel in H7.
          assert ((l', s') = (l, s')).
          { functional_extensionality_dep_pair_r => n'.
            apply functional_extensionality => lv'.
            apply functional_extensionality => i.
            apply functional_extensionality => ns.
            rewrite (H7 _ _ _ _) // . }
          rewrite H.
          functional_extensionality_dep_pair_r => n'.
          rewrite /eqfun in H8.
          simplify_update_state => p.
          { subst.
            move: (H8 n') => {H8}.
            case: (@eqnP n' n') => p.
            { rewrite (introT eqP p).
              subst.
              move => H8.
              apply functional_extensionality => sv.
              move: (H8 sv) => {H8}.
              case: (sv_eqP _ x1 sv) => H0.
              { rewrite (introT eqP H0) /= .
                subst.
                move=> H0.
                rewrite (introT eqP erefl) => // . }
              { apply (introF eqP) in H0.
                simplify_update_state.
                rewrite H0 => H1.
                apply functional_extensionality => // . }}
            { rewrite (introF eqP p).
              simplify_update_state => // . }}
          { move: (H8 n').
            rewrite (introF eqP p) => H0.
            apply functional_extensionality => sv // .
            apply functional_extensionality => i.
            rewrite (H0 sv i) => // . }}
        { rewrite/=/sassign => ns.
          move: (H8 n) => {H8} H8.
          rewrite (introT eqP erefl) in H8.
          move: (H8 x1) => {H8} H8.
          rewrite (introT eqP erefl) in H8.
          move: (H8 ns).
          rewrite /mask_of/bool_of_int/= => {H8}.
          case:ifP => H H0; try by right.
          left.
          split => // .
        }
      }
    }
    { (* <= *)
      destruct x as [lv | sv]; constructor;
      case: H;
      case => [la | sa]; case; case s; case s' => {s} {s'} l s l' s';
        case => H H0 H1; subst => //= n'.
      { case: ifP => H0 y.
        {
          apply (elimT eqP) in H0.
          subst.
          simplify_update_state.
          case: ifP => H2 i.
          { apply (elimT eqP) in H2.
            subst.
            rewrite /=/lassign in H1.
            rewrite /mask_of/bool_of_int/eqfun/= => ns.
            rewrite (introT eqP erefl).
            move: (H1 ns i) => {H1}.
            rewrite /= .
            case => H H0.
            rewrite in_set.
            case:ifP => //= => H2.
            { rewrite eq_sym.
              case:ifP => H3.
              { rewrite H0 => //= . }
              { rewrite H3/negb in H0.
                rewrite H => // .
                rewrite H3/negb.
                  by right. }
            }
            { apply negbT in H2.
              rewrite negbK in H2.
              rewrite H2 in H0.
              rewrite H => // .
                by left. }
          }
          { move=> ns.
              by rewrite H2. }}
        { simplify_update_state => p.
            by rewrite (introT eqP p) in H0. }}
      { case: ifP => H0 y.
        { apply (elimT eqP) in H0.
          subst.
          case:ifP => // H2 ns.
          { apply (elimT eqP) in H2.
            subst.
            simplify_update_state.
            move: (H1 ns) => {H1}.
            case => H0.
            { case: H0 => H0 H1.
              rewrite H0.
              case:ifP => // . }
            { assert [exists i in mask_of m, ~~((l',s')[[[es]]](i) != ns)].
              { move: H0; clear => H0.
                apply (introT existsP).
                apply (elimT existsP) in H0.
                case: H0 => i H0.
                exists i.
                apply/andP.
                move/andP in H0.
                case: H0 => H0.
                move/andP.
                case => H1 H2.
                split => // .
                apply negbT.
                  by rewrite H1. }
              rewrite -negb_forall_in in H.
              rewrite (negbTE H).
              rewrite (introT eqP erefl) // . }
          }
          { simplify_update_state.
              by rewrite H2. }
        }
        { simplify_update_state => H2.
            by apply (elimF eqP) in H0. }
      }
    }
  Qed.

  Definition stable :=
    fun e P =>
      forall (mu : mask) (s s' : state),
        eval P mu s s' ->
        forall i : T, i \notin mu -> s[[e]](i) = s'[[e]](i).

  Lemma lem_2 : forall e P,
                  stable e P ->
                  forall mu s s',
                    eval P (mu :&: (mask_of (E_under_state s e))) s s' ->
                    (mu :&: (mask_of (E_under_state s' e)))
                      \subset (mu :&: (mask_of (E_under_state s e))).
  Proof.
    move=> e P H mu s s' H0.
    apply (introT subsetP).
    move=> i.
    move: (H _ _ _ H0 i) => {H}.
    rewrite 4!in_set/bool_of_int.
    case: (i \in mu) => // .
    case: (s[[e]](i)) => // .
    case => // .
    rewrite eq_refl/negb andbF.
    case:ifP => // H.
    move=> H1.
    move: (introT eqP (H1 erefl)).
    rewrite eq_sym H // .
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
    split; rewrite /all/T_mask/mask_of/bool_of_int => H.
    { apply setP => i.
      rewrite in_set in_setT (H i) // . }
    { apply setP in H => i.
      move: (H i).
      rewrite in_set in_setT // . }
  Qed.

  Lemma lem_5_2 : forall e, none e <-> mask_of e = empty.
  Proof.
    split; rewrite /none/empty/mask_of/bool_of_int => H.
    { apply setP => i.
      rewrite in_set in_set0 (H i) // . }
    { apply setP in H => i.
      move: (H i).
      rewrite in_set in_set0 => H0.
      apply negbT in H0.
      rewrite negbK // in H0. }
  Qed.

  Lemma while_stable :
    forall e P,
      stable e P ->
      stable e (WHILE e DO P).
  Proof.
    rewrite /stable => e P H mu s s' H0 i H1.
    remember (WHILE e DO P) as W.
    induction H0; inversion HeqW; subst => // .
    assert (i \in (mu :&:[set i | bool_of_int (s[[e]](i))]) ->
                  i \in mu).
    { rewrite in_setI.
      case/andP => //. }
    rewrite (H _ _ _ H0_ i (contra H0 H1)) (IHeval2 erefl (contra H0 H1)) // .
  Qed.

  Lemma lem_2_while :
    forall e P,
      stable e P ->
      forall mu s s',
        eval (WHILE e DO P) mu s s' ->
        (mask_of (E_under_state s' e)) \subset (mask_of (E_under_state s e)).
  Proof.
    rewrite /stable/mask_of/bool_of_int => e P H mu s s' H0.
    apply (introT subsetP) => i.
    remember (WHILE e DO P) as W.
    induction H0; inversion HeqW; subst => // {IHeval1} {HeqW}.
    move: (H _ _ _ H0_ i).
    move: (while_stable _ _ H _ _ _ H0_0 i).
    rewrite in_setI 2!in_set/bool_of_int.
    clear.
    remember (s[[e]](i) != 0) as b.
    move: Heqb.
    case: b => // .
    rewrite andbF /negb.
    move=> H H0 H1.
    case:ifP => // .
    rewrite -(H0 erefl) -(H1 erefl) => H2.
    rewrite H2 // in H.
  Qed.

  Lemma Soundness_while :
    forall phi e p m,
      (forall z : T -> int,
         regular p ->
         forall s s' : state,
           phi s /\ (forall i : T, s [[e ]]( i) = z i) ->
           eval p (mask_of (fun i0 : T => e_and [tuple m i0; z i0])) s
                  s' -> phi s') ->
      regular (WHILE e DO p) ->
      forall s s' m',
        (mask_of m') :&: (mask_of (E_under_state s e)) =
        (mask_of m) :&: (mask_of (E_under_state s e)) ->
        eval (WHILE e DO p) (mask_of m') s s' ->
        phi s ->
        phi s' /\ none (fun i : T => e_and [tuple m' i; s' [[e ]]( i)]).
  Proof.
    move=> phi e p m H H0 s s' m' H2 H1 H3.
    move: H2 H3.
    remember (WHILE e DO p) as W.
    remember (mask_of m') as Mu.
    move: m' HeqMu.
    induction H1; inversion HeqW; subst; unfold none in *; intros.
    { symmetry in HeqMu. apply lem_5_2 in HeqMu.
      split; try assumption; intros.
      generalize (HeqMu i). intro.
      rewrite (elimT eqP (HeqMu i)). destruct (s[[e]](i)); reflexivity. }
    { subst. clear IHeval1.
      inversion H0; subst.
      move: (H (E_under_state s e) H6 s s' (conj H3 (fun i => refl_equal _))); intros.
      clear H HeqW.
      rewrite 2!setI_e_and in IHeval2.
      rewrite H2 in H1,H1_,IHeval2.
      rewrite -setI_e_and in H1.
      move: (IHeval2 erefl H0 (fun i => e_and [tuple m' i; s[[e]](i)]) erefl).       move: (elimT setIidPr (lem_2 _ _ H5 _ _ _ H1_)).
      rewrite setICA -setIA setIA setIid setIA -?setI_e_and H2 => H4 H' {IHeval2}.
      move: (H' H4 (H1 H1_)) => {H'} H7.
      case:H7 => H7 H8.
      split => // i {H7}.
      move: (H8 i) => {H8}.
      rewrite H2 in H1_0.
      move: (elimT setIidPr (lem_2_while _ _ H5 _ _ _ (E_While _ _ _ _ _ _ _ erefl H1_ H1_0))).
      rewrite /e_and/= int_of_boolK.
      rewrite /mask_of.
      move/setP => H8.
      move: (H8 i) => {H8}.
      rewrite 4!in_set.
      move=> H7.
      rewrite -andbA H7 //.
    }
  Qed.

  Theorem Soundness : forall phi (m : T -> int) p psi,
                        Hoare_proof phi m p psi ->
                        regular p ->
                        hoare_quadruple phi m p psi.
  Proof.
    intros phi m p psi H.
    induction H; unfold hoare_quadruple in *; intros.
    { inversion H1; subst; done. }
    {
      inversion H1; subst; apply H0.
      { right => i.
        apply setP in H4.
        move: (H4 i).
        rewrite /mask_of/empty in_set in_set0 /bool_of_int/negb.
        case (m i == 0) => // . }
      { left => i.
        apply setP in H2.
        move: (H2 i).
        rewrite /mask_of/T_mask in_set in_setT // .
      }
    }
    { apply H1.
      apply (IHHoare_proof H2 s) => // .
      apply H0 => // . }
    { inversion H1; subst.
      inversion H3; subst;
      eapply (IHHoare_proof2 H7); try eapply (IHHoare_proof1 H6);
      try eassumption; rewrite <- H8; econstructor.
    }
    {
      destruct (lem_1 s s' n x es e m) as [H2 H2']. clear H2'.
      apply H2 in H1.
      destruct H1 as [x0 [H1 H1']].
      move: (H0 _ H1').
        by rewrite H1.
    }
    {
      inversion H3; inversion H5; subst.
      { generalize (H0 _ H8 s' s' (conj H4 (fun i => refl_equal _))); intro.
        rewrite -setI_e_and-H13/empty set0I in H6.
        move: (H2 _ H10 s' s' (H6 (E_Inactive _ _))) => H7.
        rewrite -setI_e_and-H13/empty set0I in H7.
        apply (H7 (E_Inactive _ _ )). }
      { rewrite setI_e_and in H18.
        rewrite setD_e_and_neg in H19.
        apply (H2 (E_under_state s e) H10 s'0 s'
                  (H0 _ H8 s s'0 (conj H4 (fun i => refl_equal _)) H18) H19). }
    }
    { apply (Soundness_while _ _ _ _ H0 H1 _ _ m (refl_equal _) H3 H2). }
  Qed.

  Definition wlp (m : T -> int) P (phi : assertion) : assertion :=
    fun st => forall st', eval P (mask_of m) st st' ->
                          phi st'.

  Lemma while_sub :
    forall e p m s s' s'',
      stable e p ->
      (m :&: mask_of (E_under_state s' e)) \subset (m :&: (mask_of (E_under_state s e))) ->
      eval (WHILE e DO p) (m :&: (mask_of (E_under_state s' e))) s' s'' ->
      eval (WHILE e DO p) (m :&: (mask_of (E_under_state s e))) s' s''.
  Proof.
    intros.
    generalize dependent s.
    remember (WHILE e DO p) as W.
    remember (m :&: (mask_of (E_under_state s' e))) as mu.
    induction H1; inversion HeqW; intros.
    { eapply E_While; try eapply E_Inactive.
      rewrite -setIA [mask_of _ :&: _]setIC setIA-Heqmu set0I // . }
    { subst.
      move: (elimT setIidPr H1) => H2.
      rewrite setIA [_ :&: m]setIC setIA setIid in H2.
      rewrite -setIA setIid in H1_,H1_0.
      econstructor.
      { reflexivity. }
      { rewrite H2; eassumption. }
      { rewrite H2; eassumption. }
    }
  Qed.

  Lemma H_Conseq_pre : forall (phi psi phi' : assertion) m p,
                         Hoare_proof phi' m p psi ->
                         (forall s, phi s -> phi' s) ->
                         Hoare_proof phi m p psi.
  Proof.
    intros.
    apply (H_Conseq _ _ _ _ m p H H0 (fun s => id)).
  Qed.

  Lemma H_Conseq_post : forall (phi psi psi' : assertion) m p,
                         Hoare_proof phi m p psi' ->
                         (forall s, psi' s -> psi s) ->
                         Hoare_proof phi m p psi.
  Proof.
    intros.
    apply (H_Conseq _ _ _ _ m p H (fun s => id) H0).
  Qed.

  Theorem Relative_Completeness' : forall phi (m : T -> int) p psi,
                                     regular p ->
                                     hoare_quadruple phi m p psi ->
                                     Hoare_proof (wlp m p psi) m p psi.
  Proof.
    intros phi m p.
    generalize dependent m.
    generalize dependent phi.
    induction p; intros.
    { rename t into es.
      eapply H_Conseq_pre.
      { eapply H_Assign. }
      { simpl. intros.
        eapply H1.
        destruct v; apply lem_1; exists x'; split; try reflexivity; assumption. }}
    { eapply H_Conseq_pre.
      { econstructor. }
      { unfold wlp. intros. eapply H1. econstructor. }}
    { unfold hoare_quadruple in H0.
      eapply H_Conseq_pre.
      { econstructor. }
      { unfold wlp. intros. eapply H1.
        destruct H2;
          match goal with
            | [H2 : all m|-_] => apply lem_5_1 in H2
            | [H2 : none m|-_] => apply lem_5_2 in H2
          end; try rewrite H2; try constructor. }}
    { eapply H_Seq with (wlp m p2 psi).
      { eapply H_Conseq_pre.
        { inversion H; subst.
          eapply IHp1; try assumption.
          unfold hoare_quadruple.
          unfold wlp. intros.
          unfold hoare_quadruple in H0.
          eapply H0 with (s:=s). eassumption.
          econstructor; eassumption. }
        { intros. unfold wlp. intros.
          eapply H1.
          econstructor; eassumption. }}
      { inversion H; subst.
        eapply IHp2 with (wlp m p2 psi); try assumption.
        unfold hoare_quadruple, wlp. intros.
        eapply H1.
        assumption. }}
    { eapply H_If; intros.
      { eapply H_Conseq_pre.
        { inversion H; subst.
          eapply IHp1 with
          (phi :=
             (fun s => wlp (fun i => e_and [tuple m i; z i]) p1
                           (wlp (fun i => e_and [tuple m i; e_neg [tuple z i]])
                                p2 psi) s /\
                       (forall i, s[[e]](i) = z i))); try assumption.
          unfold hoare_quadruple. intros.
          destruct H1.
          eapply H1.
          eassumption. }
        { intros. destruct H1.
          unfold wlp. intros.
          unfold wlp in H1.
          apply H1.
          rewrite -setI_e_and in H3.
          rewrite -setD_e_and_neg in H4.
          econstructor; try eapply H3; try eapply H4.
          apply setP => i.
          rewrite /mask_of.
          rewrite 2!in_set (H2 i) // . }}
      { inversion H; subst.
        eapply IHp2 with
        (phi :=
           (fun s => wlp (fun i => e_and [tuple m i; e_neg [tuple z i]]) p2 psi s /\
                     (forall i, s[[e]](i) = z i))); try assumption.
        unfold hoare_quadruple. intros.
        destruct H1.
        unfold wlp in H1.
        eapply H1.
        eassumption. }}
    { inversion H; subst.
      remember
        (fun s =>
           exists z, (forall i, s[[e]](i) = z i) /\
                     wlp (fun i => e_and [tuple m i; z i]) (WHILE e DO p) psi s)
        as wp.
      assert (forall z,
                Hoare_proof (fun s => wp s /\ (forall i, s[[e]](i) = z i))
                            (fun i => e_and [tuple m i; z i]) p wp).
      { intros.
        unfold hoare_quadruple in H0.
        eapply H_Conseq_pre.
        { eapply IHp with (phi:=fun s => wp s /\ (forall i, s[[e]](i) = z i));
          try assumption; subst.
          unfold hoare_quadruple. intros.
          destruct H1 as [ [z' [H1 H1']] H1''].
          exists (E_under_state s' e).
          split; try reflexivity.
          unfold wlp. intros.
          apply H1'.
          rewrite -setI_e_and in H2, H5|-*.
          apply functional_extensionality in H1.
          apply functional_extensionality in H1''.
          rewrite <- H1.
          rewrite <- H1'' in H2.
          generalize H2 H3 H5; clear; intros.
          econstructor; try rewrite -setI_e_and -setIA setIid => // ;
            try eassumption.
          apply (lem_2 _ _ H3) in H2.
          rewrite -setI_e_and in H5.
          apply while_sub; assumption. }
        { intros.
          destruct H1.
          unfold wlp; intros.
          rewrite Heqwp in H1|-*.
          destruct H1 as [z' [H1 H1']].
          exists (E_under_state st' e).
          split; try reflexivity.
          unfold wlp. intros.
          unfold wlp in H1'.
          apply H1'.
          rewrite -?setI_e_and in H5,H6|-*.
          apply functional_extensionality in H1.
          apply functional_extensionality in H2.
          rewrite <- H1.
          rewrite <- H2 in H5.
          generalize (lem_2 _ _ H3 _ _ _ H5); intro.
          econstructor; try apply while_sub; try eassumption.
          rewrite -setIA setIid // . }}
      { econstructor.
        { eapply H_While. eassumption. }
        { intros.
          rewrite Heqwp.
          exists (E_under_state s e).
          split; try reflexivity.
          unfold wlp. intros.
          rewrite -setI_e_and in H5.
          eapply H2.
          generalize H5; clear; intros.
          rewrite setI_e_and in H5.
          remember (WHILE e DO p) as W.
          remember (mask_of (fun i => e_and [tuple m i; s[[e]](i)])) as mu.
          induction H5; try (inversion HeqW).
          { eapply E_While; try eapply E_Inactive.
            rewrite setI_e_and -Heqmu // . }
          { subst.
            generalize H5_ H5_0; clear; intros.
            rewrite -setI_e_and in H5_,H5_0.
            econstructor; try eassumption.
            rewrite -setIA setIid // .
          }}
        { cbv beta.
          intros.
          destruct H2.
          apply lem_5_2 in H5.
          rewrite Heqwp in H2.
          destruct H2 as [z [H2 H2']].
          unfold wlp in H2'.
          eapply H2'.
          assert (mask_of (fun i => e_and [tuple m i; z i]) = empty).
          { apply setP=> i.
            apply setP in H5.
            move: (H5 i).
            rewrite ?in_set -(H2 i) => // . }
          rewrite H6.
          econstructor. }}}
  Qed.

  Theorem Relative_Completeness : forall phi (m : T -> int) p psi,
                                    regular p ->
                                    hoare_quadruple phi m p psi ->
                                    Hoare_proof phi m p psi.
  Proof.
    intros.
    econstructor; try eapply Relative_Completeness'; try eassumption;
    try unfold wlp; intros.
    - apply (H0 _ _ H1 H2).
    - assumption.
  Qed.
End SIMT_Definition.
