Require Import Vectors.VectorDef.
Require Import ZArith.
Import VectorNotations.

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

  Definition mask := T -> bool.
  Definition empty : mask := fun _ => false.
  Definition T_mask : mask := fun _ => true.

  Definition meet (mu mu' : mask) : mask := fun i => andb (mu i) (mu' i).
  Definition diff (mu mu' : mask) : mask := fun i => andb (mu i) (negb (mu' i)).

  Definition s_es n s := fun (es : t E n) i => map (fun e => s[[e]](i)) es.
  Notation "s '[[[' es ']]](' i ')'" := (s_es _ s es i) (at level 50).
End SIMT_Definition.
