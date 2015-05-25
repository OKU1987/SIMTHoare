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
End SIMT_Definition.
