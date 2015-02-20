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
End SIMT_Definition.
