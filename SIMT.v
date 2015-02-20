Require Import Vectors.VectorDef.
Require Import ZArith.

Section SIMT_Definition.
  Variable num_threads : { n : nat & (n > 0)%nat}. (* the number of threads *)
  Definition N := projT1 num_threads.

  Definition arity := nat.
  Definition variable_name := nat.
End SIMT_Definition.
