Require Import SIMT.
Require Import ssreflect ssrfun ssrbool ssrnat.
Require Import tuple ssrint.

Section SIMT_verification_util.
  Variable num_threads : {n : nat | 0 < n}.
  Definition N := sval num_threads.


  Inductive program_with_inv : Type :=
  | Prg : program -> program_with_inv
  | seq' : program_with_inv -> program_with_inv -> program_with_inv
  | P_if' : E -> program_with_inv -> program_with_inv -> program_with_inv
  | P_while' : E -> program_with_inv -> assertion num_threads -> program_with_inv.
  Notation "'WHILE' e 'DO' P 'with' phi" := (P_while' e P phi) (at level 140).
  Notation "s '[[' e ']](' i ')'" := (E_under_state num_threads s e i) (at level 50).
  Coercion Prg : program >-> program_with_inv.

  Fixpoint remove_inv (P : program_with_inv) : program :=
    match P with
      | Prg p => p
      | seq' p p' => SIMT.seq (remove_inv p) (remove_inv p')
      | P_if' e p p' => P_if e (remove_inv p) (remove_inv p')
      | P_while' e p _ => P_while e (remove_inv p)
    end.


  Inductive Hoare_proof' : assertion num_threads -> (T num_threads -> int) -> program_with_inv -> assertion num_threads -> Prop :=
  | hoare_pf : forall phi m (P : program) psi, Hoare_proof _ phi m P psi ->
                                               Hoare_proof' phi m P psi
  | H_Conseq' : forall (phi phi' psi psi' : assertion _) m P,
                  Hoare_proof' phi m P psi ->
                  (forall s, phi' s -> phi s) ->
                  (forall s, psi s -> psi' s) ->
                  Hoare_proof' phi' m P psi'
  | H_Seq' : forall phi m P psi Q chi,
               Hoare_proof' phi m P psi ->
               Hoare_proof' psi m Q chi ->
               Hoare_proof' phi m (seq' P Q) chi
  | H_If' : forall phi psi chi e m P Q,
              (forall z, Hoare_proof' (fun s => phi s /\ (forall i, s[[e]](i) = z i)) (fun i => e_and [tuple m i;  z i]) P (psi z)) ->
              (forall z, Hoare_proof' (psi z) (fun i => e_and [tuple m i; e_neg [tuple z i]]) Q chi) ->
              Hoare_proof' phi m (P_if' e P Q) chi
  | H_While' : forall phi m e P,
                 (forall z, Hoare_proof' (fun s => phi s /\ (forall i, s[[e]](i) = z i)) (fun i => e_and [tuple m i; z i]) P phi) ->
                 Hoare_proof' phi m (WHILE e DO P with phi) (fun s => phi s /\ none _ (fun i : T _ => e_and [tuple m i; s[[e]](i)])).


  Lemma hoare_proof_remove_inv : forall phi m P psi,
                                   Hoare_proof' phi m P psi ->
                                   Hoare_proof _ phi m (remove_inv P) psi.
  Proof.
    move=> phi m P psi H.
    induction H => //= .
    { eapply H_Conseq; eassumption. }
    { eapply H_Seq; eassumption. }
    { eapply H_If; eassumption. }
    { eapply H_While; eassumption. }
  Qed.
End SIMT_verification_util.
