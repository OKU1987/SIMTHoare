Require Import SIMT.
Require Import ssreflect ssrfun ssrbool ssrnat.
Require Import tuple ssrint.

Section SIMT_verification_util.
  Variable num_threads : {n : nat | 0 < n}.
  Definition N := sval num_threads.

  Inductive program_with_inv : Type :=
  | asgn' : forall n, V n -> n.-tuple E -> E -> program_with_inv
  | skip' : program_with_inv
  | sync' : program_with_inv
  | seq' : program_with_inv -> program_with_inv -> program_with_inv
  | P_if' : E -> program_with_inv -> program_with_inv -> program_with_inv
  | P_while' : E -> program_with_inv -> assertion num_threads -> program_with_inv.
  Notation "'WHILE' e 'DO' P 'with' phi" := (P_while' e P phi) (at level 140).
  Notation "s '[[' e ']](' i ')'" := (E_under_state num_threads s e i) (at level 50).
(*
  Fixpoint emb_with_inv (P : program) : program_with_inv :=
    match P with
    | asgn n v es e => asgn' n v es e
    | skip => skip'
    | sync => sync'
    | seq P Q => seq' (emb_with_inv P) (emb_with_inv Q)
    | P_if e P Q => P_if' e (emb_with_inv P) (emb_with_inv Q)
    | P_while' 
  Coercion Prg : program >-> program_with_inv.
 *)
  Fixpoint remove_inv (P : program_with_inv) : program :=
    match P with
    | asgn' n v es e => asgn n v es e
    | skip' => skip
    | sync' => sync
    | seq' p p' => SIMT.seq (remove_inv p) (remove_inv p')
    | P_if' e p p' => P_if e (remove_inv p) (remove_inv p')
    | P_while' e p _ => P_while e (remove_inv p)
    end.

  Inductive Hoare_proof' : assertion num_threads -> (T num_threads -> int) -> program_with_inv -> assertion num_threads -> Prop :=
  | H_Skip' : forall phi m, Hoare_proof' phi m skip' phi
  | H_Sync' : forall (phi : assertion num_threads) m, Hoare_proof' (fun s => (all num_threads m \/ none num_threads m) -> phi s) m sync' phi
  | H_Assign' : forall n x es e m (phi : assertion num_threads),
      Hoare_proof' (fun s : state num_threads =>
                      forall x', assign num_threads s n x' m x es e ->
                                 phi (update_state num_threads s n x x'))
                   m (asgn' n x es e) phi
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



  Lemma H_Conseq_pre' : forall (phi psi phi' : assertion num_threads) m p,
                         Hoare_proof' phi' m p psi ->
                         (forall s, phi s -> phi' s) ->
                         Hoare_proof' phi m p psi.
  Proof.
    intros.
    apply (H_Conseq' _ _ _ _ m p H H0 (fun s => id)).
  Qed.

  Lemma H_Conseq_post' : forall (phi psi psi' : assertion num_threads) m p,
                         Hoare_proof' phi m p psi' ->
                         (forall s, psi' s -> psi s) ->
                         Hoare_proof' phi m p psi.
  Proof.
    intros.
    apply (H_Conseq' _ _ _ _ m p H (fun s => id) H0).
  Qed.

  Lemma hoare_proof_remove_inv : forall phi m P psi,
                                   Hoare_proof' phi m P psi ->
                                   Hoare_proof _ phi m (remove_inv P) psi.
  Proof.
    move=> phi m P psi H.
    induction H => //= ; try (econstructor; fail).
    { eapply H_Assign; eassumption. }
    { eapply H_Conseq; eassumption. }
    { eapply H_Seq; eassumption. }
    { eapply H_If; eassumption. }
    { eapply H_While; eassumption. }
  Qed.
End SIMT_verification_util.
