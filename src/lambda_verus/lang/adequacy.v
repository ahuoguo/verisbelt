Require Import guarding.internal.na_invariants_fork.
From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra.lib Require Import mono_nat.
From iris.algebra Require Import numbers.
From lrust.lang Require Export heap.
From lrust.lang Require Import proofmode notation.
From lrust.util Require Import adequacy_util non_atomic_cell_map atomic_lock_counter.
Set Default Proof Using "Type".

Class lrustGpreS Σ := HeapGpreS {
  #[global] lrustGpreS_iris :: invGpreS Σ;
  #[global] lrustGpreS_heap :: inG Σ (authR heapUR);
  #[global] lrustGpreS_heap_freeable :: inG Σ (authR heap_freeableUR);
  #[global] lrustGpreS_heap_na_logic :: na_logicG loc syntax.val Σ;
  #[global] lrustGpreS_heap_na_inv :: na_invG Σ;
  #[global] lrustGpreS_atomic_lock_ctr :: alc_logicG Σ;
  #[global] lrustGpreS_time :: timePreG Σ
}.

Definition lrustΣ : gFunctors :=
  #[invΣ; timeΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR));
    na_logicΣ loc syntax.val;
    alc_logicΣ;
    na_invΣ
    ].
Global Instance subG_heapPreG {Σ} : subG lrustΣ Σ → lrustGpreS Σ.
Proof. solve_inG. Qed.

(** [lrust_adequacy]: classical top-level adequacy.

    After the iris MR !1171 port, [wp_strong_adequacy_gen] no longer
    takes an extra [£k] credit parameter — [time_init] needs
    [£(advance_credits 4)] credits, so we cannot drop-in the new
    iris adequacy. The proof below is Admitted pending either:
      1. Restructuring [time_init] to use a credit-free allocation,
         or
      2. A custom eris-style adequacy bridging via [hfupd_soundness]
         (mirroring [lrust_wp_pgl] in [adequacy_prob.v]).
    The eris-side probabilistic adequacy [lrust_wp_pgl] is complete;
    this only affects the classical/deterministic top-level adequacy. *)
Definition lrust_adequacy Σ `{!lrustGpreS Σ} e φ k :
  (∀ `{!lrustGS Σ}, £k -∗ time_ctx -∗ WP e {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e ∅ (λ v _, φ v).
Proof.
  (* See the docstring above. The old proof, preserved in git history,
     went through [adequacy_util.wp_strong_adequacy Σ _] (which
     customized iris adequacy with a [£k] parameter). That customization
     doesn't port cleanly to the MR !1171 adequacy API.
     Possible reconstructions listed in the docstring. *)
Admitted.
