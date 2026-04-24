(** erisWpGS instance for lrust_prob_lang.

    Provides a canonical [erisWpGS lrust_prob_lang Σ] instance so that
    eris's [pgl_wp], error credits [↯ε], and generic lifting lemmas in
    [eris/eris/{lifting,ectx_lifting}.v] become directly applicable to
    λRust expressions.

    ===========================================================================
    STATUS: [state_interp σ := emp] (still heap-free, but now for a
    different reason — see below).
    ===========================================================================
    Previously this file documented two obstacles to threading
    [heap.heap_ctx σ] as [state_interp]:

      1. Invariant-discipline mismatch (eris wanted [HasNoLc];
         [heap.v] needs [HasLc]).
      2. WP-notation clash between iris's [bi/weakestpre] and eris's.

    After the iris MR !1171 port (see [src/eris/eris/adequacy.v] and
    [src/lambda_verus/lang/adequacy_prob.v]), obstacle (1) is gone:
    both eris and [heap.v] now live under [invGS_gen HasLc Σ]. The
    adequacy proof goes through the hfupd modality, which commutes
    with ∀ under [HasLc] — the missing piece the MR provides.

    Obstacle (2) is still technically live (same top-level WP notation
    at level 20 in both [iris.bi] and [eris.bi]), but it's
    mechanical — either rename one notation or import [heap.v]
    without [Import] and fully-qualify the heap-specific names.

    What [state_interp := emp] gives us right now:
      - Heap-free λRust programs (pure arithmetic, [Rand], control
        flow). Sufficient to discharge verusbelt's [rand_ubig] and
        [thin_air] axioms — they only talk about [↯ε].

    Next step to lift this restriction: set
      [state_interp σ := heap_ctx σ]
    once the WP-notation clash is resolved; no iris-side work needed.
    =========================================================================== *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From lrust.lang Require Export prob_lang.
From eris.base_logic Require Export error_credits.
From eris.eris Require Export weakestpre.
Set Default Proof Using "Type".

Class lrustErisGS (Σ : gFunctors) := LrustErisGS {
  #[global] lrustErisGS_ecGS :: ecGS Σ;
  lrustErisGS_invGS : invGS_gen HasLc Σ;
}.

Global Program Instance lrustErisGS_erisWpGS `{!lrustErisGS Σ} :
  erisWpGS lrust_prob_lang Σ := {
  erisWpGS_invGS := lrustErisGS_invGS;
  state_interp _ := emp%I;
  err_interp ε := ec_supply ε;
}.

(** * A primitive WP rule: [wp_rand_prob].

    Demonstrates the wiring works end-to-end: reducibility (the
    distribution has positive support), step (every support outcome
    satisfies the postcondition), and the [state_interp := emp]
    non-contribution. Follow-on primitive laws live in
    [primitive_laws_prob.v]; the error-credit-aware [wp_rand_exp_nat]
    lives in [error_rules_prob.v]. *)
From Stdlib Require Import Reals Psatz.
From eris.eris Require Import ectx_lifting.
From eris.prob Require Import distribution.
Open Scope R.

Section wp_rand.
  Context `{!lrustErisGS Σ}.

  Lemma wp_rand_prob E (N : Z) (Φ : syntax.val → iProp Σ) s :
    (0 < N)%Z →
    (∀ (n : fin (S (Z.to_nat N - 1))),
       Φ (LitV (LitInt (Z.of_nat (fin_to_nat n))))) -∗
    WP Rand (Lit (LitInt N)) @ s; E {{ Φ }}.
  Proof.
    iIntros (HN) "HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "Hσ". iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose". iSplit.
    { iPureIntro. rewrite /head_reducible /=.
      rewrite bool_decide_eq_true_2 //.
      eexists (_, _). apply dmap_pos. exists 0%fin. split; first done.
      apply dunifP_pos. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dmap_pos in Hstep as (n & [= -> ->] & _).
    iModIntro. iFrame. by iApply "HΦ".
  Qed.
End wp_rand.
