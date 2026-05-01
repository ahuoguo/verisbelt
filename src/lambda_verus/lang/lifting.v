(** Lifting lemmas for [lrust_prob_lang]'s eris-based WP.

    Defines the [lrustGS] resource bundle, plumbs it as the canonical
    [erisWpGS] instance with [state_interp σ := heap_ctx σ], and
    derives the heap and pure WP rules over [pgl_wp]. *)
Require Import guarding.internal.na_invariants_fork.
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From clutch.eris Require Export weakestpre.
From clutch.eris Require Import ectx_lifting.
From clutch.base_logic Require Export error_credits.
From clutch.prob Require Import distribution.
From lrust.lang Require Export lang.
From lrust.lang Require heap.   (* no Import: avoids iris WP notation clash *)
From lrust.util Require Import update non_atomic_cell_map atomic_lock_counter.
Set Default Proof Using "Type".
Import uPred.

Open Scope Z_scope.

(** [lrustGS] bundles the heap, lifetime/threadpool and atomic-lock-counter
    ghost state, an invariant interface (HasLc — required for eris's
    hfupd-based adequacy) and eris's error-credit ghost state. *)
Class lrustGS Σ := LRustGS {
  lrustGS_invGS : invGS_gen HasLc Σ;
  #[global] lrustGS_na_invGS :: na_invG Σ;
  #[global] lrustGS_atomic_lock_ctr_invGS :: alc_logicG Σ;
  #[global] lrustGS_gen_heapGS :: heap.heapGS Σ;
  #[global] lrustGS_ecGS :: ecGS Σ;
}.

(** The plain [invGS] needed by [heap.v] is the same as [lrustGS_invGS]
    (both are [invGS_gen HasLc Σ]). *)
Global Instance lrustGS_invGS_inst `{!lrustGS Σ} : invGS Σ
  := lrustGS_invGS.

Global Program Instance lrustGS_erisWpGS `{!lrustGS Σ} :
  erisWpGS lrust_prob_lang Σ := {
  erisWpGS_invGS := lrustGS_invGS;
  state_interp σ := heap.heap_ctx σ;
  err_interp ε := ec_supply ε;
}.

Global Opaque lrustGS_invGS.

(** * WP rules. *)

Open Scope R.

Section lifting.
  Context `{!lrustGS Σ}.

  (** [Rand]: uniform sampling over [0..N-1]. *)
  Lemma wp_rand E (N : Z) (Φ : val → iProp Σ) s :
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

  (** [Alloc]: fresh-block allocation. *)
  Lemma wp_alloc E (n : Z) s :
    (0 < n)%Z →
    {{{ True }}} Alloc (Lit (LitInt n)) @ s; E
    {{{ (l : loc) (sz : nat), RET LitV (LitLoc l);
        ⌜n = sz⌝ ∗ heap.heap_freeable l 1 sz ∗
        heap.heap_mapsto_vec l (repeat (LitV LitPoison) sz) }}}.
  Proof.
    iIntros (Hn Φ) "_ HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "Hσ".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=.
      rewrite bool_decide_eq_true_2 //.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iMod (heap.heap_alloc with "Hσ") as "(Hσ & Hf & Hl)"; [exact Hn| |].
    { intros m.
      assert (fresh_loc σ1 +ₗ m = (fresh_block σ1, m)) as ->;
        [rewrite /fresh_loc /shift_loc /=; f_equal; lia|].
      apply is_fresh_block. }
    iModIntro. iFrame "Hσ".
    iApply ("HΦ" $! _ (Z.to_nat n)). iFrame. iPureIntro. lia.
  Qed.

  (** [Read] from a non-atomic cell at read-state 0. *)
  Lemma wp_read E l v s :
    ↑non_atomic_cell_map.naN ⊆ E →
    {{{ ▷ heap.heap_mapsto l v }}} Read (Lit (LitLoc l)) @ s; E
    {{{ RET v; heap.heap_mapsto l v }}}.
  Proof.
    iIntros (HE Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "Hσ". iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.points_to_heap_reading0 with "Hl Hh")
      as "(Hl & Hh & %Hσl)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /= Hσl /=.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iModIntro. iSplitL "Hh Hf ato"; [iExists hF; by iFrame|].
    rewrite language.to_of_val /=. by iApply ("HΦ" with "Hl").
  Qed.

  (** [Write] to a non-atomic cell at read-state 0. *)
  Lemma wp_write E l v v' s :
    ↑non_atomic_cell_map.naN ⊆ E →
    {{{ ▷ heap.heap_mapsto l v }}} Write (Lit (LitLoc l)) (of_val v') @ s; E
    {{{ RET LitV LitPoison; heap.heap_mapsto l v' }}}.
  Proof.
    iIntros (HE Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "Hσ". iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.atomic_write _ _ _ v' with "Hl Hh")
      as "(%Hσl & Hl & Hh)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite to_of_val Hσl.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= to_of_val Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iModIntro. iSplitL "Hh Hf ato".
    { iExists hF. iFrame.
      iPureIntro. eauto using heap.heap_freeable_rel_stable. }
    by iApply ("HΦ" with "Hl").
  Qed.

  (** [Free]: deallocate a freeable region. *)
  Lemma wp_free E (n : Z) l vl s :
    ↑non_atomic_cell_map.naN ⊆ E →
    n = length vl →
    {{{ ▷ heap.heap_mapsto_vec l vl ∗ ▷ heap.heap_freeable l 1 (length vl) }}}
      Free (Lit (LitInt n)) (Lit (LitLoc l)) @ s; E
    {{{ RET LitV LitPoison; True }}}.
  Proof.
    iIntros (HE Hn Φ) "[>Hl >Hf] HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "Hσ".
    iMod (heap.heap_free with "Hσ Hl Hf") as "(%Hpos & %Hbnd & Hσ)"; [done..|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite bool_decide_eq_true_2 //.
      eexists (_, _).
      rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iModIntro. iFrame "Hσ". by iApply "HΦ".
  Qed.

End lifting.
