(** Lifting lemmas for [lrust_prob_lang]'s eris-based WP.

    Defines the [lrustGS] resource bundle, plumbs it as the canonical
    [erisWpGS] instance with [state_interp σ := heap_ctx σ], and
    derives the heap and pure WP rules over [pgl_wp]. *)
Require Import guarding.internal.na_invariants_fork.
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From clutch.eris Require Export weakestpre.
From clutch.eris Require Import ectx_lifting lifting.
From clutch.base_logic Require Export error_credits.
From clutch.prob Require Import distribution.
From lrust.lang Require Export lang time.
From lrust.lang Require heap.   (* no Import: avoids iris WP notation clash *)
From lrust.util Require Import update non_atomic_cell_map atomic_lock_counter.
From guarding Require Import guard.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".
Import uPred.

Open Scope Z_scope.

(** [lrustGS] bundles the heap, lifetime/threadpool and atomic-lock-counter
    ghost state, an invariant interface (HasLc — required for eris's
    [fupd_finally]-based adequacy, iris MR 1217), eris's error-credit
    ghost state, and the time-receipt ghost state.

    [timeGS] gives access to the persistent and cumulative time-receipt
    resources [⧖n] / [⧗n] used by the typing layer to pay for the
    later-credit cascade in nested [ty_gho] / [ty_gho_pers] depths.
    The actual *minting* of credits via [wp_persistent_time_receipt]
    relies on [HasLc] later credits — see [time.v] for the time-step
    invariant and the credit-extraction lemmas. *)
Class lrustGS Σ := LRustGS {
  lrustGS_invGS : invGS_gen HasLc Σ;
  #[global] lrustGS_na_invGS :: na_invG Σ;
  #[global] lrustGS_atomic_lock_ctr_invGS :: alc_logicG Σ;
  #[global] lrustGS_gen_heapGS :: heap.heapGS Σ;
  #[global] lrustGS_ecGS :: ecGS Σ;
  #[global] lrustGS_gen_timeGS :: timeGS Σ;
}.

(** The plain [invGS] needed by [heap.v] is the same as [lrustGS_invGS]
    (both are [invGS_gen HasLc Σ]). *)
Global Instance lrustGS_invGS_inst `{!lrustGS Σ} : invGS Σ
  := lrustGS_invGS.

(** [state_interp n σ] bundles the heap with the per-step
    [time_interp n] component.  The step index [n] is advanced by
    the WP framework on each [prim_step] (eris-lc threads it
    through [pgl_wp_pre]).  This is what lets
    [wp_persistent_time_receipt_lc] open [time_ctx] under a step
    and extract a fresh [⧖(d+1)] given an external [⧗1]. *)
Global Program Instance lrustGS_erisWpGS `{!lrustGS Σ} :
  erisWpGS lrust_prob_lang Σ := {
  erisWpGS_invGS := lrustGS_invGS;
  state_interp n σ := (heap.heap_ctx σ ∗ time_interp n)%I;
  err_interp ε := ec_supply ε;
  num_laters_per_step n := sum_advance_credits (n + 1);
}.
Next Obligation.
  iIntros (Σ ? n σ) "[$ Ht]".
  iMod (time_interp_step with "Ht") as "$". done.
Qed.

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
    iIntros (ns σ1) "[Hσ Ht]". iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose". iSplit.
    { iPureIntro. rewrite /head_reducible /=.
      rewrite bool_decide_eq_true_2 //.
      eexists (_, _). apply dmap_pos. exists 0%fin. split; first done.
      apply dunifP_pos. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dmap_pos in Hstep as (n & [= -> ->] & _).
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "Hσ Ht". by iApply "HΦ".
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
    iIntros (ns σ1) "[Hσ Ht]".
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
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "Hσ Ht".
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
    iIntros (ns σ1) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.points_to_heap_reading0 with "Hl Hh")
      as "(Hl & Hh & %Hσl)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /= Hσl /=.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iSplitL "Hh Hf ato Ht"; [iSplitR "Ht"; [iExists hF; by iFrame|by iFrame]|].
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
    iIntros (ns σ1) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.atomic_write _ _ _ v' with "Hl Hh")
      as "(%Hσl & Hl & Hh)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite to_of_val Hσl.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= to_of_val Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iSplitL "Hh Hf ato Ht".
    { iSplitR "Ht"; last by iFrame. iExists hF. iFrame.
      iPureIntro. eauto using heap.heap_freeable_rel_stable. }
    by iApply ("HΦ" with "Hl").
  Qed.

  (** [Read] through a leaf-guard:  given an abstract resource [G]
      gated by a leaf-guard [G &&{↑NllftG; d}&&> ((l,c) #↦ v)], spend
      [£d] later credits and consume [G] to read [v] from the cell.
      [G] is returned unchanged.

      Mirrors upstream verisbelt's [wp_read_na_guarded] (eris-port:
      atomic instead of non-atomic, since we stripped concurrency).
      Built on top of [heap.heap_read]. *)
  (** Scalar (cell-level) form. *)
  Lemma wp_read_guarded_cell E (l: loc) (cells: list cell_id) (w: val) (G: iProp Σ) d s :
    ↑non_atomic_cell_map.naN ⊆ E →
    {{{ (G &&{↑NllftG; d}&&> heap.heap_mapsto_cells_fancy l cells (heap.FVal w))
        ∗ G ∗ £d }}}
      Read (Lit (LitLoc l)) @ s; E
    {{{ RET w; G }}}.
  Proof.
    iIntros (HE Φ) "(#Hguard & HG & H£) HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (ns σ1) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.atomic_read with "H£ Hguard HG Hh")
      as (n) "(%Hσl & HG & Hh)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /= Hσl /=.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iSplitL "Hh Hf ato Ht".
    { iSplitR "Ht"; last by iFrame. iExists hF. by iFrame. }
    rewrite language.to_of_val /=. by iApply ("HΦ" with "HG").
  Qed.

  (** Vector form (mirroring upstream's [wp_read_na_guarded_cells_singleton]):
      takes the guard at the vec-form mapsto; case-splits on the cell-trace
      list internally, deriving False for non-singleton traces. *)
  Lemma wp_read_guarded_singleton E (l: loc) (c: list (list cell_id))
                                  (w: val) (G: iProp Σ) d s :
    ↑non_atomic_cell_map.naN ⊆ E →
    {{{ (G &&{↑NllftG; d}&&> heap.heap_mapsto_cells_val_vec l c [w])
        ∗ G ∗ £d }}}
      Read (Lit (LitLoc l)) @ s; E
    {{{ RET w; G }}}.
  Proof.
    iIntros (HE Φ) "(#Hguard & HG & H£) HΦ".
    destruct c as [|c0 [|c1 c2]].
    - (* c = [] : vec is False. *)
      iApply fupd_pgl_wp.
      iMod (guards_open_later _ _ E (↑NllftG) d with "Hguard HG")
        as "Hop"; first solve_ndisj.
      iMod (lc_fupd_elim_laterN with "H£ Hop") as ">[[] _]".
    - (* c = [c0] : vec is [cell ∗ True]; weaken guard. *)
      rewrite /heap.heap_mapsto_cells_val_vec /heap.heap_mapsto_cells_fancy_vec /=.
      iAssert (G &&{↑NllftG; d}&&>
               heap.heap_mapsto_cells_fancy l c0 (heap.FVal w))%I as "#Hguard'".
      { iApply (guards_weaken_rhs_sep_l with "Hguard"). }
      iApply (wp_read_guarded_cell with "[$Hguard' $HG $H£]"); [done|].
      iIntros "!> HG". by iApply "HΦ".
    - (* c = c0 :: c1 :: c2 : inner part is False. *)
      iApply fupd_pgl_wp.
      iMod (guards_open_later _ _ E (↑NllftG) d with "Hguard HG")
        as "Hop"; first solve_ndisj.
      iMod (lc_fupd_elim_laterN with "H£ Hop") as ">[Hvec _]".
      rewrite /heap.heap_mapsto_cells_val_vec /heap.heap_mapsto_cells_fancy_vec /=.
      iDestruct "Hvec" as "[_ []]".
  Qed.

  (** [Write] through a leaf-guard:  given an abstract resource [G]
      gated by [G &&{↑NllftG; d}&&> (l #↦_)] (cell-state) and the
      current cell mapsto [l #↦ v'], spend [£(3*d+1)] later credits
      and atomically write [v] over the cell.  [G] is returned with
      the new cell mapsto [l #↦ v].

      Mirrors upstream verisbelt's [wp_write_na_guarded] (eris-port:
      atomic instead of non-atomic).  Built on top of [heap.heap_write]. *)
  Lemma wp_write_guarded E (l: heap.cloc1) (w w': val) (G: iProp Σ) d s :
    ↑non_atomic_cell_map.naN ⊆ E →
    {{{ (G &&{↑NllftG; d}&&> heap.heap_complete_mapsto l) ∗ G
        ∗ heap.heap_complete_mapsto_fancy l (heap.FVal w') ∗ £(3*d+1) }}}
      Write (Lit (LitLoc l.1)) (of_val w) @ s; E
    {{{ RET LitV LitPoison;
        heap.heap_complete_mapsto_fancy l (heap.FVal w) ∗ G }}}.
  Proof.
    iIntros (HE Φ) "(#Hguard & HG & Hl & H£) HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (ns σ1) "[Hσ Ht]".
    iMod (heap.heap_write σ1 l w' w E G d HE with "H£ Hσ Hguard HG Hl")
      as "(%Hσl & Hσ & HG & Hl)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite to_of_val Hσl.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= to_of_val Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iSplitL "Hσ Ht"; [by iFrame|].
    iApply ("HΦ" with "[$Hl $HG]").
  Qed.

  (** Vector-form write through a leaf-guard.  Mirrors upstream's pattern
      via [mapsto_vec_untether_singleton]: takes the [cloc]-level vec
      fancy mapsto and the [cloc]-level leaf-guard, case-splits on the
      trace list (deriving False for non-singleton), and on the singleton
      case performs the atomic write returning the new vec fancy mapsto. *)
  Lemma wp_write_guarded_singleton E (l: loc) (c: list (list cell_id))
                                   (w w': val) (G: iProp Σ) d s :
    ↑non_atomic_cell_map.naN ⊆ E →
    {{{ (G &&{↑NllftG; d+1}&&> heap.heap_complete_mapsto_vec (l, c)) ∗ G
        ∗ heap.heap_complete_mapsto_fancy_vec (l, c) [heap.FVal w']
        ∗ £(3*(d+1)+1) }}}
      Write (Lit (LitLoc l)) (of_val w) @ s; E
    {{{ RET LitV LitPoison;
        heap.heap_complete_mapsto_fancy_vec (l, c) [heap.FVal w] ∗ G }}}.
  Proof.
    iIntros (HE Φ) "(#Hguard & HG & Hvec & H£) HΦ".
    destruct c as [|c0 [|c1 c2]].
    - (* c = [] : vec is False. *)
      rewrite /heap.heap_complete_mapsto_fancy_vec /=.
      iDestruct "Hvec" as %[].
    - (* c = [c0] : singleton, unfold to scalar and apply wp_write_guarded. *)
      rewrite /heap.heap_complete_mapsto_vec /heap.heap_complete_mapsto_vec' /=.
      rewrite /heap.heap_complete_mapsto_fancy_vec /heap.heap_complete_mapsto_fancy_vec' /=.
      iDestruct "Hvec" as "[Hl _]".
      iAssert (G &&{↑NllftG; d+1}&&> heap.heap_complete_mapsto (l, c0))%I as "#Hguard'".
      { iApply (guards_weaken_rhs_sep_l with "Hguard"). }
      iApply (wp_write_guarded _ (l, c0) w w' G (d+1) with "[$Hguard' $HG $Hl $H£]");
        [done|].
      iIntros "!> [Hl HG]". iApply "HΦ". iFrame "HG".
      iSplit; last done. iFrame "Hl".
    - (* c = c0 :: c1 :: c2 : inner part is False. *)
      rewrite /heap.heap_complete_mapsto_fancy_vec /=.
      iDestruct "Hvec" as "[_ []]".
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
    iIntros (ns σ1) "[Hσ Ht]".
    iMod (heap.heap_free with "Hσ Hl Hf") as "(%Hpos & %Hbnd & Hσ)"; [done..|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite bool_decide_eq_true_2 //.
      eexists (_, _).
      rewrite dret_1_1 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "Hσ Ht". by iApply "HΦ".
  Qed.

  Lemma wp_cumulative_time_receipt1 E e Φ s :
    to_val e = None → ↑advN ∪ ↑timeN ⊆ E →
    time_ctx -∗
    (⧗1 -∗ WP e @ s; E ∖ ↑advN {{ Φ }}) -∗
    WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnv Hmask) "#TIME Hwp".
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (ns σ1 ε1) "[[Hσ Ht] Hε]".
    iMod persistent_time_receipt_0 as "⧖0".
    iMod (step_cumulative_time_receipt _ ns 0 with "TIME Ht ⧖0")
      as "(%Hns1 & Htm1 & EnFalse & Hcum2 & Hclose)"; first set_solver.
    (* Split ⧗(0+2) = ⧗2 into ⧗1 + ⧗1, give one to user. *)
    replace (0 + 2)%nat with (1 + 1)%nat by lia.
    iDestruct "Hcum2" as "[⧗1 _]".
    iSpecialize ("Hwp" with "⧗1").
    rewrite pgl_wp_unfold /pgl_wp_pre /= Hnv.
    iMod ("Hwp" $! (ns - 1)%nat σ1 ε1 with "[$Hσ $Htm1 $Hε]") as "Hwp".
    iModIntro.
    iApply (glm_mono_pred with "[Hclose EnFalse] Hwp").
    iIntros ([e2 σ2] ε2) "Hwp".
    iIntros "credit". rewrite /num_laters_per_step /=.
    (* Outer's credit: £(S sum_advance_credits(ns+1)) = £1 + £(sum_advance_credits(ns+1)). *)
    iDestruct "credit" as "[Hc1 credit]".
    rewrite (sum_advance_credits_ge1 (ns + 1)); last by lia.
    (* credit : £(2^(S(ns+1)) * ac(2^(S(ns+1))) + sum_advance_credits(ns+1-1))
       = £(2^(S(S ns)) * ac(2^(S(S ns))) + sum_advance_credits ns) *)
    iDestruct "credit" as "[credit1 credit2]".
    replace (ns + 1 - 1)%nat with ns by lia.
    iCombine "credit2 Hc1" as "credit_inner".
    (* credit_inner : £(S sum_advance_credits ns) = £(S num_laters_per_step (ns-1)) *)
    rewrite /num_laters_per_step /=.
    replace (ns - 1 + 1)%nat with ns by lia.
    iMod ("Hwp" with "credit_inner") as "Hwp".
    iIntros "!> !>". iMod "Hwp". iModIntro.
    (* After peeling first step-fupd, Hwp : |={∅}▷=>^(num_laters_per_step (ns-1)) |={∅,E∖↑advN}=> ... *)
    (* Goal: |={∅}▷=>^(num_laters_per_step ns) |={∅,E}=> ... *)
    iApply (step_fupdN_nmono (sum_advance_credits ns)).
    { rewrite /num_laters_per_step. lia. }
    iApply (step_fupdN_wand with "Hwp"). iIntros ">([Hheap Ht] & Hε & Hwp_inner)".
    replace (S (ns - 1)) with ns by lia.
    iMod ("Hclose" with "[$Ht $EnFalse credit1]") as "Ht".
    { iApply (lc_weaken with "credit1").
      replace (ns + 1)%nat with (S ns) by lia.
      reflexivity. }
    iModIntro. iFrame "Hheap Ht Hε".
    iApply (pgl_wp_mask_mono with "Hwp_inner"). set_solver.
  Qed.

  Lemma wp_persistent_time_receipt n E e Φ s :
    to_val e = None → ↑advN ∪ ↑timeN ⊆ E →
    time_ctx -∗
    ⧖n -∗
    (£(advance_credits n) -∗ ⧖(S n) -∗ WP e @ s; E ∖ ↑advN {{ Φ }}) -∗
    WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnv Hmask) "#TIME #⧖n Hwp".
    iApply (wp_cumulative_time_receipt1 with "TIME"); [done|done|].
    iIntros "⧗1". iApply fupd_pgl_wp.
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗1 ⧖n")
      as "[#⧖Sn H£]"; first solve_ndisj.
    iModIntro.
    replace (n + 1)%nat with (S n) by lia.
    by iApply ("Hwp" with "H£ ⧖Sn").
  Qed.

  Lemma wp_write_guarded_more_credits E (l: heap.cloc1)
        (w w': val) (G: iProp Σ) d d' s :
    ↑non_atomic_cell_map.naN ∪ ↑timeN ⊆ E →
    time_ctx -∗
    {{{ (G &&{↑NllftG; d}&&> heap.heap_complete_mapsto l) ∗ G
        ∗ heap.heap_complete_mapsto_fancy l (heap.FVal w') ∗ £(3*d+1) ∗ ⧖d' }}}
      Write (Lit (LitLoc l.1)) (of_val w) @ s; E
    {{{ RET LitV LitPoison;
        heap.heap_complete_mapsto_fancy l (heap.FVal w) ∗ G ∗ £(6*d' + 1) }}}.
  Proof.
    iIntros (HE) "#TIME". iIntros (Φ) "!> (#Hguard & HG & Hl & H£ & #⧖d') HΦ".
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (ns σ1 ε1) "[[Hσ Ht] Hε]".
    iMod cumulative_time_receipt_0 as "⧗0".
    iMod (time_receipt_le' with "TIME Ht ⧖d' ⧗0") as "[%Htime [Ht _]]";
      first solve_ndisj.
    assert (↑non_atomic_cell_map.naN ⊆ E) as HE_na by solve_ndisj.
    iMod (heap.heap_write σ1 l w' w E G d HE_na with "H£ Hσ Hguard HG Hl")
      as "(%Hσl & Hσ & HG & Hl)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iApply (glm_prim_step (Write (Lit (LitLoc l.1)) (of_val w)) σ1).
    iExists _, nnreal_zero, ε1.
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (_, _). rewrite /head_step_prob /= to_of_val Hσl.
      rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iSplit; [iPureIntro; simpl; lra|].
    iSplit.
    { iPureIntro. eapply pgl_pos_R, pgl_trivial. simpl; lra. }
    iIntros (e2 σ2 [_ Hpos]) "!>".
    (* Determinism: prim_step on Write at known location is dret. *)
    simpl in Hpos.
    assert (head_reducible (Write (Lit (LitLoc l.1)) (of_val w)) σ1) as Hred.
    { eexists (_, _). rewrite /head_step_prob /= to_of_val Hσl.
      rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    pose proof (head_prim_step_eq _ _ Hred) as Heq.
    rewrite Heq in Hpos.
    rewrite /head_step /= /head_step_prob /= to_of_val Hσl in Hpos.
    apply dret_pos in Hpos. inversion Hpos. subst e2 σ2.
    iIntros "credit".
    (* credit : £(S (num_laters_per_step ns)).  Extract £(6*d'+1). *)
    assert (6*d' + 1 ≤ S (sum_advance_credits (ns + 1)))%nat as Hbound.
    { assert (sum_advance_credits (ns + 1) =
              ((2 ^ S (ns+1)) * advance_credits (2 ^ S (ns+1))
                + sum_advance_credits ns)%nat) as HSAC.
      { rewrite (sum_advance_credits_ge1 (ns + 1)); last lia.
        replace (ns + 1 - 1)%nat with ns by lia. reflexivity. }
      rewrite HSAC.
      assert (d' ≤ 2 ^ S (ns+1))%nat as Hd'.
      { rewrite Nat.add_0_r in Htime.
        eapply Nat.le_trans; [exact Htime|].
        apply Nat.pow_le_mono_r; lia. }
      assert (10 ≤ advance_credits (2 ^ S (ns+1)))%nat as Hac10.
      { rewrite /advance_credits. lia. }
      nia. }
    iDestruct (lc_weaken (6*d' + 1) with "credit") as "H£6"; first exact Hbound.
    iApply (step_fupdN_le 1 (S (num_laters_per_step ns))); [lia|done|].
    iApply step_fupdN_intro; [done|]. simpl.
    iNext. iMod "Hclose" as "_".
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "Hε".
    iSplitL "Hσ Ht"; [by iFrame|].
    change (Lit LitPoison) with (of_val (LitV LitPoison)).
    iApply pgl_wp_value'. iApply ("HΦ" with "[$Hl $HG $H£6]").
  Qed.

End lifting.

(** Tactic mirroring [clutch.prob_lang.class_instances.solve_pure_exec]:
    use [case_match] + [simplify_eq] to destructure the [match]
    expressions inside [head_step_prob], then close with [dret_1_1]. *)
Local Ltac solve_exec_puredet :=
  intros σ; simpl; (repeat case_match); simplify_eq;
  rewrite dret_1_1 //.

Local Ltac solve_exec_safe :=
  intros σ; eexists (_, σ); simpl;
  (repeat case_match); simplify_eq;
  rewrite dret_1_1 //; lra.

Local Ltac solve_pure_exec :=
  intros _; apply nsteps_once;
  apply pure_head_step_pure_step;
  constructor; [solve_exec_safe | solve_exec_puredet].

(** Beta reduction: [App (Rec f xl e) (of_val <$> vs) → e[f, xl ↦ ...]]. *)
Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) :=
  as_rec : e = Rec f xl erec.
Global Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Global Instance AsRec_rec_val f xl e `{!Closed (f :b: xl +b+ []) e} :
  AsRec (of_val (RecV f xl e)) f xl e := eq_refl.
Global Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

(** [AsVal e] says [e] is the [of_val] of some value — used in [pure_rec]
    to assert all argument expressions are values. *)
Class AsVal (e : expr) := as_val : ∃ v, of_val v = e.
Global Instance AsVal_lit l : AsVal (Lit l).
Proof. by exists (LitV l). Qed.
Global Instance AsVal_of_val v : AsVal (of_val v).
Proof. by exists v. Qed.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) :=
  do_subst_l : subst_l xl esl e = Some er.
Global Hint Extern 0 (DoSubstL [] [] _ _) => exact eq_refl : typeclass_instances.
Global Hint Extern 1 (DoSubstL (_ :: _) (_ :: _) _ _) =>
  rewrite /DoSubstL; cbn; reflexivity : typeclass_instances.

(** Recursive [DoSubstL] step.  Lets typeclass resolution peel a single
    [(b, e)] off the front and recurse on the remaining tail —
    crucially, the tail need not be syntactic [_ :: _], so this works
    when the tail is a [plistc binder _] / [map of_val plistc] that
    only reduces via a separate base-case instance (e.g.
    [function.do_subst_plv]). *)
Global Instance do_subst_l_cons_step (b : binder) (e : expr)
    (bl : list binder) (esl : list expr) (body result : expr) :
  DoSubstL bl esl body result →
  DoSubstL (b :: bl) (e :: esl) body (subst' b e result) | 5.
Proof. rewrite /DoSubstL /= => ->. done. Qed.

(** Companion typeclass instances for [pure_rec] resolution on
    applications of the form [(rec: f xl := e)%V (map of_val vsl)]
    where [vsl] is a *symbolic* [vec val (length xl)] (typical of
    continuation bodies in [typing/cont.v]).

    Upstream verusbelt (iris-WP) got these "for free" via
    [iris.program_logic.{language,lifting}]: the iris-side
    [Class AsVal] has [Global Instance as_vals_of_val :
    TCForall AsVal (of_val <$> vs)] (language.v:271), and iris's
    [lifting.v] provides [DoSubstL xl (of_val <$> vec_to_list vsl)
    e (subst_v xl vsl e)] as a global instance.  When ported to pgl_wp,
    we re-defined [AsVal] [DoSubstL] locally above without those companions.

    Without these instances, [wp_rec] / [wp_pure (App _ _)] fires
    [pure_rec] which then can't resolve [TCForall AsVal (map of_val
    vsl)] (Coq's typeclass search doesn't unfold [map] for symbolic
    [vsl]) and can't resolve [DoSubstL] (the default [Hint Extern]
    runs [cbn; reflexivity] which can't reduce [subst_l] on a
    symbolic vec).  The two instances + the [Closed]-by-assumption
    hint below close all three holes. *)
Global Instance TCForall_AsVal_map_of_val (vl : list val) :
  TCForall AsVal (map of_val vl).
Proof. induction vl as [|v vl IH]; constructor; [exact _|exact IH]. Qed.

Global Instance TCForall_AsVal_vec_of_val {n} (vl : vec val n) :
  TCForall AsVal (map of_val (vec_to_list vl)).
Proof. apply TCForall_AsVal_map_of_val. Qed.

Global Instance do_subst_l_rec_vec (kb : binder) (bl : list binder)
    (k : val) (vsl : vec val (length bl)) e :
  DoSubstL (kb :: bl) (of_val k :: map of_val (vec_to_list vsl)) e
           (subst' kb (of_val k) (subst_v bl vsl e)).
Proof.
  rewrite /DoSubstL /=.
  pose proof (subst_v_eq bl vsl e) as Heq.
  unfold subst_v in *. rewrite -Heq /=. done.
Qed.

(** Let typeclass search use [Closed] *hypotheses* from the proof
    context.  [pure_rec] has a [Closed (f :b: xl +b+ []) erec]
    premise; for a *symbolic* [erec] (typical of continuation
    bodies) the default [solve_closed] tactic can't fire, but the
    Coq-level [Closed] hypothesis bound at the lemma statement is
    available to [assumption]. *)
Global Hint Extern 1 (Closed _ _) => assumption : typeclass_instances.

Global Instance pure_rec e f xl erec erec' el :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ? Hsubst.
  assert (Hguard : Forall (λ ei, is_Some (to_val ei)) el ∧
                   Closed (f :b: xl +b+ []) erec).
  { split; [|done]. eapply Forall_impl; [exact Hel|].
    intros e' [v <-]. eexists. apply to_of_val. }
  intros _. apply nsteps_once. apply pure_head_step_pure_step.
  assert (Hgoal : ∀ σ,
    head_step_prob (App (Rec f xl erec) el) σ = dret (erec', σ)).
  { intros σ. rewrite /head_step_prob.
    rewrite (bool_decide_eq_true_2 _ Hguard). by rewrite Hsubst. }
  constructor.
  - intros σ. eexists (erec', σ).
    change (head_step_prob (App (Rec f xl erec) el) σ (erec', σ) > 0).
    rewrite Hgoal. rewrite dret_1_1 //. lra.
  - intros σ.
    change (head_step_prob (App (Rec f xl erec) el) σ (erec', σ) = 1).
    rewrite Hgoal. apply dret_1_1; reflexivity.
Qed.

Global Instance pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (lit_of_bool (bool_decide (n1 ≤ n2)%Z))).
Proof.
  intros _. apply nsteps_once. apply pure_head_step_pure_step.
  constructor.
  - intros σ. eexists (_, σ). simpl. (repeat case_match); simplify_eq.
    rewrite dret_1_1 //. lra.
  - intros σ. simpl. (repeat case_match); simplify_eq.
    rewrite dret_1_1 //.
Qed.

Global Instance pure_eq_int z1 z2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt z1)) (Lit (LitInt z2)))
                  (Lit (lit_of_bool (bool_decide (z1 = z2)%Z))).
Proof.
  intros _. apply nsteps_once. apply pure_head_step_pure_step.
  constructor.
  - intros σ. eexists (_, σ). simpl.
    destruct z1; cbn -[bool_decide]; by rewrite dret_1_1; first lra.
  - intros σ. simpl.
    destruct z1; cbn -[bool_decide]; by rewrite dret_1_1.
Qed.

Global Instance pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit (LitInt z1)) (Lit (LitInt z2)))
                  (Lit (LitInt (z1 + z2)%Z)).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit (LitInt z1)) (Lit (LitInt z2)))
                  (Lit (LitInt (z1 - z2)%Z)).
Proof. solve_pure_exec. Qed.

Global Instance pure_mult z1 z2 :
  PureExec True 1 (BinOp MultOp (Lit (LitInt z1)) (Lit (LitInt z2)))
                  (Lit (LitInt (z1 * z2)%Z)).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset l z :
  PureExec True 1 (BinOp OffsetOp (Lit (LitLoc l)) (Lit (LitInt z)))
                  (Lit (LitLoc (shift_loc l z))).
Proof. solve_pure_exec. Qed.

Global Instance pure_case (i : Z) e el :
  PureExec ((0 ≤ i)%Z ∧ el !! Z.to_nat i = Some e) 1
           (Case (Lit (LitInt i)) el) e | 10.
Proof.
  intros [Hi Heq]. apply nsteps_once. apply pure_head_step_pure_step.
  constructor.
  - intros σ. eexists (e, σ). simpl.
    rewrite (bool_decide_true _ Hi) Heq. rewrite dret_1_1 //. lra.
  - intros σ. simpl. rewrite (bool_decide_true _ Hi) Heq.
    apply dret_1_1; reflexivity.
Qed.

Global Instance pure_if (b : bool) e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof.
  intros _. destruct b; (apply nsteps_once; apply pure_head_step_pure_step;
    constructor; [intros σ; eexists (_, σ); simpl; rewrite dret_1_1 //; lra
                  |intros σ; simpl; apply dret_1_1; reflexivity]).
Qed.
