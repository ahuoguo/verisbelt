(** Probabilistic type soundness for [lrust_prob_lang].

    Bridges typed-program derivations to a pgl (probabilistic graded
    lifting) mass bound on [exec n].

    - [type_soundness]: the general typing-layer form, parameterised
      over [𝔅 : syn_type], a predicate transformer
      [tr : predl_trans' [] 𝔅], and a postcondition predicate
      [post : pred' (~~𝔅)].  Given a [typed_body] derivation with
      transformer [tr] and the source-level obligation
      [tr post -[] ⊤], conclude [pgl (exec n) (λ _, True) 0].
      Allocates [llft_ctx], [time_ctx], [invctx] inside the WP via
      [fupd_pgl_wp] and threads them into the [typed_body].

    - [type_soundness_trivial]: the [True]-transformer instantiation
      of [type_soundness].  Kept as a convenience corollary.

    - [type_soundness_val]: bridges [typed_val v ty a] — the typing
      layer's notion that value [v] inhabits semantic type [ty] at
      refinement [a] — to a pgl bound on [exec n (of_val v, σ)].
      Sanity-check that the bridge exposes the typed-instr WP and
      threads it through the [typed_body] obligation.

   ** Comparison with the upstream verusbelt [type_soundness] **

    Upstream verusbelt's [soundness.v] proves an operational-safety
    theorem (see [docker-contents/clean-src/.../soundness.v]):

        Theorem type_soundness `{!typePreG Σ} (main : val) σ t c :
          (∀ `{!typeG Σ}, typed_val main main_type c) →
          rtc erased_step ([main [exit_cont]%E], (∅, false)) (t, σ) →
          nonracing_threadpool t σ ∧
          (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
    
    Our [type_soundness] uses `pgl` instead of `rtc erased_step`

 *)

From iris.algebra Require Import frac dfrac_agree auth lib.mono_nat numbers.
From iris.base_logic.lib Require Import invariants own fancy_updates.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.common Require Import language exec.
From clutch.eris Require Import weakestpre.
From guarding.internal Require Import na_invariants_fork.
From lrust.util Require Import cancellable_na_invariants cancellable
                                 non_atomic_cell_map atomic_lock_counter.
From guarding.lib Require Import fractional cancellable.
From lrust.lifetime Require Import lifetime_full.
From lrust.lang Require Import adequacy proofmode notation lang heap lifting time.
From lrust.typing Require Import type programs.
Import uPred.
Set Default Proof Using "Type".

(** Pre-ghost-state bundle for [type_soundness]: extends
    [lrustErisGpreS] with the typing-layer pre-classes
    ([llft_logicGpreS], [frac_logicG], [ecInv_logicG],
    [cancellable_na_invariants.na_invG] for cnaInv_logicG, etc.). *)
Class typePreG (Σ : gFunctors) := PreTypeG {
  #[global] type_preG_lrustErisGpreS :: lrustErisGpreS Σ;
  #[global] type_preG_lftGS :: llft_logicGpreS Σ;
  #[global] type_preG_frac_logicG :: frac_logicG Σ;
  #[global] type_preG_ecInv_logicG :: ecInv_logicG Σ;
  #[global] type_preG_cna_invG :: cancellable_na_invariants.na_invG Σ;
  #[global] type_preG_agree_pairΣ :: inG Σ (dfrac_agreeR (leibnizO nat))
}.

Theorem type_soundness `{!typePreG Σ}
    {𝔅 : syn_type} (tr : predl_trans' [] 𝔅) (post : pred' (~~𝔅))
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  tr post -[] ⊤ →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ⊢ typed_body (𝔄l := []) (𝔅 := 𝔅) [] []
                   (InvCtx [] static AtomicClosed) [] +[] e tr) →
  pgl (exec n (e, σ)) (λ _, True) 0.
Proof.
  intros Hσ Htr Hbody.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (advance_credits 4 + 1 + n))).
  rewrite laterN_later -except_0_into_later.
  iMod (hfupd_soundness HasLc (advance_credits 4 + 1) ⊤) as (Hinv) "(H£ & Hhfupd)".
  iApply "Hhfupd".
  iMod (ec_alloc nnreal_zero) as (Hec) "[Hs _]"; [simpl; lra|].
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  (* Allocate time ghost state, keeping ALL fragments so we can
     install [time_ctx] for the SAME [timeGS] as state_interp uses. *)
  iMod (own_alloc ((●MN 2) ⋅ (mono_nat_lb 2))) as (γglob) "[Hglob Hglobf]";
    [by apply mono_nat_both_valid|].
  iMod (own_alloc (●MN 0)) as (γpers) "Hpers";
    [by apply mono_nat_auth_valid|].
  iMod (own_alloc ((● 2%nat) ⋅ (◯ 2%nat))) as (γcum) "[HcumA HcumF]";
    [by apply auth_both_valid|].
  iMod (own_alloc (to_frac_agree (A:=leibnizO bool) (1 / 2) true ⋅
                   to_frac_agree (A:=leibnizO bool) (1 / 2) true)) as (γbool) "[Hbool HboolB]".
  { rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial. }
  iMod (own_alloc (to_frac_agree (A:=leibnizO nat) (1 / 2) 2%nat ⋅
                   to_frac_agree (A:=leibnizO nat) (1 / 2) 2%nat)) as (γsum) "[HsumA HsumB]".
  { rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial. }
  pose (Htime := TimeG Σ _ _ _ _ γglob γpers γcum γbool γsum).
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustGS := LRustGS Σ Hinv _ _ Hheap Hec Htime).
  (* Split credits: most for [time_ctx] storage, [£1] for [llft_alloc]. *)
  rewrite lc_split. iDestruct "H£" as "[H£time H£lft]".
  iAssert (£(2 * advance_credits 2))%I with "[H£time]" as "H£timeStorage".
  { iApply (lc_weaken with "H£time"). unfold advance_credits. lia. }
  (* Bridge to pgl via [wp_refRcoupl_hfupd]; the time-ctx, llft, and
     invctx invariants get allocated *inside* the WP, where [fupd_pgl_wp]
     lets us discharge [fupd] modalities (unlike the outer hfupd). *)
  iPoseProof (wp_refRcoupl_hfupd 1 nnreal_zero e σ n (λ _, True)) as "H".
  iSpecialize ("H" with "[-]"); last first.
  { iSpecialize ("H" $! (advance_credits 4 + 1)%nat). iApply "H". }
  rewrite /state_interp /= /heap.heap_ctx.
  iSplitR "Hs Hglobf HcumA Hpers H£timeStorage HsumA HboolB HsumB HcumF H£lft"; last first.
  { iFrame "Hs".
    iApply fupd_pgl_wp.
    iMod (inv_alloc timeN ⊤ (∃ n' m',
              own time_global_name (mono_nat_lb (n' + m')) ∗
              own time_cumulative_name (● n') ∗
              own time_persistent_name (●MN m') ∗
              £ (n' * advance_credits (n' + m')) ∗
              own time_sum_name (to_frac_agree (A:=leibnizO nat) (1/2)%Qp (n' + m')%nat))%I
            with "[Hglobf HcumA Hpers H£timeStorage HsumA]") as "#TIME_N".
    { iNext. iExists 2%nat, 0%nat. iFrame "HcumA Hpers HsumA".
      rewrite Nat.add_0_r. iFrame "Hglobf".
      iApply (lc_weaken with "H£timeStorage").
      unfold advance_credits. lia. }
    iMod (inv_alloc advN ⊤ (∃ n', enable time_enabled_bool_name true ∗
              own time_sum_name (to_frac_agree (A:=leibnizO nat) (1/2)%Qp (n' + 2 + n')%nat) ∗
              cumulative_time_receipt (n' + 2)%nat)%I
            with "[HboolB HsumB HcumF]") as "#TIME_A".
    { iNext. iExists 0%nat. simpl.
      iFrame "HboolB HsumB". rewrite /cumulative_time_receipt. iFrame. }
    iAssert (time_ctx) with "[]" as "#TIME".
    { iSplit; [iApply "TIME_N" | iApply "TIME_A"]. }
    iMod (llft_alloc with "H£lft") as (Hlft) "#LFT".
    pose (Hcna := {| cnaInv_na_inv_inG := type_preG_cna_invG |}).
    iMod (@invctx_alloc Σ _ _ _ Hcna ⊤) as (tid) "Hinvctx".
    pose (Htype := @TypeG Σ HlrustGS Hlft _ _ _).
    iPoseProof (Hbody Htype Hcna) as "Hb".
    iModIntro.
    iApply (pgl_wp_mono _ _ _ (λ _, cont_postcondition)).
    { iIntros (v) "_". iPureIntro. done. }
    iApply ("Hb" $! tid -[] ⊤ post []
              with "LFT TIME [] [] Hinvctx [] [] []").
    - iApply big_sepL_nil. done.
    - iApply big_sepL_nil. done.
    - iIntros (c Hin). by inversion Hin.
    - simpl; done.
    - iPureIntro. exact Htr. }
  iSplitL "Hvγ Hfγ Hpool Hctr".
  { iExists ∅. iFrame "Hvγ Hfγ".
    iSplit.
    { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
      by rewrite lookup_empty in Hbad. }
    rewrite /heap.heap_ato_ctx. iFrame. }
  iLeft. iFrame "Hbool Hglob". iPureIntro. lia.
Qed.

Theorem type_soundness_trivial `{!typePreG Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ⊢ typed_body (𝔄l := []) (𝔅 := unitₛ) [] []
                   (InvCtx [] static AtomicClosed) [] +[] e
                   (λ _ _ _, True%type)) →
  pgl (exec n (e, σ)) (λ _, True) 0.
Proof.
  intros Hσ Hbody.
  apply (type_soundness (𝔅 := unitₛ) (λ _ _ _, True%type)
                        (λ _ _, True%type) e σ n Hσ);
    [done|exact Hbody].
Qed.

Theorem type_soundness_val `{!typePreG Σ}
    {𝔄 : syn_type} (v : val) (a : ~~𝔄)
    (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ}, ∃ ty : type 𝔄, typed_val v ty a) →
  pgl (exec n (of_val v, σ)) (λ _, True) 0.
Proof.
  intros Hσ Hval.
  apply (type_soundness_trivial _ σ n Hσ).
  intros HtypeG HcnaInv.
  destruct (Hval HtypeG HcnaInv) as [ty Hty].
  pose proof (Hty [] [] (InvCtx [] static AtomicClosed)) as Hinstr.
  rewrite /typed_instr_ty /typed_instr in Hinstr.
  iIntros (tid xl mask post iκs)
          "LFT TIME E_ L_ Hinv _Hcctx Htctx _".
  iApply (pgl_wp_wand with "[-]").
  - iApply (Hinstr tid (λ _ _, True%type) mask iκs xl
            with "LFT TIME E_ L_ Hinv Htctx []").
    iPureIntro. done.
  - iIntros (v') "_". done.
Qed.
