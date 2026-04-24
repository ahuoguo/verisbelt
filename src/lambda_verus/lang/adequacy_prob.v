(** Probabilistic adequacy for [lrust_prob_lang] — HasLc port.

    Claims the eris-style pgl adequacy theorem:

      0 ≤ ε  →
      (∀ [lrustErisGS Σ], ⊢ ↯ε -∗ WP e {{ v, ⌜φ v⌝ }})
      →  pgl (exec n (e, σ)) φ ε

    After the iris MR !1171 port, the internal currency is
    [hfupd] (half-fupd) rather than [step_fupdN] — this is what lets
    the forall-commutation inside [pgl_dbind'] and [glm_erasure]
    go through under [HasLc]. The outer extraction uses
    [hfupd_soundness]. *)
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.prelude Require Import options.
From eris.common Require Export language exec.
From eris.base_logic Require Export error_credits.
From eris.eris Require Export weakestpre adequacy.
From eris.prob Require Export distribution graded_predicate_lifting.
From lrust.lang Require Export prob_lang heap_prob.
Import uPred.
Set Default Proof Using "Type".

Section adequacy.
  Context `{!erisWpGS lrust_prob_lang Σ}.

  (** WP → hfupd adequacy. Produces hfupd so the top-level extraction
      via [hfupd_soundness] works under [HasLc]. The credit count is
      [0]: all conversions go through [elim_fupd_hfupd_plain] or the
      equivalent tactics, without needing extra credits. *)
  Theorem wp_refRcoupl_hfupd
      (ε : nonnegreal) (e : syntax.expr) (σ : syntax.state) n φ :
    state_interp σ ∗ err_interp ε ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    |={0; ⊤|}=> ▷^n ◇ ⌜pgl (exec n (e, σ)) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ ε); iIntros "(Hσ & Hε & Hwp)".
    - rewrite /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (fupd_plain_hfupd' 0 ⊤ ⊤).
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        rewrite to_of_val.
        iPureIntro.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + iApply hfupd_intro. simpl.
        rewrite /bi_except_0. iRight. rewrite Heq.
        iPureIntro. apply pgl_dzero, Rle_ge, cond_nonneg.
    - destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (elim_fupd_hfupd_plain (S n) 0 ⊤ ⊤ ⌜φ v⌝
          ⌜pgl (exec (S n) (of_val v, σ)) φ ε⌝); [lia|].
        iSplitL; [iApply "Hwp"|].
        iIntros (l Hl) "Hpure". assert (l = 0%nat) as -> by lia.
        iApply hfupd_intro.
        iDestruct "Hpure" as %Hφv.
        iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        erewrite exec_is_final; [|rewrite /= to_of_val //].
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iSpecialize ("Hwp" with "[$Hσ $Hε]").
        iApply (elim_fupd_hfupd_plain (S n) 0 ⊤ ∅ _
          ⌜pgl (dbind (exec n) (ectx_language.prim_step e σ)) φ ε⌝
          with "[$Hwp]"); first lia.
        iIntros (l Hl) "Hlift". assert (l = 0%nat) as -> by lia.
        rewrite Nat.add_0_r. replace (S n - 0)%nat with (S n) by lia.
        (* Convert glm's payload [▷ |={∅,⊤}=> state*err*WP] into the
           hfupd continuation expected by [glm_erasure]. *)
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε2, |={0; ∅|}=> ▷^(S n)
             ◇ ⌜pgl (exec n (e2, σ2)) φ ε2⌝)%I
            with "[%] [] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([e' σ'] ε2) "H".
          (* Goal: |={0;∅|}=> ▷^(S n) ◇ ⌜pgl (exec n (e', σ')) φ ε2⌝
             H : ▷ |={∅,⊤}=> state_interp σ' ∗ err_interp ε2 ∗ WP e' {{...}} *)
          iApply (laterN_hfupd 1). iNext.
          iApply (elim_fupd_hfupd_plain n 0 ∅ ⊤
            (state_interp σ' ∗ err_interp ε2 ∗ WP e' {{ v, ⌜φ v⌝ }})%I
            ⌜pgl (exec n (e', σ')) φ ε2⌝ with "[$H]"); first lia.
          iIntros (l Hl') "(Hσ & Hε & Hwp)".
          assert (l = 0%nat) as -> by lia.
          rewrite Nat.add_0_r. replace (n - 0)%nat with n by lia.
          iApply ("IH" with "[$Hσ $Hε $Hwp]"). }
        change (ectx_language.prim_step e σ) with (step (e, σ)).
        rewrite -exec_Sn_not_final; last by rewrite /is_final /= Heq.
        iApply (glm_erasure with "H"); [done|done].
  Qed.

End adequacy.

(** Top-level adequacy theorem, extracted via [hfupd_soundness]. *)
Theorem lrust_wp_pgl `{!ecGpreS Σ, !invGpreS Σ}
    (e : syntax.expr) (σ : syntax.state) n (ε : R) φ :
  0 <= ε →
  (∀ `{!lrustErisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ ε.
Proof.
  intros Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S n)).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl. intros. eapply Rle_trans; [apply prob_le_1|done]. }
  iMod (hfupd_soundness HasLc 0 ⊤) as (Hinv) "(_ & Hhfupd)".
  iApply "Hhfupd".
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (?) "[Hs Hf]"; [done|].
  set (HlrustErisGS := LrustErisGS Σ _ Hinv).
  change ε with (nonneg ε').
  iPoseProof (wp_refRcoupl_hfupd ε' e σ n φ) as "H".
  iApply "H".
  rewrite /state_interp /=.
  iSplitR; [done|]. iFrame "Hs".
  iApply Hwp. iFrame "Hf".
Qed.
