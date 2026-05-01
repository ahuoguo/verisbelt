(** Probabilistic adequacy for [lrust_prob_lang] — HasLc port.

    *** STATUS: not in build (see _CoqProject). ***

    Blocked on upstream clutch: [clutch.eris.adequacy.glm_erasure] is
    declared inside a [Section adequacy. Context `{!erisGS Σ}.] block,
    where [erisGS] fixes [Λ = prob_lang] (clutch's heap-lang). The proof
    body itself uses only language-generic machinery (glm, prim_step,
    exec, state_step, get_active), so a polymorphic version
    [glm_erasure (Λ : language) ...] is achievable. Once upstream
    exposes that (or we re-prove it locally), the rest of this file
    compiles unchanged.

    Reference: in our previous vendored eris (commit on
    [experiment/hlc-eris]), [glm_erasure] sat under
    [Context `{!erisWpGS Λ Σ}] and was polymorphic, which is why this
    file used to compile. *)
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import auth.
From guarding.internal Require Import na_invariants_fork.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter.
From lrust.lang Require adequacy.  (* for lrustGpreS — don't Import: iris WP clash *)
From clutch.common Require Export language exec.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export weakestpre adequacy.
From clutch.prob Require Export distribution graded_predicate_lifting.
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
        iMod "Hwp" as "%". iModIntro.
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
        iSplitL "Hwp"; [iApply "Hwp"|].
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
          ⌜pgl (dbind (exec n) (prim_step e σ)) φ ε⌝
          with "[$Hwp]"); first lia.
        iIntros (l Hl) "Hlift". assert (l = 0%nat) as -> by lia.
        rewrite Nat.add_0_r. replace (S n - 0)%nat with (S n) by lia.
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε2, |={0; ∅|}=> ▷^(S n)
             ◇ ⌜pgl (exec n (e2, σ2)) φ ε2⌝)%I
            with "[%] [] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([e' σ'] ε2) "H".
          iApply (laterN_hfupd 1). iNext.
          iApply (elim_fupd_hfupd_plain n 0 ∅ ⊤
            (state_interp σ' ∗ err_interp ε2 ∗ WP e' {{ v, ⌜φ v⌝ }})%I
            ⌜pgl (exec n (e', σ')) φ ε2⌝); first lia.
          iSplitL "H"; [iApply "H"|].
          iIntros (l' Hl') "(Hσ' & Hε' & Hwp')".
          assert (l' = 0%nat) as -> by lia.
          rewrite Nat.add_0_r. replace (n - 0)%nat with n by lia.
          iApply ("IH" with "[$Hσ' $Hε' $Hwp']"). }
        replace (prim_step e σ) with (step (e, σ)) by reflexivity.
        rewrite -exec_Sn_not_final; last by rewrite /is_final /to_final /= Heq.
        iApply (glm_erasure e σ n φ ε); [done|].
        iExact "H".
  Qed.

End adequacy.

(** Pre-ghost-state for the probabilistic adequacy theorem. Reuses
    [lrustGpreS] from [lang/adequacy.v] (heap + freeable + na-inv +
    alc + time + invGpreS) and adds [ecGpreS] for eris's error
    credits. *)
Class lrustErisGpreS (Σ : gFunctors) := LrustErisGpreS {
  #[global] lrustErisGpreS_lrustGpreS :: adequacy.lrustGpreS Σ;
  #[global] lrustErisGpreS_ecGS :: ecGpreS Σ;
}.

(** Top-level probabilistic adequacy, extracted via [hfupd_soundness].
    Works for any initial heap σ whose entries are all in the [RSt 0]
    state (which is the natural form for an "initial" heap — σ = ∅
    trivially satisfies it, as does anything built up by [init_mem]). *)
Theorem lrust_wp_pgl `{!lrustErisGpreS Σ}
    (e : syntax.expr) (σ : syntax.state) n (ε : R) φ :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  0 <= ε →
  (∀ `{!lrustErisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ ε.
Proof.
  intros Hσ Hε Hwp.
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
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  (* Heap ghost state. [non_atomic_map_alloc_heap] allocates the
     non-atomic-map for σ given the [RSt 0] side condition. *)
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustErisGS := LrustErisGS Σ Hec Hinv Hheap _ _).
  change ε with (nonneg ε').
  iPoseProof (wp_refRcoupl_hfupd ε' e σ n φ) as "H".
  iApply "H".
  (* state_interp σ = heap_ctx σ — assemble from the allocated pieces. *)
  rewrite /state_interp /= /heap.heap_ctx.
  iSplitL "Hvγ Hfγ Hpool Hctr".
  { iExists ∅. iFrame "Hvγ Hfγ".
    iSplit.
    { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
      by rewrite lookup_empty in Hbad. }
    rewrite /heap.heap_ato_ctx. iFrame. }
  iFrame "Hs". iApply Hwp. iFrame "Hf".
Qed.
