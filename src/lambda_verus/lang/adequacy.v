(** Probabilistic adequacy for [lrust_prob_lang] — HasLc port.

    The headline theorem [lrust_wp_pgl] extracts a concrete pgl mass
    bound on [exec n (e, σ)] from a WP triple, via [hfupd_soundness]
    over [HasLc].

    Upstream [clutch.eris.adequacy.glm_erasure] is declared inside
    [Section adequacy. Context `{!erisGS Σ}.], where [erisGS] fixes
    [Λ = clutch.prob_lang].  The proof body itself uses only
    language-generic machinery ([glm], [prim_step], [exec],
    [state_step], [get_active]), but the section context locks the
    language, so we can't reuse it as-is for [lrust_prob_lang].

    Resolution: we re-prove [glm_erasure] (and its two helpers
    [pgl_dbind'] / [pgl_dbind_adv']) locally, in a section over
    [erisWpGS lrust_prob_lang Σ].  Cases 1 and 2 of the original
    proof transfer verbatim.  Case 3 (state_step / tape erasure) is
    *unreachable* for [lrust_prob_lang] because it has no presampling
    tapes: [state_idx = Empty_set] and [get_active σ = []]
    ([lang.v:792-796]).  Inside [big_orL_mono] we obtain
    [α : Empty_set] as the loop variable and discharge with
    [destruct α].  This sidesteps the upstream dependence on
    [prob_lang.erasure.prim_coupl_step_prim] which is tape-specific.

    Reference: in our previous vendored eris (commit on
    [experiment/hlc-eris]), [glm_erasure] sat under
    [Context `{!erisWpGS Λ Σ}] and was polymorphic — once upstream
    lifts it out of [Section adequacy] this file can fall back to
    importing [clutch.eris.adequacy] and dropping the local copy. *)
From iris.proofmode Require Import base proofmode.
From iris.bi Require Import lib.fixpoint_mono.
From iris.base_logic.lib Require Import fancy_updates.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Import own invariants.
From iris.algebra Require Import auth lib.mono_nat numbers dfrac_agree.
From guarding.internal Require Import na_invariants_fork.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter.
From lrust.lifetime Require Import lifetime_full.
From clutch.common Require Export language exec.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export weakestpre.
From clutch.prob Require Export distribution graded_predicate_lifting.
From lrust.lang Require Export lang heap lifting time.
Import uPred.
Set Default Proof Using "Type".

Section adequacy.
  Context `{!erisWpGS lrust_prob_lang Σ}.

  (** Pure-monotonicity through [▷^k ◇ ⌜·⌝]. *)
  Local Lemma laterN_except_0_pure_mono k (P Q : Prop) :
    (P → Q) → ((▷^k ◇ ⌜P⌝ : iProp Σ)%I ⊢ ▷^k ◇ ⌜Q⌝).
  Proof. intros HPQ. apply bi.laterN_mono, bi.except_0_mono, bi.pure_mono, HPQ. Qed.

  (** Local hfupd-shape variants of [pgl_dbind] / [pgl_dbind_adv].
      The plain pgl versions (in [graded_predicate_lifting]) take a
      pure side condition; here we want to slot them into a proof
      where the side condition is gated by [|={0; ∅|}=> ▷^(S n) ◇ …]. *)
  Lemma pgl_dbind' `{Countable A, Countable A'} (L : nat)
    (f : A → distr A') (μ : distr A) (Rel : A → Prop) (T : A' → Prop)
    (ε ε' : R) n :
    ⌜(0 <= ε)%R⌝ -∗
    ⌜(0 <= ε')%R⌝ -∗
    ⌜pgl μ Rel ε⌝ -∗
    (∀ a, ⌜Rel a⌝ -∗ |={L; ∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T ε'⌝) -∗
    |={L; ∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + ε')%R⌝.
  Proof.
    iIntros (Hε Hε' HR) "H".
    iApply (hfupd_mono _ _ (▷^(S n) ◇ ⌜∀ a, Rel a → pgl (f a) T ε'⌝)%I).
    { apply (laterN_except_0_pure_mono (S n)). intros Hall.
      eapply pgl_dbind; eauto. }
    iIntros (a HRa). iApply ("H" with "[//]").
  Qed.

  Lemma pgl_dbind_adv' `{Countable A, Countable A'} (L : nat)
    (f : A → distr A') (μ : distr A) (Rel : A → Prop) (T : A' → Prop)
    (ε : R) (ε' : A → R) n :
    ⌜(0 <= ε)%R⌝ -∗
    ⌜exists r, forall a, (0 <= ε' a <= r)%R⌝ -∗
    ⌜pgl μ Rel ε⌝ -∗
    (∀ a, ⌜Rel a⌝ -∗ |={L; ∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T (ε' a)⌝) -∗
    |={L; ∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))%R⌝.
  Proof.
    iIntros (Hε [r Hr] HR) "H".
    iApply (hfupd_mono _ _ (▷^(S n) ◇ ⌜∀ a, Rel a → pgl (f a) T (ε' a)⌝)%I).
    { apply (laterN_except_0_pure_mono (S n)). intros Hall.
      eapply pgl_dbind_adv; [done|exists r; done|done|done]. }
    iIntros (a HRa). iApply ("H" with "[//]").
  Qed.

  Local Definition cfgO := (prodO (exprO lrust_prob_lang) (stateO lrust_prob_lang)).

  (** [glm_erasure] in hfupd form, specialised to [lrust_prob_lang].

      Cases 1 (thin-air ε-inflation) and 2 (prim_step) follow the
      upstream proof verbatim.  Case 3 (state_step) is unreachable
      because [get_active σ = []] for [lrust_prob_lang] (no
      presampling tapes); inside [big_orL_mono] the loop variable
      [α] has type [state_idx lrust_prob_lang = Empty_set], so we
      close with [destruct α]. *)
  (** Level-polymorphic [glm_erasure]: the inner glm payload AND
      the outer hfupd are quantified over the level [M], so we
      can specialize to whatever level the surrounding context
      demands.  Both the glm payload's content and the fixpoint
      predicate Φ carry [∀ M, |={M; ∅|}=> ▷^(M + S n) ◇ ⌜pgl⌝]. *)
  Lemma glm_erasure (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
      (n : nat) φ (ε : nonnegreal) :
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
        ∀ M : nat, |={M; ∅|}=> ▷^(M + S n) ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)
      ⊢ ∀ L : nat, |={L; ∅|}=> ▷^(L + S n) ◇ ⌜pgl (exec (S n) (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm /glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ -∗
                  ∀ L : nat, |={L; ∅|}=> ▷^(L + S n) ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   ∀ M : nat, |={M; ∅|}=> ▷^(M + S n) ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iApply ("H" $! ((_, _)) with "Hfix"). }
    clear Hv.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & %Hsum & %Hlift & H)|Hbad]] %Hv".

    (* Case 1: thin-air ε-inflation. *)
    - iIntros (L).
      iApply (hfupd_mono _ _ (▷^(L + S n) ◇ ⌜∀ ε' : nonnegreal,
          (ε'' < ε')%R → pgl (exec (S n) (e1, σ1)) φ ε'⌝)%I).
      { apply (laterN_except_0_pure_mono (L + S n)). intros Hall.
        eapply pgl_epsilon_limit; auto.
        - apply Rle_ge, cond_nonneg.
        - intros ε' Hε'.
          apply (Hall (mknonnegreal ε' (Rle_trans _ _ _ (cond_nonneg _) (Rlt_le _ _ Hε'))) Hε'). }
      iIntros (ε' Hε').
      destruct (decide (ε' < 1)%R) as [Hε'1|Hε'1]; last first.
      { iApply hfupd_intro. iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro. apply pgl_1. lra. }
      iApply (elim_fupd_hfupd_plain (L + S n) L ∅ ∅ _
        ⌜pgl (exec (S n) (e1, σ1)) φ ε'⌝); [lia|].
      iSplitL "H"; [iApply ("H" $! ε' with "[//]")|].
      iIntros (l Hl) "Hst".
      iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
      rewrite -(dret_id_left' (λ _ : (), exec (S n) (e1, σ1)) tt).
      have heq : (L + S n - L + l = S (n + l))%nat by lia.
      rewrite heq.
      iApply (hfupd_mono _ _
        (▷^(S (n + l)) ◇ ⌜pgl (dret tt ≫= λ _ : (), exec (S n) (e1, σ1)) φ (ε1' + ε2')⌝)%I).
      { apply (laterN_except_0_pure_mono (S (n + l))).
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
      iApply (pgl_dbind' l _ (dret tt) R' φ ε1' ε2' (n + l)).
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply tgl_implies_pgl, Hlift'. }
      iIntros (a HRa). destruct a.
      iSpecialize ("Hwand'" with "[//]").
      (* Hwand' : ⌜to_val e1 = None⌝ -∗ ∀ L', |={L';∅|}=> ▷^(L' + S n) ◇ ⌜pgl⌝.
         Apply to to_val proof, then specialize L' := l. *)
      iSpecialize ("Hwand'" with "[//]").
      iSpecialize ("Hwand'" $! l).
      rewrite dret_id_left.
      have heq2 : (l + S n = S (n + l))%nat by lia.
      rewrite heq2.
      iApply "Hwand'".

    (* Case 2: prim_step with adv composition. *)
    - iIntros (L).
      rewrite exec_Sn_not_final; [|by rewrite /is_final /= Hv].
      iApply (hfupd_mono _ _ (▷^(L + S n) ◇ ⌜pgl (prim_step e1 σ1 ≫= exec n) φ
        (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ))%R⌝)%I).
      { apply (laterN_except_0_pure_mono (L + S n)). intros Hpgl.
        eapply pgl_mon_grading; [|exact Hpgl]. done. }
      have heq0 : (L + S n = S (L + n))%nat by lia.
      rewrite heq0.
      iApply (pgl_dbind_adv' L (exec n) (prim_step e1 σ1) R φ
                              ε1 ε2 (L + n)).
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. exists r. intros a. split; [apply cond_nonneg | apply Hr]. }
      { done. }
      iIntros ([e' σ'] HRes).
      iApply (elim_fupd_hfupd_plain (S (L + n)) L ∅ ∅ _
        ⌜pgl (exec n (e', σ')) φ (ε2 (e', σ'))⌝); [lia|].
      iSplitL "H"; [iApply ("H" with "[//]")|].
      iIntros (l Hl) "Hst".
      iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
      rewrite -(dret_id_left' (λ _ : (), exec n (e', σ')) tt).
      have heq : (S (L + n) - L + l = S (n + l))%nat by lia.
      rewrite heq.
      iApply (hfupd_mono _ _ (▷^(S (n + l)) ◇
        ⌜pgl (dret tt ≫= λ _ : (), exec n (e', σ')) φ (ε1' + ε2')⌝)%I).
      { apply (laterN_except_0_pure_mono (S (n + l))).
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
      iApply (pgl_dbind' l _ (dret tt) R' φ ε1' ε2' (n + l)).
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply tgl_implies_pgl, Hlift'. }
      iIntros (a HRa). destruct a.
      iSpecialize ("Hwand'" with "[//]").
      iSpecialize ("Hwand'" $! l).
      rewrite dret_id_left.
      have heq2 : (l + S n = S (n + l))%nat by lia.
      rewrite heq2.
      iApply "Hwand'".

    (* Case 3: state_step — unreachable for [lrust_prob_lang]
       because [state_idx = Empty_set]. *)
    - iIntros (L).
      iDestruct (big_orL_mono _ (λ _ _,
                     |={L; ∅|}=> ▷^(L + S n)
                       ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I
                  with "Hbad") as "Hbad".
      { iIntros (i α _) "_". destruct α. }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      destruct α.
  Qed.

  (** WP → hfupd adequacy. Produces hfupd so the top-level extraction
      via [hfupd_soundness] works under [HasLc]. The credit count is
      [0]: all conversions go through [elim_fupd_hfupd_plain] or the
      equivalent tactics, without needing extra credits. *)
  Theorem wp_refRcoupl_hfupd k
      (ε : nonnegreal) (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n φ :
    state_interp k σ ∗ err_interp ε ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    ∀ L : nat, |={L; ⊤|}=> ▷^(L + n) ◇ ⌜pgl (exec n (e, σ)) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (k e σ ε); iIntros "(Hσ & Hε & Hwp)"; iIntros (L).
    - rewrite Nat.add_0_r /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (fupd_plain_hfupd' L ⊤ ⊤).
        iMod "Hwp" as "%". iModIntro.
        iPureIntro.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + iApply hfupd_intro. iApply laterN_intro.
        rewrite /bi_except_0. iRight.
        iPureIntro. apply pgl_dzero, Rle_ge, cond_nonneg.
    - destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (elim_fupd_hfupd_plain (L + S n) L ⊤ ⊤ ⌜φ v⌝
          ⌜pgl (exec (S n) (of_val v, σ)) φ ε⌝); [lia|].
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l Hl) "Hpure".
        iApply hfupd_intro.
        iDestruct "Hpure" as %Hφv.
        iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        erewrite exec_is_final; [|rewrite /= to_of_val //].
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iSpecialize ("Hwp" $! k with "[$Hσ $Hε]").
        iApply (elim_fupd_hfupd_plain (L + S n) L ⊤ ∅ _
          ⌜pgl (dbind (exec n) (prim_step e σ)) φ ε⌝
          with "[$Hwp]"); first lia.
        iIntros (l Hl) "Hlift".
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε2, ∀ M : nat, |={M; ∅|}=> ▷^(M + S n)
             ◇ ⌜pgl (exec n (e2, σ2)) φ ε2⌝)%I
            with "[%] [] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([e' σ'] ε2) "H". iIntros (M).
          have heqMS : (M + S n = S (M + n))%nat by lia.
          rewrite heqMS.
          iApply (laterN_hfupd 1). iNext.
          iApply (elim_fupd_hfupd_plain (M + n) M ∅ ⊤
            (state_interp (S k) σ' ∗ err_interp ε2 ∗ WP e' {{ v, ⌜φ v⌝ }})%I
            ⌜pgl (exec n (e', σ')) φ ε2⌝); first lia.
          iSplitL "H"; [iApply "H"|].
          iIntros (l' Hl') "(Hσ' & Hε' & Hwp')".
          (* Apply IH with level l'. *)
          iPoseProof ("IH" $! (S k) e' σ' ε2 with "[$Hσ' $Hε' $Hwp']") as "IHr".
          iSpecialize ("IHr" $! l').
          have heqM : (M + n - M + l' = l' + n)%nat by lia.
          rewrite heqM.
          iApply (hfupd_mono with "IHr").
          apply bi.laterN_mono, bi.except_0_mono, bi.pure_mono. done. }
        replace (prim_step e σ) with (step (e, σ)) by reflexivity.
        rewrite -exec_Sn_not_final; last by rewrite /is_final /to_final /= Heq.
        iPoseProof (glm_erasure e σ n φ ε Heq with "H") as "Heras".
        iSpecialize ("Heras" $! l).
        have heqL : (L + S n - L + l = l + S n)%nat by lia.
        rewrite heqL.
        iApply "Heras".
  Qed.

End adequacy.

(** Pre-ghost-state bundle: heap + freeable + na-inv (pool name) +
    alc + time + invGpreS, all the inG/preG instances we need to
    allocate the post-class [lrustGS Σ] from scratch. *)
Class lrustGpreS (Σ : gFunctors) := LrustGpreS {
  #[global] lrustGpreS_invGpreS :: invGpreS Σ;
  #[global] lrustGpreS_heap_inG :: inG Σ (authR heap.heapUR);
  #[global] lrustGpreS_heap_freeable_inG :: inG Σ (authR heap.heap_freeableUR);
  #[global] lrustGpreS_na_logicG :: na_logicG loc val Σ;
  #[global] lrustGpreS_na_invG :: na_invG Σ;
  #[global] lrustGpreS_alc_logicG :: alc_logicG Σ;
  #[global] lrustGpreS_timePreG :: timePreG Σ;
}.

(** Adds [ecGpreS] for eris's error credits. *)
Class lrustErisGpreS (Σ : gFunctors) := LrustErisGpreS {
  #[global] lrustErisGpreS_lrustGpreS :: lrustGpreS Σ;
  #[global] lrustErisGpreS_ecGpreS :: ecGpreS Σ;
}.

(** Top-level probabilistic adequacy, extracted via [hfupd_soundness].
    Works for any initial heap σ whose entries are all in the [RSt 0]
    state (which is the natural form for an "initial" heap — σ = ∅
    trivially satisfies it, as does anything built up by [init_mem]).

    The user-supplied WP proof is parameterised over [lrustGS Σ] —
    that's the post-allocation class that already bundles [invGS_gen
    HasLc], [heapGS], [na_invG], [alc_logicG], [ecGS], and [timeGS]. *)
Theorem lrust_wp_pgl `{!lrustErisGpreS Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n (ε : R) (K : nat) φ :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε)%R →
  (∀ `{!lrustGS Σ}, ⊢ £ K -∗ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ ε.
Proof.
  intros Hσ Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (K + n))).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)%R) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl. intros. eapply Rle_trans; [apply prob_le_1|done]. }
  iMod (hfupd_soundness HasLc K ⊤) as (Hinv) "(H£ & Hhfupd)".
  iApply "Hhfupd".
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  iMod (own_alloc ((●MN 2) ⋅ (mono_nat_lb 2))) as (γglob) "[Hglob _]";
    [by apply mono_nat_both_valid|].
  iMod (own_alloc (●MN 0)) as (γpers) "_";
    [by apply mono_nat_auth_valid|].
  iMod (own_alloc ((● 2%nat) ⋅ (◯ 2%nat))) as (γcum) "_";
    [by apply auth_both_valid|].
  iMod (own_alloc (to_frac_agree (A:=leibnizO bool) (1 / 2) true ⋅
                   to_frac_agree (A:=leibnizO bool) (1 / 2) true)) as (γbool) "[Hbool _]".
  { rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial. }
  iMod (own_alloc (to_frac_agree (A:=leibnizO nat) (1 / 2) 2%nat ⋅
                   to_frac_agree (A:=leibnizO nat) (1 / 2) 2%nat)) as (γsum) "_".
  { rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial. }
  pose (Htime := TimeG Σ _ _ _ _ γglob γpers γcum γbool γsum).
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustGS := LRustGS Σ Hinv _ _ Hheap Hec Htime).
  change ε with (nonneg ε').
  iPoseProof (wp_refRcoupl_hfupd 1 ε' e σ n φ) as "H".
  iSpecialize ("H" with "[Hs Hf H£ Hvγ Hfγ Hpool Hctr Hbool Hglob]").
  { rewrite /state_interp /= /heap.heap_ctx.
    iSplitR "Hs Hf H£"; last first.
    { iFrame "Hs". iPoseProof (Hwp HlrustGS) as "Hwp'".
      iApply ("Hwp'" with "H£ Hf"). }
    iSplitL "Hvγ Hfγ Hpool Hctr".
    { iExists ∅. iFrame "Hvγ Hfγ".
      iSplit.
      { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
        by rewrite lookup_empty in Hbad. }
      rewrite /heap.heap_ato_ctx. iFrame. }
    iLeft. iFrame "Hbool Hglob". iPureIntro. lia. }
  iApply ("H" $! K).
Qed.
