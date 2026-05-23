(** Probabilistic adequacy for [lrust_prob_lang] — HasLc port,
    using iris MR 1217's [fupd_finally] modality directly.

    The headline theorem [lrust_wp_pgl] extracts a concrete pgl mass
    bound on [exec n (e, σ)] from a WP triple via
    [fupd_finally_soundness] over [HasLc].

    The local [glm_erasure] re-proof is specialised to
    [lrust_prob_lang], where case 3 (state_step / tape erasure) is
    vacuous because [state_idx = Empty_set] and [get_active σ = []].
    [wp_refRcoupl] handles arbitrary [num_laters_per_step] (our setup
    uses [sum_advance_credits (n+1)]); the user supplies a sufficient
    [£K] credit budget that's split per step via [total_step_credits]. *)
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

  (** Push [∀] through [▷^n ◇] of plain pure props (via [fupd_finally]). *)
  Lemma step_fupdN_pure_forall_intro {A} (Φ : A → Prop) n E :
    (∀ a, |={E|}=> ▷^n ◇ ⌜Φ a⌝) ⊢ |={E|}=> ▷^n ◇ ⌜∀ a, Φ a⌝ : iProp Σ.
  Proof.
    iIntros "H".
    iApply (fupd_finally_mono _ _ (▷^n ◇ ⌜∀ a, Φ a⌝)%I); last first.
    { iApply fupd_finally_forall. iIntros (a). iApply "H". }
    rewrite -laterN_forall. apply bi.laterN_mono.
    rewrite -except_0_forall. apply bi.except_0_mono.
    apply pure_forall_2.
  Qed.

  Lemma pgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜(0 <= ε)%R⌝ -∗
    ⌜(0 <= ε')%R⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a, ⌜R a⌝ -∗ |={∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T ε'⌝) -∗
    |={∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + ε')%R⌝.
  Proof.
    iIntros (Hε Hε' Hpgl) "H".
    iAssert (∀ a, |={∅|}=> ▷^(S n) ◇ ⌜R a → pgl (f a) T ε'⌝)%I with "[H]" as "H".
    { iIntros (a). destruct (ExcludedMiddle (R a)) as [HR|HnR].
      - iSpecialize ("H" $! a with "[//]").
        iApply (fupd_finally_mono with "H").
        apply (laterN_except_0_pure_mono (S n)). by intros.
      - iApply fupd_finally_intro. iPureIntro. by intros. }
    iPoseProof (step_fupdN_pure_forall_intro _ (S n) ∅ with "H") as "H".
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S n)). intros Hall.
    eapply pgl_dbind; eauto.
  Qed.

  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜(0 <= ε)%R⌝ -∗
    ⌜exists r, forall a, (0 <= ε' a <= r)%R⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a, ⌜R a⌝ -∗ |={∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))%R⌝.
  Proof.
    iIntros (Hε [r Hr] Hpgl) "H".
    iAssert (∀ a, |={∅|}=> ▷^(S n) ◇ ⌜R a → pgl (f a) T (ε' a)⌝)%I with "[H]" as "H".
    { iIntros (a). destruct (ExcludedMiddle (R a)) as [HR|HnR].
      - iSpecialize ("H" $! a with "[//]").
        iApply (fupd_finally_mono with "H").
        apply (laterN_except_0_pure_mono (S n)). by intros.
      - iApply fupd_finally_intro. iPureIntro. by intros. }
    iPoseProof (step_fupdN_pure_forall_intro _ (S n) ∅ with "H") as "H".
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S n)). intros Hall.
    eapply pgl_dbind_adv; [done|exists r; done|done|done].
  Qed.

  (** Helper: introduce a plain prop under [|={E|}=> ▷^l ◇ ·]. *)
  Local Lemma fupd_finally_plain_intro {E n} (P : iProp Σ) `{!Plain P} :
    P ⊢ |={E|}=> ▷^n ◇ P.
  Proof.
    iIntros "HP".
    iApply (fupd_finally_mono _ _ (▷^n ◇ P)%I).
    { apply bi.laterN_mono, bi.except_0_intro. }
    iApply fupd_finally_intro. by iApply plain_plainly.
  Qed.

  (** Helper: weaken [|={E1, E2}=> P] (with [P] plain) to
      [|={E1|}=> ▷^l ◇ P]. *)
  Local Lemma fupd_to_fupd_finally (l : nat) (E1 E2 : coPset) {P : iProp Σ} `{!Plain P} :
    (|={E1, E2}=> P) ⊢ |={E1|}=> ▷^l ◇ P.
  Proof.
    iIntros "H". iApply fupd_fupd_finally. iMod "H" as "HP".
    iModIntro. by iApply (fupd_finally_plain_intro P).
  Qed.

  (** Helper: push [▷^l] through [|={E|}=> ▷^k ◇ ·] (combining laters). *)
  Local Lemma laterN_fupd_finally (l : nat) {E} k (P : iProp Σ) :
    ▷^l (|={E|}=> ▷^k ◇ P) ⊢ |={E|}=> ▷^(l + k) ◇ P.
  Proof.
    induction l as [|l IH]; simpl.
    - iIntros "H". by iApply (fupd_finally_mono with "H").
    - iIntros "H". rewrite IH. rewrite fupd_finally_later.
      iApply (fupd_finally_mono with "H"). iIntros "H".
      by rewrite except_0_laterN except_0_idemp.
  Qed.

  (** Eliminate [|={E1, E2}=> P] into a fupd_finally [|={E1|}=> ▷^k ◇ Q]
      via a continuation that takes [P] (consumed at [E2]) and produces
      [|={E2|}=> ▷^(k-l') ◇ Q].  This is the workhorse for chaining the
      glm/WP step with the recursive call to [wp_refRcoupl]. *)
  Local Lemma elim_fupd_fupd_finally (k l : nat) (E1 E2 : coPset) (P Q : iProp Σ) :
    l ≤ k →
    (|={E1, E2}=> P) ∗ (∀ l', ⌜l' = l⌝ -∗ P -∗ |={E2|}=> ▷^(k - l') ◇ Q)
    ⊢ |={E1|}=> ▷^k ◇ Q.
  Proof.
    iIntros (Hlk) "[H1 H2]".
    iApply fupd_fupd_finally. iMod "H1" as "HP". iModIntro.
    iSpecialize ("H2" $! l with "[//] HP").
    iApply (fupd_finally_mono with "H2").
    replace k with (l + (k - l))%nat at 2 by lia.
    rewrite laterN_add. iIntros "H". by iApply laterN_intro.
  Qed.

  Local Definition cfgO := (prodO (exprO lrust_prob_lang) (stateO lrust_prob_lang)).

  (** [glm_erasure] in fupd_finally form, specialised to
      [lrust_prob_lang].  Parametrised over a separate later-count
      [k ≥ 1] and exec-offset [n] (instead of the upstream uniform
      [S n] for both) so it can be used with the polynomial
      [total_step_credits] later-budget.  Case 3 (state_step) is
      unreachable because [state_idx = Empty_set] (lang.v:792-796);
      inside [big_orL_mono] the loop variable [α] has type
      [Empty_set] and we close with [destruct α]. *)
  Lemma glm_erasure (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
      (k n : nat) φ (ε : nonnegreal) :
    1 ≤ k →
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
        |={∅|}=> ▷^k ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)
      ⊢ |={∅|}=> ▷^k ◇ ⌜pgl (exec (S n) (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hk Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm /glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ -∗
                  |={∅|}=> ▷^k ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   |={∅|}=> ▷^k ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iApply ("H" $! ((_, _)) with "Hfix"). }
    clear Hv.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & %Hsum & %Hlift & H)|Hbad]] %Hv".

    (* Case 1: thin-air ε-inflation. *)
    - iApply (fupd_finally_mono _ (▷^k ◇ ⌜∀ ε' : nonnegreal,
          (ε'' < ε')%R → pgl (exec (S n) (e1, σ1)) φ ε'⌝)%I).
      { apply (laterN_except_0_pure_mono k). intros Hall.
        eapply pgl_epsilon_limit; auto.
        - apply Rle_ge, cond_nonneg.
        - intros ε' Hε'.
          apply (Hall (mknonnegreal ε' (Rle_trans _ _ _ (cond_nonneg _) (Rlt_le _ _ Hε'))) Hε'). }
      iIntros (ε' Hε').
      destruct (decide (ε' < 1)%R) as [Hε'1|Hε'1]; last first.
      { iApply fupd_finally_intro. iApply plain_plainly.
        iApply bi.laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro. apply pgl_1. lra. }
      iApply (elim_fupd_fupd_finally k 0 ∅ ∅ _
        ⌜pgl (exec (S n) (e1, σ1)) φ ε'⌝); [lia|].
      iSplitL "H"; [iApply ("H" $! ε' with "[//]")|].
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      rewrite Nat.sub_0_r.
      iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
      rewrite -(dret_id_left' (λ _ : (), exec (S n) (e1, σ1)) tt).
      iApply (fupd_finally_mono _
        (▷^k ◇ ⌜pgl (dret tt ≫= λ _ : (), exec (S n) (e1, σ1)) φ (ε1' + ε2')⌝)%I).
      { apply (laterN_except_0_pure_mono k).
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
      destruct k as [|k']; [lia|].
      iApply (pgl_dbind' _ (dret tt) R' (λ x, φ x) ε1' ε2' k').
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply tgl_implies_pgl, Hlift'. }
      iIntros (a HRa). destruct a.
      iSpecialize ("Hwand'" with "[//]").
      iSpecialize ("Hwand'" with "[//]").
      rewrite dret_id_left.
      iApply "Hwand'".

    (* Case 2: prim_step with adv composition. *)
    - rewrite exec_Sn_not_final; [|by rewrite /is_final /= Hv].
      iApply (fupd_finally_mono _ (▷^k ◇ ⌜pgl (prim_step e1 σ1 ≫= exec n) φ
        (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ))%R⌝)%I).
      { apply (laterN_except_0_pure_mono k). intros Hpgl.
        eapply pgl_mon_grading; [|exact Hpgl]. done. }
      destruct k as [|k']; [lia|].
      iApply pgl_dbind_adv'.
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. exists r. intros a. split; [apply cond_nonneg | apply Hr]. }
      { done. }
      iIntros ([e' σ'] HRes).
      iApply (elim_fupd_fupd_finally (S k') 0 ∅ ∅ _
        ⌜pgl (exec n (e', σ')) φ (ε2 (e', σ'))⌝); [lia|].
      iSplitL "H"; [iApply ("H" with "[//]")|].
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      rewrite Nat.sub_0_r.
      iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
      rewrite -(dret_id_left' (λ _ : (), exec n (e', σ')) tt).
      iApply (fupd_finally_mono _ (▷^(S k') ◇
        ⌜pgl (dret tt ≫= λ _ : (), exec n (e', σ')) φ (ε1' + ε2')⌝)%I).
      { apply (laterN_except_0_pure_mono (S k')).
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
      iApply (pgl_dbind' _ (dret tt) R' (λ x, φ x) ε1' ε2' k').
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply tgl_implies_pgl, Hlift'. }
      iIntros (a HRa). destruct a.
      iSpecialize ("Hwand'" with "[//]").
      rewrite dret_id_left.
      iApply "Hwand'".

    (* Case 3: state_step — unreachable for [lrust_prob_lang]
       because [state_idx = Empty_set]. *)
    - iDestruct (big_orL_mono _ (λ _ _,
                   |={∅|}=> ▷^k
                     ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I
                with "Hbad") as "Hbad".
      { iIntros (i α _) "_". destruct α. }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      destruct α.
  Qed.

  (** Total credit budget for [n] WP steps starting at step counter [k].
      Used as both the [£]-input AND the [▷^?]-output count of the
      polynomial-aware [wp_refRcoupl]. *)
  Fixpoint total_step_credits (k n : nat) : nat :=
    match n with
    | 0%nat => 0%nat
    | S n' => S (num_laters_per_step k) + total_step_credits (S k) n'
    end.

  Lemma total_step_credits_S k n :
    total_step_credits k (S n) =
    (S (num_laters_per_step k) + total_step_credits (S k) n)%nat.
  Proof. reflexivity. Qed.

  (** Chain-absorption helper.  Given a step-fupd-N chain of length [m]
      ending in [|={∅, E}=> P] (with a non-plain [P], typically WP +
      [state_interp] + [err_interp]), and a wand [P -∗ |={E|}=> ▷^(k - m)
      ◇ Q] for plain [Q], produce [|={∅|}=> ▷^k ◇ Q].  The [m] laters
      from the chain are absorbed into the outer [▷^k] buffer. *)
  Local Lemma elim_step_fupdN_chain (m k : nat) (E : coPset) (P Q : iProp Σ)
      `{!Plain Q} :
    m ≤ k →
    (|={∅}▷=>^m |={∅, E}=> P) -∗
    (P -∗ |={E|}=> ▷^(k - m) ◇ Q) -∗
    |={∅|}=> ▷^k ◇ Q.
  Proof.
    iIntros (Hmk) "Hchain Hwand".
    (* Step 1: combine the chain with the wand by composing the inner
       fupd ([|={∅,E}=> P] then [P -∗ |={E|}=> ...]) into a single
       fupd_finally inside the chain. *)
    iPoseProof (step_fupdN_wand ∅ ∅ m _
      (|={∅|}=> ▷^(k - m) ◇ Q)%I with "Hchain [Hwand]") as "Hchain".
    { iIntros "Hinner".
      iApply fupd_fupd_finally. iMod "Hinner" as "HP". iModIntro.
      iApply ("Hwand" with "HP"). }
    (* Step 2: collapse the step-fupd-N chain into [|={∅|}=> ▷^m ◇ ...]. *)
    iPoseProof (step_fupdN_fupd_finally ∅ ∅ m
      (▷^(k - m) ◇ Q)%I with "Hchain") as "Hfinal".
    (* Step 3: simplify [▷^m ◇ (▷^(k-m) ◇ Q) ⊢ ▷^k ◇ Q] using
       [except_0_laterN] + [except_0_idemp] + [laterN_add].  This is
       a pure iProp entailment, so we discharge via [fupd_finally_mono]'s
       Coq-level side condition. *)
    iApply (fupd_finally_mono _ _ (▷^k ◇ Q)%I); last iApply "Hfinal".
    transitivity (▷^m (▷^(k - m) ◇ Q) : iProp Σ)%I.
    - apply bi.laterN_mono. rewrite except_0_laterN except_0_idemp //.
    - rewrite -laterN_add.
      replace (m + (k - m))%nat with k by lia.
      done.
  Qed.

  (** [wp_refRcoupl]: WP → fupd_finally adequacy.  Polynomial-aware —
      at each WP step we peel [S (num_laters_per_step k)] credits off
      the budget to feed the WP-step continuation's wand, and absorb
      the resulting [|={∅}▷=>^(S (num_laters_per_step k))] chain's
      laters into the outer [▷^...] buffer (sized at
      [total_step_credits k n]). *)
  Theorem wp_refRcoupl k
      (ε : nonnegreal) (e : language.expr lrust_prob_lang)
      (σ : language.state lrust_prob_lang) n φ :
    £ (total_step_credits k n) ∗ state_interp k σ ∗ err_interp ε ∗
      WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤|}=> ▷^(total_step_credits k n) ◇ ⌜pgl (exec n (e, σ)) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (k e σ ε); iIntros "(Hlc & Hσ & Hε & Hwp)".
    - rewrite /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (fupd_to_fupd_finally 0 ⊤ ⊤).
        iMod "Hwp" as "%". iModIntro.
        iPureIntro.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + iApply fupd_finally_intro. iApply plain_plainly. simpl.
        rewrite /bi_except_0. iRight.
        iPureIntro. apply pgl_dzero, Rle_ge, cond_nonneg.
    - rewrite total_step_credits_S.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        iApply (elim_fupd_fupd_finally _ 0 ⊤ ⊤ ⌜φ v⌝
          ⌜pgl (exec (S n) (of_val v, σ)) φ ε⌝); [lia|].
        rewrite pgl_wp_value_fupd'.
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l' ->) "%Hφv".
        iApply fupd_finally_intro. iApply plain_plainly.
        iApply bi.laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        erewrite exec_is_final; [|rewrite /= to_of_val //].
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iSpecialize ("Hwp" $! k with "[$Hσ $Hε]").
        (* Peel [S (num_laters_per_step k)] credits for this step's
           step-fupd-N chain, save [total_step_credits (S k) n] for
           the recursive call. *)
        iDestruct (lc_split (S (num_laters_per_step k))
                            (total_step_credits (S k) n) with "Hlc")
          as "[Hcred Hlc]".
        iApply (elim_fupd_fupd_finally (total_step_credits k (S n)) 0 ⊤ ∅ _
          ⌜pgl (prim_step e σ ≫= exec n) φ ε⌝); first lia.
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l' ->) "Hlift".
        rewrite Nat.sub_0_r.
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε2, |={∅|}=> ▷^(S (num_laters_per_step k)
                                                + total_step_credits (S k) n)
             ◇ ⌜pgl (exec n (e2, σ2)) φ ε2⌝)%I
            with "[%] [Hcred Hlc] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([e' σ'] ε') "H".
          (* H : £(S np k) -∗ |={∅}▷=>^(S np k) |={∅,⊤}=>
                   state_interp (S k) σ' ∗ err ε' ∗ WP e' ... *)
          iSpecialize ("H" with "Hcred").
          (* Use [elim_step_fupdN_chain] to absorb the
             [|={∅}▷=>^(S np k)] chain into the outer buffer's first
             [S np k] laters; recurse on [|={⊤|}=> ▷^(total_step_credits (S k) n)
             ◇ ⌜pgl⌝] for the rest. *)
          iApply (elim_step_fupdN_chain (S (num_laters_per_step k))
                    _ ⊤
                    (state_interp (S k) σ' ∗ err_interp ε' ∗
                       WP e' {{ v, ⌜φ v⌝ }})%I
                    ⌜pgl (exec n (e', σ')) φ ε'⌝
                  with "H").
          { lia. }
          iIntros "(Hσ' & Hε' & Hwp')".
          replace (S (num_laters_per_step k) + total_step_credits (S k) n -
                   S (num_laters_per_step k))%nat
            with (total_step_credits (S k) n) by lia.
          iApply ("IH" $! (S k) with "[$Hlc $Hσ' $Hε' $Hwp']"). }
        replace (prim_step e σ) with (step (e, σ)) by reflexivity.
        rewrite -exec_Sn_not_final; last by rewrite /is_final /to_final /= Heq.
        (* Explicit-args [iPoseProof] form avoids the heavy unification
           cost of [iApply (glm_erasure with "H")] — the [k]/[n]
           arguments are pinned down rather than left as metavariables
           for unification. *)
        iPoseProof
          (glm_erasure e σ
             (S (num_laters_per_step k) + total_step_credits (S k) n)
             n φ ε with "H") as "Heras".
        { lia. }
        { exact Heq. }
        iApply "Heras".
  Qed.

End adequacy.

(** Outside-section version of [total_step_credits] for [lrust_prob_lang],
    using the [sum_advance_credits (k+1)] schedule from [lifting.v]'s
    [lrustGS_erisWpGS] instance.  Needed for [lrust_wp_pgl] which is
    stated outside the [Section adequacy] (so doesn't have access to
    [num_laters_per_step] through the section's typeclass). *)
Fixpoint lrust_total_step_credits (k n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | S n' => S (sum_advance_credits (k + 1)) + lrust_total_step_credits (S k) n'
  end.

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

(** Top-level probabilistic adequacy, extracted via
    [fupd_finally_soundness] over [HasLc].  The [K] parameter is the
    initial later-credit budget — for our setup with
    [num_laters_per_step n = sum_advance_credits (n+1)], the user
    should supply [K ≥ lrust_total_step_credits 1 n] (the sum of per-step
    credit needs from the starting step counter [1] over [n] steps). *)
Theorem lrust_wp_pgl `{!lrustErisGpreS Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    n (ε : R) (K : nat) φ :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε)%R →
  (∀ `{!lrustGS Σ},
      ⊢ £ K -∗ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ ε.
Proof.
  intros Hσ Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (lrust_total_step_credits 1 n))).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)%R) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl. intros. eapply Rle_trans; [apply prob_le_1|done]. }
  apply (fupd_finally_soundness HasLc (K + lrust_total_step_credits 1 n) ⊤).
  iIntros (Hinv) "Hlc_total".
  (* Split: K credits for the user's WP, total_step_credits for wp_refRcoupl. *)
  iDestruct (lc_split K (lrust_total_step_credits 1 n) with "Hlc_total")
    as "[H£ Hlc]".
  set ε' := mknonnegreal ε Hε.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  iMod (own_alloc (●MN 2 ⋅ mono_nat_lb 2)) as (γglob) "[A B]";
    [by apply mono_nat_both_valid|].
  iMod (own_alloc (●MN 0)) as (γpers) "_";
    [by apply mono_nat_auth_valid|].
  iMod (own_alloc (● 0%nat)) as (γcum) "_";
    [by apply auth_auth_valid|].
  iMod (own_alloc
          (to_frac_agree (A:=leibnizO bool) (1/2) true ⋅
           to_frac_agree (A:=leibnizO bool) (1/2) true))
    as (γbool) "[Hbool _]".
  { rewrite frac_agree_op_valid Qp.half_half. split; trivial. }
  iMod (own_alloc
          (to_frac_agree (A:=leibnizO nat) (1/2) 0%nat ⋅
           to_frac_agree (A:=leibnizO nat) (1/2) 0%nat))
    as (γsum) "_".
  { rewrite frac_agree_op_valid Qp.half_half. split; trivial. }
  pose (Htime := TimeG Σ _ _ _ _ γglob γpers γcum γbool γsum).
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustGS := LRustGS Σ Hinv _ _ Hheap Hec Htime).
  change ε with (nonneg ε').
  iPoseProof (wp_refRcoupl 1 ε' e σ n φ) as "H".
  iSpecialize ("H" with "[-]").
  { iFrame "Hlc".
    iSplitR "Hs H£ Hf".
    { rewrite /state_interp /=. iSplitR "A Hbool".
      - rewrite /heap.heap_ctx. iExists ∅. iFrame "Hvγ Hfγ".
        iSplit.
        { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
          by rewrite lookup_empty in Hbad. }
        rewrite /heap.heap_ato_ctx. iFrame.
      - (* time_interp 1 in left disjunct (enabled true). *)
        iLeft. iFrame. iPureIntro. lia. }
    iFrame "Hs".
    iPoseProof (Hwp HlrustGS) as "Hwp'".
    iApply ("Hwp'" with "H£ Hf"). }
  iApply "H".
Qed.
