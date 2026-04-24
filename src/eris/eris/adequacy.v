(** Probabilistic adequacy core lemmas — HasLc port using hfupd.

    Original clutch/eris adequacy proved [pgl_dbind'], [glm_erasure],
    [wp_refRcoupl_step_fupdN] in step-fupd-N form, relying on
    [BiFUpdSbi] for the universal-commutation [step_fupdN_plain_forall].
    Under [HasLc] [BiFUpdSbi] is not inhabited, so that form breaks.

    Iris MR !1171 introduced the half-fupd modality [|={n;E|}=> P],
    whose forall-commutation [hfupd_forall_2] holds under HasLc.
    We port eris's adequacy to land in hfupd form throughout; the
    top-level theorem in [lrust.lang.adequacy_prob] uses
    [hfupd_soundness] to extract the pure [pgl] fact. *)
From Stdlib Require Import Classical.
From iris.proofmode Require Import base proofmode.
From iris.bi Require Export lib.fixpoint_mono big_op.
From iris.base_logic.lib Require Import invariants fancy_updates.
From iris.prelude Require Import options.

From eris.prelude Require Import stdpp_ext iris_ext.
From eris.common Require Export language erasable exec.
From eris.base_logic Require Import error_credits.
From eris.eris Require Import weakestpre.
From eris.prob Require Import distribution graded_predicate_lifting.
Import uPred.

Section adequacy.
  Context `{!erisWpGS Λ Σ}.

  Local Definition cfgO := (prodO (exprO Λ) (stateO Λ)).

  (** Pure-mono lift: push a Coq implication through [▷^ ◇ ⌜·⌝]. *)
  Local Lemma laterN_except_0_pure_mono m (P Q : Prop) :
    (P → Q) → ((▷^m ◇ ⌜P⌝ : iProp Σ) ⊢ ▷^m ◇ ⌜Q⌝).
  Proof.
    intros HPQ. apply bi.laterN_mono, bi.except_0_mono, bi.pure_mono, HPQ.
  Qed.

  (** hfupd-form pgl_dbind' with hfupd-valued continuations.
      Preserves the [▷^(S n) ◇] structure end-to-end, so this composes
      cleanly with the WP/glm plumbing. *)
  Lemma pgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a, ⌜R a⌝ -∗ |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T ε'⌝) -∗
    |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + ε')⌝.
  Proof.
    iIntros (H1 H2 H3) "H".
    iApply (hfupd_mono _ _ (▷^(S n) ◇ ⌜∀ a, R a → pgl (f a) T ε'⌝)%I).
    { iIntros "H". iStopProof.
      apply bi.later_mono, bi.laterN_mono, bi.except_0_mono.
      apply bi.pure_mono. intros Hall.
      eapply pgl_dbind; eauto. }
    rewrite bi.pure_forall.
    rewrite except_0_forall laterN_forall later_forall.
    iApply hfupd_forall_2. iIntros (a).
    destruct (classic (R a)) as [HR|HNR]; last first.
    { iApply hfupd_intro. iApply laterN_intro.
      rewrite /bi_except_0. iRight. iPureIntro. done. }
    iApply (hfupd_mono _ _ _ with "(H [//])").
    apply bi.later_mono, bi.laterN_mono, bi.except_0_mono, bi.pure_mono.
    intros ? _. done.
  Qed.

  (** Adv version: ε' depends on outcome. *)
  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a, ⌜R a⌝ -∗ |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T (ε' a)⌝) -∗
    |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))⌝.
  Proof.
    iIntros (H1 [r Hr] H3) "H".
    iApply (hfupd_mono _ _ (▷^(S n) ◇ ⌜∀ a, R a → pgl (f a) T (ε' a)⌝)%I).
    { iIntros "H". iStopProof.
      apply bi.later_mono, bi.laterN_mono, bi.except_0_mono.
      apply bi.pure_mono. intros Hall.
      eapply pgl_dbind_adv; [done|exists r; done|done|done]. }
    rewrite bi.pure_forall.
    rewrite except_0_forall laterN_forall later_forall.
    iApply hfupd_forall_2. iIntros (a).
    destruct (classic (R a)) as [HR|HNR]; last first.
    { iApply hfupd_intro. iApply laterN_intro.
      rewrite /bi_except_0. iRight. iPureIntro. done. }
    iApply (hfupd_mono _ _ _ with "(H [//])").
    apply bi.later_mono, bi.laterN_mono, bi.except_0_mono, bi.pure_mono.
    intros ? _. done.
  Qed.

  (** Helper: lift a pure mono over [▷^n ◇ ⌜P⌝] shapes to the BI level. *)
  Local Lemma hfupd_laterN_except_0_pure_mono n m E (P Q : Prop) :
    (P → Q) → (|={m; E|}=> ▷^n ◇ ⌜P⌝ : iProp Σ) ⊢ |={m; E|}=> ▷^n ◇ ⌜Q⌝.
  Proof.
    intros HPQ. apply hfupd_mono.
    apply bi.laterN_mono, bi.except_0_mono, bi.pure_mono, HPQ.
  Qed.

  (** [glm_erasure], hfupd version.
      Input: a glm derivation whose per-branch predicate is in
      step-fupd-N form (what the WP produces).
      Output: an hfupd-wrapped pure pgl fact. *)
  Lemma glm_erasure (e : language.expr Λ) (σ : language.state Λ)
      (n : nat) φ (ε : nonnegreal) :
    (∀ σ : language.state Λ, language.get_active σ = []) →
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
        |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)
      ⊢ |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (exec (S n) (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hactive Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm /glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ -∗
                  |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iApply ("H" $! ((_, _)) with "Hfix"). }
    clear Hv.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & %Hsum & %Hlift & H)|H]] %Hv".

    (* Case 1: thin air ε-inflation. H : ∀ ε' > ε'',
         ={∅}=∗ exec_stutter (Φ @ (e1,σ1)) ε'. *)
    - iApply (hfupd_mono _ _ (▷^(S n) ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I);
        [by iIntros "$"|].
      iApply (hfupd_mono _ _ (▷^(S n) ◇ ⌜∀ ε' : nonnegreal,
          (ε'' < ε')%R → pgl (exec (S n) (e1, σ1)) φ ε'⌝)%I).
      { iIntros "H". iStopProof.
        apply bi.later_mono, bi.laterN_mono, bi.except_0_mono, bi.pure_mono.
        intros Hall. eapply pgl_epsilon_limit; auto.
        - apply Rle_ge, cond_nonneg.
        - intros ε' Hε'.
          apply (Hall (mknonnegreal ε' (Rle_trans _ _ _ (cond_nonneg _) (Rlt_le _ _ Hε'))) Hε'). }
      rewrite bi.pure_forall except_0_forall laterN_forall later_forall.
      iApply hfupd_forall_2. iIntros (ε').
      destruct (decide (ε'' < ε')%R) as [Hε'|Hε']; last first.
      { iApply hfupd_intro. iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro. intros Hlt. done. }
      iSpecialize ("H" $! ε' with "[//]").
      iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅
        (exec_stutter (λ ε0 : nonnegreal, (⌜to_val e1 = None⌝ -∗
          |={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε0⌝)%I) ε')
        ⌜ε'' < ε' → pgl (exec (S n) (e1, σ1)) φ ε'⌝); [lia|].
      iFrame "H".
      iIntros (l Hl) "Hexecs".
      assert (l = 0%nat) as -> by lia.
      iDestruct "Hexecs" as "[%R' [%ε1' [%ε2' (%Hsum' & %Hlift' & Hwand')]]]".
      apply tgl_implies_pgl in Hlift'.
      simpl. rewrite Nat.add_0_r. replace (S n - 0)%nat with (S n) by lia.
      destruct (classic (R' tt)) as [HR'tt | HnR'tt].
      { iSpecialize ("Hwand'" with "[]"); [by iPureIntro|].
        iSpecialize ("Hwand'" with "[]"); [by iPureIntro|].
        iApply (hfupd_mono _ _ (▷^(S n) ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε2'⌝)%I).
        { iIntros "H". iStopProof.
          apply bi.later_mono, bi.laterN_mono, bi.except_0_mono, bi.pure_mono.
          intros ?. intros _. eapply pgl_mon_grading; [|done].
          pose proof (cond_nonneg ε1'). simpl in *. lra. }
        iApply "Hwand'". }
      iApply hfupd_intro. iApply laterN_intro.
      rewrite /bi_except_0. iRight. iPureIntro. intros _. apply pgl_1.
      unfold pgl in Hlift'.
      assert ((λ a : (), Datatypes.negb (bool_decide (R' a))) tt = true) as Hbd.
      { rewrite /= bool_decide_eq_false_2 //. }
      rewrite (prob_dret_true _ _ Hbd) in Hlift'.
      pose proof (cond_nonneg ε2'). simpl in *. lra.

    (* Case 2: prim_step with adv composition *)
    - rewrite exec_Sn_not_final; [|by rewrite /is_final /= Hv].
      iApply (hfupd_mono _ _ (▷^(S n) ◇ ⌜pgl (prim_step e1 σ1 ≫= exec n) φ
        (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ))%R⌝)%I).
      { iIntros "Hupd". iStopProof.
        apply bi.later_mono, bi.laterN_mono, bi.except_0_mono, bi.pure_mono.
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. done. }
      iApply pgl_dbind_adv'; [iPureIntro; apply cond_nonneg|
                               iPureIntro; exists r; intros a;
                                 split; [apply cond_nonneg | apply Hr]|
                               done|].
      iIntros ([e' σ'] HR).
      iSpecialize ("H" $! e' σ' with "[//]").
      iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅
        (exec_stutter (λ ε0 : nonnegreal,
          (|={0; ∅|}=> ▷^(S n) ◇ ⌜pgl (exec n (e', σ')) φ ε0⌝)%I) (ε2 (e', σ')))
        ⌜pgl (exec n (e', σ')) φ (ε2 (e', σ'))⌝); [lia|].
      iFrame "H".
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      rewrite Nat.add_0_r. replace (S n - 0)%nat with (S n) by lia.
      iDestruct "Hst" as "[%R' [%ε1' [%ε2' (%Hsum' & %Hlift' & Hwand')]]]".
      apply tgl_implies_pgl in Hlift'.
      destruct (classic (R' tt)) as [HR'tt | HnR'tt].
      { iSpecialize ("Hwand'" with "[]"); [by iPureIntro|].
        iApply (hfupd_mono _ _ _ with "Hwand'").
        apply bi.later_mono, bi.laterN_mono, bi.except_0_mono, bi.pure_mono.
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl].
        pose proof (cond_nonneg ε1'). simpl in *. lra. }
      iApply hfupd_intro. iApply laterN_intro.
      rewrite /bi_except_0. iRight. iPureIntro. apply pgl_1.
      unfold pgl in Hlift'.
      assert ((λ a : (), Datatypes.negb (bool_decide (R' a))) tt = true) as Hbd.
      { rewrite /= bool_decide_eq_false_2 //. }
      rewrite (prob_dret_true _ _ Hbd) in Hlift'.
      pose proof (cond_nonneg ε2'). simpl in *. lra.

    (* Case 3: state_step — vacuous since get_active = [] *)
    - specialize (Hactive σ1).
      iDestruct "H" as "H".
      rewrite Hactive /=. done.
  Qed.

End adequacy.
 