(** Error-credit rules for [lrust_prob_lang], ported from
    [clutch.eris.error_rules] (which is hard-coded to clutch's
    [prob_lang] via the [erisGS] section). The proof bodies are
    language-generic — they use only [pgl_wp_unfold], [glm_*],
    [ec_*], and [exec_stutter_*], all of which are polymorphic in [Λ]. *)
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.eris Require Import weakestpre lifting ectx_lifting.
From clutch.prob Require Import distribution couplings.
From clutch.prelude Require Import stdpp_ext.
From lrust.lang Require Export lifting.
Set Default Proof Using "Type".

Local Open Scope R.

(** Reducibility / support of [Rand z] in our language: the [prim_step]
    distribution of [Rand (Lit (LitInt z))] is supported on
    [(Lit (LitInt n), σ)] for [n : fin (Z.to_nat z)]. *)
(** [Rand z] is head-reducible whenever [0 < z]. *)
Lemma head_reducible_rand z σ1 :
  (0 < z)%Z →
  head_reducible (Λ:=lrust_prob_ectx_lang) (Rand (Lit (LitInt z))) σ1.
Proof.
  intros Hz. rewrite /head_reducible /= bool_decide_eq_true_2 //.
  eexists (_, _). apply dmap_pos. exists 0%fin. split; first done.
  apply dunifP_pos.
Qed.

Lemma pgl_rand_trivial z σ1 :
  (0 < z)%Z →
  pgl
    (prim_step (Λ:=lrust_prob_ectx_lang) (Rand (Lit (LitInt z))) σ1)
    (λ ρ2, ∃ (n : fin (Z.to_nat z)),
        ρ2 = (Lit (LitInt (Z.of_nat (fin_to_nat n))), σ1)) 0.
Proof.
  intros Hz.
  pose proof (head_reducible_rand z σ1 Hz) as Hred.
  pose proof (head_prim_step_eq (Λ:=lrust_prob_ectx_lang) _ σ1 Hred) as Heq.
  rewrite Heq.
  rewrite /head_step /= bool_decide_eq_true_2 //.
  rewrite /dmap.
  rewrite -(Rplus_0_r 0).
  eapply (pgl_dbind _ _ _ _ _ 0); [done|done| |by apply pgl_trivial].
  intros n _. apply pgl_dret.
  pose proof (fin_to_nat_lt n) as Hn.
  assert (fin_to_nat n < Z.to_nat z)%nat as Hn' by lia.
  exists (nat_to_fin Hn'). f_equal. f_equal. f_equal.
  by rewrite fin_to_nat_to_fin.
Qed.

Section error_rules.
  Context `{!lrustGS Σ}.

  (** Error induction by increasing.

      If we have [↯ ε] and the WP holds whenever we have a strictly
      larger amount [↯ ε'], then the WP holds with [↯ ε]. *)
  Lemma wp_err_incr e ε E Φ :
    to_val e = None ->
    ↯ ε ∗
      (∀ ε', ⌜ (ε < ε')%R ⌝ -∗ ↯ (ε') -∗ WP e @ E {{ Φ }} )
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "[Herr Hwp]".
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (ns σ1 ε2) "[Hσ1 Hε2]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iApply glm_err_incr_step.
    iIntros (ε') "%Hε'".
    apply Rlt_le in Hε' as Hε''.
    pose (diff :=((ε' - ε2) Hε'')%NNR).
    destruct (decide (ε' < 1)%R); last first.
    { iApply exec_stutter_spend.
      iPureIntro. simpl in *. simpl. lra. }
    replace (ε') with (ε2 + diff)%NNR;
      last (apply nnreal_ext; rewrite /diff; simpl; lra).
    iMod (ec_supply_increase _ diff with "[$]") as "[??]".
    { rewrite /diff. simpl. simpl in *. lra. }
    iPoseProof (ec_combine with "[$]") as "Herr".
    iSpecialize ("Hwp" with "[] Herr").
    { iPureIntro. simpl in *. simpl. lra. }
    rewrite !pgl_wp_unfold /pgl_wp_pre /=.
    rewrite H.
    iMod ("Hclose'").
    iMod ("Hwp" with "[$]").
    by iApply exec_stutter_free.
  Qed.

  (** Thin-air error credits: the WP can be proved as if you had any
      strictly positive amount of error credits.

      Verusbelt's [thin_air] axiom is exactly this rule. *)
  Lemma wp_err_pos e E Φ :
    to_val e = None ->
    (∀ ε, ⌜ (0 < ε)%R ⌝ -∗ ↯ (ε) -∗ WP e @ E {{ Φ }} )
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "?".
    iMod (ec_zero) as "Herr".
    iApply (wp_err_incr with "[$]"); auto.
  Qed.

  Lemma wp_err_pos_post e E Φ :
    to_val e = None →
    WP e @ E {{ Φ }} ⊢
      WP e @ E {{ v, ∃ ε : R, ⌜(0 < ε)%R⌝ ∗ ↯ ε ∗ Φ v }}.
  Proof.
    iIntros (Hnv) "Hwp".
    iApply wp_err_pos; first done.
    iIntros (ε Hε) "Hcr".
    iApply (pgl_wp_wand with "Hwp").
    iIntros (v) "HΦ".
    iExists ε. iFrame "Hcr HΦ". iPureIntro. exact Hε.
  Qed.

  (** Expectation-preserving rand sampling.

      For [Rand z] (with [0 < z]), we sample [n : fin (Z.to_nat z)]
      uniformly. Given [↯ ε1] and a function [ε2 : nat → R] such that
      the average error budget across outcomes is at most [ε1], we can
      step to [Lit (LitInt n)] with [↯ (ε2 n)] for the sampled [n].

      Verusbelt's [rand_ubig] axiom is this rule (modulo the [UBig]
      vs [Z] big-integer encoding). *)
  Lemma wp_rand_exp_nat z (ε1 : R) (ε2 : nat -> R) E Φ :
    (0 < z)%Z →
    (∀ n, (0 <= ε2 n <= 1)%R) →
    (SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat z)%nat
        then (1 / Z.to_nat z) * ε2 n
        else 0)%R <= ε1)%R →
    ↯ ε1 -∗
    ▷ (∀ (n : nat), ⌜ (n < Z.to_nat z)%nat ⌝ ∗ ↯ (ε2 n) -∗
                    Φ (LitV (LitInt (Z.of_nat n)))) -∗
    WP Rand (Lit (LitInt z)) @ E {{ Φ }}.
  Proof.
    iIntros (Hz Hleq Hε1) "Herr HΦ".
    assert (forall n, 0 <= ε2 n)%R as Hleq1 by (intros; apply Hleq).
    assert (forall n, ε2 n <= 1)%R as Hleq2 by (intros; apply Hleq).
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (ns σ1 ε_now) "[[Hσ Ht] Hε]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iApply glm_adv_comp; simpl.
    iDestruct (ec_supply_ec_inv with "Hε Herr") as %(ε1' & ε3 & Hε_now & Hε1').
    set (ecfn := (λ (ρ : expr * state),
                  ε3 +
                    match ρ with
                    | (Lit (LitInt n), σ) =>
                        if bool_decide (σ = σ1)
                        then if bool_decide (0 ≤ n)%Z
                             then if bool_decide (Z.to_nat n < Z.to_nat z)%nat
                                  then mknonnegreal _ (Hleq1 (Z.to_nat n))
                                  else nnreal_zero
                             else nnreal_zero
                        else nnreal_zero
                    | _ => nnreal_zero
                    end)%NNR).
    iExists
      (λ (ρ : expr * state),
        ∃ (n : Z), (0 <= n)%Z /\ (Z.to_nat n < Z.to_nat z)%nat /\
                   ρ = (Lit (LitInt n), σ1)), nnreal_zero, ecfn.
    iSplit.
    { iPureIntro. eapply head_prim_reducible.
      by apply head_reducible_rand. }
    iSplit.
    { iPureIntro. exists (ε3 + 1)%R.
      intros (e & σ); simpl.
      apply Rplus_le_compat; [lra|].
      repeat (case_match; simpl; try lra).
      apply Hleq2. }
    iSplit.
    { iPureIntro.
      rewrite /ecfn /= Rplus_0_l.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus.
      - rewrite Rplus_comm.
        subst.
        apply Rplus_le_compat.
        + etrans; eauto.
          etrans; last first.
          * apply (SeriesC_le_inj _
                     (λ ρ : expr * state,
                         let (e, σ) := ρ in
                         if bool_decide (σ = σ1) then
                           match e with
                           | Lit (LitInt n) =>
                               if bool_decide (0 ≤ n)%Z
                               then if bool_decide (Z.to_nat n < Z.to_nat z)%nat
                                    then Some (Z.to_nat n)
                                    else None
                               else None
                           | _ => None
                           end
                         else None)).
            ** intros. real_solver.
            ** intros ρ1 ρ2 m Hc1 Hc2.
               repeat (case_bool_decide || case_match); simplify_eq.
               f_equal. do 3 f_equal. apply Z2Nat.inj; auto.
            ** eapply ex_seriesC_ext;
                 last apply (ex_seriesC_nat_bounded
                              (λ n, 1 / Z.to_nat z * ε2 n) (Z.to_nat z - 1)).
               intros n. case_bool_decide as Hlt;
                 case_bool_decide as Hle; try done; lia.
          * apply SeriesC_le.
            ** intros [e σ]; split.
               *** apply Rmult_le_pos; auto.
               *** case_bool_decide; simplify_eq.
                   **** do 4 (case_match; simpl; (try (rewrite Rmult_0_r; lra))).
                        2: { rewrite Rmult_0_r.
                             rewrite (bool_decide_eq_true_2 (σ1 = σ1)); [|reflexivity].
                             cbn. lra. }
                        apply bool_decide_eq_true_1 in H1.
                        apply bool_decide_eq_true_1 in H2.
                        rewrite bool_decide_eq_true_2; last reflexivity.
                        simpl.
                        rewrite bool_decide_eq_true_2; last by lia.
                        apply Rmult_le_compat_r; [auto|].
                        rewrite (head_prim_step_eq (Λ:=lrust_prob_ectx_lang)
                                  _ _ (head_reducible_rand z _ Hz)).
                        rewrite /head_step /= bool_decide_eq_true_2 //.
                        rewrite /dmap /pmf /= /dbind_pmf /dunifP.
                        setoid_rewrite dunif_pmf.
                        replace (S (Z.to_nat z - 1)) with (Z.to_nat z) by lia.
                        rewrite SeriesC_scal_l /= /Rdiv Rmult_1_l.
                        rewrite <- Rmult_1_r.
                        apply Rmult_le_compat_l.
                        { left. apply Rinv_0_lt_compat. apply lt_0_INR. lia. }
                        rewrite /pmf /= /dret_pmf.
                        assert (Z.to_nat n < Z.to_nat z)%nat as Hbnd by lia.
                        erewrite <- (SeriesC_singleton (nat_to_fin Hbnd)).
                        apply SeriesC_le; [|apply ex_seriesC_singleton].
                        intro; split; [real_solver|].
                        case_bool_decide; try real_solver.
                        rewrite bool_decide_eq_true_2; [lra|].
                        simplify_eq. apply fin_to_nat_inj.
                        rewrite fin_to_nat_to_fin.
                        rewrite Nat2Z.id //.
                   **** rewrite (bool_decide_eq_false_2 (σ = σ1)); [|done].
                        cbn.
                        etrans; [|right; eapply Rmult_0_l].
                        apply Rmult_le_compat_r; [auto|]. right.
                        rewrite (head_prim_step_eq (Λ:=lrust_prob_ectx_lang)
                                  _ _ (head_reducible_rand z _ Hz)).
                        rewrite /head_step /= bool_decide_eq_true_2 //.
                        rewrite /dmap /pmf /= /dbind_pmf /dunifP.
                        setoid_rewrite dunif_pmf.
                        rewrite SeriesC_scal_l /= /Rdiv.
                        erewrite (SeriesC_ext _ (λ _, 0));
                          [rewrite SeriesC_0; auto; by rewrite Rmult_0_r|].
                        intro; rewrite dret_0; auto.
                        intro; simplify_eq.
            ** eapply ex_seriesC_finite_from_option.
               instantiate (1 := (λ k : nat, (Lit (LitInt (Z.of_nat k)), σ1)) <$> (seq 0%nat (Z.to_nat z))).
               intros [e σ].
               split.
               --- case_bool_decide; last first.
                   { inversion 1. done. }
                   case_match; try (by inversion 1).
                   case_match; try (by inversion 1).
                   case_bool_decide; try (by inversion 1).
                   case_bool_decide; try (by inversion 1).
                   intros _. subst.
                   eapply list_elem_of_fmap_2'; last first.
                   { repeat f_equal. instantiate (1 := Z.to_nat n). lia. }
                   rewrite elem_of_seq. lia.
               --- intros Hin. apply list_elem_of_fmap_1 in Hin.
                   destruct Hin as [k [Heq Hk]].
                   inversion Heq.
                   replace (bool_decide (_=_)) with true.
                   2: { case_bool_decide; done. }
                   replace (bool_decide _) with true.
                   2: { case_bool_decide; lia. }
                   case_match; first done.
                   apply bool_decide_eq_false_1 in H.
                   rewrite elem_of_seq in Hk.
                   exfalso.
                   apply H.
                   lia.
        + rewrite SeriesC_scal_r.
          rewrite <- Rmult_1_l.
          apply Rmult_le_compat; auto; try lra; apply cond_nonneg.
      - by apply ex_seriesC_scal_r.
      - eapply ex_seriesC_ext; last eapply ex_seriesC_list.
        intros [e σ].
        instantiate (2 := (λ k : nat, (Lit (LitInt (Z.of_nat k)), σ1)) <$> (seq 0%nat (Z.to_nat z))).
        case_bool_decide; last first.
        + repeat (case_match; try (simpl; lra)).
          exfalso. apply H. subst.
          eapply list_elem_of_fmap_2'; last first.
          { apply bool_decide_eq_true_1 in H2, H3. repeat f_equal.
            - instantiate (1 := Z.to_nat n). lia.
            - done.
          }
          rewrite elem_of_seq.
          apply bool_decide_eq_true_1 in H4.
          lia.
        + instantiate (1 :=
                         (λ '(e, s), (prim_step (Λ:=lrust_prob_ectx_lang) (Rand (Lit (LitInt z))) σ1 (e, s) *
                                        match e with
                                        | Lit (LitInt n) =>
                                            if bool_decide (s = σ1)
                                            then if bool_decide (0 ≤ n)%Z
                                                 then if bool_decide (Z.to_nat n < Z.to_nat z)%nat
                                                      then ε2 (Z.to_nat n)
                                                      else nnreal_zero
                                                 else nnreal_zero
                                            else nnreal_zero
                                        | _ => nnreal_zero
                                        end)%R)).
          simpl. repeat f_equal.
          repeat (case_match; try (simpl; lra)). }
    iSplit.
    { iPureIntro.
      eapply pgl_mon_pred; last first.
      - apply (pgl_rand_trivial z σ1 Hz).
      - intros (e2, σ2) [n Heq].
        pose proof (fin_to_nat_lt n) as Hnlt.
        exists (Z.of_nat (fin_to_nat n)).
        split; [lia|].
        split; [rewrite Nat2Z.id; done|].
        done. }
    iIntros (e2 σ2) "%H".
    destruct H as (n & Hn1 & Hn2 & Hn3); simplify_eq.
    rewrite /ecfn.
    rewrite bool_decide_eq_true_2; last done.
    rewrite bool_decide_eq_true_2; last first.
    { lia. }
    rewrite bool_decide_eq_true_2; last done.
    iMod (ec_supply_decrease with "Hε Herr") as (????) "Hε2".
    iModIntro.
    destruct (Rlt_decision (nonneg ε3 + (ε2 (Z.to_nat n)))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro. simpl. lra. }
    iApply exec_stutter_free.
    iIntros "Hcred".
    iDestruct (lc_succ with "Hcred") as "[Hc1 Hcred_rest]".
    simpl.
    iMod (lc_fupd_elim_later with "Hc1 HΦ") as "HΦ".
    iMod (ec_supply_increase ε3 (mknonnegreal _ (Hleq1 (Z.to_nat n))) with "[Hε2]")
      as "[Hε2 Hcr]".
    { simpl. lra. }
    { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
    iMod "Hclose'".
    iMod (time_interp_step with "Ht") as "Ht".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose2". iFrame "Hσ Ht Hε2".
    iApply bi.later_intro.
    iApply fupd_intro.
    iApply (step_fupdN_intro ∅ ∅ (sum_advance_credits (ns + 1))); [done|].
    iApply (bi.laterN_intro (sum_advance_credits (ns + 1))).
    iMod "Hclose2".
    iApply (pgl_wp_value _ _ _ (Lit (LitInt n)) (LitV (LitInt n))); [done|].
    replace (LitV (LitInt n)) with (LitV (LitInt (Z.of_nat (Z.to_nat n)))); last first.
    { f_equal. f_equal. by rewrite Z2Nat.id. }
    iApply "HΦ". iFrame. iPureIntro. lia.
  Qed.

End error_rules.
