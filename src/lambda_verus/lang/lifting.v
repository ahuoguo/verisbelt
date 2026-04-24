Require Import guarding.internal.na_invariants_fork.
From guarding Require Import guard.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require Export lang heap time.
From lrust.lang Require Import tactics.
From lrust.util Require Import update non_atomic_cell_map atomic_lock_counter.
Set Default Proof Using "Type".
Import uPred.

Open Scope Z_scope.

Class lrustGS Σ := LRustGS {
  lrustGS_invGS : invGS Σ;
  #[global] lrustGS_na_invGS :: na_invG Σ;
  #[global] lrustGS_atomic_lock_ctr_invGS :: alc_logicG Σ;
  #[global] lrustGS_gen_heapGS :: heapGS Σ;
  #[global] lrustGS_gen_timeGS :: timeGS Σ
}.

Global Program Instance lrustGS_irisGS `{!lrustGS Σ} : irisGS lrust_lang Σ := {
  iris_invGS := lrustGS_invGS;
  state_interp σ stepcnt κs _ := (@heap_ctx Σ _ lrustGS_invGS lrustGS_na_invGS lrustGS_atomic_lock_ctr_invGS σ ∗ time_interp stepcnt)%I;
  fork_post _ := True%I;
  num_laters_per_step n := (sum_advance_credits (n + 1))%nat
}.
Next Obligation.
  intros. iIntros "/= [$ H]". by iMod (time_interp_step with "H") as "$".
Qed.

Global Opaque iris_invGS.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  end.

Ltac inv_bin_op_eval :=
  repeat match goal with
  | H : bin_op_eval _ ?c _ _ _ |- _ => is_constructor c; inversion H; clear H; simplify_eq/=
  end.

Local Hint Extern 0 (atomic _) => solve_atomic : core.
Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.

Local Hint Constructors head_step bin_op_eval lit_neq lit_eq : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) :=
  as_rec : e = Rec f xl erec.
Global Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Global Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

Class DoSubst (x : binder) (es : expr) (e er : expr) :=
  do_subst : subst' x es e = er.
Global Hint Extern 0 (DoSubst _ _ _ _) =>
  rewrite /DoSubst; simpl_subst; reflexivity : typeclass_instances.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) :=
  do_subst_l : subst_l xl esl e = Some er.
Global Instance do_subst_l_nil e : DoSubstL [] [] e e.
Proof. done. Qed.
Global Instance do_subst_l_cons x xl es esl e er er' :
  DoSubstL xl esl e er' → DoSubst x es er' er →
  DoSubstL (x :: xl) (es :: esl) e er.
Proof. rewrite /DoSubstL /DoSubst /= => -> <- //. Qed.
Global Instance do_subst_vec xl (vsl : vec val (length xl)) e :
  DoSubstL xl (of_val <$> vec_to_list vsl) e (subst_v xl vsl e).
Proof. by rewrite /DoSubstL subst_v_eq. Qed.

Section lifting.
Context `{!lrustGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types e : expr.
Implicit Types ef : option expr.

Local Open Scope nat_scope.

Lemma sqr_bound (n: nat) :
    (2 ^ (S n) * 2^ (S n) ≤ (sum_advance_credits (n + 1))).
Proof.
  destruct n.
  - cbn; lia.
  - rewrite Nat.add_1_r.
    cbn [sum_advance_credits Nat.pow].
    rewrite /advance_credits.
    nia.
Qed.

Lemma Sexp_le_exp_S_lemma (n: nat) :
    (S (2 ^ (S n))) ≤ (2 ^ (S (S n))).
Proof.
    cbn.
    assert (2 ^ n ≥ 1) as H1; last by lia.
    induction n; cbn; nia.
Qed.
    
Lemma sqr_bound' (n: nat) :
    ((2 ^ (S (S n))) * ((2^ (S (S n)))) ≤ (sum_advance_credits (n + 1))).
Proof.
  destruct n.
  - cbn; lia.
  - rewrite Nat.add_1_r.
    cbn [sum_advance_credits Nat.pow].
    rewrite /advance_credits.
    nia.
Qed.

Lemma sqr_bound'' (n: nat) :
    (S (2 ^ (S n)) * (S (2^ (S n))) ≤ (sum_advance_credits (n + 1))).
Proof.
    assert (0 ≤ S (2 ^ (S n))) as H1. { nia. }
    assert (∀ x y z, 0 ≤ x → x ≤ y → y * y ≤ z → x * x ≤ z) as H. { intros. nia. }
    apply (H _ _ _ H1 (Sexp_le_exp_S_lemma n) (sqr_bound' n)).
Qed.

Lemma wp_step_fupdN_time_receipt n m E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗
    (⧗m ∧ ((|={E1∖E2,∅}=> |={∅}▷=>^(S ((n + m) * (n + m))) |={∅,E1∖E2}=> P) ∗
           WP e @ E2 {{ v, P ={E1}=∗ Φ v }})) -∗
  WP e @ E1 {{ Φ }}.
Proof.
  iIntros (???) "#TIME #Hn H".
  iApply (wp_step_fupdN (S ((n + m) * (n + m))) _ _ E2)=>//. iSplit.
  - iIntros "* [_ Ht]". iMod (time_receipt_le with "TIME Ht Hn [H]") as "[% ?]"=>//.
    + iDestruct "H" as "[$ _]".
    + iApply fupd_mask_weaken.
      2: { iIntros "_ !> !% /=". 
           have Hx := sqr_bound ns.
           nia.
      }
      set_solver.
  - iDestruct "H" as "[_ $]".
Qed.

Lemma wp_step_fupdN_time_receipt' n m E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗
    (⧗m ∧ ((|={E1∖E2,∅}=> |={∅}▷=>^((S ((S (n + m)) * S (n + m)))) |={∅,E1∖E2}=> P) ∗
           WP e @ E2 {{ v, P ={E1}=∗ Φ v }})) -∗
  WP e @ E1 {{ Φ }}.
Proof.
  iIntros (???) "#TIME #Hn H".
  iApply (wp_step_fupdN (S (((S (n + m)) * S (n + m)))) _ _ E2)=>//. iSplit.
  - iIntros "* [_ Ht]". iMod (time_receipt_le with "TIME Ht Hn [H]") as "[% ?]"=>//.
    + iDestruct "H" as "[$ _]".
    + iApply fupd_mask_weaken.
      2: { iIntros "_ !> !% /=". 
           have Hx := sqr_bound'' ns.
           nia.
      }
      set_solver.
  - iDestruct "H" as "[_ $]".
Qed.

Lemma wp_step_fupdN_persistent_time_receipt n E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗ (|={E1∖E2,∅}=> |={∅}▷=>^(S (n * n)) |={∅, E1∖E2}=> P) -∗
  WP e @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ E1 {{ Φ }}.
Proof. 
  iIntros (???) "#TIME #Hn HP Hwp".
  iApply (wp_step_fupdN_time_receipt _ _ E1 E2 with "TIME Hn [> -]")=>//.
  iMod cumulative_time_receipt_0 as "$". iFrame. by rewrite -plus_n_O.
Qed.


Lemma wp_step_fupdN_persistent_time_receipt' n E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗ (|={E1∖E2,∅}=> |={∅}▷=>^(S ((S n) * (S n))) |={∅, E1∖E2}=> P) -∗
  WP e @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ E1 {{ Φ }}.
Proof. 
  iIntros (???) "#TIME #Hn HP Hwp".
  iApply (wp_step_fupdN_time_receipt' _ _ E1 E2 with "TIME Hn [> -]")=>//.
  iMod cumulative_time_receipt_0 as "$". iFrame. by rewrite -plus_n_O.
Qed.

Lemma wp_cumulative_time_receipt_linear E e Φ d :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  ⧖d -∗
  (⧗(S (S d)) -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}. 
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "#TIME ⧖ Hwp".
  iIntros (?????) "[Hσ Ht]".
  iMod (step_cumulative_time_receipt with "TIME Ht ⧖") as "[%ns1 [Ht [EnFalse [⧗ Hclose]]]]"=>//. { solve_ndisj. }
  replace (d + 2) with (S (S d)) by lia.
  (* iDestruct "⧗" as "[⧗ ⧗1 ]". *)
  iDestruct ("Hwp" with "⧗") as "Hwp".
  iMod ("Hwp" $! _ (ns-1)%nat _ [] 0%nat with "[$]") as "[$ Hwp]".
  iIntros "!>" (e2 σ2 efs stp) "credit".
  iDestruct "credit" as "[Hc1 credit]".
  rewrite (sum_advance_credits_ge1 (ns+1)); last by lia.
  iDestruct "credit" as "[credit1 credit2]".
  iCombine "credit2 Hc1" as "credit2".
  replace (ns - 1 + 1)%nat with ns by lia.
  replace (ns + 1 - 1)%nat with ns by lia.
  iMod ("Hwp" $! e2 σ2 efs stp with "credit2") as "Hwp".
  iIntros "!> !>". iMod "Hwp". iModIntro.
  iApply (step_fupdN_nmono (sum_advance_credits (ns))); first by lia.
  iApply (step_fupdN_wand with "Hwp"). iIntros ">([$ Ht] & Hwp & $)".
  replace (S (ns - 1))%nat with ns by lia.
  iMod ("Hclose" with "[EnFalse Ht credit1]") as "?". {
    iFrame. iApply (lc_weaken with "credit1"). 
    rewrite !Nat.add_1_r.
    cbn [Nat.pow].
    opose proof (advance_credits_mono (2 * 2 ^ ns) (2 * (2 * 2 ^ ns)) _);nia.
  }
  iFrame.
  iApply (wp_wand with "[Hwp]"); [iApply (wp_mask_mono with "Hwp"); solve_ndisj|].
  iIntros "!> % H". by iApply "H".
Qed.

Lemma wp_cumulative_time_receipt2 E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  (⧗2 -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}. 
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "#TIME Hwp".
  iIntros (?????) "[Hσ Ht]".
  iMod persistent_time_receipt_0 as "⧖".
  iMod (step_cumulative_time_receipt with "TIME Ht ⧖") as "[%ns1 [Ht [EnFalse [[⧗1 ⧗2] Hclose]]]]"=>//. { solve_ndisj. }
  iDestruct ("Hwp" with "⧗2") as "Hwp".
  iMod ("Hwp" $! _ (ns-1)%nat _ [] 0%nat with "[$]") as "[$ Hwp]".
  iIntros "!>" (e2 σ2 efs stp) "credit".
  iDestruct "credit" as "[Hc1 credit]".
  rewrite (sum_advance_credits_ge1 (ns+1)); last by lia.
  iDestruct "credit" as "[credit1 credit2]".
  iCombine "credit2 Hc1" as "credit2".
  replace (ns - 1 + 1)%nat with ns by lia.
  replace (ns + 1 - 1)%nat with ns by lia.
  iMod ("Hwp" $! e2 σ2 efs stp with "credit2") as "Hwp".
  iIntros "!> !>". iMod "Hwp". iModIntro.
  iApply (step_fupdN_nmono (sum_advance_credits (ns))); first by lia.
  iApply (step_fupdN_wand with "Hwp"). iIntros ">([$ Ht] & Hwp & $)".
  replace (S (ns - 1))%nat with ns by lia.
  iMod ("Hclose" with "[EnFalse Ht credit1]") as "?". {
    iFrame. iApply (lc_weaken with "credit1"). 
    rewrite !Nat.add_1_r.
    cbn [Nat.pow].
    opose proof (advance_credits_mono (2 * 2 ^ ns) (2 * (2 * 2 ^ ns)) _);nia.
  }
  iFrame.
  iApply (wp_wand with "[Hwp]"); [iApply (wp_mask_mono with "Hwp"); solve_ndisj|].
  iIntros "!> % H". by iApply "H".
Qed.

Lemma wp_cumulative_time_receipt1 E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗ 
  (⧗1 -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "#TIME Hwp".
  iIntros (?????) "[Hσ Ht]".
  iMod persistent_time_receipt_0 as "⧖".
  iMod (step_cumulative_time_receipt with "TIME Ht ⧖") as "[%ns1 [Ht [EnFalse [[_ ⧗ ] Hclose]]]]"=>//. { solve_ndisj. }
  replace 2 with (1+1) by lia.
  iDestruct "⧗" as "[⧗ _]".
  iDestruct ("Hwp" with "⧗") as "Hwp".
  iMod ("Hwp" $! _ (ns-1)%nat _ [] 0%nat with "[$]") as "[$ Hwp]".
  iIntros "!>" (e2 σ2 efs stp) "credit".
  iDestruct "credit" as "[Hc1 credit]".
  rewrite (sum_advance_credits_ge1 (ns+1)); last by lia.
  iDestruct "credit" as "[credit1 credit2]".
  iCombine "credit2 Hc1" as "credit2".
  replace (ns - 1 + 1)%nat with ns by lia.
  replace (ns + 1 - 1)%nat with ns by lia.
  iMod ("Hwp" $! e2 σ2 efs stp with "credit2") as "Hwp".
  iIntros "!> !>". iMod "Hwp". iModIntro.
  iApply (step_fupdN_nmono (sum_advance_credits (ns))); first by lia.
  iApply (step_fupdN_wand with "Hwp"). iIntros ">([$ Ht] & Hwp & $)".
  replace (S (ns - 1))%nat with ns by lia.
  iMod ("Hclose" with "[EnFalse Ht credit1]") as "?". {
    iFrame. iApply (lc_weaken with "credit1"). 
    rewrite !Nat.add_1_r.
    cbn [Nat.pow].
    nia.
  }
  iFrame.
  iApply (wp_wand with "[Hwp]"); [iApply (wp_mask_mono with "Hwp"); solve_ndisj|].
  iIntros "!> % H". by iApply "H".
Qed.

Lemma wp_persistent_time_receipt n E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  ⧖n -∗
  (£(advance_credits n) -∗ ⧖(S n) -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  intros tceq Hmask. iIntros "#TIME #⧖ Hwp".
  iApply wp_cumulative_time_receipt1; trivial.
  iIntros "⧗".
  iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[⧖S £]"; first by solve_ndisj.
  replace (n+1)%nat with (S n) by lia.
  iApply ("Hwp" with "£ ⧖S").
Qed.

(** Pure reductions *)
Local Ltac solve_exec_safe :=
  intros; destruct_and?; subst; do 3 eexists; econstructor; simpl; eauto with lia.
Local Ltac solve_exec_puredet :=
  simpl; intros; destruct_and?; inv_head_step; inv_bin_op_eval; inv_lit; done.
Local Ltac solve_pure_exec :=
  intros ?; apply nsteps_once, pure_base_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Global Instance pure_rec e f xl erec erec' el :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ??. solve_pure_exec.
  eapply Forall_impl; [exact Hel|]. intros e' [v <-]. rewrite to_of_val; eauto.
Qed.

Close Scope nat_scope.

Global Instance pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (bool_decide (n1 ≤ n2))).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_int n1 n2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2))) (Lit (bool_decide (n1 = n2))).
Proof. case_bool_decide; solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_r l :
  PureExec True 1 (BinOp EqOp (Lit (LitLoc l)) (Lit (LitInt 0))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_l l :
  PureExec True 1 (BinOp EqOp (Lit (LitInt 0)) (Lit (LitLoc l))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 + z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 - z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_mult z1 z2 :
  PureExec True 1 (BinOp MultOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 * z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset l z  :
  PureExec True 1 (BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z)) (Lit $ LitLoc $ l +ₗ z).
Proof. solve_pure_exec. Qed.

Global Instance pure_case i e el :
  PureExec (0 ≤ i ∧ el !! (Z.to_nat i) = Some e) 1 (Case (Lit $ LitInt i) el) e | 10.
Proof. solve_pure_exec. Qed.

Global Instance pure_if b e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof. destruct b; solve_pure_exec. Qed.

Lemma wp_nd_int E :
  {{{ True }}} NdInt @ E
  {{{ z, RET LitV $ LitInt z; True }}}.
Proof.
  iIntros (? _) "Φ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[σ t] !>"; iSplit. { unshelve auto. apply 0. }
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (time_interp_step with "t") as "$". iFrame "σ". iIntros "credit".
  by iDestruct ("Φ" with "[//]") as "$".
Qed.

Lemma wp_rand E (N : Z) :
  0 < N →
  {{{ True }}} Rand (Lit (LitInt N)) @ E
  {{{ (z : Z), RET LitV $ LitInt z; ⌜0 ≤ z < N⌝ }}}.
Proof.
  iIntros (? Φ _) "HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[σ t] !>"; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply (RandS N 0); lia. }
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (time_interp_step with "t") as "$". iFrame "σ". iIntros "credit".
  iModIntro. iSplit; first done. iApply ("HΦ" $! z). iPureIntro. lia.
Qed.

(** Heap *)
Lemma wp_alloc E (n : Z) :
  0 < n →
  {{{ True }}} Alloc (Lit $ LitInt n) @ E
  {{{ l (sz: nat), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…sz ∗ l ↦∗ repeat (LitV LitPoison) sz }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht] !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (heap_alloc with "Hσ") as "[$ Hl]"; [done..|].
  iMod (time_interp_step with "Ht") as "$". iIntros "credit".
  iModIntro; iSplit=> //. iApply ("HΦ" $! _ (Z.to_nat n)). auto with lia iFrame.
Qed.

Lemma wp_free E (n:Z) l vl :
  ↑naN ⊆ E →
  n = length vl →
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (Hmask ? Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf") as "(% & % & Hσ)"=>//.
  iMod (time_interp_step with "Ht") as "$".
  iModIntro; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iIntros "credit".
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; auto.
Qed.

Lemma wp_read_sc_guarded_cells E l c v d G :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> l ↦[^ c] v) ∗ G ∗ £(d) }}} Read (Lit $ LitLoc l) @ E {{{ RET v; G }}}.
Proof.
  iIntros (Hmask Φ) "[#Gv [G £]] HΦ". iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iMod (atomic_read with "£ [Gv] G Hσ") as (n0) "[%Heq [rim Hσ]]". { trivial. } { rewrite /heap_mapsto_cells_fancy. unfold fv2sum. iFrame "Gv". }
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>". iFrame.
  iSplit. { iPureIntro. eauto using heap_freeable_rel_stable. }
  iSplit; last done.
  (* clear dependent σ1 n. *)
  iApply wp_value.
  iApply ("HΦ" with "rim").
Qed.

Lemma wp_read_sc E l v :
  ↑naN ⊆ E →
  {{{ ▷ l ↦ v }}} Read (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦ v }}}.
Proof.
  iIntros (Hmask Φ) ">pt ToΦ".
  iMod lc_zero as "£0".
  iApply (wp_read_sc_guarded_cells E l [] v 0 with "[pt £0]"); trivial.
  iFrame.
  rewrite /heap_mapsto_cells_fancy /heap_mapsto /=.
  iApply guards_refl.
Qed.

Lemma wp_read_na_guarded_cells E l c G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦[^ c] v)) ∗ G ∗ £(3*d) }}} Read (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  iIntros (Hmask Φ) "[#Gv [G £]] HΦ". iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iDestruct (lc_weaken d with "£") as "£"; first lia.
  iMod (atomic_read with "£ [Gv] G Hσ") as (n0) "[%Heq [rim Hσ]]". { trivial. }
  { rewrite /heap_mapsto_cells_fancy. unfold fv2sum. iFrame "Gv". }
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit. { iPureIntro. eexists _, _, _, _. eapply ReadS; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>". iFrame.
  iSplit. { iPureIntro. eauto using heap_freeable_rel_stable. }
  iSplit; last done.
  iApply wp_value.
  iApply ("HΦ" with "rim").
Qed.

(* Heap-Read *)
Lemma wp_read_na_guarded_cells_0 E l c G v :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN}&&> (l ↦[^ c] v)) ∗ G }}} Read (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  iIntros (Hmask 𝛷) "[g G]". iMod (lc_zero) as "£0".
  iApply wp_read_na_guarded_cells; first trivial. iFrame "g G". done.
Qed.

Lemma wp_read_na E l v :
  ↑naN ⊆ E →
  {{{ ▷ l ↦ v }}} Read (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦ v }}}.
Proof.
  iIntros (Hmask Φ) ">pt ToΦ".
  iMod lc_zero as "£0".
  iApply (wp_read_na_guarded_cells E l [] (l ↦ v)%I v 0 with "[pt £0]"); trivial.
  iFrame. iApply guards_refl.
Qed.

Lemma wp_read_na_guarded_cells_singleton E l c G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦[^ c]∗ [v])) ∗ G ∗ £(3*d) }}} Read (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  case: c=> >; last first.
  { setoid_rewrite guards_weaken_rhs_sep_l. exact: wp_read_na_guarded_cells. }
  iIntros (??) "(gd & G & £ & _) _".
  iAssert (|={E}=> False)%I with "[gd G £]" as ">[]".
  iMod (guards_open_later with "gd G") as "to"=>//.
  iMod (lc_fupd_elim_laterN with "£ to") as ">[[] _]".
Qed.

Lemma wp_read_na_guarded E l G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦ v)) ∗ G ∗ £(3*d) }}} Read (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  intros Hmask. have Ha := wp_read_na_guarded_cells_singleton E l [[]] G v d. simpl in Ha.
  unfold heap_mapsto_cells_val_vec in Ha. simpl in Ha. unfold heap_mapsto_fancy_vec in Ha.
  simpl in Ha. unfold heap_mapsto. setoid_rewrite bi.sep_True in Ha; last by apply _.
  apply Ha. apply Hmask.
Qed.


(* The extra +1 in £ is problematic*)
Lemma wp_write_sc_guarded E l c e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d+1) }}} Write (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask <- Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
  iMod (heap_write with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose".
    iSplit. { iPureIntro. eexists _, _, _, _. eapply WriteS; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1.
  iApply wp_value.
  iApply ("HΦ" with "[$Hv' $G]").
Qed.

(* The extra £1 is the problem *)
Lemma wp_write_sc E l e v v' :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ ▷ l ↦ v' ∗ £1 }}} Write (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (Hmask IntoVal Φ) "[>pt £] ToΦ".
  (* iMod lc_zero as "£0". *)
  iApply (wp_write_sc_guarded E l [] e v v' 0 (True)%I with "[pt £]"); trivial.
   - iFrame. replace ((l, []) #↦_)%I with (True : iProp Σ)%I.
     2: { unfold heap_complete_mapsto. simpl. trivial. }
     iApply guards_true.
   - iNext. iIntros "[A B]". iApply "ToΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed. 

Lemma wp_write_na_guarded E l c e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d+1) }}} Write (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask <- Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
  iMod (heap_write with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. eexists _, _, _, _. eapply WriteS; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iFrame "Hσ". iSplit; last done.
  iApply wp_value. iApply "HΦ". iFrame.
Qed.

Lemma wp_write_na_guarded_0 E l cells e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,cells) #↦_)) ∗ G ∗ (l,cells) #↦ v' ∗ £(3*d+1) }}} Write (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,cells) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask Hval 𝛷) "H HΦ".
  iApply (wp_write_na_guarded with "H"); done.
Qed.

Local Open Scope nat_scope.

Lemma wp_write_na_guarded_more_credits E l c e v v' d G d' :
  ↑naN ∪ ↑timeN ⊆ E →
  IntoVal e v →
  time_ctx -∗
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d+1) ∗ ⧖(d') }}} Write (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G ∗ £(6*d'+1) }}}.
Proof.
  iIntros (Hmask <-) "#TIME". iIntros (Φ). iModIntro.
  iIntros "(#guards & G & Hv & £ & ⧖) HΦ".
  rewrite !wp_unfold /wp_pre /=. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
  iMod (heap_write _ _ _ v with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by set_solver.
  iMod cumulative_time_receipt_0 as "⧗0".
  iMod (time_receipt_le' with "TIME Ht ⧖ ⧗0") as "[%Htimebound [Ht ⧗0]]"; first by set_solver.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. apply base_prim_reducible. eexists _, _, _, _. eapply WriteS; eauto. }
  iIntros (e2 σ2 efs Hstep) "credit". iModIntro. iNext. iModIntro.
  iApply (step_fupdN_intro); first by set_solver. iNext. iMod "Hclose" as "_".
  assert (base_step (Write (Lit (LitLoc l)) (of_val v)) σ1 κ e2 σ2 efs) as Hbasestep.
    { apply base_reducible_prim_step; trivial. eexists _, _, _, _. eapply WriteS; eauto. }
  inv_head_step.
  iMod (time_interp_step with "Ht") as "$".
  iModIntro.
  iFrame "Hσ".
  iSplit; last done.
  iApply wp_value. iApply "HΦ". iFrame "Hv' G".
  (* Extract £(6*d'+1) from the per-step credit budget. *)
  iApply (lc_weaken with "credit").
  rewrite Nat.add_1_r. cbn [sum_advance_credits].
  assert (stepcnt + 1 = S stepcnt) as -> by lia. cbn [sum_advance_credits].
  assert (d' ≤ 2 ^ S (S stepcnt)) as Hd'. { cbn [Nat.pow]. lia. }
  rewrite /advance_credits. nia.
Qed.
  
Lemma wp_write_na E l e v v' :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ ▷ l ↦ v' ∗ £1 }}} Write (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (Hmask IntoVal Φ) "[>pt £] ToΦ".
  iApply (wp_write_na_guarded E l [] e v v' 0 (True)%I with "[pt £]"); trivial.
   - iFrame. replace ((l, []) #↦_)%I with (True : iProp Σ)%I.
     2: { unfold heap_complete_mapsto. simpl. trivial. }
     iApply guards_true.
   - iNext. iIntros "[A B]". iApply "ToΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed.

(* Heap-Move-Cell *)
(*
In practice, you'll usually want to use one of the "untether" lemmas directly, since these
are more flexible because they let you separate the logical step of moving the cell from
the physical steps of moving data. The proof here illustrates the concept.
Also, this matches the special case presented in the paper.
*)
Lemma wp_cell_move_na E l l' cell v' :
  ↑naN ⊆ E →
  {{{ l ↦! (FCell cell) ∗ l' ↦ v' ∗ £1 }}} Write (Lit $ LitLoc l') (Read (Lit $ LitLoc l)) @ E
  {{{ RET LitV LitPoison; ∃ v, l ↦ v ∗ l' ↦! (FCell cell) }}}.
Proof.
  intros Hmask. iIntros (𝛷) "(pt & pt' & £) post". iApply wp_fupd.
  (* untether the cell from the location, get a concrete value v *)
  iMod (mapsto_vec_untether1 (l, []) (FCell cell) with "pt") as (v) "[pt [retether ?]]".
  (* copy the concrete value v *)
  change (Write (Lit (LitLoc l')) (Read (Lit (LitLoc l))))
      with (fill_item (WriteRCtx (LitV (LitLoc l'))) (Read (Lit (LitLoc l)))).
  iApply wp_bind.
  iApply (wp_read_na with "pt"); first trivial. iModIntro. iIntros "pt".
  iApply (wp_write_na _ _ _ v with "[pt' £]"); [trivial|done| |].
  { iFrame. }
  (* retether the cell to the new location *)
  iModIntro. iIntros "pt'".
  iMod ("retether" $! (l', []) with "[pt']") as "[? pt']". { iSplitR. { done. }
    unfold heap_complete_mapsto_fancy, split_at_last, rev. simpl.
    unfold heap_mapsto. iFrame "pt'".
  }
  iModIntro. iApply "post". iFrame.
Qed.

Lemma wp_eq_loc E (l1 : loc) (l2: loc) v1 v2 P Φ :
  ↑naN ⊆ E →
  (P -∗ ▷ l1 ↦ v1) →
  (P -∗ ▷ l2 ↦ v2) →
  (P -∗ ▷ Φ (LitV (bool_decide (l1 = l2)))) →
  P -∗ WP BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ E {{ Φ }}.
Proof.
  iIntros (Hmask Hl1 Hl2 Hpost) "HP".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply wp_lift_pure_det_base_step_no_fork';
      [done|solve_exec_safe|solve_exec_puredet|].
    iAssert (▷ (WP Lit true @ E {{ v, Φ v }}))%I with "[HP]" as "X".
     + iApply wp_value. by iApply Hpost.
     + iNext. iIntros. iFrame "X".
  - iApply wp_lift_atomic_base_step_no_fork; subst=>//.
    iIntros (σ1 stepcnt κ κs n') "[Hσ1 Ht]".
    iMod (time_interp_step with "Ht") as "$".
    iModIntro. inv_head_step. iSplitR.
    { iPureIntro. repeat eexists. econstructor. eapply BinOpEqFalse. by auto. }
    (* We need to do a little gymnastics here to apply Hne now and strip away a
       ▷ but also have the ↦s. *)
    iAssert ((▷ ∃ v, l1 ↦ v) ∧ (▷ ∃ v, l2 ↦ v) ∧ ▷ Φ (LitV false))%I
      with "[HP]" as "HP".
    { iSplit; last iSplit.
      + iExists _. by iApply Hl1.
      + iExists _. by iApply Hl2.
      + by iApply Hpost. }
    clear Hl1 Hl2. iNext. iIntros (e2 σ2 efs Hs) "£".
    inv_head_step. iSplitR=>//. inv_bin_op_eval; inv_lit.
    + iDestruct "HP" as "[Hl1 _]".
      iDestruct "Hl1" as (?) "Hl1".
      iMod (heap_read σ2 with "Hσ1 Hl1") as "[_ [_ %X]]"; first by set_solver.
      destruct X as [n0 X]. exfalso. simplify_eq.
    + iDestruct "HP" as "[_ [Hl2 _]]".
      iDestruct "Hl2" as (?) "Hl2".
      iMod (heap_read σ2 with "Hσ1 Hl2") as "[_ [_ %X]]"; first by set_solver.
      destruct X as [n0 X]. exfalso. simplify_eq.
    + iDestruct "HP" as "[_ [_ $]]". done.
Qed.

(** Proof rules for working on the n-ary argument list. *)
Lemma wp_app_ind E f (el : list expr) (Ql : vec (val → iProp Σ) (length el)) vs Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> vs ++ vl) @ E {{ Φ }}) -∗
    WP App f ((of_val <$> vs) ++ el) @ E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=. by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el))
      with (fill_item (AppRCtx vf vs el) e).
    iApply wp_bind. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "* Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma wp_app_vec E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof. iIntros (Hf). by iApply (wp_app_ind _ _ _ _ []). Qed.

Lemma wp_app (Ql : list (val → iProp Σ)) E f el Φ :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.

Close Scope nat_scope.
 
End lifting.
