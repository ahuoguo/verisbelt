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
Print invGS_gen.
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
      rewrite dret_1_1 //. lra. }
    iNext. iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iModIntro. iFrame "Hσ". by iApply "HΦ".
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

(** [pure_eq_int]: deferred — [bin_op_eval_fn EqOp (LitInt _) (LitInt _)]
    goes through [(λ b, lit_of_bool b) <$> lit_eq_dec _ _]; the [<$>]
    on [option] doesn't reduce under [simpl]/[cbn] without an explicit
    rewrite chain we haven't worked out. *)

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
