From lrust.lang Require Export notation.
From lrust.lang Require Import heap proofmode.
From lrust.util Require Import non_atomic_cell_map update.
From guarding Require Import guard.
From lrust.lifetime Require Import lifetime_full.
From iris.base_logic.lib Require Import later_credits.
Set Default Proof Using "Type".

Definition memcpy : val :=
  rec: "memcpy" ["dst";"len";"src"] :=
    if: "len" ≤ #0 then #☠
    else "dst" <- !"src";;
         "memcpy" ["dst" +ₗ #1 ; "len" - #1 ; "src" +ₗ #1].

Notation "e1 <-{ n } ! e2" :=
  (App (of_val memcpy) [e1%E; Lit (LitInt n); e2%E])
  (at level 80, n at next level, format "e1  <-{ n }  ! e2") : expr_scope.

Notation "e1 <-{ n ',Σ' i } ! e2" :=
  (e1%E%E <- #(LitInt i);; e1 +ₗ #(LitInt 1) <-{n} !e2)%E
  (at level 80, n, i at next level, format "e1  <-{ n ,Σ  i }  ! e2") : expr_scope.

Lemma wp_memcpy `{!lrustGS Σ} E l1 l2 vl1 vl2 (n : Z) :
  ↑non_atomic_cell_map.naN ⊆ E →
  Z.of_nat (length vl1) = n → Z.of_nat (length vl2) = n →
  {{{ l1 ↦∗ vl1 ∗ l2 ↦∗ vl2 }}}
    #l1 <-{n} !#l2 @ E
  {{{ RET #☠; l1 ↦∗ vl2 ∗ l2 ↦∗ vl2 }}}.
Proof.
  iIntros (? Hvl1 Hvl2 Φ) "(Hl1 & Hl2) HΦ".
  iLöb as "IH" forall (n l1 l2 vl1 vl2 Hvl1 Hvl2). wp_rec. wp_op; case_bool_decide; wp_if.
  - iApply "HΦ". assert (n = O) by lia; subst.
    destruct vl1, vl2; try discriminate. by iFrame.
  - destruct vl1 as [|v1 vl1], vl2 as [|v2 vl2], n as [|n|]; try (discriminate || lia).
    revert Hvl1 Hvl2. intros [= Hvl1] [= Hvl2]; rewrite !heap_mapsto_vec_cons. subst n.
    iDestruct "Hl1" as "[Hv1 Hl1]". iDestruct "Hl2" as "[Hv2 Hl2]".
    Local Opaque Zminus.
    wp_read; wp_write. do 3 wp_op. iApply ("IH" with "[%] [%] Hl1 Hl2"); [lia..|].
    iIntros "!> [Hl1 Hl2]"; iApply "HΦ"; by iFrame.
Qed.

(** [wp_memcpy_guarded]: upstream-shape guarded memcpy with
    per-iteration credit refresh via [wp_write_guarded_more_credits].
    The credit budget is independent of [n]; each iteration consumes
    [£d] for the read and [£(3*d+1)] for the write, and gets back
    [£(6*d+1)] from the write's bonus, so the budget refreshes itself.

    Mirrors verisbelt's [wp_memcpy_guarded] (with atomic primitives
    in place of non-atomic). *)
Lemma wp_memcpy_guarded `{!lrustGS Σ} E (l1 l2 : heap.cloc)
      (vl1 vl2 : list val) (Hw Hr : iProp Σ) (n : Z) d :
  ↑non_atomic_cell_map.naN ∪ ↑timeN ⊆ E →
  Z.of_nat (length vl1) = n → Z.of_nat (length vl2) = n →
  time_ctx -∗
  {{{ heap.heap_complete_mapsto_val_vec l1 vl1 ∗
      (Hw &&{↑NllftG; d}&&> heap.heap_complete_mapsto_vec l1) ∗
      (Hr &&{↑NllftG; d}&&> heap.heap_mapsto_cells_val_vec l2.1 l2.2 vl2)
      ∗ Hw ∗ Hr
      ∗ ⧖d ∗ £(6*d+1) }}}
    #(l1.1) <-{n} !#(l2.1) @ E
  {{{ RET LitV LitPoison;
      heap.heap_complete_mapsto_val_vec l1 vl2 ∗ Hw ∗ Hr }}}.
Proof.
  iIntros (HE Hvl1 Hvl2) "#TIME".
  iIntros (Φ) "!> (Hl1 & wguard & rguard & Hw & Hr & #⧖d & H£) HΦ".
  iLöb as "IH" forall (n l1 l2 vl1 vl2 Hvl1 Hvl2).
  wp_rec. wp_op; case_bool_decide; wp_if.
  - iApply "HΦ". assert (n = O) by lia; subst.
    destruct vl1, vl2; try discriminate. by iFrame.
  - destruct vl1 as [|v1 vl1], vl2 as [|v2 vl2], n as [|n|];
      try (discriminate || lia).
    revert Hvl1 Hvl2. intros [= Hvl1] [= Hvl2]. subst n.
    destruct l1 as [l1 cells1]; destruct cells1 as [|c1 cells1]; first by done.
    rewrite heap.heap_mapsto_cloc_vals_vec_cons.
    iDestruct "Hl1" as "[Hv1 Hl1]".
    rewrite heap.heap_mapsto_cloc_emp_cons.
    destruct l2 as [l2 cells2]; destruct cells2 as [|c2 cells2].
    { iApply fupd_pgl_wp.
      iMod (guards_open_later _ _ E (↑NllftG) d with "rguard Hr")
        as "Hop"; first solve_ndisj.
      iDestruct (lc_weaken d with "H£") as "H£'"; first lia.
      iMod (lc_fupd_elim_laterN with "H£' Hop") as ">[Hvec _]".
      rewrite /heap.heap_mapsto_cells_val_vec /heap.heap_mapsto_cells_fancy_vec /=.
      by iDestruct "Hvec" as %[]. }
    simpl. rewrite heap.heap_mapsto_cells_val_vec_cons.
    iDestruct (guards_weaken_rhs_sep_l with "wguard") as "#wguard1".
    iDestruct (guards_weaken_rhs_sep_r with "wguard") as "#wguard2".
    iDestruct (guards_weaken_rhs_sep_l with "rguard") as "#rguard1".
    iDestruct (guards_weaken_rhs_sep_r with "rguard") as "#rguard2".
    (* Split £(6*d+1) into £d (read) + £(3*d+1) (write_more_credits)
       + £(2*d) (slack, discarded — the write returns £(6*d+1) for
       the recursive call). *)
    iDestruct (lc_weaken (d + ((3*d+1) + (2*d))) with "H£") as "H£all";
      first lia.
    iDestruct (lc_split with "H£all") as "[H£1 H£rest]".
    iDestruct (lc_split with "H£rest") as "[H£2 _]".
    wp_bind (!#l2)%E.
    iApply (wp_read_guarded_cell with "[$rguard1 $Hr $H£1]"); first solve_ndisj.
    iIntros "!> Hr".
    wp_bind (#l1 <- v2)%E.
    iApply (wp_write_guarded_more_credits _ (l1, c1) v2 v1 Hw d d
              with "TIME [$wguard1 $Hw $Hv1 $H£2 $⧖d]");
      first solve_ndisj.
    iIntros "!> (Hv2 & Hw & H£fresh)".
    wp_seq. do 3 wp_op.
    iApply ("IH" $! (Z.pos (Pos.of_succ_nat (length vl1)) - 1)%Z
              (l1 +ₗ 1, cells1) (l2 +ₗ 1, cells2)
              with "[%] [%] Hl1 wguard2 rguard2 Hw Hr H£fresh");
      [lia..|].
    iIntros "!> [Hl1 [Hw Hr]]".
    iApply "HΦ". iFrame "Hw Hr".
    rewrite heap.heap_mapsto_cloc_vals_vec_cons. iFrame.
Qed.
