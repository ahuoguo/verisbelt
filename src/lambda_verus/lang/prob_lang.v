(** Probabilistic variant of lrust_lang for eris.

    Imports [syntax.v] (pure Coq λRust syntax) + eris's probabilistic
    language framework; produces a [head_step : expr → state → distr
    (expr * state)] with [Rand #N] sampling from the uniform
    distribution over [0..N-1].

    The relational [syntax.head_step] is kept alongside for
    Iris-based WP compatibility during the Pass C migration. *)
From Stdlib Require Import Reals Psatz.
From stdpp Require Import gmap fin_maps countable ssreflect.
From eris.common Require Export language ectx_language ectxi_language.
From eris.prob Require Export distribution.
From eris.prelude Require Import stdpp_ext classical.
From lrust.lang Require Export syntax.
(* After importing eris (which has ectxiLanguage record fields named
   [expr]/[val]/[state]/[head_step]/…), re-importing syntax last ensures
   syntax's concrete types shadow the record projections in this file. *)
Import syntax.
Set Default Proof Using "Type".
Open Scope R.

(** * Computable, probabilistic head step *)

(** Computable pointer/integer equality — the probabilistic variant of
    [lit_eq] from [syntax.v]. We drop the [LocUnallocL/R] non-deterministic
    cases: pointer equality is fully structural here. *)
Definition lit_eq_dec (l1 l2 : base_lit) : option bool :=
  match l1, l2 with
  | LitInt z1, LitInt z2 => Some (bool_decide (z1 = z2))
  | LitLoc p1, LitLoc p2 => Some (bool_decide (p1 = p2))
  | LitInt 0%Z, LitLoc _ | LitLoc _, LitInt 0%Z => Some false
  | _, _ => None
  end.

Definition bin_op_eval_fn (op : bin_op) (l1 l2 : base_lit) : option base_lit :=
  match op, l1, l2 with
  | PlusOp, LitInt z1, LitInt z2 => Some (LitInt (z1 + z2))
  | MinusOp, LitInt z1, LitInt z2 => Some (LitInt (z1 - z2))
  | MultOp, LitInt z1, LitInt z2 => Some (LitInt (z1 * z2))
  | LeOp, LitInt z1, LitInt z2 =>
      Some (lit_of_bool (bool_decide (z1 ≤ z2)%Z))
  | EqOp, _, _ =>
      (λ b, lit_of_bool b) <$> lit_eq_dec l1 l2
  | OffsetOp, LitLoc l, LitInt z => Some (LitLoc (shift_loc l z))
  | _, _, _ => None
  end.

Definition fresh_loc (σ : state) : loc := (fresh_block σ, 0%Z).

Definition head_step_prob (e : expr) (σ : state) : distr (expr * state) :=
  match e with
  | App (Rec f xl e) el =>
      if bool_decide (Forall (λ ei, is_Some (to_val ei)) el ∧
                      Closed (f :b: xl +b+ []) e) then
        match subst_l (f :: xl) (Rec f xl e :: el) e with
        | Some e' => dret (e', σ)
        | None => dzero
        end
      else dzero
  | BinOp op (Lit l1) (Lit l2) =>
      match bin_op_eval_fn op l1 l2 with
      | Some l' => dret (Lit l', σ)
      | None => dzero
      end
  (* Uniform sampling from [0, N). [dunifP k] samples from [fin (S k)],
     so with bound [Z.to_nat N - 1] we get [fin (Z.to_nat N)] when N ≥ 1. *)
  | Rand (Lit (LitInt N)) =>
      if bool_decide (0 < N)%Z then
        dmap (λ n : fin (S (Z.to_nat N - 1)),
              (Lit (LitInt (Z.of_nat (fin_to_nat n))), σ))
             (dunifP (Z.to_nat N - 1))
      else dzero
  | Read (Lit (LitLoc l)) =>
      match σ !! l with
      | Some (RSt _, v) => dret (of_val v, σ)
      | _ => dzero
      end
  | Write (Lit (LitLoc l)) e2 =>
      match to_val e2, σ !! l with
      | Some v, Some (RSt 0, _) =>
          dret (Lit LitPoison, <[l := (RSt 0, v)]> σ)
      | _, _ => dzero
      end
  | Alloc (Lit (LitInt n)) =>
      if bool_decide (0 < n)%Z then
        let ℓ := fresh_loc σ in
        dret (Lit (LitLoc ℓ), init_mem ℓ (Z.to_nat n) σ)
      else dzero
  | Free (Lit (LitInt n)) (Lit (LitLoc l)) =>
      if bool_decide (0 < n)%Z then
        dret (Lit LitPoison, free_mem l (Z.to_nat n) σ)
      else dzero
  | Case (Lit (LitInt i)) el =>
      if bool_decide (0 ≤ i)%Z then
        match el !! Z.to_nat i with
        | Some ei => dret (ei, σ)
        | None => dzero
        end
      else dzero
  (* Unbounded non-determinism ([NdInt]) is not expressible as a
     discrete probability distribution; it is stuck in the
     probabilistic semantics. Use [Rand #N] for bounded sampling. *)
  | _ => dzero
  end.

(** * Trivial [state_step] / [get_active] — no presampling tapes.

    [state_idx := Empty_set] — there are no tape identifiers. *)
Definition state_step_prob (σ : state) (α : Empty_set) : distr state := dzero.
Definition get_active (σ : state) : list Empty_set := [].

(** * Evaluation-context decomposition *)

(** [decomp_item e = Some (Ki, e')] iff [e = fill_item Ki e'] and [e']
    is not a value. Left-to-right evaluation order. *)
Definition decomp_item (e : expr) : option (ectx_item * expr) :=
  let noval (e' : expr) (Ki : ectx_item) :=
    match to_val e' with Some _ => None | None => Some (Ki, e') end in
  match e with
  | BinOp op e1 e2 =>
      match to_val e1 with
      | None => noval e1 (BinOpLCtx op e2)
      | Some v1 => noval e2 (BinOpRCtx op v1)
      end
  | Read e' => noval e' ReadCtx
  | Rand e' => noval e' RandCtx
  | Write e1 e2 =>
      match to_val e1 with
      | None => noval e1 (WriteLCtx e2)
      | Some v1 => noval e2 (WriteRCtx v1)
      end
  | Alloc e' => noval e' AllocCtx
  | Free e1 e2 =>
      match to_val e1 with
      | None => noval e1 (FreeLCtx e2)
      | Some v1 => noval e2 (FreeRCtx v1)
      end
  | Case e' el => noval e' (CaseCtx el)
  | App e' el =>
      (* Either [e'] is not a value (AppLCtx), or we're walking the
         argument list left-to-right (AppRCtx). *)
      match to_val e' with
      | None => noval e' (AppLCtx el)
      | Some v =>
          (* Scan [el] for the first non-value argument. *)
          let fix scan (vl : list val) (el : list expr) : option (ectx_item * expr) :=
            match el with
            | [] => None
            | e'' :: el' =>
                match to_val e'' with
                | None => Some (AppRCtx v (reverse vl) el', e'')
                | Some v' => scan (v' :: vl) el'
                end
            end in
          scan [] el
      end
  | _ => None
  end.

(** * Expression ordering (well-founded) via structural height *)
Fixpoint expr_height (e : expr) : nat :=
  match e with
  | Var _ | Lit _ | NdInt => 0
  | Rec _ _ e => S (expr_height e)
  | BinOp _ e1 e2 | Write e1 e2 | Free e1 e2 =>
      S (Nat.max (expr_height e1) (expr_height e2))
  | App e el | Case e el =>
      S (Nat.max (expr_height e) (list_max (expr_height <$> el)))
  | Read e | Alloc e | Rand e => S (expr_height e)
  end.

Definition expr_ord (e1 e2 : expr) : Prop := (expr_height e1 < expr_height e2)%nat.

Lemma expr_ord_wf' h e : (expr_height e ≤ h)%nat → Acc expr_ord e.
Proof.
  revert e; induction h as [|h IH]; intros e Hh; constructor; intros e' He'.
  - rewrite /expr_ord in He'. lia.
  - apply IH. rewrite /expr_ord in He'. lia.
Qed.

Lemma expr_ord_wf : well_founded expr_ord.
Proof. red. intros e. eapply expr_ord_wf'. done. Qed.

(** * Countability of [ectx_item] (required by the eris mixin). *)
Global Instance ectx_item_eq_dec : EqDecision ectx_item.
Proof. solve_decision. Defined.

Global Instance ectx_item_countable : Countable ectx_item.
Proof.
  set (enc := λ Ki,
    match Ki with
    | BinOpLCtx op e2 => GenNode 0 [GenLeaf (inl op); GenLeaf (inr (inl e2))]
    | BinOpRCtx op v1 => GenNode 1 [GenLeaf (inl op); GenLeaf (inr (inr v1))]
    | AppLCtx el      => GenNode 2 [GenLeaf (inr (inl (App (Lit LitPoison) el)))]
    | AppRCtx v vl el => GenNode 3 [GenLeaf (inr (inr v));
                                    GenLeaf (inr (inl (App (Lit LitPoison) (map of_val vl))));
                                    GenLeaf (inr (inl (App (Lit LitPoison) el)))]
    | ReadCtx         => GenNode 4 []
    | WriteLCtx e2    => GenNode 5 [GenLeaf (inr (inl e2))]
    | WriteRCtx v1    => GenNode 6 [GenLeaf (inr (inr v1))]
    | AllocCtx        => GenNode 7 []
    | FreeLCtx e2     => GenNode 8 [GenLeaf (inr (inl e2))]
    | FreeRCtx v1     => GenNode 9 [GenLeaf (inr (inr v1))]
    | CaseCtx el      => GenNode 10 [GenLeaf (inr (inl (App (Lit LitPoison) el)))]
    | RandCtx         => GenNode 11 []
    end).
  set (unpack_list := λ e,
    match e with App _ el => el | _ => [] end).
  set (unpack_vals := λ e,
    match e with App _ el =>
      foldr (λ e' acc, match to_val e' with Some v => v :: acc | None => acc end) [] el
    | _ => []
    end).
  set (dec := λ t,
    match t with
    | GenNode 0 [GenLeaf (inl op); GenLeaf (inr (inl e2))] => BinOpLCtx op e2
    | GenNode 1 [GenLeaf (inl op); GenLeaf (inr (inr v1))] => BinOpRCtx op v1
    | GenNode 2 [GenLeaf (inr (inl e))] => AppLCtx (unpack_list e)
    | GenNode 3 [GenLeaf (inr (inr v)); GenLeaf (inr (inl evl)); GenLeaf (inr (inl eel))] =>
        AppRCtx v (unpack_vals evl) (unpack_list eel)
    | GenNode 4 [] => ReadCtx
    | GenNode 5 [GenLeaf (inr (inl e2))] => WriteLCtx e2
    | GenNode 6 [GenLeaf (inr (inr v1))] => WriteRCtx v1
    | GenNode 7 [] => AllocCtx
    | GenNode 8 [GenLeaf (inr (inl e2))] => FreeLCtx e2
    | GenNode 9 [GenLeaf (inr (inr v1))] => FreeRCtx v1
    | GenNode 10 [GenLeaf (inr (inl e))] => CaseCtx (unpack_list e)
    | GenNode 11 [] => RandCtx
    | _ => ReadCtx (* unreachable *)
    end).
  refine (inj_countable' enc dec _).
  intros [| | | v vl el | | | | | | | |]; simpl; subst unpack_list unpack_vals;
    try reflexivity.
  (* AppRCtx: round-trip [vl] through [map of_val] + [foldr to_val]. *)
  f_equal. clear v el. induction vl as [|w vl IH]; simpl; [reflexivity|].
  by rewrite to_of_val IH.
Qed.

(** * EctxiLanguage mixin obligations

    The trivial ones ([state_step_*]) are discharged here; the
    non-trivial cases ([val_stuck_prob], [head_step_mass_prob],
    [head_ctx_step_val_prob], [decomp_*]) are left as a follow-up. *)

Lemma state_step_head_not_stuck e σ σ' (α : Empty_set) :
  state_step_prob σ α σ' > 0 →
  (∃ ρ, head_step_prob e σ ρ > 0) ↔ (∃ ρ', head_step_prob e σ' ρ' > 0).
Proof. destruct α. Qed.

Lemma state_step_mass σ (α : Empty_set) :
  α ∈ get_active σ → SeriesC (state_step_prob σ α) = 1.
Proof. destruct α. Qed.

Lemma val_stuck_prob e σ ρ :
  head_step_prob e σ ρ > 0 → to_val e = None.
Proof.
  intros Hstep. destruct e eqn:He; simpl in *; try reflexivity;
    try (rewrite dzero_0 in Hstep; lra).
Qed.

Lemma head_ctx_step_val_prob Ki e σ ρ :
  head_step_prob (fill_item Ki e) σ ρ > 0 → is_Some (to_val e).
Proof.
  intros H. destruct Ki; simpl in H; (repeat case_match);
    try (rewrite dzero_0 in H; lra);
    try (eexists; simpl; reflexivity); eauto using to_of_val.
  - apply bool_decide_eq_true in H1 as [_ HC]. simpl. case_decide; eauto.
    contradiction.
  - apply bool_decide_eq_true in H1 as [HF _].
    apply Forall_app in HF as [_ HF]. apply Forall_cons in HF as [He _]. exact He.
Qed.

Lemma head_step_mass_prob e σ :
  (∃ ρ, head_step_prob e σ ρ > 0) → SeriesC (head_step_prob e σ) = 1.
Proof.
  intros [ρ Hρ]. destruct e; simpl in *; (repeat case_match);
    try (rewrite dzero_0 in Hρ; lra);
    try (rewrite dret_mass; reflexivity).
  rewrite dmap_mass dunifP_mass. reflexivity.
Qed.

Lemma decomp_expr_ord Ki e e' :
  decomp_item e = Some (Ki, e') → expr_ord e' e.
Proof.
  rewrite /expr_ord /decomp_item.
  destruct e; try discriminate; (repeat case_match); try discriminate;
    try (intros [= <- <-]; simpl; lia).
  generalize (@nil val) as vl. induction el as [|e'' el' IH]; intros vl Hscan.
  - discriminate.
  - destruct (to_val e'') eqn:Hv''.
    + specialize (IH _ Hscan).
      cbn [expr_height list_max fmap list_fmap] in *.
      simpl list_max. lia.
    + injection Hscan as <- <-. cbn [expr_height].
      change (expr_height <$> e'' :: el') with
             (expr_height e'' :: (expr_height <$> el')).
      simpl list_max. lia.
Qed.

Lemma decomp_fill_item Ki e :
  to_val e = None → decomp_item (fill_item Ki e) = Some (Ki, e).
Proof.
  intros Hnv. destruct Ki; simpl; rewrite ?Hnv; try reflexivity.
  all: rewrite ?to_of_val ?Hnv //.
  (* AppRCtx: induction over the accumulator-threading scan. *)
  assert (∀ acc,
    (fix scan (vl0 : list val) (el0 : list expr) {struct el0} :
        option (ectx_item * expr) :=
      match el0 with
      | [] => None
      | e'' :: el' =>
          match to_val e'' with
          | Some v' => scan (v' :: vl0) el'
          | None => Some (AppRCtx v (reverse vl0) el', e'')
          end
      end) acc ((of_val <$> vl) ++ e :: el)
    = Some (AppRCtx v (reverse acc ++ vl) el, e)) as Hgen.
  { intros acc. induction vl as [|v' vl' IH] in acc |- *; simpl.
    - rewrite Hnv app_nil_r. done.
    - rewrite to_of_val IH. f_equal. f_equal. f_equal.
      rewrite reverse_cons -app_assoc. done. }
  specialize (Hgen []). rewrite Hgen reverse_nil //.
Qed.

Lemma decomp_fill_item_2 e e' Ki :
  decomp_item e = Some (Ki, e') → fill_item Ki e' = e ∧ to_val e' = None.
Proof.
  rewrite /decomp_item. destruct e; try discriminate;
    (repeat case_match); try discriminate;
    try (intros [= <- <-]; simpl; split; [rewrite ?of_to_val //|done]).
  1,3,4: f_equal; by apply of_to_val.
  (* AppRCtx: extract the structural relation from the scan, then read off
     the fill_item and non-value facts. *)
  assert (∀ acc,
    (fix scan (vl : list val) (el0 : list expr) {struct el0} :
        option (ectx_item * expr) :=
      match el0 with
      | [] => None
      | e'' :: el' =>
          match to_val e'' with
          | Some v' => scan (v' :: vl) el'
          | None => Some (AppRCtx v (reverse vl) el', e'')
          end
      end) acc el = Some (Ki, e') →
    ∃ vls elr, el = (of_val <$> vls) ++ e' :: elr
      ∧ Ki = AppRCtx v (reverse acc ++ vls) elr ∧ to_val e' = None) as Hgen.
  { clear. induction el as [|e0 el' IH]; intros acc Hscan.
    - discriminate.
    - simpl in Hscan. destruct (to_val e0) eqn:He0.
      + apply IH in Hscan as (vls & elr & -> & HK & ?).
        exists (v0 :: vls), elr. split; [|split]; [| |done].
        { simpl. apply of_to_val in He0. rewrite He0 //. }
        { rewrite HK. rewrite reverse_cons -app_assoc //. }
      + injection Hscan as <- <-. exists [], el'. split; [|split]; [| |done].
        { simpl. reflexivity. }
        { rewrite app_nil_r //. } }
  intros Hscan. apply Hgen in Hscan as (vls & elr & -> & -> & ?).
  apply of_to_val in H. rewrite -H. split; [|done]. reflexivity.
Qed.

(** * Canonical [ectxiLanguage] for the probabilistic λRust. *)

Lemma lrust_prob_lang_mixin :
  EctxiLanguageMixin of_val to_val fill_item decomp_item expr_ord
    head_step_prob state_step_prob get_active.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_stuck_prob,
    state_step_head_not_stuck, state_step_mass, head_step_mass_prob,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val_prob,
    decomp_fill_item, decomp_fill_item_2, expr_ord_wf, decomp_expr_ord.
Qed.

Canonical Structure lrust_prob_ectxi_lang :=
  EctxiLanguage get_active lrust_prob_lang_mixin (def_val := LitV LitPoison).
Canonical Structure lrust_prob_ectx_lang := EctxLanguageOfEctxi lrust_prob_ectxi_lang.
Canonical Structure lrust_prob_lang := LanguageOfEctx lrust_prob_ectx_lang.
