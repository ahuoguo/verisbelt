(** Pure λRust syntax + the clutch [ectxi_language] wrapper.

    The pure-data section is wrapped in [Module Export pure] so that its
    names ([expr], [val], [state], [to_val], [of_val], …) can be
    re-imported after [clutch.common.language]'s [Export]; otherwise
    clutch's record projections of the same names would shadow our
    inductives. *)
From stdpp Require Export strings binders.
From stdpp Require Import gmap countable.
From stdpp Require Export ssreflect.
From iris.prelude Require Import options.
Set Default Proof Using "Type".

(* nat → Z coercion and expr/val scope delimiters normally come with
   iris.bi.prelude and iris.bi.weakestpre.*)
Coercion Z.of_nat : nat >-> Z.
Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Declare Scope val_scope.
Delimit Scope val_scope with V.

Open Scope Z_scope.

Module Export pure.

(** Expressions and vals. *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Declare Scope loc_scope.
Bind Scope loc_scope with loc.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Inductive base_lit : Set :=
| LitPoison | LitLoc (l : loc) | LitInt (n : Z).
Inductive bin_op : Set :=
| PlusOp | MinusOp | MultOp | LeOp | EqOp | OffsetOp.

Notation "[ ]" := (@nil binder) : binder_scope.
Notation "a :: b" := (@cons binder a%binder b%binder)
  (at level 60, right associativity) : binder_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons binder x1%binder (@cons binder x2%binder
        (..(@cons binder xn%binder (@nil binder))..))) : binder_scope.
Notation "[ x ]" := (@cons binder x%binder (@nil binder)) : binder_scope.

Inductive expr :=
| Var (x : string)
| Lit (l : base_lit)
| Rec (f : binder) (xl : list binder) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| NdInt
| Rand (e : expr)
| App (e : expr) (el : list expr)
| Read (e : expr)
| Write (e1 e2: expr)
| Alloc (e : expr)
| Free (e1 e2 : expr)
| Case (e : expr) (el : list expr).

Arguments App _%E _%E.
Arguments Case _%E _%E.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Lit _ | NdInt => true
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write e1 e2 | Free e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Read e | Alloc e | Rand e => is_closed X e
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Global Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Global Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

Inductive val :=
| LitV (l : base_lit)
| RecV (f : binder) (xl : list binder) (e : expr) `{!Closed (f :b: xl +b+ []) e}.

Bind Scope val_scope with val.

Definition of_val (v : val) : expr :=
  match v with
  | RecV f x e => Rec f x e
  | LitV l => Lit l
  end.

Definition to_val (e : expr) : option val :=
  match e with
  | Rec f xl e =>
    if decide (Closed (f :b: xl +b+ []) e) then Some (RecV f xl e) else None
  | Lit l => Some (LitV l)
  | _ => None
  end.

(** The state: heaps of vals*lockstate. Lock_state is kept for backward-compat
    with heap.v's CMRA; after the concurrency strip it stays RSt 0 throughout. *)
Inductive lock_state :=
| WSt | RSt (n : nat).
Definition state : Type := gmap loc (lock_state * val).

(** Evaluation contexts *)
Inductive ectx_item :=
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| AppLCtx (e2 : list expr)
| AppRCtx (v : val) (vl : list val) (el : list expr)
| ReadCtx
| WriteLCtx (e2 : expr)
| WriteRCtx (v1 : val)
| AllocCtx
| FreeLCtx (e2 : expr)
| FreeRCtx (v1 : val)
| CaseCtx (el : list expr)
| RandCtx.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | AppLCtx e2 => App e e2
  | AppRCtx v vl el => App (of_val v) ((of_val <$> vl) ++ e :: el)
  | ReadCtx => Read e
  | WriteLCtx e2 => Write e e2
  | WriteRCtx v1 => Write (of_val v1) e
  | AllocCtx => Alloc e
  | FreeLCtx e2 => Free e e2
  | FreeRCtx v1 => Free (of_val v1) e
  | CaseCtx el => Case e el
  | RandCtx => Rand e
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | NdInt => NdInt
  | Rand e => Rand (subst x es e)
  | App e el => App (subst x es e) (map (subst x es) el)
  | Read e => Read (subst x es e)
  | Write e1 e2 => Write (subst x es e1) (subst x es e2)
  | Alloc e => Alloc (subst x es e)
  | Free e1 e2 => Free (subst x es e1) (subst x es e2)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr) : option expr :=
  match xl, esl with
  | [], [] => Some e
  | x::xl, es::esl => subst' x es <$> subst_l xl esl e
  | _, _ => None
  end.
Arguments subst_l _%binder _ _%E.

Definition subst_v (xl : list binder) (vsl : vec val (length xl))
                   (e : expr) : expr :=
  Vector.fold_right2 (λ b, subst' b ∘ of_val) e _ (list_to_vec xl) vsl.
Arguments subst_v _%binder _ _%E.

Lemma subst_v_eq (xl : list binder) (vsl : vec val (length xl)) e :
  Some $ subst_v xl vsl e = subst_l xl (of_val <$> vec_to_list vsl) e.
Proof.
  revert vsl. induction xl=>/= vsl; inv_vec vsl=>//=v vsl. by rewrite -IHxl.
Qed.

(** The stepping relation *)
(* Be careful to make sure that poison is always stuck when used for anything
   except for reading from or writing to memory! *)
Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition lit_of_bool (b : bool) : base_lit :=
  LitInt $ Z_of_bool b.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).

Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.

Fixpoint init_mem (l:loc) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => <[l:=(RSt 0, LitV LitPoison)]>(init_mem (l +ₗ 1) n σ)
  end.

Fixpoint free_mem (l:loc) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => delete l (free_mem (l +ₗ 1) n σ)
  end.

Inductive lit_eq (σ : state) : base_lit → base_lit → Prop :=
(* No refl case for poison *)
| IntRefl z : lit_eq σ (LitInt z) (LitInt z)
| LocRefl l : lit_eq σ (LitLoc l) (LitLoc l)
(* Comparing unallocated pointers can non-deterministically say they are equal
   even if they are not.  Given that our `free` actually makes addresses
   re-usable, this may not be strictly necessary, but it is the most
   conservative choice that avoids UB (and we cannot use UB as this operation is
   possible in safe Rust).  See
   <https://internals.rust-lang.org/t/comparing-dangling-pointers/3019> for some
   more background. *)
| LocUnallocL l1 l2 :
    σ !! l1 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2)
| LocUnallocR l1 l2 :
    σ !! l2 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2).

Inductive lit_neq : base_lit → base_lit → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → lit_neq (LitInt z1) (LitInt z2)
| LocNeq l1 l2 :
    l1 ≠ l2 → lit_neq (LitLoc l1) (LitLoc l2)
| LocNeqNullR l :
    lit_neq (LitLoc l) (LitInt 0)
| LocNeqNullL l :
    lit_neq (LitInt 0) (LitLoc l).

Inductive bin_op_eval (σ : state) : bin_op → base_lit → base_lit → base_lit → Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval σ PlusOp (LitInt z1) (LitInt z2) (LitInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval σ MinusOp (LitInt z1) (LitInt z2) (LitInt (z1 - z2))
| BinOpMult z1 z2 :
    bin_op_eval σ MultOp (LitInt z1) (LitInt z2) (LitInt (z1 * z2))
| BinOpLe z1 z2 :
    bin_op_eval σ LeOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 ≤ z2))
| BinOpEqTrue l1 l2 :
    lit_eq σ l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool true)
| BinOpEqFalse l1 l2 :
    lit_neq l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool false)
| BinOpOffset l z :
    bin_op_eval σ OffsetOp (LitLoc l) (LitInt z) (LitLoc $ l +ₗ z).

Notation stuck_term := (App (Lit (LitInt 0)) []).

Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
| BinOpS op l1 l2 l' σ :
    bin_op_eval σ op l1 l2 l' →
    head_step (BinOp op (Lit l1) (Lit l2)) σ [] (Lit l') σ []
| NdIntS z σ :
    head_step NdInt σ [] (Lit (LitInt z)) σ []
| RandS N z σ :
    0 ≤ z → z < N →
    head_step (Rand (Lit (LitInt N))) σ [] (Lit (LitInt z)) σ []
| BetaS f xl e e' el σ:
    Forall (λ ei, is_Some (to_val ei)) el →
    Closed (f :b: xl +b+ []) e →
    subst_l (f::xl) (Rec f xl e :: el) e = Some e' →
    head_step (App (Rec f xl e) el) σ [] e' σ []
| ReadS l n v σ:
    σ !! l = Some (RSt n, v) →
    head_step (Read (Lit $ LitLoc l)) σ [] (of_val v) σ []
| WriteS l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (RSt 0, v') →
    head_step (Write (Lit $ LitLoc l) e) σ
              []
              (Lit LitPoison) (<[l:=(RSt 0, v)]>σ)
              []
| AllocS n l σ :
    0 < n →
    (∀ m, σ !! (l +ₗ m) = None) →
    head_step (Alloc $ Lit $ LitInt n) σ
              []
              (Lit $ LitLoc l) (init_mem l (Z.to_nat n) σ)
              []
| FreeS n l σ :
    0 < n →
    (∀ m, is_Some (σ !! (l +ₗ m)) ↔ 0 ≤ m < n) →
    head_step (Free (Lit $ LitInt n) (Lit $ LitLoc l)) σ
              []
              (Lit LitPoison) (free_mem l (Z.to_nat n) σ)
              []
| CaseS i el e σ :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    head_step (Case (Lit $ LitInt i) el) σ [] e σ [].

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_stuck e1 σ1 κ e2 σ2 ef :
  head_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
  head_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
Proof.
  destruct Ki; inversion_clear 1; decompose_Forall_hyps;
    simplify_option_eq; by eauto.
Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  map of_val vl1 ++ e1 :: el1 = map of_val vl2 ++ e2 :: el2 →
  vl1 = vl2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by rewrite to_of_val in H1.
  - subst. by rewrite to_of_val in H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto. by apply (inj of_val).
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1 as [| | |v1 vl1 el1| | | | | | | |],
           Ki2 as [| | |v2 vl2 el2| | | | | | | |];
  intros He1 He2 EQ; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
  destruct (list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2); auto. congruence.
Qed.

Lemma shift_loc_assoc l n n' : l +ₗ n +ₗ n' = l +ₗ (n + n').
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0 l : l +ₗ 0 = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_assoc_nat l (n n' : nat) : l +ₗ n +ₗ n' = l +ₗ (n + n')%nat.
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0_nat l : l +ₗ 0%nat = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Global Instance shift_loc_inj l : Inj (=) (=) (shift_loc l).
Proof. destruct l as [b o]; intros n n' [= ?]; lia. Qed.

Lemma shift_loc_block l n : (l +ₗ n).1 = l.1.
Proof. done. Qed.

Lemma lookup_init_mem σ (l l' : loc) (n : nat) :
  l.1 = l'.1 → l.2 ≤ l'.2 < l.2 + n →
  init_mem l n σ !! l' = Some (RSt 0, LitV LitPoison).
Proof.
  intros ?. destruct l' as [? l']; simplify_eq/=.
  revert l. induction n as [|n IH]=> /= l Hl; [lia|].
  assert (l' = l.2 ∨ l.2 + 1 ≤ l') as [->|?] by lia.
  { by rewrite -surjective_pairing lookup_insert_eq. }
  rewrite lookup_insert_ne; last by destruct l; intros ?; simplify_eq/=; lia.
  rewrite -(shift_loc_block l 1) IH /=; last lia. done.
Qed.

Lemma lookup_init_mem_ne σ (l l' : loc) (n : nat) :
  l.1 ≠ l'.1 ∨ l'.2 < l.2 ∨ l.2 + n ≤ l'.2 →
  init_mem l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> /= l Hl; auto.
  rewrite -(IH (l +ₗ 1)); last (simpl; intuition lia).
  apply lookup_insert_ne. intros ->; intuition lia.
Qed.

Definition fresh_block (σ : state) : block :=
  let loclst : list loc := elements (dom σ : gset loc) in
  let blockset : gset block := foldr (λ l, ({[l.1]} ∪.)) ∅ loclst in
  fresh blockset.

Lemma is_fresh_block σ i : σ !! (fresh_block σ,i) = None.
Proof.
  assert (∀ (l : loc) ls (X : gset block),
    l ∈ ls → l.1 ∈ foldr (λ l, ({[l.1]} ∪.)) X ls) as help.
  { induction 1; set_solver. }
  rewrite /fresh_block /shift_loc /= -(not_elem_of_dom (D := gset loc)) -elem_of_elements.
  move=> /(help _ _ ∅) /=. apply is_fresh.
Qed.

Lemma alloc_fresh n σ :
  let l := (fresh_block σ, 0) in
  let init := repeat (LitV $ LitInt 0) (Z.to_nat n) in
  0 < n →
  head_step (Alloc $ Lit $ LitInt n) σ [] (Lit $ LitLoc l) (init_mem l (Z.to_nat n) σ) [].
Proof.
  intros l init Hn. apply AllocS; [exact Hn|].
  intros i. apply (is_fresh_block _ i).
Qed.

Lemma lookup_free_mem_ne σ l l' n : l.1 ≠ l'.1 → free_mem l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> l ? //=.
  rewrite lookup_delete_ne; last congruence.
  apply IH. by rewrite shift_loc_block.
Qed.

Lemma delete_free_mem σ l l' n :
  delete l (free_mem l' n σ) = free_mem l' n (delete l σ).
Proof.
  revert l'. induction n as [|n IH]=> l' //=. 
  by rewrite delete_delete IH.
Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof.
  revert e X Y. fix FIX 1; destruct e=>X Y/=; try naive_solver.
  - naive_solver set_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split; [by eauto|].
    induction el=>/=; naive_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split; [by eauto|].
    induction el=>/=; naive_solver.
Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert e X. fix FIX 1; destruct e=> X /=; rewrite ?bool_decide_spec ?andb_True=> He ?;
    repeat case_bool_decide; simplify_eq/=; f_equal;
    try by intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
Qed.

Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply is_closed_subst with []; set_solver. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof. apply is_closed_weaken_nil. induction v; simpl; auto. Qed.

Lemma is_closed_to_val X e v : to_val e = Some v → is_closed X e.
Proof. intros <-%of_to_val. apply is_closed_of_val. Qed.

Lemma subst_is_closed X x es e :
  is_closed X es → is_closed (x::X) e → is_closed X (subst x es e).
Proof.
  revert e X. fix FIX 1; destruct e=>X //=; repeat (case_bool_decide=>//=);
    try naive_solver; rewrite ?andb_True; intros.
  - set_solver.
  - eauto using is_closed_weaken with set_solver.
  - eapply is_closed_weaken; first done.
    destruct (decide (BNamed x = f)), (decide (BNamed x ∈ xl)); set_solver.
  - split; first naive_solver. induction el; naive_solver.
  - split; first naive_solver. induction el; naive_solver.
Qed.

Lemma subst'_is_closed X b es e :
  is_closed X es → is_closed (b:b:X) e → is_closed X (subst' b es e).
Proof. destruct b; first done. apply subst_is_closed. Qed.

(* Operations on literals *)
Lemma lit_eq_state (σ1 σ2 : state) l1 l2 :
  (∀ l, σ1 !! l = None ↔ σ2 !! l = None) →
  lit_eq σ1 l1 l2 → lit_eq σ2 l1 l2.
Proof. intros Heq. inversion 1; econstructor; eauto; eapply Heq; done. Qed.

Lemma bin_op_eval_state σ1 σ2 op l1 l2 l' :
  (∀ l, σ1 !! l = None ↔ σ2 !! l = None) →
  bin_op_eval σ1 op l1 l2 l' → bin_op_eval σ2 op l1 l2 l'.
Proof.
  intros Heq. inversion 1; econstructor; eauto using lit_eq_state.
Qed.

(* Misc *)
Lemma stuck_not_head_step σ e' κ σ' ef :
  ¬head_step stuck_term σ e' κ σ' ef.
Proof. inversion 1. Qed.

(** Equality and other typeclass stuff *)
Global Instance base_lit_dec_eq : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance bin_op_dec_eq : EqDecision bin_op.
Proof. solve_decision. Defined.

Fixpoint expr_beq (e : expr) (e' : expr) : bool :=
  let fix expr_list_beq el el' :=
    match el, el' with
    | [], [] => true
    | eh::eq, eh'::eq' => expr_beq eh eh' && expr_list_beq eq eq'
    | _, _ => false
    end
  in
  match e, e' with
  | Var x, Var x' => bool_decide (x = x')
  | Lit l, Lit l' => bool_decide (l = l')
  | Rec f xl e, Rec f' xl' e' =>
    bool_decide (f = f') && bool_decide (xl = xl') && expr_beq e e'
  | BinOp op e1 e2, BinOp op' e1' e2' =>
    bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
  | NdInt, NdInt => true
  | Rand e, Rand e' => expr_beq e e'
  | App e el, App e' el' | Case e el, Case e' el' =>
    expr_beq e e' && expr_list_beq el el' 
  | Read e, Read e' => expr_beq e e'
  | Write e1 e2, Write e1' e2' =>
    expr_beq e1 e1' && expr_beq e2 e2'
  | Alloc e, Alloc e' => expr_beq e e'
  | Free e1 e2, Free e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | _, _ => false
  end.
Lemma expr_beq_correct (e1 e2 : expr) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e1 e2; fix FIX 1.
    destruct e1 as [| | | | | |? el1| | | | |? el1],
             e2 as [| | | | | |? el2| | | | |? el2]; simpl; try done;
  rewrite ?andb_True ?bool_decide_spec ?FIX;
  try (split; intro; [destruct_and?|split_and?]; congruence).
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (FIX el1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (FIX el1h). naive_solver. }
    clear FIX. naive_solver.
Qed.
Global Instance expr_dec_eq : EqDecision expr.
Proof.
 refine (λ e1 e2, cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
Defined.
Global Instance val_dec_eq : EqDecision val.
Proof.
 refine (λ v1 v2, cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
Defined.

Global Instance expr_inhabited : Inhabited expr := populate (Lit LitPoison).
Global Instance val_inhabited : Inhabited val := populate (LitV LitPoison).

(** Countable instances. Required by clutch's probabilistic ectxiLanguage.
    loc is a pair of [positive] (= block) and [Z], both countable. *)
Global Instance base_lit_countable : Countable base_lit.
Proof.
  refine (inj_countable'
    (λ l, match l with
      | LitPoison => inl ()
      | LitLoc l => inr (inl l)
      | LitInt n => inr (inr n)
      end)
    (λ x, match x with
      | inl () => LitPoison
      | inr (inl l) => LitLoc l
      | inr (inr n) => LitInt n
      end) _).
  by intros [].
Qed.

Local Close Scope Z_scope.
Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable'
    (λ op, match op with
      | PlusOp => 0%nat | MinusOp => 1%nat | MultOp => 2%nat
      | LeOp => 3%nat | EqOp => 4%nat | OffsetOp => 5%nat
      end)
    (λ n : nat, match n with
      | 0 => PlusOp | 1 => MinusOp | 2 => MultOp
      | 3 => LeOp | 4 => EqOp | _ => OffsetOp
      end) _).
  by intros [].
Qed.
Local Open Scope Z_scope.

Global Instance lock_state_eq_dec : EqDecision lock_state.
Proof. solve_decision. Defined.
Global Instance lock_state_countable : Countable lock_state.
Proof.
  refine (inj_countable'
    (λ s, match s with WSt => inl () | RSt n => inr n end)
    (λ x, match x with inl () => WSt | inr n => RSt n end) _).
  by intros [].
Qed.

Global Instance expr_countable : Countable expr.
Proof.
  set (enc := fix go e :=
    match e with
    | Var x => GenLeaf (inl (inl x))
    | Lit l => GenLeaf (inr (inl l))
    | Rec f xl e =>
        GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inr (inr xl)); go e]
    | BinOp op e1 e2 =>
        GenNode 1 [GenLeaf (inr (inl (LitInt (match op with
          | PlusOp => 0 | MinusOp => 1 | MultOp => 2
          | LeOp => 3 | EqOp => 4 | OffsetOp => 5
          end)))); go e1; go e2]
    | NdInt => GenNode 2 []
    | Rand e => GenNode 3 [go e]
    | App e el => GenNode 4 (go e :: map go el)
    | Read e => GenNode 5 [go e]
    | Write e1 e2 => GenNode 6 [go e1; go e2]
    | Alloc e => GenNode 7 [go e]
    | Free e1 e2 => GenNode 8 [go e1; go e2]
    | Case e el => GenNode 9 (go e :: map go el)
    end).
  set (dec := fix go t :=
    match t with
    | GenLeaf (inl (inl x)) => Var x
    | GenLeaf (inr (inl l)) => Lit l
    | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inr (inr xl)); e] =>
        Rec f xl (go e)
    | GenNode 1 [GenLeaf (inr (inl (LitInt n))); e1; e2] =>
        BinOp (match n with
          | 0 => PlusOp | 1 => MinusOp | 2 => MultOp
          | 3 => LeOp | 4 => EqOp | _ => OffsetOp
          end) (go e1) (go e2)
    | GenNode 2 [] => NdInt
    | GenNode 3 [e] => Rand (go e)
    | GenNode 4 (e :: el) => App (go e) (map go el)
    | GenNode 5 [e] => Read (go e)
    | GenNode 6 [e1; e2] => Write (go e1) (go e2)
    | GenNode 7 [e] => Alloc (go e)
    | GenNode 8 [e1; e2] => Free (go e1) (go e2)
    | GenNode 9 (e :: el) => Case (go e) (map go el)
    | _ => Lit LitPoison (* unreachable *)
    end).
  refine (inj_countable' enc dec _).
  fix go 1.
  intros [x | l | f xl e | op e1 e2 | | e | e el | e | e1 e2 | e | e1 e2 | e el]; simpl.
  - done.
  - done.
  - by rewrite go.
  - destruct op; by rewrite !go.
  - done.
  - by rewrite go.
  - f_equal; [by rewrite go|]. induction el as [|e' el' IH]; simpl; [done|]. by rewrite go IH.
  - by rewrite go.
  - by rewrite !go.
  - by rewrite go.
  - by rewrite !go.
  - f_equal; [by rewrite go|]. induction el as [|e' el' IH]; simpl; [done|]. by rewrite go IH.
Qed.

Global Instance val_countable : Countable val.
Proof.
  refine (inj_countable of_val to_val _).
  intros v; by rewrite to_of_val.
Qed.

(* The Iris-specific [leibnizO] canonical structures and the
   [EctxiLanguageMixin] instance live in [lang.v], which re-exports
   this file along with the relevant Iris modules. *)

(* Define some derived forms *)
Notation Lam xl e := (Rec BAnon xl e) (only parsing).
Notation Let x e1 e2 := (App (Lam [x] e2) [e1]) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV xl e := (RecV BAnon xl e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV [x] e2) [] []).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitPoison) (Lit LitPoison)).
Coercion lit_of_bool : bool >-> base_lit.
Notation If e0 e1 e2 := (Case e0 (@cons expr e2 (@cons expr e1 (@nil expr))))
  (only parsing).
Notation Newlft := (Lit LitPoison) (only parsing).
Notation Endlft := (Seq Skip (Seq Skip Skip)) (only parsing).
Notation Share := (Seq Skip Skip) (only parsing).
Notation UniqBor := (Seq Skip Skip) (only parsing).
Notation ReBor := (Seq Skip Skip) (only parsing).
Notation SplitBor := (Seq Skip Skip) (only parsing).

End pure.

(** ============================================================================
    Clutch [ectxi_language] wrapping (formerly [prob_lang.v]).
    =========================================================================== *)
From Stdlib Require Import Reals Psatz.
From stdpp Require Import fin_maps.
From clutch.common Require Export language ectx_language ectxi_language.
From clutch.prob Require Export distribution.
From clutch.prelude Require Import stdpp_ext classical.

(* Re-export [pure] so that [expr], [val], [state], [to_val], [of_val], …
   refer to our inductives instead of [clutch.common.language]'s
   record projections that were just [Export]ed above. The re-export
   here re-binds the names in the order: clutch first, [pure] last,
   so [pure] dominates downstream of this file. *)
Export pure.

Global Open Scope Z_scope.
Local Open Scope R.

(** * Computable, probabilistic head step *)

(** Computable pointer/integer equality — the probabilistic variant of
    [lit_eq] from [lang.v]. We drop the [LocUnallocL/R] non-deterministic
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
