From stdpp Require Import fin_maps.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".

(** We define an alternative representation of expressions in which the
embedding of values and closed expressions is explicit. By reification of
expressions into this type we can implement substitution, closedness
checking, atomic checking, and conversion into values, by computation. *)
Module W.
Inductive expr :=
| Val (v : val) (e : pure.expr) (H : to_val e = Some v)
| ClosedExpr (e : pure.expr) `{!Closed [] e}
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
| Case (e : expr) (el : list expr)
.

Fixpoint to_expr (e : expr) : pure.expr :=
  match e with
  | Val v e' _ => e'
  | ClosedExpr e _ => e
  | Var x => pure.Var x
  | Lit l => pure.Lit l
  | Rec f xl e => pure.Rec f xl (to_expr e)
  | BinOp op e1 e2 => pure.BinOp op (to_expr e1) (to_expr e2)
  | NdInt => pure.NdInt
  | Rand e => pure.Rand (to_expr e)
  | App e el => pure.App (to_expr e) (map to_expr el)
  | Read e => pure.Read (to_expr e)
  | Write e1 e2 => pure.Write (to_expr e1) (to_expr e2)
  | Alloc e => pure.Alloc (to_expr e)
  | Free e1 e2 => pure.Free (to_expr e1) (to_expr e2)
  | Case e el => pure.Case (to_expr e) (map to_expr el)
  end.

Ltac of_expr e :=
  lazymatch e with
  | pure.Var ?x => constr:(Var x)
  | pure.Lit ?l => constr:(Lit l)
  | pure.Rec ?f ?xl ?e => let e := of_expr e in constr:(Rec f xl e)
  | pure.BinOp ?op ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op e1 e2)
  | pure.NdInt => constr:(NdInt)
  | pure.Rand ?e => let e := of_expr e in constr:(Rand e)
  | pure.App ?e ?el =>
    let e := of_expr e in let el := of_expr el in constr:(App e el)
  | pure.Read ?e => let e := of_expr e in constr:(Read e)
  | pure.Write ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Write e1 e2)
  | pure.Alloc ?e => let e := of_expr e in constr:(Alloc e)
  | pure.Free ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Free e1 e2)
  | pure.Case ?e ?el =>
     let e := of_expr e in let el := of_expr el in constr:(Case e el)
  | @nil pure.expr => constr:(@nil expr)
  | @cons pure.expr ?e ?el =>
    let e := of_expr e in let el := of_expr el in constr:(e::el)
  | to_expr ?e => e
  | of_val ?v => constr:(Val v (of_val v) (to_of_val v))
  | _ => match goal with
         | H : to_val e = Some ?v |- _ => constr:(Val v e H)
         | H : Closed [] e |- _ => constr:(@ClosedExpr e H)
         end
  end.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ _ _ | ClosedExpr _ _ => true
  | Var x => bool_decide (x ∈ X)
  | Lit _ | NdInt => true
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write e1 e2 | Free e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Read e | Alloc e | Rand e => is_closed X e
  end.
Lemma is_closed_correct X e : is_closed X e → pure.is_closed X (to_expr e).
Proof.
  revert e X. fix FIX 1; destruct e=>/=;
    try naive_solver eauto using is_closed_to_val, is_closed_weaken_nil.
  - induction el=>/=; naive_solver.
  - induction el=>/=; naive_solver.
Qed.

(* We define [to_val (ClosedExpr _)] to be [None] since [ClosedExpr]
constructors are only generated for closed expressions of which we know nothing
about apart from being closed. Notice that the reverse implication of
[to_val_Some] thus does not hold. *)
Definition to_val (e : expr) : option val :=
  match e with
  | Val v _ _ => Some v
  | Rec f xl e =>
    if decide (is_closed (f :b: xl +b+ []) e) is left H
    then Some (@RecV f xl (to_expr e) (is_closed_correct _ _ H)) else None
  | Lit l => Some (LitV l)
  | _ => None
  end.
Lemma to_val_Some e v :
  to_val e = Some v → of_val v = W.to_expr e.
Proof.
  revert v. induction e; intros; simplify_option_eq; auto using of_to_val.
Qed.
Lemma to_val_is_Some e :
  is_Some (to_val e) → ∃ v, of_val v = to_expr e.
Proof. intros [v ?]; exists v; eauto using to_val_Some. Qed.
Lemma to_val_is_Some' e :
  is_Some (to_val e) → is_Some (pure.to_val (to_expr e)).
Proof. intros [v ?]%to_val_is_Some. exists v. rewrite -to_of_val. by f_equal. Qed.

Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Val v e H => Val v e H
  | ClosedExpr e _ => ClosedExpr e
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
Lemma to_expr_subst x er e :
  to_expr (subst x er e) = pure.subst x (to_expr er) (to_expr e).
Proof.
  revert e x er. fix FIX 1; destruct e=>/= ? er; repeat case_bool_decide;
    f_equal; eauto using is_closed_nil_subst, is_closed_to_val, eq_sym.
  - induction el=>//=. f_equal; auto.
  - induction el=>//=. f_equal; auto.
Qed.

Definition is_atomic (e: expr) : bool :=
  match e with
  | Read e | Alloc e | Rand e => bool_decide (is_Some (to_val e))
  | Write e1 e2 | Free e1 e2 =>
    bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | _ => false
  end.
(** [is_atomic_correct] under clutch's [head_atomic] signature is a
    follow-up — clutch's [Atomic] takes a probabilistic [prim_step] and
    uses a different inversion shape than iris's. The lemma is unused
    by the heap WP rules in [lifting.v] (which call
    [wp_lift_atomic_head_step] directly), so we defer it. *)

End W.

Ltac solve_closed :=
  match goal with
  | |- Closed ?X ?e =>
     let e' := W.of_expr e in change (Closed X (W.to_expr e'));
     apply W.is_closed_correct; vm_compute; exact I
  end.
Global Hint Extern 0 (Closed _ _) => solve_closed : typeclass_instances.

Ltac solve_into_val :=
  match goal with
  | |- IntoVal ?e ?v =>
     let e' := W.of_expr e in change (of_val v = W.to_expr e');
     apply W.to_val_Some; simpl; unfold W.to_expr;
     ((unlock; exact eq_refl) || (idtac; exact eq_refl))
  end.
Global Hint Extern 10 (IntoVal _ _) => solve_into_val : typeclass_instances.

Ltac solve_as_val :=
  match goal with
  | |- AsVal ?e =>
     let e' := W.of_expr e in change (∃ v, of_val v = W.to_expr e');
     apply W.to_val_is_Some, (bool_decide_unpack _); vm_compute; exact I
  end.
Global Hint Extern 10 (AsVal _) => solve_as_val : typeclass_instances.

(** [solve_atomic]: deferred along with [W.is_atomic_correct]. *)

(** Substitution *)
Ltac simpl_subst :=
  unfold subst_v; simpl;
  repeat match goal with
  | |- context [subst ?x ?er ?e] =>
      let er' := W.of_expr er in let e' := W.of_expr e in
      change (subst x er e) with (subst x (W.to_expr er') (W.to_expr e'));
      rewrite <-(W.to_expr_subst x); simpl (* ssr rewrite is slower *)
  end;
  unfold W.to_expr; simpl.
Arguments W.to_expr : simpl never.
Arguments subst : simpl never.

(** The tactic [inv_head_step] performs inversion on hypotheses of the
shape [head_step]. The tactic will discharge head-reductions starting
from values, and simplifies hypothesis related to conversions from and
to values, and finite map operations. This tactic is slightly ad-hoc
and tuned for proving our lifting lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : Lit _ = of_val ?v |- _ =>
    apply (f_equal (to_val)) in H; rewrite to_of_val in H;
    injection H; clear H; intro
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_val e tac :=
  let rec go e :=
  match e with
  | of_val ?v => v
  | Lit ?l => constr:(LitV l)
  | Rec ?f ?xl ?e => constr:(RecV f xl e)
  end in let v := go e in tac v.

Ltac reshape_expr e tac :=
  let rec go_fun K f vs es :=
    match es with
    | [] => idtac          (* All args are values; outer tac call already tried. *)
    | ?e :: ?es => reshape_val e ltac:(fun v => go_fun K f (v :: vs) es)
    | ?e :: ?es => go (AppRCtx f (reverse vs) es :: K) e
    end
  with go K e :=
  match e with
  | _ => tac K e
  | BinOp ?op ?e1 ?e2 =>
     reshape_val e1 ltac:(fun v1 => go (BinOpRCtx op v1 :: K) e2)
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | App ?e ?el => reshape_val e ltac:(fun f => go_fun K f (@nil val) el)
  | App ?e ?el => go (AppLCtx el :: K) e
  | Read ?e => go (ReadCtx :: K) e
  | Write ?e1 ?e2 =>
    reshape_val e1 ltac:(fun v1 => go (WriteRCtx v1 :: K) e2)
  | Write ?e1 ?e2 => go (WriteLCtx e2 :: K) e1
  | Alloc ?e => go (AllocCtx :: K) e
  | Rand ?e => go (RandCtx :: K) e
  | Free ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (FreeRCtx v1 :: K) e2)
  | Free ?e1 ?e2 => go (FreeLCtx e2 :: K) e1
  | Case ?e ?el => go (CaseCtx el :: K) e
  end
  in go (@nil ectx_item) e.
