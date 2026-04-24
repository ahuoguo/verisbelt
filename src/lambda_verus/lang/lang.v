(** Iris ectxi_language wrapping for lrust_lang.

    All pure Coq syntax (expr, val, state, fill_item, head_step, ...)
    lives in [syntax.v]. This file re-exports that content along with
    the Iris program-logic framework and adds the canonical
    [EctxiLanguage] structure. *)
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From lrust.lang Require Export syntax.
From iris.prelude Require Import options.
Set Default Proof Using "Type".

Open Scope Z_scope.

Canonical Structure stateO := leibnizO state.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

Lemma lrust_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val,
    val_stuck, fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.
Canonical Structure lrust_ectxi_lang := EctxiLanguage lrust_lang_mixin.
Canonical Structure lrust_ectx_lang := EctxLanguageOfEctxi lrust_ectxi_lang.
Canonical Structure lrust_lang := LanguageOfEctx lrust_ectx_lang.

Lemma stuck_irreducible K σ : irreducible (fill K stuck_term) σ.
Proof.
  apply: (irreducible_fill (K:=ectx_language.fill K)); first done.
  apply prim_base_irreducible.
  - inversion 1.
  - apply ectxi_language_sub_redexes_are_values.
    intros [] ??; simplify_eq/=; eauto; discriminate_list.
Qed.
