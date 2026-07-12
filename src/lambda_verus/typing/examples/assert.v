From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.eris Require Import weakestpre.
From lrust.lang Require Import notation lifting proofmode tactics.
From lrust.typing Require Import type type_context programs cont function
                                  own bool int uninit product mod_ty.
Set Default Proof Using "Type".

Local Open Scope R.

(** [assert]: a closed value that takes a bool argument [b], returns
    [#0] on [true], and goes to UB ([!(#☠)]) on [false].  Simple
    (no fn-type wrapping) — coin_flip uses this with [wp_assert]. *)
Definition assert : val :=
  (λ: ["b"], if: "b" then #0 else !(#☠))%V.

Section assert_spec.
  Context `{!lrustGS Σ}.

  (** Combined WP spec: pay [↯ 1] on [false], nothing on [true].
      The two single-branch lemmas below are corollaries. *)
  Lemma wp_assert (b : bool) E :
    (if b then True%I else ↯ 1) ⊢ WP (assert [ #b ])%E @ E {{ _, True }}.
  Proof.
    iIntros "H". rewrite /assert. unlock.
    wp_lam. wp_if.
    destruct b.
    - by iApply pgl_wp_value.
    - iExFalso. iApply (ec_contradict with "H"). lra.
  Qed.

  Lemma wp_assert_true E :
    ⊢ WP (assert [ #true ])%E @ E {{ _, True }}.
  Proof. iApply (wp_assert true). done. Qed.

  Lemma wp_assert_false E :
    ↯ 1 ⊢ WP (assert [ #false ])%E @ E {{ _, True }}.
  Proof. iApply (wp_assert false). Qed.

End assert_spec.

(** [assert_fn]: the fn-typed assertion (full Verus form).
    Takes a [Box<bool>] (typed [box bool_ty]) and returns [()]. *)
Definition assert_fn : val :=
  (fn: ["b"] :=
    let: "b'" := !"b" in
    if: "b'" then
      let: "r" := new [ #0] in
      return: ["r"]
    else
      let: "r" := !(#☠) in
      return: ["r"])%V.

Section assert_type_section.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Local Definition assert_fn_body : expr :=
    (let: "b'" := !"b" in
     if: "b'" then
       let: "r" := new [ #0] in
       return: ["r"]
     else
       let: "r" := !(#☠) in
       return: ["r"])%E.

  Local Instance assert_fn_body_closed :
    Closed (<> :b: ("return" :: ["b"])%binder +b+ []) assert_fn_body.
  Proof. unfold assert_fn_body. solve_closed. Qed.

  Lemma assert_type :
    typed_val assert_fn
      ((fn(∅; bool_ty) → ()) (λ (_c : ~~ ()) Φ '-[(_l, b)],
                                λ mask, b = true ∧ ∀ ret, Φ ret mask))
      (RecV <> ("return" :: ["b"])%binder assert_fn_body, ()).
  Proof.
    unfold assert_fn. unlock.
    opose proof (@type_fn _ _ _
        ()                   (* A : Type *)
        [boolₛ]              (* 𝔄l : syn_typel *)
        ()                   (* 𝔅 : syn_type *)
        ()                   (* ℭ : syn_type *)
        ()                   (* tr : ~~ℭ *)
        (λ y: (), FP ∅ +[bool_ty] () AtomicClosed)
        (λ (_c: ~~ ()) Φ '-[(_l, b)], λ mask, b = true ∧ ∀ ret, Φ ret mask)
        (_)
        [BNamed "b"] _ _ _
    ) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl.
    destruct wl as [bv []]. unfold assert_fn_body. simpl_subst.
    iApply (typed_body_impl with "[]"); last first.
    { iApply (type_let with "[]").
      - by eapply (type_deref_instr (𝔅 := boolₛ) _ bool_ty);
          [apply bool_stack_okay|done|apply read_own_copy, bool_copy].
      - apply tctx_extract_elt_here_exact.
      - reflexivity.
      - iIntros (v). simpl_subst. iApply type_if.
        + apply tctx_extract_elt_here_exact.
        (* true branch *)
        + iApply (type_new_subtype () 0 with "[]"); first by lia.
          { apply uninit_unit_1. }
          iIntros. simpl_subst.
          iApply type_jump.
          * by left.
          * apply tctx_extract_elt_here_exact.
          * reflexivity.
        (* false branch: poison-deref UB → vacuous *)
        + iApply typed_body_vacuous. }
    intros post [[l b] []] mask.
    simpl. unfold trans_upper. simpl.
    intros [Hb Hforall]. intros [l1 b1] Heq. inversion Heq. subst l1. subst b1.
    destruct b; last by done. intros. by apply Hforall.
    Unshelve. eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.

End assert_type_section.
