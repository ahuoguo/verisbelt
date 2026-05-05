From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Set Default Proof Using "Type".

Section bool.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Program Definition bool_ty: type boolₛ :=
    {|
      pt_size := 1;
      pt_gho (b: ~~boolₛ) _ := True%I ;
      pt_phys (b: ~~boolₛ) _ := [ FVal #b ] ;
    |}%I.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  
  Global Instance bool_copy: Copy bool_ty.
  Proof. split. - typeclasses eauto. - iIntros. iPureIntro. done. Qed.

  Global Instance bool_send: Send bool_ty.
  Proof.
    split. intros. unfold syn_abstract in H. subst x'. trivial.
  Qed.
  
  Global Instance bool_sync: Sync bool_ty.
  Proof. split; trivial. split; iSplit; done. Qed.

  (** [bool_resolve] removed along with [resolve]. *)


  Lemma bool_stack_okay : StackOkay bool_ty.
  Proof. done. Qed.

  Lemma type_bool_instr (b: bool) : typed_val #b bool_ty b.
  Proof.
    iIntros (????????) "_ _ _ $$ _ %Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply pgl_wp_value. iExists -[b]. iSplit; [|done]. iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat. iFrame "⧖".
    iSplit; done.
  Qed.

  Lemma type_bool {𝔄l 𝔅} (b: bool) (T: tctx 𝔄l) x e tr E L (I: invctx) (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := #b in e) (λ post al, tr post (b -:: al)).
  Proof.
    iIntros. iApply type_let; [apply type_bool_instr|solve_typing|done..].
  Qed.

  (** [type_nd_bool_instr] / [type_nd_bool] removed: [NdBool] desugars
      to [#0 ≤ NdInt], so it inherits [NdInt]'s lack of a probabilistic
      WP rule (cf. [int.v]). *)

  Lemma type_if {𝔄l 𝔅l ℭ} p (T: tctx 𝔄l) (T': tctx 𝔅l) e1 e2 tr1 tr2 trx E L I (C: cctx ℭ) :
    tctx_extract_ctx E L +[p ◁ bool_ty] T T' trx →
    typed_body E L I C T' e1 tr1 -∗ typed_body E L I C T' e2 tr2 -∗
    typed_body E L I C T (if: p then e1 else e2)
      (trx ∘ (λ post '(b -:: vl), if b then tr1 post vl else tr2 post vl)).
  Proof.
    iIntros (?) "e1 e2". iApply typed_body_tctx_incl; [done|]=>/=.
    iIntros (?[b ?]???) "/= #LFT #TIME #E L I C [p T] %Obs".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (?? _) "_".
    iDestruct 1 as "[_true %Hphys]".
    inversion Hphys. subst v.
    destruct b; wp_case.
    - iApply ("e1" with "LFT TIME E L I C T"). by iPureIntro.
    - iApply ("e2" with "LFT TIME E L I C T"). by iPureIntro.
  Qed.
End bool.

(** [bool_resolve] removed along with [resolve]. *)
