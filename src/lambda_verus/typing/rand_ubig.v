(** Typing-layer rules for the verusbelt randomness axioms:
    [thin_air] (mint a positive credit from nothing) and
    [rand_ubig] (expectation-preserving uniform sampling).

    ** Verus credit encoding **

    Verus models error credits as [Tracked<ErrorCreditResource(ε)>] —
    a PCM token at a single global ghost location.  The eris [↯ε]
    has the same shape. We model error credits as follows:

        error_credit_ty ε
          = own_ptr_0 (tracked_ty (error_credit_core ε))

    - [error_credit_core ε] ≡ [ErrorCreditResource(ε)]: [ty_size := 0],
      [ty_phys := []], [ty_gho := ↯ε].
    - [tracked_ty _] ≡ [Tracked<_>] (ghost wrapper, in [tracked.v]).
    - [own_ptr_0] is a 1-byte path-witness handle.  Needed because
      [tctx_elt_interp] requires [ty_phys = [FVal v]] for every
      [p ◁ ty] entry — a 0-sized type can't live at a path.  This
      file defines a minimal stand-in; could be replaced with
      [own.v:own_ptr 0] now that [own.v] is in build.  The handle
      [loc] is purely a tctx artifact, not a Verus concept (the
      credit lives globally in [ecGS]). *)

From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.eris Require Import weakestpre.
From clutch.prob Require Import distribution.
From lrust.lang Require Export notation error_rules.
From lrust.lang.lib Require Import new_delete.
From lrust.typing Require Export type programs int tracked.
Set Default Proof Using "Type".

Local Open Scope R.

Section error_credit_type.
  Context `{!typeG Σ}.

  (** [error_credit_core ε]: ghost-only eris credit.  [ty_gho := ↯ε],
      [ty_size := 0], [ty_phys := []]. *)
  Program Definition error_credit_core (ε : R) : type unitₛ := {|
    ty_size := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho _ _ _ _ := ↯ ε;
    ty_gho_pers _ _ _ _ := True%I;
    ty_phys _ _ := [];
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. iIntros (??????? _ _) "$". by iIntros "$". Qed.
  Next Obligation. iIntros (??????? _ _). by iIntros "$". Qed.
  Next Obligation. by iIntros. Qed.

  (** [own_ptr_0]: 1-byte location handle wrapping a 0-sized ghost
      type so it satisfies [tctx_elt_interp]'s path-witness.

      Differences vs [own.v:own_ptr 0]:
      1. No heap mapsto / [freeable_sz] in [ty_gho] — [own_ptr]'s
         [(fst x) ↦!∗ ty_phys (snd x) tid ∗ freeable_sz n ty.(ty_size)]
         degenerates to [True] when [ty_size = 0], but its presence
         still implies an allocation lifecycle.  Verus's
         [ErrorCreditResource] is a global PCM token with no address,
         so we drop the heap layer entirely.
      2. No depth shift on the inner [ty_gho].  [own_ptr] gates
         [ty_gho] by [[S(d') := d]] and wraps the inner in [▷],
         forcing consumers to depth ≥ 1.  [own_ptr_0] passes the
         inner [ty_gho] through verbatim, so [error_credit_ty]
         works at any depth.

      Sound only for [ty_size := 0] inner types. *)
  Program Definition own_ptr_0 {𝔄} (ty : type 𝔄) : type (at_locₛ 𝔄) := {|
    ty_size := 1;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho x d g tid := ty.(ty_gho) x.2 d g tid;
    ty_gho_pers x d g tid := ty.(ty_gho_pers) x.2 d g tid;
    ty_phys x _ := [FVal (LitV (LitLoc x.1))];
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    intros 𝔄 ty d g d' g' x tid Hd Hg.
    iIntros "H".
    iDestruct (ty.(ty_gho_depth_mono) _ _ _ _ x.2 tid Hd Hg with "H") as "[$ $]".
  Qed.
  Next Obligation.
    intros 𝔄 ty d g d' g' x tid Hd Hg. iApply ty.(ty_gho_pers_depth_mono); done.
  Qed.
  Next Obligation.
    intros 𝔄 ty x d g tid. iApply (ty_gho_pers_impl _ ty).
  Qed.

  (** [error_credit_ty ε]: see file header for layer breakdown.
      Coq refinement: [loc * unit] (loc is the handle artifact). *)
  Definition error_credit_ty (ε : R) : type (at_locₛ (trackedₛ unitₛ)) :=
    own_ptr_0 (tracked_ty (error_credit_core ε)).

  (** [error_credit_some_core]: existential-credit ghost core.  The
      [ε] is hidden under [ty_gho := ∃ε>0, ↯ε], mirroring Verus's
      opaque [Tracked<ErrorCreditResource>] whose [view()] returns
      [Carrier(ε)] under an existential. *)
  Program Definition error_credit_some_core : type unitₛ := {|
    ty_size := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho _ _ _ _ := (∃ ε : R, ⌜(0 < ε)%R⌝ ∗ ↯ ε)%I;
    ty_gho_pers _ _ _ _ := True%I;
    ty_phys _ _ := [];
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. iIntros (?????? _ _) "$". by iIntros "$". Qed.
  Next Obligation. iIntros (?????? _ _). by iIntros "$". Qed.
  Next Obligation. by iIntros. Qed.

  (** [error_credit_some_ty]: location-handle wrapper around
      [error_credit_some_core].  Carries [∃ε>0, ↯ε] in its ghost
      payload. *)
  Definition error_credit_some_ty : type (at_locₛ (trackedₛ unitₛ)) :=
    own_ptr_0 (tracked_ty error_credit_some_core).

End error_credit_type.

(** Notation: [↯_T ε] mirrors the eris [↯ ε] but at the typing layer. *)
Notation "'↯_T' ε" := (error_credit_ty ε)
  (at level 8, format "↯_T  ε") : lrust_type_scope.

Section typing_rules.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  (** [thin_air] in raw WP form.  Kept WP-shaped because
      [typed_instr]'s plain-tctx output can't host the existential
      [∃ε > 0] that the consumer chooses post-hoc. *)
  Lemma type_thin_air e E Φ :
    to_val e = None →
    (∀ ε : R, ⌜(0 < ε)%R⌝ -∗ ↯ ε -∗ WP e @ E {{ Φ }}) ⊢
    WP e @ E {{ Φ }}.
  Proof. apply wp_err_pos. Qed.

  (** [type_thin_air_instr]: Verus's [thin_air()] at the typing layer.
      Mints a fresh [↯_T ε] at a user-supplied path [c] (which must
      evaluate to a literal location [l], typically picked as a magic
      handle like [#(LitLoc (42%positive, 1337))]).  The location is
      a tctx artifact only — no allocation happens.

      Soundness note (matches the Verus comment): the underlying
      [wp_err_pos] only fires inside a WP/fupd, which is exactly the
      shape of [typed_instr]'s body.  Asserting [∃ε>0, ↯ε] outside
      such a context would be unsound. *)
  Lemma type_thin_air_instr {𝔅l}
      (c : path) (l : loc) (e : expr) (T' : val → tctx 𝔅l)
      (tr : predl_trans [] 𝔅l) E L I :
    eval_path c = Some (LitV (LitLoc l)) →
    to_val e = None →
    (∀ ε : R, (0 < ε)%R →
        typed_instr E L I +[c ◁ ↯_T ε] e T'
          (λ post '-[_], λ mask, tr post -[] mask)) →
    typed_instr E L I +[] e T' tr.
  Proof.
    iIntros (Hev Hnv Hinner tid post mask iκs []).
    iIntros "#LFT #TIME #E_ HL Hinv _ %Hpre".
    iApply type_thin_air; first done.
    iIntros (ε Hε) "Hcr".
    iApply fupd_pgl_wp.
    iMod persistent_time_receipt_0 as "#⧖0".
    iModIntro.
    iApply (Hinner ε Hε tid post mask iκs -[(l, ())]
            with "LFT TIME E_ HL Hinv [Hcr] [//]").
    iSplit; last done.
    rewrite /tctx_elt_interp /=.
    iExists (LitV (LitLoc l)), 0%nat.
    iSplit; first done.
    iFrame "⧖0".
    rewrite /ty_own /=. by iFrame "Hcr".
  Qed.

  Lemma type_thin_air_incr_instr {𝔅l}
      (ε : R) (c : path) (e : expr) (T' : val → tctx 𝔅l)
      (tr : predl_trans [at_locₛ unitₛ] 𝔅l) E L I :
    to_val e = None →
    (∀ ε' : R, (ε < ε')%R →
        typed_instr E L I +[c ◁ ↯_T ε'] e T' tr) →
    typed_instr E L I +[c ◁ ↯_T ε] e T' tr.
  Proof.
    iIntros (Hnv Hinner tid post mask iκs [[l []] []]).
    iIntros "#LFT #TIME #E_ L_ Hinv Htctx %Hpre".
    iDestruct "Htctx" as "[Tc _]".
    rewrite /tctx_elt_interp /=.
    iDestruct "Tc" as (v d Hev) "[#⧖d [Hcr %Hphys]]".
    iApply wp_err_incr; first done.
    iFrame "Hcr".
    iIntros (ε' Hε') "Hcr'".
    iApply (Hinner ε' Hε' tid post mask iκs -[(l, ())]
            with "LFT TIME E_ L_ Hinv [Hcr'] [//]").
    rewrite /tctx_elt_interp /=.
    iSplit; last done.
    iExists v, d. iFrame "⧖d Hcr'". iSplit; done.
  Qed.

  (** [type_thin_air_post_instr]: typed-instr analog of
      [wp_err_pos_post].  Given any [typed_instr], strengthens its
      output tctx with a fresh [c ◁ error_credit_some_ty] — the credit
      type whose [ty_gho] contains [∃ ε > 0, ↯ ε].  This puts the
      existential *inside* the type rather than in a CPS quantifier,
      matching Verus's [thin_air] ensures-clause shape literally:

          ensures ∃ε>0, ret.view() = Carrier(ε)

      Like [wp_err_pos_post], soundness comes from the underlying
      [wp_err_pos] which only fires inside a WP — the proof invokes
      it on the WP that [typed_instr] unfolds to. *)
  Lemma type_thin_air_post_instr {𝔄l 𝔅l}
      (T: tctx 𝔄l) (e : expr) (T' : val → tctx 𝔅l)
      (c : path) (l : loc) (tr : predl_trans 𝔄l 𝔅l) E L I :
    eval_path c = Some (LitV (LitLoc l)) →
    to_val e = None →
    typed_instr E L I T e T' tr →
    typed_instr E L I T e
      (λ v, (c ◁ error_credit_some_ty) +:: T' v)
      (λ post, tr (λ outs mask, post ((l, ()) -:: outs) mask)).
  Proof.
    iIntros (Hev Hnv Hinner tid post mask iκs xl).
    iIntros "#LFT #TIME #E_ HL Hinv T %Hpre".
    iApply pgl_wp_fupd.
    iApply wp_err_pos; first done.
    iIntros (ε Hε) "Hcr".
    iApply (pgl_wp_wand with "[HL Hinv T]").
    { iApply (Hinner tid (λ outs mask, post ((l, ()) -:: outs) mask)
                    mask iκs xl with "LFT TIME E_ HL Hinv T [//]"). }
    iIntros (v) "(%xl' & HL & Hinv & Ht & %Hpost)".
    iMod persistent_time_receipt_0 as "#⧖0".
    iModIntro.
    iExists ((l, ()) -:: xl').
    iFrame "HL Hinv".
    iSplit; last by iPureIntro.
    iSplitL "Hcr".
    - rewrite /tctx_elt_interp /=.
      iExists (LitV (LitLoc l)), 0%nat.
      iSplit; first done. iFrame "⧖0".
      rewrite /ty_own /=. iSplit; last done.
      iExists ε. iFrame "Hcr". by iPureIntro.
    - iFrame.
  Qed.

  (** [rand_ubig] in iris triple form (the most directly usable form). *)
  Lemma wp_rand_ubig (z : Z) (ε1 : R) (ε2 : nat → R) (E : coPset) :
    (0 < z)%Z →
    (∀ n, (0 <= ε2 n <= 1)%R) →
    (SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat z)%nat
        then (1 / Z.to_nat z) * ε2 n
        else 0)%R <= ε1)%R →
    {{{ ↯ ε1 }}}
      rand #z @ E
    {{{ (n : nat), RET #(Z.of_nat n);
        ⌜(n < Z.to_nat z)%nat⌝ ∗ ↯ (ε2 n) }}}.
  Proof.
    iIntros (Hz Hb Hε Φ) "Herr HΦ".
    iApply (wp_rand_exp_nat with "Herr"); [done|done|done|].
    iNext. iIntros (n) "[%Hn Hcr]". iApply "HΦ". by iFrame.
  Qed.

  (** Value-indexed [ε2]: off-path values get refund [0] ([↯0] is trivial). *)
  Definition ε2_at (z : Z) (ε2 : nat → R) (v : val) : R :=
    match v with
    | LitV (LitInt m) =>
        if bool_decide (0 ≤ m)%Z then
          if bool_decide (Z.to_nat m < Z.to_nat z)%nat then ε2 (Z.to_nat m)
          else 0
        else 0
    | _ => 0
    end.

  (** [rand_ubig] in [typed_instr] form.  Consumes [c ◁ ↯_T ε1],
      returns [v ◁ int; c ◁ ↯_T (ε2_at z ε2 v)].  Predicate transformer
      is pure (∀ n < z, post). *)
  Lemma type_rand_ubig_instr (z : Z) (ε1 : R) (ε2 : nat → R) (c : path) E L I :
    (0 < z)%Z →
    (∀ n, (0 <= ε2 n <= 1)%R) →
    (SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat z)%nat
        then (1 / Z.to_nat z) * ε2 n
        else 0)%R <= ε1)%R →
    typed_instr E L I
      +[c ◁ ↯_T ε1]
      (rand #z)
      (λ v, +[v ◁ int; c ◁ ↯_T (ε2_at z ε2 v)])
      (λ post '-[(l, ())], λ mask,
        ∀ n : nat, (n < Z.to_nat z)%nat →
          post -[(Z.of_nat n : Z); (l, ())] mask).
  Proof.
    iIntros (Hz Hb Hε tid post mask iκs [[l []] []]).
    iIntros "_ _ _ $ $ T %Obs".
    iDestruct "T" as "[Tc _]".
    rewrite /tctx_elt_interp /=.
    iDestruct "Tc" as (v d Hev) "[#⧖d [Hcr %Hphys]]".
    inversion Hphys; subst v.
    iApply pgl_wp_fupd.
    iApply (wp_rand_exp_nat with "Hcr"); [done|done|done|].
    iNext. iIntros (n) "[%Hn Hcr2]".
    iMod persistent_time_receipt_0 as "#⧖0".
    iModIntro.
    iExists -[(Z.of_nat n : Z); (l, ())].
    rewrite /tctx_elt_interp /=.
    iAssert (↯ (ε2_at z ε2 #(Z.of_nat n)))%I with "[Hcr2]" as "Hcr2".
    { replace (ε2_at z ε2 #(Z.of_nat n)) with (ε2 n); first iFrame.
      rewrite /ε2_at /=.
      rewrite (bool_decide_eq_true_2 (0 ≤ Z.of_nat n)%Z); last lia.
      rewrite (bool_decide_eq_true_2 (Z.to_nat (Z.of_nat n) < Z.to_nat z)%nat); last lia.
      by rewrite Nat2Z.id. }
    iSplitL "Hcr2"; last by (iPureIntro; apply Obs).
    iSplit.
    - (* #(Z.of_nat n) ◁ int *)
      iExists (LitV (LitInt (Z.of_nat n))), 0%nat.
      iSplit; first done.
      iFrame "⧖0".
      rewrite /ty_own /=. by iSplit.
    - iSplit; last done.
      (* c ◁ ↯_T (ε2_at z ε2 #(Z.of_nat n)) *)
      iExists (LitV (LitLoc l)), d.
      iSplit; first done.
      iFrame "⧖d".
      rewrite /ty_own /=.
      by iFrame.
  Qed.

  (** [type_rand_case]: case-splitting variant of [type_rand_ubig_instr]
      that exposes the sample [n] as a Coq nat per branch.  For each
      [n < z], the body is typed with [#(Z.of_nat n) ◁ int] and
      [c ◁ ↯_T (ε2 n)] at concrete values — letting
      [type_credit_contradict] absorb branches where [ε2 n = 1]. *)
  Lemma type_rand_case {𝔄l 𝔅} (z : Z) (ε1 : R) (ε2 : nat → R) (c : path) x e
      (T' : tctx 𝔄l) E L (I: invctx) (C: cctx 𝔅) :
    (0 < z)%Z →
    (∀ n, (0 <= ε2 n <= 1)%R) →
    (SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat z)%nat
        then (1 / Z.to_nat z) * ε2 n
        else 0)%R <= ε1)%R →
    Closed (x :b: []) e →
    (∀ (n : nat),
      (n < Z.to_nat z)%nat →
      ⊢ typed_body E L I C
          (#(Z.of_nat n) ◁ int +:: c ◁ ↯_T (ε2 n) +:: T')
          (subst' x #(Z.of_nat n) e)
          (λ _ _ _, True%type)) →
    ⊢ typed_body E L I C (c ◁ ↯_T ε1 +:: T') (let: x := rand #z in e)
        (λ _ _ _, True%type).
  Proof.
    iIntros (Hz Hb Hε Hcle Hbody).
    iIntros (tid xl mask post iκs).
    destruct xl as [[lc []] cl].
    iIntros "#LFT #TIME #E L Hinv Hcctx [Hcred Hrest] _".
    rewrite /tctx_elt_interp /=.
    iDestruct "Hcred" as (v dv Hev) "[#⧖v [Hcr %Hphys]]".
    inversion Hphys; subst v.
    wp_bind (Rand _).
    iApply (wp_rand_exp_nat with "Hcr"); [done|done|done|].
    iNext. iIntros (m) "[%Hm Hcr2]".
    iMod persistent_time_receipt_0 as "#⧖0".
    wp_let.
    (* Apply the per-n typed_body for this specific m. *)
    iApply ((Hbody m Hm) $! tid (Z.of_nat m -:: (lc, ()) -:: cl) mask post iκs
            with "LFT TIME E L Hinv Hcctx [Hcr2 Hrest] [%]").
    - simpl.
      iSplitR "Hcr2 Hrest".
      { rewrite /tctx_elt_interp /=.
        iExists (LitV (LitInt (Z.of_nat m))), 0%nat.
        iSplit; first done. iFrame "⧖0".
        rewrite /ty_own /=. by iSplit. }
      iSplitL "Hcr2".
      { rewrite /tctx_elt_interp /=.
        iExists (LitV (LitLoc lc)), dv.
        iSplit; first done. iFrame "⧖v".
        rewrite /ty_own /=. by iFrame. }
      iFrame "Hrest".
    - exact Logic.I.
  Qed.

  (** [type_credit_contradict_after_rand]: variant matching the tctx
      shape after [type_rand_case] — [int] head, then [↯_T 1], then rest. *)
  Lemma type_credit_contradict_after_rand {𝔄l 𝔅} (T': tctx 𝔄l) E L
      (I: invctx) (C: cctx 𝔅) (z : Z) (p : path) e tr :
    ⊢ typed_body E L I C (#z ◁ int +:: p ◁ ↯_T 1 +:: T') e tr.
  Proof.
    iIntros (tid xl mask post iκs).
    destruct xl as [zv [[lc []] cl]].
    iIntros "_ _ _ _ _ _ [_Hint [Hcred _]] _".
    rewrite /tctx_elt_interp /=.
    iDestruct "Hcred" as (v d Hev) "[#⧖ [Hcr _]]".
    iExFalso. iApply (ec_contradict with "Hcr"). lra.
  Qed.

  (** [type_credit_contradict]: a tctx-head [↯_T 1] is contradictory
      ([ec_contradict]); discharges any [typed_body]. *)
  Lemma type_credit_contradict {𝔄l 𝔅} (T': tctx 𝔄l) E L (I: invctx)
      (C: cctx 𝔅) (p : path) e :
    ⊢ typed_body E L I C (p ◁ ↯_T 1 +:: T') e (λ _ _ _, True%type).
  Proof.
    iIntros (tid xl mask post iκs).
    destruct xl as [[lc []] cl].
    iIntros "_ _ _ _ _ _ [Hcr_tctx _] _".
    rewrite /tctx_elt_interp /=.
    iDestruct "Hcr_tctx" as (v d Hev) "[#⧖ [Hcr _]]".
    iExFalso. iApply (ec_contradict with "Hcr"). lra.
  Qed.

End typing_rules.
