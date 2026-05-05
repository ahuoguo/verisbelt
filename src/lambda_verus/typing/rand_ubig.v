(** Typing-layer rule for the verusbelt [rand_ubig] axiom.

    ** Why [error_credit_ty] has a [ty_phys] location handle even
    though Verus's [ErrorCredit] is purely a global PCM resource. **

    On the Verus side ([ub/ub.rs] in the verus repo), [ErrorCredit] is
    a [Tracked] PCM resource at the *single global ghost location*
    [EC_GLOBAL_LOC()].  There is no per-credit physical address, no
    heap cell — it's a global-RA-only resource (the eris [↯ε] is
    exactly the same).  So semantically, [error_credit_ty ε] should
    have *no* physical content.

    But verusbelt's typed-context machinery forces a witness on every
    [p ◁ ty] entry.  Concretely, [type_context.v:tctx_elt_interp]
    unfolds [p ◁ ty] to

        ∃v d, ⌜eval_path p = Some v⌝ ∗ ⧖d ∗ ty_own ty x d d tid [FVal v]

    and [type.v:ty_own] requires [ty_phys x tid = [FVal v]].  A
    purely 0-sized type ([ty_phys := []]) therefore *cannot* live at
    a path entry — the equality [[] = [FVal v]] is [False].

    Verusbelt's convention for binding a purely-ghost resource to a
    typed-context path is to wrap it in [own_ptr 0]: e.g.
    [ghost.v:47,64,83] uses [own_ptr 0 (ghost_ty ty)].  The 0-allocation
    [own_ptr] adds a 1-sized location handle whose only role is to
    satisfy the path-witness machinery; the inner ghost type carries
    the real resource.  The closest existing combinator for our case
    is [own_ptr 0 (tracked_ty error_credit_core)], but [own_ptr] /
    the surrounding [pptr.v] machinery is OOB, so we inline the
    composite into a single [type (at_locₛ unitₛ)]:

      ty_size  := 1                  (the [own_ptr 0] location handle)
      ty_phys  := [FVal #(x.1)]      (purely a path-witness — *not*
                                      a Verus-side concept)
      ty_gho   := ↯ε                  (the actual eris/Verus credit,
                                      living globally in [ecGS] —
                                      this is the load-bearing field)

    The location [x.1] in [ty_phys] is **not** where the credit
    "lives".  Like [EC_GLOBAL_LOC()] on the Verus side, the credit
    has no per-instance address.  [x.1] is just a fresh syntactic
    handle so [c ◁ ↯_T ε] can mention the credit by source-level
    name [c] in a [tctx].

    Two ways to avoid the handle if you want stricter semantic
    fidelity:

    1. Move error credits out of [tctx] into a separate purely-ghost
       context (analogous to [invctx]).  Then no path/witness is
       needed, but [rand_ubig] can't refer to the credit by name [c]
       — it'd consume "the" ambient credit instead.

    2. Generalize [tctx_elt_interp] to allow 0-sized entries with
       [ty_phys = []] and [eval_path p = None].  Substantial
       verusbelt-side surgery; affects every existing typing rule. *)

From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.eris Require Import weakestpre.
From clutch.prob Require Import distribution.
From lrust.lang Require Export notation error_rules.
From lrust.lang.lib Require Import new_delete.
From lrust.typing Require Export type programs int.
Set Default Proof Using "Type".

Local Open Scope R.

Section error_credit_type.
  Context `{!typeG Σ}.

  (** [error_credit_ty ε] : a [type (at_locₛ unitₛ)] that bundles
      [own_ptr 0 (tracked_ty (ErrorCredit ε))] in a single definition.

      The Coq refinement is [at_locₛ unitₛ ≡ loc * unit] — the
      [loc] component is the [own_ptr 0] handle (a path-witness
      artifact, see file header), and [unit] is the trivial
      refinement of the inner [tracked_ty error_credit_core].
      [ty_gho] carries the actual eris error-credit ghost [↯ε];
      this — and only this — is what semantically corresponds to
      Verus's [ErrorCreditResource] at [EC_GLOBAL_LOC()]. *)
  Program Definition error_credit_ty (ε : R) : type (at_locₛ unitₛ) := {|
    ty_size := 1;
    ty_lfts := [];
    ty_E := [];
    (* [ty_gho]: the load-bearing field — the eris error credit, a
       global ghost resource (no location), exactly mirroring Verus's
       [Tracked<ErrorCreditResource>] at [EC_GLOBAL_LOC()]. *)
    ty_gho _ _ _ _ := ↯ ε;
    ty_gho_pers _ _ _ _ := True%I;
    (* [ty_phys]: a path-witness slot, NOT a Verus-side concept.
       The credit lives globally in [ecGS] — this is a vestigial
       artifact of [tctx_elt_interp]'s requirement that every
       [p ◁ ty] entry produce a [FVal v] matching [eval_path p].

       Why a [LitLoc] and not a [LitUnit] (which would more honestly
       express "no payload")?  The [type] record's [ty_phys_eq2]
       obligation forces [ty_phys x tid = syn_phys x], so [ty_phys]
       is structurally pinned to whichever [syn_type] we picked.
       Surveying [syn_type.v:syn_phys], no syn_type produces a
       [FVal (LitV LitUnit)] — the only choices for a 1-sized
       refinement are [Zₛ] ([LitInt]), [boolₛ] ([LitBool]),
       [locₛ]/[at_locₛ _]/[at_clocₛ _]/[uniq_borₛ _] ([LitLoc]),
       [exec_funₛ _] (function value).  Of those, the
       [own_ptr 0]-shaped [at_locₛ unitₛ] is the verusbelt-faithful
       choice — it's what [own_ptr 0 (ghost_ty _)] uses in
       [ghost.v].  A genuine "unit-payload" syn_type with
       [syn_phys x = [FVal (LitV LitUnit)]] doesn't exist; adding
       one would be a verusbelt-side change with no upside (the
       byte-level distinction between [LitLoc] and [LitUnit] is
       irrelevant to the path-witness role). *)
    ty_phys x _ := [FVal (LitV (LitLoc x.1))];
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. iIntros (??????? _ _) "$". by iIntros "$". Qed.
  Next Obligation. iIntros (??????? _ _). by iIntros "$". Qed.
  Next Obligation. by iIntros. Qed.

End error_credit_type.

(** Notation: [↯_T ε] mirrors the eris [↯ ε] but at the typing layer. *)
Notation "'↯_T' ε" := (error_credit_ty ε)
  (at level 8, format "↯_T  ε") : lrust_type_scope.

Section typing_rules.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  (** [thin_air] in raw WP form.  The [∀ ε, ⌜0 < ε⌝ -∗ ↯ε -∗ …] shape
      means the *consumer* receives some unspecified positive credit and
      must complete the proof with that.  Lifting this to a
      [typed_instr]-shaped rule isn't a one-liner because [typed_instr]
      fixes the output tctx up front, so the credit amount can't be
      chosen post-hoc.  The natural typed form would parameterise the
      output tctx by an existential ε:

        typed_instr E L I +[] (new [#0]) (λ v, ∃ ε, +[v ◁ ↯_T ε ∗ ⌜0<ε⌝]) …

      which doesn't fit upstream's plain-tctx output schema; it would
      need a refinement-existential output.  Until that machinery is
      built, [thin_air] is best left in WP form. *)
  Lemma type_thin_air e E Φ :
    to_val e = None →
    (∀ ε : R, ⌜(0 < ε)%R⌝ -∗ ↯ ε -∗ WP e @ E {{ Φ }}) ⊢
    WP e @ E {{ Φ }}.
  Proof. apply wp_err_pos. Qed.

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

  (** Value-indexed extension of [ε2].  Off the live sampling path
      (where the WP can return a non-int value, even if the
      probabilistic semantics rules that out) the refund is [0]; a
      [↯0] is the trivial credit. *)
  Definition ε2_at (z : Z) (ε2 : nat → R) (v : val) : R :=
    match v with
    | LitV (LitInt m) =>
        if bool_decide (0 ≤ m)%Z then
          if bool_decide (Z.to_nat m < Z.to_nat z)%nat then ε2 (Z.to_nat m)
          else 0
        else 0
    | _ => 0
    end.

  (** [rand_ubig] in [typed_instr]-style form, using the
      verusbelt-faithful [↯_T ε] tracked-credit type.

      Reading the rule:
      - Input tctx [+[c ◁ ↯_T ε1]]: a single tracked credit of [ε1]
        bound at path [c].
      - Output tctx [λ v, +[v ◁ int; c ◁ ↯_T (ε2_at z ε2 v)]]: the
        sampled int [v] gets typed at [int], and the *refunded* credit
        [↯(ε2 n)] is re-bound at the same handle [c].
      - Predicate transformer (Prop-only): for every legal sample [n],
        the post-condition must hold.  All iProp resource flow happens
        through [tctx_interp] of the input/output tctxs — the
        transformer carries only the pure relational content.

      The proof is currently admitted; it requires unfolding
      [tctx_elt_interp] on the [↯_T ε1] entry to extract [↯ε1], invoking
      [wp_rand_exp_nat], and re-packaging [↯(ε2 n)] back into the
      [↯_T (ε2 n)] output entry.  ~30 lines of bureaucracy that doesn't
      change the rule's *shape*. *)
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

End typing_rules.
