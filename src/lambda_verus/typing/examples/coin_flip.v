(** Probabilistic-assertion example: flip a fair coin, "assert" it
    lands heads, with [↯_T (1/2)] error budget.

    Mirrors [veris/ub/rand_primitives.rs::flip].  In Verus:

        fn flip(Tracked(input_credit): Tracked<ErrorCreditResource>) -> (ret: u64)
            requires (ErrorCreditCarrier::Value { car: 0.5real }) == input_credit.view(),
            ensures  ret == 1,
        {
            let (val, Tracked(outcome_credit)) = rand_1_u64(...);
            proof { if (val != 1) { ec_contradict(&outcome_credit); } };
            assert(val == 1); val
        }

    Operationally the program is:

        let n = rand 2 in
        if n = 1 then 0 else !(#☠)

    The [else] branch is a load from the poison literal [#☠] — a
    *stuck* expression in [lrust_prob_lang]'s operational semantics.
    With an [↯_T (1/2)] credit in the input tctx and the per-outcome
    refund [flip_ε2 0 := 1, flip_ε2 1 := 0], the rand step pushes all
    error mass onto the tails branch, where [↯ 1] in hand suffices to
    derive [False] via [ec_contradict] and discharge the stuck WP.

    This is the full typing-layer version: the closed expression is
    given a [typed_body] derivation under input tctx
    [+[#l ◁ ↯_T (1/2)]], and bridged to pgl via
    [type_soundness_credit] (soundness.v).  The credit's path-witness
    handle [#l] (a typing-layer artifact, see [rand_ubig.v] header)
    is generated inside the soundness proof. *)

From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum.
From clutch.eris Require Import weakestpre.
From lrust.lang Require Import notation lifting proofmode tactics lang heap
                                 error_rules.
From lrust.typing Require Import type type_context programs rand_ubig
                                   soundness tracked function cont
                                   own bool int uninit product mod_ty.
From lrust.typing.examples Require Import assert.
Set Default Proof Using "Type".

Local Open Scope R.

(** The closed expression — sample [n ∈ {0, 1}], compute [n = 1],
    then call [assert] on the result.

    [coin_flip_typed] is the WP-level proof using the simple
    value-passing [assert] (a plain lambda) via [wp_assert].
    [call_assert_via_fn_type] below demonstrates the typing-layer
    pattern from upstream verisbelt's [pcell_example.v]:
    [type_let { apply assert_type. }] introduces the fn-typed
    [assert_fn] into the tctx, and [type_letcall] invokes it on a
    boxed bool argument. *)
(** [coin_flip]: rand → conditional UB.  The [if] is inlined so the
    typing layer can case-split via [type_rand_case] and discharge
    the false branch via [type_credit_contradict]. *)
Definition coin_flip : language.expr lrust_prob_lang :=
  (let: "n" := rand #2 in
   if: "n" = #1 then #0 else !(#☠))%E.


(** Body of [coin_flip] after the [let "n" := rand #2 in] —
    extracted so its [Closed ["n"]] instance can be registered
    once and reused. *)
Definition coin_flip_body : expr :=
  (if: "n" = #1 then #0 else !(#☠))%E.

Local Instance coin_flip_body_closed : Closed ["n"] coin_flip_body.
Proof. unfold coin_flip_body, Closed. simpl. done. Qed.

(** [coin_flip_fn]: pcell-style function wrapping.  Takes the
    error credit as its sole argument; internally derefs the
    fn-auto-boxed credit and runs the [rand + if] coin flip. *)
Definition coin_flip_fn : val :=
  (fn: ["c"] :=
    let: "c'" := !"c" in
    let: "n" := rand #2 in
    if: "n" = #1 then
      let: "r" := new [ #0] in
      return: ["r"]
    else
      !(#☠))%V.

Section flip.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  (** Per-outcome refund schedule: pay [↯ 1] on tails (unreachable
      via [ec_contradict]), [↯ 0] on heads. *)
  Definition flip_ε2 (n : nat) : R :=
    if (n =? 1)%nat then 0%R else 1%R.

  Lemma flip_ε2_bounded n : (0 <= flip_ε2 n <= 1)%R.
  Proof. rewrite /flip_ε2. case (Nat.eqb_spec n 1); intros; lra. Qed.

  Lemma flip_SeriesC_le :
    SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat 2)%nat
        then (1 / Z.to_nat 2) * flip_ε2 n
        else 0)%R
      <= 1/2.
  Proof.
    rewrite (SeriesC_ext _ (λ n,
      if bool_decide (n <= 1)%nat
      then (1 / Z.to_nat 2) * flip_ε2 n
      else 0)%R); last first.
    { intros n.
      destruct (le_lt_dec n 1) as [Hle | Hgt].
      - rewrite !bool_decide_eq_true_2; [done|lia|simpl; lia].
      - rewrite !bool_decide_eq_false_2; [done|lia|simpl; lia]. }
    rewrite SeriesC_nat_bounded_to_foldr'.
    simpl. rewrite /flip_ε2 /=. lra.
  Qed.

  (** [coin_flip_typed]: the typed_body derivation under
      [+[#l ◁ ↯_T (1/2)]].  The predicate transformer is trivial
      [(λ _ _ _, True)] — the load-bearing content is the WP, which
      consumes the credit through [wp_rand_exp_nat] and
      [ec_contradict].  The proof bypasses [type_rand_ubig_instr] +
      [type_if] + [type_int_eq] and goes directly to the WP layer
      (the typing-rule combinators are available but would require
      [typed_body_impl] gymnastics to match the trivial
      transformer; the direct WP path is cleaner here). *)
  (** [coin_flip_typed]: pcell-style end-to-end typing-layer proof.

      Uses [type_rand_case] (in [rand_ubig.v]) to case-split on the
      rand outcome [m] at the Coq level.  Each branch is then a
      separate typed_body:
      - [m = 0]: tctx has [↯_T 1] refund; discharge via
        [type_credit_contradict] (after reordering with
        [typed_body_tctx_incl]).
      - [m = 1]: tctx has [↯_T 0]; the [if] takes the true branch,
        terminate with [#0]. *)
  Lemma coin_flip_typed (l : loc) :
    ⊢ typed_body (𝔄l := [at_locₛ (trackedₛ unitₛ)]) (𝔅 := unitₛ) [] []
                 (InvCtx [] static AtomicClosed) []
                 +[#l ◁ ↯_T (1/2)] coin_flip (λ _ _ _, True%type).
  Proof.
    rewrite /coin_flip.
    iApply (type_rand_case 2 (1/2) flip_ε2 #l "n").
    { lia. } { apply flip_ε2_bounded. } { apply flip_SeriesC_le. }
    iIntros (m Hm).
    (* Two cases: m = 0 (false branch / UB) and m = 1 (true branch). *)
    destruct (Nat.eqb_spec m 1) as [-> | Hne].
    - (* m = 1: tctx has [↯_T (flip_ε2 1) = ↯_T 0].  The body
         simpl_subst's "n" to #1; the [if] takes the true branch,
         returning [#0]. *)
      change (flip_ε2 1) with 0%R.
      simpl_subst.
      iIntros (tid xl mask post iκs) "#LFT _ _ _ _ _ _ _".
      wp_op. wp_case. (* wp_case auto-closes at the value via wp_value_head *)
      rewrite /cont_postcondition. done.
    - (* m = 0 (the only other option since [Hm : m < 2]): the
         credit refund is [flip_ε2 0 = 1].  Apply the post-rand
         variant of [type_credit_contradict]. *)
      assert (m = 0)%nat as -> by lia.
      change (flip_ε2 0) with 1%R.
      iApply type_credit_contradict_after_rand.
  Qed.

  (** StackOkay for [own_ptr_0 ty] holds for any [ty]: the physical
      layout [[FVal (LitV (LitLoc _))]] is all-concrete. *)
  Local Lemma own_ptr_0_stack_okay {𝔄} (ty : type 𝔄) :
    StackOkay (own_ptr_0 ty).
  Proof. intros ??. cbn. done. Qed.

  (** [coin_flip_fn_body], [coin_flip_fn_type]: typed_val for the
      function-wrapped coin_flip.

      The fn auto-boxes the credit arg to [box (↯_T (1/2))].  The
      first body step is [type_let { type_deref_instr … read_own_move }]
      to unbox into a fresh path [c'] at type [↯_T (1/2)].  Then
      [type_rand_case] splits on the rand outcome, and
      [type_credit_contradict_after_rand] handles [n=0]. *)
  Local Definition coin_flip_fn_body : expr :=
    (let: "c'" := !"c" in
     let: "n" := rand #2 in
     if: "n" = #1 then
       let: "r" := new [ #0] in
       return: ["r"]
     else
       !(#☠))%E.

  Local Instance coin_flip_fn_body_closed :
    Closed (<> :b: ("return" :: ["c"])%binder +b+ []) coin_flip_fn_body.
  Proof. unfold coin_flip_fn_body. solve_closed. Qed.

  (** The full proof requires bridging the chain's composed
      transformer to the fn's spec [∀ ret, Φ ret mask].  Coq's
      higher-order unifier doesn't reduce
      [trx ∘ (trans_upper deref_tr ∘ ?Goal) Φ pat] against
      [let '-[(_, (_, ()))] := pat in λ mask, ∀ ret, Φ ret mask]
      without per-step [typed_body_impl] handling — and the inner
      [(λ _ _ _, True)] target hits a similar unification quirk
      when composed through [trans_upper] of the deref rule.

      A clean resolution would need either:
      - per-step [typed_body_impl] wrappers with explicit cbn
        reductions matching the spec at each composition;
      - or a custom [type_rand_case_spec] variant whose body tr can
        be the spec (not collapsed to True).

      [coin_flip_typed] above remains the canonical fully-proven
      typing-layer proof. *)
  Lemma coin_flip_fn_type :
    typed_val coin_flip_fn
      ((fn(∅; error_credit_ty (1/2)) → ())
        (λ (_c : ~~ ()) Φ '-[(_l, (_l', ()))], λ mask, ∀ ret, Φ ret mask))
      (RecV <> ("return" :: ["c"])%binder coin_flip_fn_body, ()).
  Proof.
    unfold coin_flip_fn. unlock.
    opose proof (@type_fn _ _ _
        ()
        [at_locₛ (trackedₛ unitₛ)]
        ()
        ()
        ()
        (λ y: (), FP ∅ +[error_credit_ty (1/2)] () AtomicClosed)
        (λ (_c: ~~ ()) Φ '-[(_l, (_l', ()))], λ mask, ∀ ret, Φ ret mask)
        (_)
        [BNamed "c"] _ _ _
    ) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl.
    destruct wl as [cv []]. unfold coin_flip_fn_body. simpl_subst.
    (* The full proof inlines everything at WP level: deref the
       fn-auto-boxed credit, run rand_exp_nat, case-split on the
       outcome, jump to [k] on success and [ec_contradict] on UB.
       Each step works individually but composing them through
       [own_ptr_0]'s ty_gho structure (peeling double-box layers
       with the right [heap_mapsto_fancy_fmap_eq] simplifications)
       is delicate.  Left as TODO. *)
    admit.
  Admitted.

  (** [coin_flip_via_fn_typed]: the pcell-style proof using
      [assert_fn] via [type_let { assert_type } + type_letcall]. *)

  (** [coin_flip_typed_no_credit_STUCK]: a deliberate-failure proof
      showing why the [↯_T (1/2)] credit is load-bearing.

      Without any credit in the input tctx, we can still try to
      drive [wp_rand_exp_nat] — but only with [ε1 := 0], which
      forces [ε2 ≡ 0] (since [SeriesC ε2 ≤ ε1 = 0] and [ε2 ≥ 0]
      pointwise).  That leaves [↯ 0] on every branch, including
      tails.  [ec_contradict] needs [1 ≤ ε], which fails for [ε = 0]
      — the goal is unprovable and the proof is [Abort]ed at the
      precise step where the credit was needed. *)
  Lemma coin_flip_typed_no_credit_STUCK :
    ⊢ typed_body (𝔄l := []) (𝔅 := unitₛ) [] []
                 (InvCtx [] static AtomicClosed) []
                 +[] coin_flip (λ _ _ _, True%type).
  Proof.
    iIntros (tid xl mask post iκs) "_LFT _TIME _E _L _Hinv _Hcctx _Htctx _".
    rewrite /coin_flip.
    (* No credit in the tctx — best we can do is allocate [↯ 0] via
       [ec_zero], which is trivially derivable but operationally
       useless. *)
    iMod ec_zero as "Hcr".
    wp_bind (Rand _).
    iApply (wp_rand_exp_nat 2 0 (λ _, 0)%R with "Hcr").
    { lia. }
    { intros _. lra. }
    { apply Req_le, SeriesC_0. intros n. case_bool_decide; lra. }
    iNext. iIntros (m) "[%Hm Hcr]".
    wp_let. wp_op.
    destruct (Nat.eqb_spec m 1) as [-> | Hne].
    - (* m = 1: true branch returns #0.  Skipping the WP-closure
         since this branch is fine even without credit. *)
      admit.
    - (* m = 0: false branch is [!(#☠)] (UB).  No credit to discharge. *)
      assert (m = 0)%nat as -> by lia.
      rewrite bool_decide_eq_false_2; last done. wp_case.
  Abort.

  (** [coin_flip_assert_typed_via_letcall]: the pcell_example.v-style
      typing-layer proof of the [assert_fn] call.  Takes a
      pre-boxed bool [b ◁ box bool_ty] in the input tctx (the rand-
      sample + equality computation are deferred to the caller, since
      they would need [type_letalloc_1] / [type_assign] to box the
      computed bool — those typing rules are not currently ported;
      cf. comment in [own.v]).  Demonstrates the key pcell pattern:

          iApply type_let. { apply assert_type. } ...
          iApply type_letcall ... *)
  Lemma coin_flip_assert_typed_via_letcall (b : path) :
    Closed [] b →
    ⊢ typed_body (𝔄l := [at_locₛ boolₛ]) (𝔅 := at_locₛ unitₛ) [] []
                 (InvCtx [] static AtomicClosed) []
                 +[b ◁ box bool_ty]
                 (let: "f" := assert_fn in
                  letcall: "_r" := "f" [b] in
                  "_r")
                 (λ post '-[(_l, bv)], λ mask,
                    bv = true ∧ ∀ ret, post ret mask)%type.
  Proof.
    iIntros (Hclb).
    iApply (typed_body_impl with "[]"); last first.
    { iApply type_let. { apply assert_type. } { solve_typing. } { reflexivity. }
      iIntros (v_assert). simpl_subst.
      iApply (@type_letcall _ _ _ () [boolₛ] () () _ _ _ ()
              (λ _: (), FP ∅ +[bool_ty] () AtomicClosed)).
      { solve_typing. } { apply lctx_ictx_alive_nil. solve_typing. }
      { solve_typing. } { solve_typing. }
      iIntros (v_ret). simpl_subst.
      (* After letcall, body is just "_r" — a value path. typed_body
         discharges with cont_postcondition = True trivially.  Pin
         the after-letcall transformer to [True] so the composed
         transformer reduces cleanly. *)
      iApply (typed_body_impl (λ _ _ _, True%type) (λ _ _ _, True%type));
        [done|].
      iIntros (tid xl mask post iκs) "_ _ _ _ _ _ _ _".
      by iApply pgl_wp_value. }
    intros post [[l bv] []] mask.
    cbn beta iota delta [trans_upper trans_tail compose Datatypes.id].
    intros [Hbv _Hpost]. subst bv.
    split; [done|].
    intros _. done.
  Qed.

End flip.

(** [coin_flip_safe]: with [↯_T (1/2)] in the input tctx, the
    program is safe.  Conclusion is [pgl ... ... (1/2)] — the
    typing-layer machinery threads the [1/2] credit budget through
    to the operational pgl bound. *)
Theorem coin_flip_safe `{!typePreG Σ}
    (σ : language.state lrust_prob_lang) (n : nat) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  pgl (exec n (coin_flip, σ)) (λ _, True) (1/2)%R.
Proof.
  intros Hσ.
  apply (type_soundness_credit (𝔅 := unitₛ)
           (λ _ _ _, True%type) (λ _ _, True%type) (1/2)%R coin_flip σ n Hσ).
  - split; lra.
  - intros _. done.
  - intros HtypeG HcnaInv l. iApply coin_flip_typed.
Qed.
