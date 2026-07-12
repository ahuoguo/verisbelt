Import EqNotations.
From lrust.typing Require Export type.
From lrust.typing Require Import own programs cont.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Fixpoint subst_plv {𝔄l} (bl: plistc binder 𝔄l) (vl: plistc val 𝔄l) (e: expr) : expr :=
  match 𝔄l, bl, vl with
  | [], _, _ => e
  | _::_, b -:: bl', v -:: vl' => subst' b v (subst_plv bl' vl' e)
  end.

Global Instance do_subst_plv {𝔄l} (bl vl: plistc _ 𝔄l) e :
  DoSubstL bl (map of_val vl) e (subst_plv bl vl e).
Proof.
  rewrite /DoSubstL. induction 𝔄l, bl, vl; [done|]=>/=. by rewrite IH𝔄l.
Qed.

Definition boxl (𝔄l: syn_typel) : syn_typel := (fmap at_locₛ 𝔄l).
Notation fn_spec 𝔄l 𝔅 ℭ := ((~~ℭ) → predl_trans' (boxl 𝔄l) (at_locₛ 𝔅)).

Section fn.
  Context `{!typeG Σ, !cnaInv_logicG Σ} {A: Type} {𝔄l 𝔅}.

  Record fn_params :=
    FP {
      fp_E_ex: lft → elctx;
      fp_ityl: typel 𝔄l;
      fp_oty: type 𝔅;
      fp_atomic_state: invctx_atomic_state
    }.

  Definition fn_params_dist n fp fp' : Prop :=
    (∀ϝ, fp.(fp_E_ex) ϝ = fp'.(fp_E_ex) ϝ) ∧
    fp.(fp_ityl) ≡{n}≡ fp'.(fp_ityl) ∧ fp.(fp_oty) ≡{n}≡ fp'.(fp_oty).

  Definition fp_E (fp: fn_params) ϝ : elctx :=
    fp.(fp_E_ex) ϝ ++ tyl_E fp.(fp_ityl) ++ tyl_outlives_E fp.(fp_ityl) ϝ ++
    fp.(fp_oty).(ty_E) ++ ty_outlives_E fp.(fp_oty) ϝ.

  Lemma elctx_sat_fp_E (fp: fn_params) ϝ ϝ' L :
    fp_E_ex fp = const [] →
    elctx_sat (ϝ' ⊑ₑ ϝ :: fp_E fp ϝ) L (fp_E fp ϝ').
  Proof.
    move=> Eq. rewrite /fp_E Eq /=. apply elctx_sat_app; [solve_typing|].
    apply elctx_sat_app. { apply (tyl_outlives_E_elctx_sat_mono ϝ'); solve_typing. }
    apply elctx_sat_app; [solve_typing|].
    apply (ty_outlives_E_elctx_sat_mono ϝ'); solve_typing.
  Qed.

  Definition tr_ret {𝔄} : predl_trans' [𝔄] (𝔄) := λ post '-[a], λ mask, post a mask.

  Fixpoint box_typel {𝔅l} (tyl: typel 𝔅l) : (typel (boxl 𝔅l)) :=
    match tyl with
      | +[] => +[]
      | (ty +:: tyl') => (box ty +:: box_typel tyl')
    end.

  Program Definition fn {ℭ} (fp: A → fn_params) (spec: fn_spec 𝔄l 𝔅 ℭ)
    : type (exec_funₛ ℭ) :=
    {|
      pt_size := 1;
      pt_gho (x: ~~ (exec_funₛ ℭ)) tid := tc_opaque
        (∃fb kb (bl: plistc _ _) e H, ⌜fst x = @RecV fb (kb :: bl) e H⌝ ∗
              ▷ □ ∀y ϝ k (wl: plistc _ _),
                typed_body (fp_E (fp y) ϝ) [ϝ ⊑ₗ []] (InvCtx [] ϝ (fp_atomic_state (fp y)))
                  [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp y))), λ v: vec _ 1, +[vhd v ◁ box (fp y).(fp_oty)] } tr_ret]
                  (hzip_with (λ _ boxty (w: val), w ◁ boxty) (box_typel (fp y).(fp_ityl)) wl)
                  (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
                  (spec (snd x))
        );
      pt_phys (x: ~~ (exec_funₛ ℭ)) tid := [FVal (fst x)];
    |}%I.
  Next Obligation. rewrite /tc_opaque. apply _. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
End fn.

Arguments fn_params {_ _} _ _.

Global Instance elctx_empty : Empty (lft → elctx) := λ _, [].

Notation "fn< p > ( E ; ity , .. , ity' ) → oty" :=
  (fn (λ p, FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T AtomicClosed))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn< p > ( E ) → oty" := (fn (λ p, FP E%EL +[] oty%T AtomicClosed))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E )  →  oty") : lrust_type_scope.
Notation "fn( E ; ity , .. , ity' ) → oty" :=
  (fn (λ _: (), FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T AtomicClosed))
  (at level 99, oty at level 200, format
    "fn( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn( E ) → oty" := (fn (λ _: (), FP E%EL +[] oty%T AtomicClosed))
  (at level 99, oty at level 200, format "fn( E )  →  oty") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Global Instance fn_send {A 𝔄l 𝔅 ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) : Send (fn fp spec).
  Proof.
    intros. split. intros. unfold syn_abstract in H. inversion H.
    unfold ty_phys, fn, ty_of_st. simpl. rewrite H1. trivial.
  Qed.

  Global Instance fn_sync {A 𝔄l 𝔅 ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) : Sync (fn fp spec).
  Proof. split; trivial. split; iSplit; iIntros "?"; done. Qed.

  Lemma fn_subtype_specialize {A B 𝔄l 𝔅 ℭ} (σ: A → B) (fp: B → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) E L :
    subtype E L (fn fp spec) (fn (fp ∘ σ) spec) idₛ.
  Proof.
    apply subtype_plain_type. iIntros "_ !> _ /=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|]. iSplit; last by done. iIntros "*".
    iIntros "#A". iFrame "A". iSplit; last by (iIntros "_"; done).
    iDestruct "A" as (fb kb bl e H) "[A #B]". iExists fb, kb, bl, e, H. iFrame "A".
    iNext. iModIntro. iIntros (y ϝ k wl). iApply "B".
  Qed.

  (** Helper: peel boxed-typed arguments off a call expression by
      eval'ing each [box ity] path to its value. *)
  Local Lemma wp_app_hasty_box {𝔄l} vl r (f: val)
    (pl: plistc _ (boxl 𝔄l)) tyl vπl tid (Φ: val → iProp Σ) :
    tctx_interp tid (hzip_with (λ _ boxty q, q ◁ boxty) (box_typel tyl) pl) vπl -∗
    (∀wl: plistc _ _,
      tctx_interp tid (hzip_with (λ _ boxty (w: val), w ◁ boxty) (box_typel tyl) wl) vπl -∗
      WP f (of_val r :: map of_val (vl ++ wl))%V {{ Φ }}) -∗
    WP f (of_val r :: map of_val vl ++ pl) {{ Φ }}.
  Proof.
    move: tyl pl vπl vl. elim=> [|???? IH].
    { iIntros "* _ Wp". iSpecialize ("Wp" $! -[] with "[//]"). by rewrite !right_id. }
    iIntros ([p pl'][??]vl) "/= [p pl'] ToWp".
    have ->: App f (of_val r :: map of_val vl ++ p :: pl') =
      fill_item (AppRCtx f (r :: vl) pl') p by done.
    iApply pgl_wp_bind. iApply (wp_hasty with "p"). iIntros (w ? _) "⧖ p".
    have ->: fill_item (AppRCtx f (r :: vl) pl') w =
      App f (of_val r :: map of_val (vl ++ [w]) ++ pl') by rewrite map_app -assoc.
    iApply (IH with "pl'"). iIntros (?) "pl'". rewrite -assoc.
    iApply ("ToWp" $! (_-::_)). iFrame "pl'". iExists w, _.
    iSplit; first by rewrite eval_path_of_val. iFrame "⧖ p".
  Qed.

  (** Helper: split [invctx_interp] into a "callee-visible" view
      (with just the fn's lifetime ϝ as the lifetime witness) and a
      closer that puts the caller's invariants back. *)
  Local Lemma invctx_interp_call Il ϝ' 𝛼 tid mask ϝ iκs :
      ϝ ⊑ ϝ' -∗
      ϝ ⊑ lft_intersect_list (fmap invctx_elt_unwrap Il) -∗
      invctx_interp tid mask iκs (InvCtx Il ϝ' 𝛼) -∗ ∃ iκs',
      invctx_interp tid mask iκs' (InvCtx [] ϝ 𝛼) ∗
          (∀ mask', invctx_interp tid mask' iκs' (InvCtx [] ϝ 𝛼) -∗
            invctx_interp tid mask' iκs (InvCtx Il ϝ' 𝛼)).
  Proof.
    unfold invctx_interp.
    iIntros "#Incl1 #InclList".
    iDestruct 1 as (na_mask at_mask) "[#masks [[cna_lifetimes #Incl] [cna_own ato]]]".
    iExists (fmap invctx_elt_unwrap Il ++ iκs).
    iSplitL.
     - iExists na_mask, at_mask. iFrame "masks cna_own ato".
       unfold invctx_to_multiset. simpl. rewrite gmultiset_disj_union_left_id.
       rewrite list_to_set_disj_app. iFrame "cna_lifetimes".
       rewrite lft_intersect_list_app.
       iApply llftl_incl_glb; first by done.
       iApply (guards_transitive with "Incl1 Incl").
     - iDestruct 1 as (na_mask' at_mask') "[#masks' [[cna_lifetimes #Incl'] [cna_own ato]]]".
       iFrame. iFrame "#".
       unfold invctx_to_multiset. simpl. rewrite gmultiset_disj_union_left_id.
       rewrite list_to_set_disj_app. iFrame "cna_lifetimes".
  Qed.

  (** [type_call_iris']: WP-level call rule.  Prophecy-free port of
      upstream's [type_call_iris']. *)
  Lemma type_call_iris' {A 𝔄l 𝔅 ℭ} L κl x (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ)
      p ql ql' (k: expr) E xl efun tid
        (post: ~~ (at_locₛ 𝔅) → Mask → Prop)
        (mask: Mask) Il ϝ' iκs G :
    AsVal k → IntoPlistc ql ql' → Timeless G →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) L (fp_E (fp x) ϝ)) →
    llft_ctx -∗ time_ctx -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗
    (G &&{↑NllftG}&&> @[lft_intersect_list κl]) -∗ G -∗
    invctx_interp tid mask iκs (InvCtx Il ϝ' (fp_atomic_state (fp x))) -∗
    tctx_elt_interp tid (p ◁ fn fp spec) efun -∗
    tctx_interp tid (hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') xl -∗
    ⌜(spec efun.2) post xl mask⌝ -∗
    (∀(ret: val) (mask': Mask) w, G -∗
      invctx_interp tid mask' iκs (InvCtx Il ϝ' (fp_atomic_state (fp x))) -∗
      tctx_elt_interp tid (ret ◁ box (fp x).(fp_oty)) w -∗ ⌜post w mask'⌝ -∗
      WP k [of_val ret] {{ _, cont_postcondition }}) -∗
    WP (call: p ql → k) {{ _, cont_postcondition }}.
  Proof.
    move=> [k' <-]-> TimelessG IctxAlv ToEfp.
    iIntros "#LFT #TIME #E #GguardsL #Gguardsκl G ii p ql %Obs k".
    iApply fupd_pgl_wp.
    iMod (llftl_begin' with "LFT") as (ϝ) "[ϝ #ϝnonempty]"; [done|].
    leaf_open "GguardsL" with "G" as "[L back]"; first by solve_ndisj.
    iDestruct (ToEfp ϝ with "L") as "#EfpPre".
    iDestruct (lctx_ictx_alive_L_guards_ϝ _ _ _ _ _ IctxAlv with "L E") as "#Lguardsϝ'".
    iDestruct (lctx_ictx_alive_L_guards_list _ _ _ _ _ IctxAlv with "L E") as "#LguardsIl".
    iMod ("back" with "L") as "G".
    iMod (llftl_borrow_shared _ ϝ with "G") as "[fGuardsG' ToG]"; first by solve_ndisj.
    iDestruct (guards_remove_later_rhs with "fGuardsG'") as "#fGuardsG". iClear "fGuardsG'".
    iDestruct (guards_transitive with "fGuardsG Gguardsκl") as "Borκl".
    iDestruct (guards_transitive with "fGuardsG GguardsL") as "fGuardsL".
    iDestruct ("EfpPre" with "[$E]") as "#Efp".
    { clear ToEfp. iClear "EfpPre". iClear "Gguardsκl".
      iInduction κl as [|κ κl] "IH"; [done|]=>/=.
      iSplit. { iApply (llftl_incl_trans with "Borκl []"). iApply llftl_intersect_incl_l. }
      iApply "IH". iModIntro. iApply llftl_incl_trans; [done|].
      iApply llftl_intersect_incl_r. }
    iModIntro. wp_bind p. iApply (wp_hasty with "p"). iIntros (?? _) "_ ".
    iDestruct 1 as "[gho %phys]". iDestruct "gho" as (fb kb bl e Hclosed) "[%Hrec #e]".
    inversion phys as [Eqv].
    have ->: (λ: ["_r"], Skip;; k' ["_r"])%E = (λ: ["_r"], Skip;; k' ["_r"])%V by unlock.
    iApply (wp_app_hasty_box [] with "ql")=>/=. iIntros (wl) "ityl".
    rewrite Hrec /=.
    have ->: ((λ: ["_r"], Skip;; k' ["_r"])%V : expr) :: map of_val wl =
             map of_val ((λ: ["_r"], Skip;; k' ["_r"])%V :: wl) by done.
    (* [wp_rec] can't reshape past [Rec fb (kb :: bl) e] because
       [to_val] gets stuck on the opaque [Closed] decide.  Apply the
       pure step manually via [lifting.wp_pure_step_later]. *)
    pose proof (@pure_rec
                  (Rec fb (kb :: bl) e) fb (kb :: bl) e
                  (subst' fb (Rec fb (kb :: bl) e)
                     (subst' kb ((λ: ["_r"], Skip ;; k' ["_r"])%V)
                        (subst_plv bl wl e)))
                  (map of_val ((λ: ["_r"], Skip;; k' ["_r"])%V :: wl))
                  eq_refl _ Hclosed _) as Hpure.
    iSpecialize ("e" $! x ϝ ((λ: ["_r"], Skip;; k' ["_r"])%V) wl).
    iApply (lifting.wp_pure_step_later _ _ _ _ _ _ _ Hpure I).
    iNext.
    iDestruct (invctx_interp_call Il ϝ' _ tid mask ϝ iκs with "[] [] ii") as (iκs') "[ii iiback]".
      { iApply (guards_transitive with "fGuardsL Lguardsϝ'"). }
      { iApply (guards_transitive with "fGuardsL LguardsIl"). }
    iApply ("e" with "LFT TIME Efp [ϝ] ii [ToG k iiback] ityl []").
    { iSplitL; [|done]. iExists _. iSplit; [by rewrite/= left_id|]. by iFrame "ϝ". }
    { rewrite cctx_interp_singleton. iIntros (v' [locret b] mask'). inv_vec v'=> v'.
      iIntros "[(%& %Eq & ϝ &_) _] Invctx [oty ?] %Obs'". rewrite/= left_id in Eq.
      rewrite -Eq. wp_rec. wp_bind Skip.
      iDestruct "ϝnonempty" as "%To".
      iDestruct (llftl_end' with "LFT ϝ") as "†ϝ"; first by trivial.
      iApply (pgl_wp_mask_mono _ (↑Nllft)); [done|].
      (* set_solver will take a long time otherwise *)
      iApply ((pgl_wp_step_fupd _ (↑Nllft) ∅ Skip ([†ϝ])%I _) ltac:(done) ltac:(set_solver) with "†ϝ").
      wp_seq. iIntros "†ϝ !>".
      wp_seq.
      iMod ("ToG" with "†ϝ") as "> G".
      iDestruct ("iiback" with "Invctx") as "Invctx".
      destruct b. iApply ("k" with "G Invctx oty [%//]"). }
    iPureIntro. simpl. exact Obs.
  Qed.

  (** [type_call]: typed_body version of call. *)
  Lemma type_call {A 𝔄l 𝔅 ℭl 𝔇l 𝔈l 𝔉 ℭ} x (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql' k trx
      trk tri E L (C: cctx 𝔉) Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l) (Tk: vec val 1 → tctx 𝔈l) :
    IntoPlistc ql ql' → Forall (lctx_lft_alive E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ fn fp spec +::
      hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    k ◁cont{L, (InvCtx Il ϝ' (fp_atomic_state (fp x))), Tk} trk ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ box (fp x).(fp_oty) +:: T') (Tk [#ret]) tri) →
    ⊢ typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (call: p ql → k) (trx ∘
      (λ post '(trp -:: adl), λ mask,
      let '(al, dl) := psep adl in
        (spec trp.2) (λ (b: ~~ (at_locₛ 𝔅)) mask, tri (trk post) (b -:: dl) mask) al mask)).
  Proof.
    move=> ? Alv ???? InTk. iApply typed_body_tctx_incl; [done|].
    iIntros (?[? adπl]mask post iκs). move: (papp_ex adπl)=> [aπl[dπl->]].
    iIntros "#LFT #TIME #E L I C /=(p & ql & T') %Obs".
    iDestruct (lctx_lft_alive_tok_list with "L E") as "#Alv"; [done|].
    iApply (type_call_iris' with "LFT TIME E [] Alv L I p ql [%]"); [done|done|..].
    { iApply guards_refl. }
    { simpl in Obs. rewrite papp_sepl papp_sepr in Obs. exact Obs. }
    iIntros (ret mask' ?) "L I ret Obs'".
    iApply fupd_pgl_wp.
    iMod (proj2 (InTk _) _ _ (_-::_) with "LFT E [] L [$ret $T'] Obs'")
      as (?) "(L & Tk & %Obs'')". { iApply guards_refl. }
    iModIntro.
    have ->: [ret: expr] = map of_val ([#ret]) by done.
    iApply ("C" with "[%//] L I Tk [%//]").
  Qed.

  (** [type_letcall]: introduce a continuation for the call result. *)
  Lemma type_letcall {A 𝔄l 𝔅 ℭ ℭl 𝔇l 𝔈} x (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql'
                     Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l) b e trx tr E L (C: cctx 𝔈)
                     `{!IntoPlistc ql ql', !Closed (b :b: []) e, !Closed [] p} :
    TCForall (Closed []) ql → Forall (lctx_lft_alive E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ fn fp spec +::
      hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    (∀ret: val, typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C
      (ret ◁ box (fp x).(fp_oty) +:: T') (subst' b ret e) tr) -∗
    typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (letcall: b := p ql in e)
      (trx ∘ (λ post '(trp -:: adl) mask,
        let '(al, dl) := psep adl in
          (spec trp.2) (λ b mask, tr post (b -:: dl) mask) al mask)).
  Proof.
    move=> Clql ????. iIntros "e". iApply type_cont_norec.
    - eapply is_closed_weaken; [done|]. set_solver+.
    - rewrite /Closed /= !andb_True. split.
      + by eapply is_closed_weaken, list_subseteq_nil.
      + eapply Is_true_eq_left, forallb_forall, List.Forall_forall, Forall_impl;
        [by apply TCForall_Forall|]=> ??.
        eapply Is_true_eq_true, is_closed_weaken=>//. set_solver+.
    - iIntros (k).
      have ->: subst' "_k" k (call: p ql → "_k")%E = subst "_k" k p $
        (λ: ["_r"], Skip;; k ["_r"])%E :: map (subst "_k" k) ql by done.
      rewrite is_closed_nil_subst; [|done].
      have ->: map (subst "_k" k) ql = ql.
      { clear -Clql. elim Clql; [done|]=>/= ????->. by rewrite is_closed_nil_subst. }
      iApply typed_body_proper; last first.
      { iApply type_call=>//; [constructor|]=> v.
        have {1}->: v = vhd [#v] by done. move: [#v]=> ?. apply tctx_incl_refl. }
      done.
    - iIntros (? ret). inv_vec ret=> ret. rewrite /subst_v /=.
      rewrite (is_closed_subst []); [| |set_solver+]; last first.
      { apply subst'_is_closed; [|done]. apply is_closed_of_val. }
      iApply "e".
  Qed.

  Lemma type_fnrec {A 𝔄l 𝔅 ℭ} tr (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) fb e bl bl'
      `{Into: !IntoPlistc bl bl', Cl: !Closed (fb :b: ("return" :: bl)%binder +b+ []) e} :
    (∀x ϝ (f: val) k (wl: plistc _ (boxl 𝔄l)),
        ⊢ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []] (InvCtx [] ϝ (fp_atomic_state (fp x)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))), λ v: vec _ 1, +[vhd v ◁ box (fp x).(fp_oty)] } tr_ret]
            (f ◁ fn fp spec +:: hzip_with (λ _ boxty (v: val), v ◁ boxty) (box_typel (fp x).(fp_ityl)) wl)
            (subst' fb f $ subst "return" k $ subst_plv bl' wl e)
            (λ post '(tr' -:: al), λ mask, tr'.2 = tr ∧ (spec tr) post al mask)%type) →
    typed_val (fnrec: fb bl := e)%V (fn fp spec) (@RecV fb ("return" :: bl)%binder e Cl, tr).
  Proof.
    move: Cl. rewrite Into. iIntros (Cl Body E L I tid post mask iκs []) "_ _ _ $ $ _ %Obs".
    rewrite /typed_instr_ty /=. unlock.
    iMod persistent_time_receipt_0 as "#⧖".
    iApply pgl_wp_value'. iExists -[((@RecV fb ("return" :: (bl' : list _))%binder e Cl)%V, tr)].
    iSplit; last by iPureIntro.
    iSplit; last done.
    iLöb as "IH".
    iExists (RecV fb ("return" :: (bl' : list _))%binder e), 0%nat.
    iSplit. { iPureIntro. by rewrite /= decide_True_pi. }
    iFrame "⧖".
    rewrite /ty_own /=. iSplit; last done.
    iExists fb, "return"%binder, bl', e, Cl.
    iSplit; first done.
    iNext. iModIntro. iIntros (y ϝ k wl).
    rewrite /typed_body.
    iIntros (tid' xl' mask' post' iκs') "#LFT #TIME #Efp L I C T %Obs'".
    iApply (Body y ϝ (RecV fb ("return" :: (bl' : list _))%binder e) k wl $! tid' (_ -:: xl') mask' post' iκs'
              with "LFT TIME Efp L I C [T] []").
    - iSplit; last by iFrame "T". iApply "IH".
    - iPureIntro. split; [done|exact Obs'].
  Qed.

  Lemma type_fn {A 𝔄l 𝔅 ℭ} tr (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) e bl bl'
      `{!IntoPlistc bl bl', !Closed ("return" :: bl +b+ []) e} :
    (∀x ϝ k (wl: plistc _ (boxl 𝔄l)),
        ⊢ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []] (InvCtx [] ϝ (fp_atomic_state (fp x)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))), λ v: vec _ 1, +[vhd v ◁ box (fp x).(fp_oty)] } tr_ret]
            (hzip_with (λ _ boxty (v: val), v ◁ boxty) (box_typel (fp x).(fp_ityl)) wl)
            (subst "return" k $ subst_plv bl' wl e) (spec tr)) →
    typed_val (fn: bl := e)%V (fn fp spec) (RecV <> ("return" :: bl)%binder e, tr).
  Proof.
    move=> Body.
    eapply type_fnrec; [apply _|]. iIntros (x ϝ f k wl).
    iApply typed_body_impl; last first.
    { iApply typed_body_tctx_incl; [|iApply Body].
      apply tctx_incl_resolve_head. }
    by move=> ?[??]? [_ ?].
  Qed.

End typing.

Ltac simpl_fp_E := rewrite /fp_E /ty_outlives_E /=.
