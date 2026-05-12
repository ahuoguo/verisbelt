From iris.proofmode Require Import environments proofmode.
From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type lft_contexts type_context cont_context inv_context proph_stubs.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Section typing.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.
  
  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body {𝔄l 𝔅} (E: elctx) (L: llctx) (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l)
    (e: expr) (tr: predl_trans' 𝔄l 𝔅) : iProp Σ := ∀tid xl mask post iκs,
    llft_ctx -∗ time_ctx -∗ elctx_interp E -∗
    llctx_interp L -∗ invctx_interp tid mask iκs I -∗ cctx_interp tid iκs post C -∗ tctx_interp tid T xl -∗
      ⌜tr post xl mask⌝ -∗ WP e {{ _, cont_postcondition }}.
  Global Arguments typed_body {_ _} _ _ _ _ _ _%E _%type.

  Global Instance typed_body_proper 𝔄l 𝔅 E L I C T e :
    Proper ((≡) ==> (≡)) (@typed_body 𝔄l 𝔅 E L I C T e).
  Proof.
    intros tr1 tr2 EQ. unfold typed_body.
    iSplit; iIntros "Hb" (?????) "A1 A2 A3 A4 A5 A6 A7 %J";
      iApply ("Hb" with "A1 A2 A3 A4 A5 A6 A7");
      iPureIntro; by apply EQ.
  Qed.

  Lemma typed_body_impl {𝔄l 𝔅} (tr tr': predl_trans' 𝔄l 𝔅) E L
      (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    (∀post xl mask, tr post xl mask → tr' post xl mask) →
    typed_body E L I C T e tr' -∗ typed_body E L I C T e tr.
  Proof.
    move=> Imp. rewrite /typed_body.
    iIntros "x" (?????) "A B C D E F G %J".
    iApply ("x" with "A B C D E F G"). iPureIntro. by apply Imp.
  Qed.

  Lemma typed_body_vacuous {𝔄l 𝔅} E L
      (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    ⊢ typed_body E L I C T e (λ _ _ _, False%type).
  Proof.
    rewrite /typed_body.
    iIntros (?????) "_ _ _ _ _ _ _ %Ha". done.
  Qed.

  Lemma typed_body_tctx_incl {𝔄l 𝔅l ℭ} tr' tr (T: tctx 𝔄l) (T': tctx 𝔅l) E L
      (I: invctx) (C: cctx ℭ) e :
    tctx_incl E L T T' tr' →
    typed_body E L I C T' e tr -∗ typed_body E L I C T e (tr' ∘ tr).
  Proof.
    iIntros ([? In]) "e". iIntros (?????) "#LFT TIME #E L Ic C T Obs".
    iApply fupd_pgl_wp.
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#guard #back]]]". { solve_ndisj. }
    iMod (In with "LFT E guard H1 T Obs") as (?) "(H1 & T' & Obs)".
      iDestruct ("back" with "H1 H2") as "back'". iMod (fupd_mask_mono with "back'") as "L". { solve_ndisj. }
    iModIntro. iApply ("e" with "LFT TIME E L Ic C T' Obs").
  Qed.

  (** Instruction *)
  Definition typed_instr {𝔄l 𝔅l} (E: elctx) (L: llctx) (I: invctx)
    (T: tctx 𝔄l) (e: expr) (T': val → tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀tid post mask iκs xl, llft_ctx -∗ time_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗ tctx_interp tid T xl -∗
      ⌜tr post xl mask⌝ -∗ WP e {{ v, ∃xl',
        llctx_interp L ∗ invctx_interp tid mask iκs I ∗ tctx_interp tid (T' v) xl' ∗ ⌜post xl' mask⌝ }}.
  Global Arguments typed_instr {_ _} _ _ _ _ _%E _ _%type.
  
  Definition typed_inv_instr {𝔄l 𝔅l} (E: elctx) (L: llctx) (I: invctx) 
    (T: tctx 𝔄l) (e: expr) (I': invctx) (T': val → tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀tid post mask iκs xl, llft_ctx -∗ time_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗ tctx_interp tid T xl -∗
      ⌜tr post xl mask⌝ -∗ WP e {{ v, ∃xl' mask',
        llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗ tctx_interp tid (T' v) xl' ∗ ⌜post xl' mask'⌝ }}.
  Global Arguments typed_instr {_ _} _ _ _ _ _%E _ _%type.

  (** Writing and Reading.

      The original verusbelt definitions wrapped the heap mapsto in a
      leaf-guard ([H &&{↑NllftG; d+1}&&> l #↦∗_]) to handle the
      [WriteNa1S]/[WriteNa2S] two-step protocol's intermediate cell
      states (visible to other threads via the cell-level [#↦∗_]
      abstraction).  Since concurrency was stripped (Scope C),
      [Write]/[Read] are single-step atomic ([lang.v:759-769]) — no
      thread can witness an intermediate state, so the leaf-guard
      collapses.  The simplified definitions use [heap_mapsto_vec l]
      (loc-level, what [wp_write]/[wp_read] in [lifting.v] actually
      consume) directly. *)

  Definition typed_write {𝔄 𝔅 𝔄' 𝔅'} (E: elctx) (L: llctx) (ty: type 𝔄) (tyb: type 𝔅)
    (ty': type 𝔄') (tyb': type 𝔅') (gt: ~~𝔄 → ~~𝔅) (st: ~~𝔄 → ~~𝔅' → ~~𝔄' → Prop) : Prop :=
    tyb.(ty_size) = tyb'.(ty_size) ∧ ∀x d (v: fancy_val) tid G,
    Timeless G →
    llft_ctx -∗ elctx_interp E -∗ (G &&{↑NllftG}&&> llctx_interp L) -∗
    G -∗ ty_own ty x d d tid [v] ={⊤}=∗ ∃(l: loc) (d':nat) (vl: list val),
      ⌜v = FVal #l⌝ ∗ ⌜d = S d'⌝ ∗
      ▷ heap.heap_mapsto_vec l vl ∗
      ▷ ty_own tyb (gt x) d' d tid (FVal <$> vl) ∗
      ∀y db' (vl': list val),
        heap.heap_mapsto_vec l vl' -∗
        ▷ ty_own tyb' y db' (S db') tid (FVal <$> vl') -∗
        ⧖(S db') -∗ £(2*db'*db' + 4*db' + 2)
        ={⊤}=∗ ∃z, G ∗ ⌜st x y z⌝ ∗ ty_own ty' z (S db') (d `max` S db') tid [v].
  Global Arguments typed_write {_ _ _ _} _ _ _%T _%T _%T _%T _%type _%type.

  Definition typed_read {𝔄 𝔅 𝔄'} (E: elctx) (L: llctx) (ty: type 𝔄) (tyb: type 𝔅)
    (ty': type 𝔄') (gt: ~~𝔄 → ~~𝔅) (st: ~~𝔄 → ~~𝔄' → Prop) : Prop := ∀x d v tid G,
    Timeless G →
    llft_ctx -∗ elctx_interp E -∗ (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
    ty_own ty x d d tid [v] -∗ £(d+1) ={⊤}=∗
      ∃(l: loc) (vl: list val), ⌜v = FVal #l⌝ ∗
        heap.heap_mapsto_vec l vl ∗
        ▷ ty_own tyb (gt x) d d tid (FVal <$> vl) ∗
        (heap.heap_mapsto_vec l vl ={⊤}=∗
          ∃z, ⌜st x z⌝ ∗ G ∗ ty_own ty' z d d tid [v]).
  Global Arguments typed_read {_ _ _} _ _ _%T _%T _%T _ _%type.

  Definition typed_instr_ty {𝔄l 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (T: tctx 𝔄l) (e: expr) (ty: type 𝔅) (tr: pred' (~~𝔅) → predl 𝔄l) : Prop :=
    typed_instr E L I T e (λ v, +[v ◁ ty]) (λ post al, tr (λ b, post -[b]) al).
  Global Arguments typed_instr_ty {_ _} _ _ _ _ _%E _%T _%type.

  Definition typed_val {𝔄} (v: val) (ty: type 𝔄) (a: ~~𝔄) : Prop :=
    ∀E L I, typed_instr_ty E L I +[] (of_val v) ty (λ post _, post a).
  Global Arguments typed_val {_} _%V _%T _%type.

  (* This lemma is helpful for specifying the predicate transformer. *)
  Lemma type_with_tr 𝔄l 𝔅 tr E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    typed_body E L I C T e tr -∗ typed_body E L I C T e tr.
  Proof. iIntros. done. Qed.

  (* This lemma is helpful when switching from proving unsafe code in Iris
     back to proving it in the type system. *)
  Lemma type_type {𝔄l 𝔅} (T: tctx 𝔄l) xl mask tr E L (I: invctx) (C: cctx 𝔅) e tid post iκs :
    typed_body E L I C T e tr -∗
    llft_ctx -∗ time_ctx -∗ elctx_interp E -∗
    llctx_interp L -∗ invctx_interp tid mask iκs I -∗ cctx_interp tid iκs post C -∗ tctx_interp tid T xl -∗
    ⌜tr post xl mask⌝ -∗ WP e {{ _, cont_postcondition }}.
  Proof.
    iIntros "Bd LFT TIME E L I C T Obs".
    iApply ("Bd" with "LFT TIME E L I C T Obs").
  Qed.

  (* TODO: Proof a version of this that substitutes into a compatible context...
     if we really want to do that. *)
  Lemma type_equivalize_lft {𝔄l 𝔅} E L I (C: cctx 𝔅) (T: tctx 𝔄l) κ κ' e tr :
    typed_body (κ ⊑ₑ κ' :: κ' ⊑ₑ κ :: E) L I C T e tr -∗
    typed_body E (κ ⊑ₗ [κ'] :: L) I C T e tr.
  Proof.
    iIntros "e" (?????) "#LFT TIME E [Eq L] I C T Obs".
    iApply fupd_pgl_wp.
    iMod (lctx_equalize_lft with "LFT Eq") as "[In In']".
    iModIntro. iApply ("e" with "LFT TIME [$E $In $In'] L I C T Obs").
  Qed.

  (** [type_dep_cond] / [type_dep] removed: they relied on
      [proph_obs_sat] / [proph_obs_impl] semantics that aren't
      meaningful under stripped prophecy. *)

  Lemma type_let' {𝔄l 𝔅l ℭl 𝔇} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr'
      (T: tctx ℭl) (I: invctx) (C: cctx 𝔇) xb e e' E L :
    Closed (xb :b: []) e' → typed_instr E L I T1 e T2 tr →
    (∀v: val, typed_body E L I C (T2 v h++ T) (subst' xb v e') tr') -∗
    typed_body E L I C (T1 h++ T) (let: xb := e in e')%E (λ post acl,
      let '(al, cl) := psep acl in tr (λ bl, tr' post (bl -++ cl)) al).
  Proof.
    iIntros "% %Inst e'" (? vπl2 ???). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #TIME #E L I C [T1 T] %Obs". wp_bind e.
    iApply (pgl_wp_wand with "[L I T1]").
    { iApply (Inst with "LFT TIME E L I T1"). iPureIntro.
      revert Obs. by rewrite /trans_upper papp_sepl. }
    iIntros (v) "A".
    iDestruct "A" as (xl') "(L & I & T2 & %Obs')". wp_let. iCombine "T2 T" as "T2T".
    iApply ("e'" with "LFT TIME E L I C T2T"). iPureIntro.
    revert Obs'. by rewrite papp_sepr.
  Qed.

  Lemma type_let'_with_inv {𝔄l 𝔅l ℭl 𝔇} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr'
      (T: tctx ℭl) (I1 I2: invctx) (C: cctx 𝔇) xb e e' E L :
    Closed (xb :b: []) e' → typed_inv_instr E L I1 T1 e I2 T2 tr →
    (∀v: val, typed_body E L I2 C (T2 v h++ T) (subst' xb v e') tr') -∗
    typed_body E L I1 C (T1 h++ T) (let: xb := e in e')%E (λ post acl,
      let '(al, cl) := psep acl in tr (λ bl, tr' post (bl -++ cl)) al).
  Proof.
    iIntros "% %Inst e'" (? vπl2 ???). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #TIME #E L I C [T1 T] %Obs". wp_bind e.
    iApply (pgl_wp_wand with "[L I T1]").
    { iApply (Inst with "LFT TIME E L I T1"). iPureIntro.
      revert Obs. by rewrite /trans_upper papp_sepl. }
    iIntros (v) "A".
    iDestruct "A" as (xl' mask') "(L & I & T2 & %Obs')". wp_let. iCombine "T2 T" as "T2T".
    iApply ("e'" with "LFT TIME E L I C T2T"). iPureIntro.
    revert Obs'. by rewrite papp_sepr.
  Qed.

  Lemma type_let {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr' trx
    (T: tctx ℭl) (T': tctx 𝔇l) E L I (C: cctx 𝔈) xb e e' tr_res :
    Closed (xb :b: []) e' → typed_instr E L I T1 e T2 tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    (∀v: val, typed_body E L I C (T2 v h++ T') (subst' xb v e') tr') -∗
    typed_body E L I C T (let: xb := e in e')%E tr_res.
  Proof.
    iIntros (???->) "?". iApply (typed_body_tctx_incl trx); [done|].
    by iApply type_let'.
  Qed.
  
  Lemma type_let_with_inv {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr' trx
    (T: tctx ℭl) (T': tctx 𝔇l) E L I1 I2 (C: cctx 𝔈) xb e e' tr_res :
    Closed (xb :b: []) e' → typed_inv_instr E L I1 T1 e I2 T2 tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    (∀v: val, typed_body E L I2 C (T2 v h++ T') (subst' xb v e') tr') -∗
    typed_body E L I1 C T (let: xb := e in e')%E tr_res.
  Proof.
    iIntros (???->) "?". iApply (typed_body_tctx_incl trx); [done|].
    by iApply type_let'_with_inv.
  Qed.

  Lemma type_val {𝔄 𝔅l ℭ} v (a: ~~𝔄) ty (T: tctx 𝔅l) E L (I: invctx) (C: cctx ℭ) xb e tr :
    Closed (xb :b: []) e → typed_val v ty a →
    (∀v': val, typed_body E L I C (v' ◁ ty +:: T) (subst' xb v' e) tr) -∗
    typed_body E L I C T (let: xb := v in e)%E (λ post bl, tr post (a -:: bl)).
  Proof.
    iIntros (? Val) "?". iApply type_let; [apply Val|solve_typing|done..].
  Qed.

  (* [type_val_dep] lets the obtained value depend on dynamic values;
    it is derived from [type_dep] and [type_val] *)
  (* 
  Lemma type_val_dep {𝔄 𝔅l B ℭl 𝔇l 𝔈} (a: B → 𝔄) ty (Tx: tctx 𝔅l)
      E L (C: cctx 𝔈) (T: tctx ℭl) (T': tctx 𝔇l) v xb e trx tr f :
    Closed (xb :b: []) e → (∀b, typed_val v ty (a b)) →
    tctx_extract_ctx E L Tx T T' trx → real_tctx E L Tx f →
    (∀v': val, typed_body E L C (v' ◁ ty +:: Tx h++ T') (subst' xb v' e) tr) -∗
    typed_body E L C T (Skip;; let: xb := v in e) (trx ∘
      (λ post bdl, let '(bl, dl) := psep bdl in tr post (a (f bl) -:: bdl))).
  Proof.
    iIntros (? Val ??) "e". iApply typed_body_impl; last first.
    { iApply type_dep; [ |done|done|].
      (* TODO: make [solve_closed] work here *)
      { rewrite /Closed /= !andb_True. split; [done|]. split; [|done].
        apply is_closed_of_val. }
      iIntros (b). iApply type_val; by [exact (Val b)|]. }
    by move=>/= ??.
  Qed.
  *)

  Lemma type_seq {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: tctx 𝔅l)
    (T: tctx ℭl) (T': tctx 𝔇l) E L (I: invctx) (C: cctx 𝔈) e e' tr tr' trx tr_res :
    Closed [] e' → typed_instr E L I T1 e (const T2) tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    typed_body E L I C (T2 h++ T') e' tr' -∗ typed_body E L I C T (e;; e')%E tr_res.
  Proof. iIntros. iApply (type_let _ (const T2))=>//. by iIntros. Qed.
  
  (* this is strictly more general than type_seq,
  should refactor to make this the default one *)
  Lemma type_seq_with_inv {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: tctx 𝔅l)
    (T: tctx ℭl) (T': tctx 𝔇l) E L (I1 I2: invctx) (C: cctx 𝔈) e e' tr tr' trx tr_res :
    Closed [] e' → typed_inv_instr E L I1 T1 e I2 (const T2) tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    typed_body E L I2 C (T2 h++ T') e' tr' -∗ typed_body E L I1 C T (e;; e')%E tr_res.
  Proof. iIntros. iApply (type_let_with_inv _ (const T2))=>//. by iIntros. Qed.

  Lemma type_newlft {𝔄l 𝔅} κl E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e tr :
    Closed [] e → (∀κ, typed_body E (κ ⊑ₗ κl :: L) I C T e tr) -∗
    typed_body E L I C T (Newlft;; e) tr.
  Proof.
    iIntros (?) "e %%%%% #LFT TIME E L I C T Obs".
    iApply fupd_pgl_wp.
    iMod (llftl_begin' with "LFT") as (Λ) "[Λ #Hinh]"; [done|].
    iModIntro.
    set κ' := lft_intersect_list κl. wp_seq.
    iApply ("e" $! κ' ⊓ Λ with "LFT TIME E [Λ $L] I C T Obs").
    rewrite /llctx_interp. iExists Λ. iFrame "Λ". by iSplit.
  Qed.
  

  (** [type_endlft], [type_resolve_instr], [type_resolve] removed:
      they depended on the [resolve] / [resolve_unblock_tctx]
      infrastructure which is unsound under eris. *)

  Lemma type_path_instr {𝔄} p (ty: type 𝔄) E L I :
    typed_instr_ty E L I +[p ◁ ty] p ty (λ post '-[v], post v).
  Proof.
    iIntros (????[vπ[]]) "_ _ _ $$ [T _] Obs". iApply (wp_hasty with "T").
    iIntros (v d _) "??". iExists -[vπ]. do 2 (iSplit; [|done]). iExists v, d.
    rewrite eval_path_of_val. by iFrame.
  Qed.

  Lemma type_letpath {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) (T: tctx 𝔅l) (T': tctx ℭl)
    (I: invctx) (C: cctx 𝔇) x p e trx tr E L :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p in e) (trx ∘ tr).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by eapply type_path_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.
  
  (** [type_assign_instr] / [type_deref_instr] / [type_memcpy_instr]:
      not yet ported.

      The infrastructure is now in place to do this:
      - [typed_write] / [typed_read] above are simplified to use
        [heap_mapsto_vec] (loc-level) directly, dropping the
        leaf-guard `H &&{N;d+1}&&> l #↦∗_` (which only existed to
        handle the [WriteNa1S]/[WriteNa2S] two-step protocol's
        observable intermediate states; concurrency stripped in
        Scope B makes the guard unnecessary).
      - [wp_persistent_time_receipt_lc] in [lang/lifting.v]
        provides the [⧖n → ⧖(S n) ∗ £(advance_credits n)] step
        used by the heap-rule proofs.
      - [wp_write] / [wp_read] in [lang/lifting.v] are usable
        directly (no [wp_write_na_guarded] wrapper needed).

      What still needs design choices to land cleanly:

      1. **[⧗] threading.** [wp_persistent_time_receipt_lc] consumes
         one [⧗1] per use.  The rule needs to acquire that [⧗1]
         from somewhere — either threaded through [typed_body] /
         [typed_instr] (typing-layer-wide change), or carried as a
         tctx entry, or supplied as an explicit iProp premise to
         each heap-rule lemma (clients pre-allocate a [⧗]-pool at
         adequacy time).
      2. **Mapsto-fancy bridging.** [typed_write] now hands back
         [heap_mapsto_vec l vl] and [▷ ty_own tyb _ _ _ (FVal <$> vl)],
         while the [tyb'] from [wp_hasty pb] uses
         [ty_own tyb' y db' db' tid [FVal vb]] (singleton).  The
         proof needs [length vl = 1] (from the size constraint)
         and to convert `[vb]` into a list-valued shape matching
         the closer.  Mechanical, but a few rewrites.

      Once those two are settled, the proof body is a
      straightforward port of the original (already present in
      verusbelt's pre-strip [programs.v]) with [wp_write] in place
      of [wp_write_na_guarded] and [wp_persistent_time_receipt_lc]
      in place of [wp_persistent_time_receipt]. *)
End typing.

Ltac via_tr_impl :=
  iStartProof;
  match goal with |- envs_entails _ (typed_body _ _ _ ?C ?T _ _) =>
    let TypeT := type of T in let TypeC := type of C in
    match eval hnf in (TypeT, TypeC) with (hlist _ ?𝔄l, list (_ ?𝔅)) =>
      iApply (typed_body_impl (𝔄l:=𝔄l) (𝔅:=𝔅)); last first
    end
  end.

Ltac via_tr_impl_with tr :=
  iStartProof;
  match goal with |- envs_entails _ (typed_body _ _ ?C ?T _ _) =>
    let TypeT := type of T in let TypeC := type of C in
    match eval hnf in (TypeT, TypeC) with (hlist _ ?𝔄l, list (_ ?𝔅)) =>
      evar (tr: predl_trans' 𝔄l 𝔅);
      iApply (typed_body_impl (𝔄l:=𝔄l) (𝔅:=𝔅) tr); last first
    end
  end.

Ltac intro_subst := iIntros (?); simpl_subst.
Ltac intro_subst_as x := iIntros (x); simpl_subst.

Global Hint Opaque typed_instr typed_write typed_read : lrust_typing.
