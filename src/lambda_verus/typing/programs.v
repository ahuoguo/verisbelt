From iris.proofmode Require Import environments proofmode.
From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type lft_contexts type_context cont_context inv_context.
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

  (** Writing and Reading — upstream verisbelt shape.  The closer
      receives an abstract [H : iProp Σ] gated by a leaf-guard
      [H &&{↑NllftG; d+1}&&> l #↦∗_].  Cell-level reads/writes through
      this guard are mediated by [wp_write_guarded] /
      [wp_read_guarded] in [lang/lifting.v] (built on top of
      [heap_write] / [heap_read] in [lang/heap.v]). *)

  Definition typed_write {𝔄 𝔅 𝔄' 𝔅'} (E: elctx) (L: llctx) (ty: type 𝔄) (tyb: type 𝔅)
    (ty': type 𝔄') (tyb': type 𝔅') (gt: ~~𝔄 → ~~𝔅) (st: ~~𝔄 → ~~𝔅' → ~~𝔄' → Prop) : Prop :=
    tyb.(ty_size) = tyb'.(ty_size) ∧ ∀x d (v: fancy_val) tid G,
    Timeless G →
    llft_ctx -∗ elctx_interp E -∗ (G &&{↑NllftG}&&> llctx_interp L) -∗
    G -∗ ty_own ty x d d tid [v] ={⊤}=∗ ∃(l: cloc) (d':nat) (H: iProp Σ),
      ⌜v = FVal #(l.1)⌝ ∗ ⌜d = S d'⌝ ∗ ▷ l #↦!∗: ty_own tyb (gt x) d' d tid ∗
      H ∗ (H &&{↑NllftG; d+1}&&> l #↦∗_) ∗
      ∀y db', ▷ l #↦!∗: ty_own tyb' y db' (S db') tid -∗ ⧖(S db') -∗
        £(2*db'*db' + 4*db' + 2) -∗ H
        ={⊤}=∗ ∃z, G ∗ ⌜st x y z⌝ ∗ ty_own ty' z (S db') (d `max` S db') tid [v].
  Global Arguments typed_write {_ _ _ _} _ _ _%T _%T _%T _%T _%type _%type.

  Definition typed_read {𝔄 𝔅 𝔄'} (E: elctx) (L: llctx) (ty: type 𝔄) (tyb: type 𝔅)
    (ty': type 𝔄') (gt: ~~𝔄 → ~~𝔅) (st: ~~𝔄 → ~~𝔄' → Prop) : Prop := ∀x d v tid G,
    Timeless G →
    llft_ctx -∗ elctx_interp E -∗ (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
    ty_own ty x d d tid [v] -∗ £(d+1) ={⊤ ∖ ↑advN}=∗
      ∃(l: cloc) (vl_concrete: list val) (vl: list fancy_val) H, ⌜v = FVal #(l.1)⌝ ∗
        ⌜length vl_concrete = length vl⌝ ∗
        H ∗ (H &&{↑NllftG; d+1}&&> (l.1 ↦[^ l.2]∗ vl_concrete)) ∗
        (∀ l₁ c₁ , (l₁, c₁) #↦∗_ ∗ (l₁, c₁) #↦∗ vl_concrete ={∅}=∗ (l₁, c₁) #↦∗_ ∗ (l₁, c₁) #↦!∗ vl) ∗
        ⌜StackOkay tyb → vl = fmap FVal vl_concrete⌝ ∗
        ▷ ty_own tyb (gt x) d d tid vl ∗ (H ={⊤ ∖ ↑advN}=∗
          ∃ z, ⌜st x z⌝ ∗ G ∗ ty_own ty' z d d tid [v]).
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
  
  (** [type_deref_instr]: typed reading via a [typed_read] proof.
      Constructs the [G &&{↑NllftG}&&> llctx_interp L] guard, invokes
      [typed_read] to obtain an abstract [Q] + leaf-guard to the
      cell-level mapsto, then runs [wp_read_guarded] (which opens
      the guard, performs the atomic read, and closes).
      The [StackOkay tyb] side-condition guarantees that the typed
      cell contents are all-[FVal] (no [FCell]), letting us read a
      concrete value. *)
  Lemma type_deref_instr {𝔄 𝔅 𝔄'} (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')
        gt st p E L I :
    StackOkay tyb →
    tyb.(ty_size) = 1%nat → typed_read E L ty tyb ty' gt st →
    typed_instr E L I +[p ◁ ty] (!p) (λ v, +[v ◁ tyb; p ◁ ty'])
      (λ post '-[a], λ mask, ∀ z, st a z → post -[gt a; z] mask).
  Proof.
    iIntros (StackOk Sz Rd tid post mask iκs [vπ []]) "#LFT #TIME #E HL $ [p _] %Obs".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (v d Hev) "#⧖ Hty".
    iApply pgl_wp_fupd.  (* wrap WP-post in [|={⊤}=>] before mask shrinks *)
    iApply (wp_persistent_time_receipt d with "TIME ⧖"); [done|solve_ndisj|].
    iIntros "H£ #⧖S".
    (* Split [£(advance_credits d)] into [£(d+1)] for Rd and [£(d+1)] for
       the wp_read_guarded later-credit budget.  Sufficient because
       [advance_credits d = 10d² + 10d + 10 ≥ 2(d+1)]. *)
    iDestruct (lc_weaken ((d+1) + (d+1)) with "H£") as "H£big".
    { rewrite /advance_credits. nia. }
    iDestruct (lc_split with "H£big") as "[H£Rd H£read]".
    iApply fupd_pgl_wp.
    iMod (llctx_interp_make_guarded L (⊤ ∖ ↑advN) with "HL")
      as (γ) "(Hh1 & Hh2 & #Hguard & #Hback)"; [solve_ndisj|].
    iMod (Rd vπ d (FVal v) tid (fractional.half γ) _
            with "LFT E Hguard Hh1 Hty H£Rd")
      as (l vl_concrete vl Q Heqv Heql) "(HQ & #QPt & _Retether & %Conc & Own & Toty')".
    inversion Heqv. subst v.
    have HConc := Conc StackOk. subst vl.
    iDestruct "Own" as "[Hgho >%Hphys]".
    (* length vl_concrete = ty_size tyb = 1 *)
    assert (length vl_concrete = 1%nat) as Sz1.
    { erewrite <- length_fmap. rewrite <- Hphys. by rewrite ty_size_eq. }
    destruct vl_concrete as [|v_read [|? ?]]; simpl in Sz1; try lia; [].
    destruct l as [l_loc l_trace]; simpl in *.
    iModIntro.
    (* Apply [wp_read_guarded_singleton] — case-splits l_trace internally
       and derives False for non-singleton traces. *)
    iApply (wp_read_guarded_singleton _ l_loc l_trace v_read Q (d+1)
              with "[$QPt $HQ $H£read]"); [solve_ndisj|].
    iIntros "!> HQ".
    iMod (fupd_mask_subseteq (⊤ ∖ ↑advN)) as "Hadv"; first solve_ndisj.
    iMod ("Toty'" with "HQ") as (z) "(%Hstz & Hh1 & Hty')".
    iMod "Hadv" as "_".
    iMod (fupd_mask_subseteq (↑NllftG)) as "Hcl"; first solve_ndisj.
    iMod ("Hback" with "Hh1 Hh2") as "L".
    iMod "Hcl" as "_".
    iModIntro. iExists -[gt vπ; z]. iFrame "L".
    iSplit; last by iPureIntro; apply Obs.
    simpl.
    iSplitL "Hgho".
    { (* v_read ◁ tyb *)
      rewrite /tctx_elt_interp /=.
      iExists v_read, d.
      iSplit; first by iPureIntro; apply eval_path_of_val.
      iFrame "⧖". rewrite /ty_own /=. iFrame "Hgho".
      iPureIntro. by rewrite -Hphys. }
    iSplitL "Hty'"; last done.
    rewrite /tctx_elt_interp /=.
    iExists (LitV (LitLoc l_loc)), d.
    iSplit; first done.
    iFrame "⧖". iFrame "Hty'".
  Qed.

  Lemma type_assign_instr {𝔄 𝔅 𝔄' 𝔅'} (ty: type 𝔄) (tyb: type 𝔅)
        (ty': type 𝔄') (tyb': type 𝔅') gt st p pb E L I :
    StackOkay tyb → StackOkay tyb' →
    tyb.(ty_size) = 1%nat →
    typed_write E L ty tyb ty' tyb' gt st →
    typed_instr E L I +[p ◁ ty; pb ◁ tyb'] (p <- pb) (λ _, +[p ◁ ty'])
      (λ post '-[a; b], λ mask, ∀ z, st a b z → post -[z] mask).
  Proof.
    iIntros (StackOkB StackOkB' Sz [Eq Wrt] tid post mask iκs [x [y []]]).
    iIntros "#LFT #TIME #E HL Hinv [p [pb _]] %Obs".
    iMod (llctx_interp_make_guarded L ⊤ with "HL")
      as (γ) "(Hh1 & Hh2 & #Hguard & #Hback)"; [solve_ndisj|].
    wp_bind p. iApply (wp_hasty with "p"). iIntros (v dp Hev_p) "#⧖dp Hty".
    iApply fupd_pgl_wp.
    iMod (Wrt x dp (FVal v) tid (fractional.half γ) _
            with "LFT E Hguard Hh1 Hty")
      as (l d' H Hveq Hd) "(↦bundle & HH & #HHguard & Hclose)".
    inversion Hveq. subst v.
    iDestruct "↦bundle" as "(%vl & >Hmap & Hown)".
    iDestruct "Hown" as "[Hgho_w >%Hphys_w]".
    destruct l as [l_loc l_trace]; simpl in *.
    (* length vl = 1 *)
    assert (length vl = 1%nat) as Sz1.
    { rewrite -Hphys_w ty_size_eq. exact Sz. }
    destruct vl as [|fv_w [|? ?]]; simpl in Sz1; try lia; [].
    pose proof (StackOkB (gt x) tid) as HOk.
    rewrite Hphys_w in HOk. simpl in HOk. destruct HOk as [HOk _].
    destruct fv_w as [v_w|c_w]; last by inversion HOk.
    iModIntro.
    wp_bind pb. iApply (wp_hasty with "pb"). iIntros (vb db Hev_b) "#⧖db Htyb'".
    iDestruct "Htyb'" as "[Hgho_b' Hphys_b']".
    iApply pgl_wp_fupd.
    (* Combine ⧖dp and ⧖db into ⧖(dp `max` db) so wp_persistent_time_receipt
       mints £(advance_credits (dp `max` db)) — enough for both [dp+1] and
       [db+1] obligations. *)
    iAssert (⧖(dp `max` db))%I as "#⧖max".
    { rewrite persistent_time_receipt_sep. iFrame "#". }
    iApply (wp_persistent_time_receipt (dp `max` db) with "TIME ⧖max");
      [done|solve_ndisj|].
    iIntros "H£ #⧖Smax".
    (* Split credits: [1] strip ▷ on Hphys_b', [3*(dp+1)+1] for wp_write,
       [2*db*db + 4*db + 2] for closer. *)
    iDestruct (lc_weaken (1 + ((3*(dp+1)+1) + (2*db*db + 4*db + 2))) with "H£")
      as "H£big".
    { rewrite /advance_credits. nia. }
    iDestruct (lc_split with "H£big") as "[H£one H£rest]".
    iDestruct (lc_split with "H£rest") as "[H£write H£closer]".
    iApply fupd_pgl_wp.
    iMod (lc_fupd_elim_later with "H£one Hphys_b'") as "%Hphys_b'".
    (* Bump [⧖Smax] down to [⧖(S db)] for Hclose's input. *)
    iAssert (⧖(S db))%I as "#⧖Sdb".
    { iApply (persistent_time_receipt_mono with "⧖Smax"). lia. }
    iModIntro.
    iApply (wp_write_guarded_singleton _ l_loc l_trace vb v_w
              H dp
              with "[$HHguard $HH Hmap $H£write]"); [solve_ndisj|..].
    { destruct l_trace as [|c0 [|c1 c2]]; rewrite /=.
      - rewrite /heap.heap_complete_mapsto_fancy_vec /=. by iDestruct "Hmap" as %[].
      - rewrite /heap.heap_complete_mapsto_fancy_vec /=.
        iDestruct "Hmap" as "[$ _]".
      - rewrite /heap.heap_complete_mapsto_fancy_vec /=.
        by iDestruct "Hmap" as "[_ []]". }
    iNext. iIntros "[Hmap' HH]".
    iMod ("Hclose" $! y db with "[Hmap' Hgho_b'] ⧖Sdb H£closer HH")
      as (z) "(Hh1 & %Hstz & Hty')".
    { iExists [heap.FVal vb]. iFrame "Hmap'".
      iNext. rewrite /ty_own /=. iSplit.
      { iDestruct (tyb'.(ty_gho_depth_mono) db db db (S db) y tid with "Hgho_b'")
          as "[$ _]"; [lia|lia]. }
      iPureIntro. rewrite Hphys_b'. reflexivity. }
    iMod (fupd_mask_subseteq (↑NllftG)) as "Hcl"; first solve_ndisj.
    iMod ("Hback" with "Hh1 Hh2") as "L".
    iMod "Hcl" as "_".
    iModIntro. iExists -[z]. iFrame "L Hinv".
    iSplit; last by (iPureIntro; apply Obs).
    simpl. iSplit; last done.
    rewrite /tctx_elt_interp /=.
    iExists (LitV (LitLoc l_loc)), (dp `max` S db).
    iSplit; first done.
    iCombine "⧖dp ⧖Sdb" as "#⧖final".
    iFrame "⧖final".
    iDestruct "Hty'" as "[Hgho_t' %Hphys_t']".
    iSplit; last done.
    iDestruct (ty'.(ty_gho_depth_mono) (S db) (dp `max` S db)
                 (dp `max` S db) (dp `max` S db) z tid with "Hgho_t'")
      as "[$ _]"; [lia|lia].
  Qed.

  (** [type_memcpy_instr]: typed memcpy via [typed_write] for the
      destination and [typed_read] for the source.  Mirrors upstream
      verisbelt's [type_memcpy_instr] verbatim minus prophecy strands. *)
  Lemma type_memcpy_instr {𝔄 𝔄' 𝔅 𝔅' ℭ ℭ'} (tyw: type 𝔄) (tyw': type 𝔄')
        (tyr: type 𝔅) (tyr': type 𝔅') (tyb: type ℭ) (tyb': type ℭ')
        gtw stw gtr str (n: Z) pw pr E L I :
    typed_write E L tyw tyb tyw' tyb' gtw stw →
    typed_read E L tyr tyb' tyr' gtr str → n = tyb'.(ty_size) →
    typed_instr E L I +[pw ◁ tyw; pr ◁ tyr] (pw <-{n} !pr)
      (λ _, +[pw ◁ tyw'; pr ◁ tyr'])
      (λ post '-[a; b], λ mask,
        ∀ zw zr, stw a (gtr b) zw → str b zr → post -[zw; zr] mask).
  Proof.
    iIntros ([Eq Wrt] Rd Hn tid post mask iκs [x [y []]]).
    iIntros "#LFT #TIME #E HL Hinv [pw [pr _]] %Obs".
    iMod (llctx_interp_make_guarded L ⊤ with "HL")
      as (γ) "(H1 & H2 & #Ghalf & #Halfback)"; [solve_ndisj|].
    iMod (fractional.frac_split_guard_in_half _ _ _ ⊤ with "H2 Ghalf")
      as (γ2) "(H2 & H3 & #Ghalf2 & #Halfback2)"; [solve_ndisj|].
    wp_bind pw. iApply (wp_hasty with "pw").
    iIntros (vw dw Hev_w) "#⧖dw tyw".
    iApply fupd_pgl_wp.
    iMod (Wrt x dw (FVal vw) tid (fractional.half γ) _
            with "LFT E Ghalf H1 tyw")
      as (l d' Hw Hveq Hd) "(↦bundle & Hw & #Hwpt & Totyw)".
    inversion Hveq. subst vw.
    iDestruct "↦bundle" as "(%vl & >↦ & Own)".
    iDestruct "Own" as "[tyb_gho >%tyb_phys]".
    iModIntro.
    wp_bind pr. iApply (wp_hasty with "pr").
    iIntros (vr dr Hev_r) "#⧖dr tyr".
    iApply pgl_wp_fupd.
    iAssert (⧖(dw `max` dr))%I as "#⧖max".
    { rewrite persistent_time_receipt_sep. iFrame "#". }
    iApply (wp_persistent_time_receipt (dw `max` dr) with "TIME ⧖max");
      [done|solve_ndisj|].
    iIntros "H£ #⧖Smax".
    set (d := S (dw `max` dr)).
    (* Split credits:
         £(dr+1)                : Rd's [£(d+1)] input
         £(6*d + 1)             : wp_memcpy_guarded (depth d, n-agnostic)
         £(dw+1)                : open Hw's guard later
         £(2*dr*dr+4*dr+2)      : Wrt's closer *)
    iDestruct (lc_weaken ((dr+1) + ((6*d + 1)
                                    + ((dw+1) + (2*dr*dr + 4*dr + 2))))
                with "H£") as "H£big".
    { subst d. rewrite /advance_credits. nia. }
    iDestruct (lc_split with "H£big") as "[£1 H£rest]".
    iDestruct (lc_split with "H£rest") as "[£6 H£rest2]".
    iDestruct (lc_split with "H£rest2") as "[£open £3]".
    iApply fupd_pgl_wp.
    iMod (Rd y dr (FVal vr) tid (fractional.half γ2) _
            with "LFT E Ghalf2 H2 tyr £1")
      as (l0 vlb_concrete vlb Hr Heqv2 Hleneq)
         "(Hr & #Hrpt' & Retether & _ & Own' & Totyr')".
    inversion Heqv2. subst vr.
    iDestruct "Own'" as "[tybP_gho >%HtypP_phys]".
    assert (length vl = ty_size tyb) as Sz.
    { rewrite -tyb_phys. apply ty_size_eq. }
    assert (length vlb_concrete = ty_size tyb') as Sz'.
    { rewrite Hleneq -HtypP_phys. apply ty_size_eq. }
    (* Untether dst fancy → concrete for wp_memcpy_guarded. *)
    iMod (mapsto_vec_untether _ _ _ ∅ with "↦")
      as (vl_concrete) "(↦ & %Hvlen & RetetherW)".
    iModIntro.
    (* Weaken both guards' later counts up to [d = S (dw `max` dr)]. *)
    iAssert (Hw &&{↑NllftG; d}&&> l #↦∗_)%I as "#Hwpt_w".
    { iApply (lguards_weaken_later with "Hwpt"). subst d. rewrite Hd. lia. }
    iAssert (Hr &&{↑NllftG; d}&&> l0.1 ↦[^ l0.2]∗ vlb_concrete)%I
      as "#Hrpt_w".
    { iApply (lguards_weaken_later with "Hrpt'"). subst d. lia. }
    iAssert (⧖d)%I as "#⧖d".
    { iApply (persistent_time_receipt_mono with "⧖Smax"). subst d. lia. }
    iApply (wp_memcpy_guarded _ l l0 vl_concrete vlb_concrete Hw Hr n d
              with "TIME [$↦ $Hwpt_w $Hrpt_w $Hw $Hr $⧖d $£6]").
    { solve_ndisj. }
    { rewrite Hvlen Sz Eq. lia. }
    { simpl. lia. }
    iNext. iIntros "(↦ & Hw & Hr)".
    (* Open Hw's guard to get the dst layout (l #↦∗_). *)
    rewrite Hd.
    iMod (guards_open_later _ _ ⊤ (↑NllftG) (S d' + 1) with "Hwpt Hw")
      as "Hop_w"; first solve_ndisj.
    iMod (lc_fupd_elim_laterN with "£open Hop_w") as ">[prefix back]".
    (* Apply Rd's polymorphic retether at dst's location with the
       post-memcpy content vlb_concrete: layout + concrete → layout + fancy_vlb. *)
    iMod (fupd_mask_subseteq ∅) as "Hmsk"; first solve_ndisj.
    iMod ("Retether" $! l.1 l.2 with "[$prefix $↦]") as "[prefix ↦_fancy]".
    iMod "Hmsk" as "_".
    rewrite -surjective_pairing.
    iMod ("back" with "prefix") as "Hw".
    (* We now have ↦_fancy : l #↦!∗ vlb (the new fancy at dst) and Hw. *)
    iAssert (⧖(S dr))%I as "#⧖Sdr".
    { iApply (persistent_time_receipt_mono with "⧖Smax"). lia. }
    iMod (fupd_mask_subseteq ⊤) as "Htop"; first set_solver.
    iMod ("Totyw" $! (gtr y) dr with "[↦_fancy tybP_gho] ⧖Sdr £3 Hw")
      as (z) "(H1 & %Hstw & ty')".
    { iExists vlb. iFrame "↦_fancy".
      iNext. rewrite /ty_own /=. iSplit.
      { iDestruct (tyb'.(ty_gho_depth_mono) dr dr dr (S dr) (gtr y) tid
                    with "tybP_gho") as "[$ _]"; [lia|lia]. }
      iPureIntro. exact HtypP_phys. }
    iMod "Htop" as "_".
    (* Apply Rd's closer. *)
    iMod (fupd_mask_subseteq (⊤ ∖ ↑advN)) as "Hadv"; first solve_ndisj.
    iDestruct ("Totyr'" with "Hr") as "Totyr'".
    iMod "Totyr'" as (zr) "(%Hstr & H3back & tyr')".
    iMod "Hadv" as "_".
    (* Recompose llctx via the two halfbacks. *)
    iMod (fupd_mask_subseteq (↑NllftG)) as "Hcl"; first solve_ndisj.
    iMod ("Halfback2" with "H3 H3back") as "H2_γ".
    iMod ("Halfback" with "H1 H2_γ") as "L".
    iMod "Hcl" as "_".
    iModIntro. iExists -[z; zr]. iFrame "L Hinv".
    iSplit; last by (iPureIntro; apply Obs).
    simpl.
    set (finalw := S (d' `max` dr)).
    iAssert (⧖finalw)%I as "#⧖finalw".
    { iApply (persistent_time_receipt_mono with "⧖Smax"). subst finalw. lia. }
    iSplitL "ty'".
    { (* pw ◁ tyw' at depth finalw = S (d' `max` dr) *)
      rewrite /tctx_elt_interp /=.
      iExists (LitV (LitLoc l.1)), finalw.
      iSplit; first done.
      iFrame "⧖finalw".
      iDestruct "ty'" as "[gho %phys]".
      iSplit; last done.
      iDestruct (tyw'.(ty_gho_depth_mono) (S dr) finalw finalw finalw z tid
                  with "gho") as "[$ _]"; subst finalw; [lia|lia]. }
    iSplit; last done.
    (* pr ◁ tyr' — bump depth to [finalw] matching upstream. *)
    rewrite /tctx_elt_interp /=.
    iExists (LitV (LitLoc l0.1)), finalw.
    iSplit; first done.
    iFrame "⧖finalw".
    iDestruct "tyr'" as "[gho %phys]".
    iSplit; last done.
    iDestruct (tyr'.(ty_gho_depth_mono) dr dr finalw finalw zr tid
                with "gho") as "[$ _]"; subst finalw; [lia|lia].
  Qed.

  Lemma type_assign {𝔄 𝔅 𝔄' 𝔅' 𝔄l 𝔅l ℭ} (ty: type 𝔄) (tyb: type 𝔅)
        (ty': type 𝔄') (tyb': type 𝔅') gt st p pb E L
        (I: invctx) (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) trx tr e :
    Closed [] e →
    tctx_extract_ctx E L +[p ◁ ty; pb ◁ tyb'] T T' trx →
    StackOkay tyb → StackOkay tyb' →
    tyb.(ty_size) = 1%nat →
    typed_write E L ty tyb ty' tyb' gt st →
    typed_body E L I C (p ◁ ty' +:: T') e tr -∗
    typed_body E L I C T (p <- pb;; e)
      (trx ∘ (λ post '(a -:: b -:: bl) mask, ∀ z, st a b z → tr post (z -:: bl) mask))%type.
  Proof.
    iIntros (Hcle Extr SOk SOk' Sz Wrt) "?".
    iApply type_seq;
      [eapply type_assign_instr; [exact SOk|exact SOk'|exact Sz|exact Wrt]
      |done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_deref {𝔄 𝔅 𝔄' 𝔄l 𝔅l ℭ} (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')
        gt st (T: tctx 𝔄l) (T': tctx 𝔅l) p x e trx tr E L
        (I: invctx) (C: cctx ℭ) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    StackOkay tyb →
    typed_read E L ty tyb ty' gt st → tyb.(ty_size) = 1%nat →
    (∀v: val, typed_body E L I C (v ◁ tyb +:: p ◁ ty' +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e)
      (trx ∘ (λ post '(a -:: al) mask, ∀ z, st a z → tr post (gt a -:: z -:: al) mask))%type.
  Proof.
    iIntros (? Extr SOk Rd Sz) "?". iApply type_let; [by eapply type_deref_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.

  (** [type_memcpy] convenience wrapper — pending [type_memcpy_instr] port. *)
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
