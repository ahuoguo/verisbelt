From clutch.eris Require Import lifting.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Class IntoVecVal {n} (el: list expr) (vl: vec val n) :=
  into_vec_val: el = map of_val vl.

Global Instance into_vec_val_nil: IntoVecVal [] [#].
Proof. done. Qed.

Global Instance into_vec_val_cons {n} e v el (vl: _ n) :
  IntoVal e v → IntoVecVal el vl → IntoVecVal (e :: el) (v ::: vl).
Proof. by move=>/= <-->. Qed.

Section typing.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Lemma type_jump {𝔄l 𝔅l ℭl 𝔇 n} (T': vec val n → tctx 𝔅l) k el
      (vl: vec val n) tr trx tr_res E L (T: tctx 𝔄l) (Tx: tctx ℭl) (I: invctx) (C: cctx 𝔇) :
    IntoVecVal el vl → k ◁cont{L, I, T'} tr ∈ C →
    tctx_extract_ctx E L (T' vl) T Tx trx →
    tr_res ≡ trx ∘ (λ post bcl mask, let '(bl, cl) := psep bcl in tr post bl mask) →
    ⊢ typed_body E L I C T (jump: k el) tr_res.
  Proof.
    move=> -> Hin TT' Htr_res.
    iApply typed_body_impl.
    { move => ??? Hpre.
      rewrite /equiv in Htr_res.
      apply Htr_res in Hpre.
      exact Hpre. }
    iApply typed_body_tctx_incl; [done|].
    iIntros (tid bcl mask post iκs).
    move: (papp_ex bcl)=> [bl[cl ->]].
    iIntros "#LFT #TIME #E L Hinv C Htctx %Obs".
    iEval (rewrite big_sepHL_1_app) in "Htctx".
    iDestruct "Htctx" as "[T' _Tx]".
    rewrite /= papp_sepl in Obs.
    wp_bind Skip. wp_seq. wp_seq.
    iApply ("C" $! (k ◁cont{L, I, T'} tr) with "[%] L Hinv T' [%]"); [done|exact Obs].
  Qed.

  Lemma type_cont {𝔄l 𝔅l ℭ} bl (T': vec val (length bl) → tctx 𝔅l) trk L' (I': invctx)
        (T: tctx 𝔄l) kb ec e tr E L (I: invctx) (C: cctx ℭ) :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k: val, typed_body E L I (k ◁cont{L', I', T'} trk :: C) T (subst' kb k e) tr) -∗
    □(∀(k: val) (vl: vec val (length bl)), typed_body E L' I'
      (k ◁cont{L', I', T'} trk :: C) (T' vl) (subst' kb k $ subst_v bl vl ec) trk) -∗
    typed_body E L I C T (letcont: kb bl := ec in e) tr.
  Proof.
    iIntros (??) "e #ec %%%%% #LFT #TIME #E L Hinv C T %Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT TIME E L Hinv [C] T [%//]").
    iLöb as "IH". iIntros (c). rewrite elem_of_cons.
    iIntros ([->|?]); [|by iApply "C"]. iIntros (???) "L' Hinv' T' %Obs'".
    cbn match. wp_rec.
    iApply ("ec" with "LFT TIME E L' Hinv' [C] T' [%//]"). by iApply "IH".
  Qed.

  Lemma type_cont_norec {𝔄l 𝔅l ℭ} bl (T': vec val (length bl) → tctx 𝔅l) trk
        L' I' (T: tctx 𝔄l) kb ec e tr E L I (C: cctx ℭ) :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k: val, typed_body E L I (k ◁cont{L', I', T'} trk :: C) T (subst' kb k e) tr) -∗
    (∀(k: val) (vl: vec val (length bl)),
      typed_body E L' I' C (T' vl) (subst' kb k $ subst_v bl vl ec) trk) -∗
    typed_body E L I C T (letcont: kb bl := ec in e) tr.
  Proof.
    iIntros (??) "e ec %%%%% #LFT #TIME #E L Hinv C T %Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT TIME E L Hinv [ec C] T [%//]").
    iIntros (c). rewrite elem_of_cons. iIntros ([->|?]); [|by iApply "C"].
    iIntros (???) "L' Hinv' T' %Obs'".
    cbn match. wp_rec.
    iApply ("ec" with "LFT TIME E L' Hinv' C T' [%//]").
  Qed.
End typing.
