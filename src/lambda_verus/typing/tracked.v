From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Set Default Proof Using "Type".

Section tracked.
  Context `{!typeG Σ}.

  (** [Tracked<T>] is [T] with the physical contents cleared out — a
      ghost-only wrapper that preserves [ty_gho]/[ty_gho_pers] and
      forces [ty_size := 0] / [ty_phys := []]. *)

  Program Definition tracked_ty {𝔄} (ty: type 𝔄) : type (trackedₛ 𝔄) := {|
    ty_size := 0;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho x d g tid := (ty.(ty_gho) x d g tid) ;
    ty_gho_pers x d g tid := (ty.(ty_gho_pers) x d g tid) ;
    ty_phys x tid := [];
  |}%I.
  Next Obligation. intros; done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros. apply (ty_gho_depth_mono ty); trivial. Qed.
  Next Obligation. intros. apply (ty_gho_pers_depth_mono ty); trivial. Qed.
  Next Obligation. intros. apply (ty_gho_pers_impl); trivial. Qed.

  Global Instance tracked_ne {𝔄} : NonExpansive (@tracked_ty 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance tracked_send {𝔄} (ty : type 𝔄) : Send ty → Send (tracked_ty ty).
  Proof. intros [Hphys]. split; trivial. Qed.

  Global Instance tracked_sync {𝔄} (ty : type 𝔄) : Sync ty → Sync (tracked_ty ty).
  Proof. intros Hsync. split; trivial.
    destruct (Hsync tid tid' x d g) as [A [B C]]. split; trivial.
  Qed.

  Global Instance tracked_copy {𝔄} (ty : type 𝔄) : Copy ty → Copy (tracked_ty ty).
  Proof.
    intros Hcopy. destruct Hcopy. split; trivial. intros. iIntros "_". iPureIntro. done.
  Qed.

  (* subtyping *)

  Lemma tracked_type_incl {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) f :
    type_incl ty ty' f ⊢ type_incl (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f).
  Proof.
    iIntros "(A & B & C & D & E)". iFrame. iSplit; done.
  Qed.

  Lemma tracked_subtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f :
      subtype E L ty ty' f → subtype E L (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f).
  Proof.
    intros Hsub. iIntros "A". iDestruct (Hsub with "A") as "#B". iModIntro.
    iIntros "E". iApply tracked_type_incl. iApply "B". iFrame.
  Qed.

  Lemma tracked_eqtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f g :
      eqtype E L ty ty' f g → eqtype E L (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f) (tracked_mapₛ g).
  Proof.
    intros [Ha Hb]. split; apply tracked_subtype; trivial.
  Qed.

End tracked.
