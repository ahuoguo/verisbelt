(** Prophecy-API stubs.

    The original verusbelt typing layer was built on a real prophecy
    construction (see [prophecy/prophecy.v] in the upstream Rocq sources).
    Eris is unsound under prophecies (Clutch POPL'24), so we hold back
    the real prophecy infrastructure and instead provide trivial stubs
    matching its API.  The stubs are sound (every operation reduces to
    [True]) but carry *no* prophecy reasoning — code that relies on real
    prophecy guarantees will fail to verify, but the typing-rule
    *signatures* still type-check, which is enough to bring [type.v] /
    [type_context.v] / [programs.v] online. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From lrust.lang Require Export proofmode notation.
From lrust.typing Require Export syn_type.
Set Default Proof Using "Type".

(** ** Namespaces *)

Definition prophN : namespace := nroot .@ "proph_stub".
Definition uniqN  : namespace := nroot .@ "uniq_stub".

(** ** Trivial contexts *)

Section stubs.
  Context `{!invGS Σ}.

  Definition proph_ctx : iProp Σ := True.
  Definition uniq_ctx  : iProp Σ := True.

  Lemma proph_ctx_intro : ⊢ proph_ctx.
  Proof. done. Qed.
  Lemma uniq_ctx_intro  : ⊢ uniq_ctx.
  Proof. done. Qed.

  Global Instance proph_ctx_persistent : Persistent proph_ctx.
  Proof. apply _. Qed.
  Global Instance uniq_ctx_persistent  : Persistent uniq_ctx.
  Proof. apply _. Qed.

End stubs.

(** ** Prophecy observations [⟨π, P⟩]

    In real eris-free verusbelt, [⟨π, P⟩] asserts that a single
    prophecy assignment witnessing [P] exists.  Here it is just
    [⌜∃ π, P π⌝]. *)

Section proph_obs_stub.
  Context `{!invGS Σ}.

  Definition proph_obs (P : proph_asn → Prop) : iProp Σ :=
    ⌜∃ π : proph_asn, P π⌝%I.

  Global Instance proph_obs_persistent P : Persistent (proph_obs P).
  Proof. apply _. Qed.

  Lemma proph_obs_true (P : proph_asn → Prop) :
    (∀ π, P π) → ⊢ proph_obs P.
  Proof.
    intros HP. iPureIntro. exists inhabitant. apply HP.
  Qed.

  Lemma proph_obs_impl P Q :
    (∀ π, P π → Q π) → proph_obs P ⊢ proph_obs Q.
  Proof.
    iIntros (Imp) "[%π %HP]". iPureIntro. exists π. by apply Imp.
  Qed.

  Lemma proph_obs_eq P Q :
    (∀ π, P π ↔ Q π) → proph_obs P ⊣⊢ proph_obs Q.
  Proof.
    intros Eq. iSplit; iApply proph_obs_impl; intros π; apply Eq.
  Qed.

  Lemma proph_obs_sat E P :
    ↑prophN ⊆ E →
    proph_ctx -∗ proph_obs P ={E}=∗ ⌜∃ π, P π⌝.
  Proof.
    iIntros (?) "_ [%π %HP]". iModIntro. iPureIntro. by exists π.
  Qed.

End proph_obs_stub.

(** Re-export the [⟨π, P⟩] notation (in [bi_scope]).  The [%type%stdpp]
    annotations force the body to parse in [type_scope] / [stdpp_scope]
    rather than [bi_scope], matching the original prophecy.v. *)
Notation "⟨ π , P ⟩" := (proph_obs (λ π, P%type%stdpp))
  (at level 1, format "⟨ π ,  P ⟩") : bi_scope.

(** ** Prophecy tokens [q :[ ξ ]] *)

Section proph_tok_stub.
  Context `{!invGS Σ}.

  Definition proph_tok (ξ : proph_var) (q : Qp) : iProp Σ := True.

End proph_tok_stub.

Notation "q :[ ξ ]" := (proph_tok ξ q)
  (at level 30, format "q  :[  ξ  ]") : bi_scope.
Notation "q :+[ ξl ]" := ([∗ list] ξ ∈ ξl, proph_tok ξ q)%I
  (at level 30, format "q  :+[  ξl  ]") : bi_scope.

(** ** Prophecy dependence [vπ ./ ξl] (stubbed to [True]) *)

Definition proph_dep {A} (vπ : proph_asn → A) (ξl : list proph_var) : Prop := True.
Notation "vπ ./ ξl" := (proph_dep vπ ξl) (at level 70).

(** ** Prophecy equality [uπ :== vπ] (stubbed to [True]) *)

Definition proph_eqz `{!invGS Σ} {A} (uπ vπ : proph_asn → A) : iProp Σ := True.
Notation "uπ :== vπ" := (proph_eqz uπ vπ) (at level 70) : bi_scope.
