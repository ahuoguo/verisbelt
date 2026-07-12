From iris.proofmode Require Import proofmode reduction environments coq_tactics.
From iris.proofmode Require Export proofmode.
From clutch.eris Require Export weakestpre.
From clutch.eris Require Import lifting.
From lrust.lang Require Export tactics lifting.
From lrust.lang Require Import heap.
From lrust.util Require Import non_atomic_cell_map.
Set Default Proof Using "Type".
Import uPred.

(** Minimal proofmode wiring against eris's [pgl_wp]. The pure-step
    fragment (value, bind, pure rule + [wp_rec/lam/let/seq/if/case])
    is ported here; the heap-touching tactics ([wp_alloc],
    [wp_read], [wp_write], [wp_free], [wp_eq_loc], [wp_nd_int]) and
    the corresponding [tac_wp_*] lemmas are deferred — they need
    notation for [↦] and the heap-side WP rules to be re-derived
    against [pgl_wp]. *)
Lemma tac_wp_value `{!lrustGS Σ} Δ E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ? ->. by apply pgl_wp_value. Qed.

Ltac wp_value_head := eapply tac_wp_value; [tc_solve|reduction.pm_prettify].

Lemma tac_wp_pure `{!lrustGS Σ} K Δ Δ' E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP fill K e2 @ E {{ Φ }}) →
  envs_entails Δ (WP fill K e1 @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> HPE Hφ ? HΔ'. rewrite into_laterN_env_sound HΔ'.
  apply: wp_pure_step_later; [|exact Hφ]. by apply (pure_exec_ctx (fill K)).
Qed.

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc;
    eapply (tac_wp_pure K);
    [simpl; tc_solve                (* PureExec *)
    |try done                       (* The pure condition for PureExec *)
    |tc_solve                       (* IntoLaters *)
    |simpl_subst; try wp_value_head (* new goal *)])
   || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_rec" := wp_pure (App _ _).
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_let.
Tactic Notation "wp_op" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_case" := wp_pure (Case _ _); try wp_value_head.

Lemma tac_wp_bind `{!lrustGS Σ} K Δ E Φ e :
  envs_entails Δ (WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. apply: pgl_wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => apply (tac_wp_bind K); simpl
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core K
    end) || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** * Heap-side proofmode: ports of [tac_wp_alloc/free/read/write] and
    their [wp_*] surface tactics, retargeted at our eris-side WP rules
    in [lifting.v]. *)
Section heap.
Context `{!lrustGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).

Lemma tac_wp_alloc K Δ Δ' E j1 j2 n Φ :
  (0 < n)%Z →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l (sz : nat), n = sz → ∃ Δ'',
    envs_app false (Esnoc (Esnoc Enil j1
                            (l ↦∗ repeat (LitV LitPoison) sz))
                          j2 (†l…sz)) Δ'
      = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Lit $ LitLoc l) @ E {{ Φ }})) →
  envs_entails Δ (WP fill K (Alloc (Lit $ LitInt n)) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΔ. rewrite -pgl_wp_bind into_laterN_env_sound /=.
  iIntros "Δ". iApply wp_alloc=>//. iNext. iIntros (l sz) "[%eq [† ↦]]".
  move: (HΔ l sz eq)=> [?[/envs_app_sound-> ->]]/=. iApply "Δ". iFrame.
Qed.

Lemma tac_wp_free K Δ Δ' Δ'' Δ''' E i1 i2 vl (n : Z) (n' : nat) l Φ :
  ↑non_atomic_cell_map.naN ⊆ E → n = length vl →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i1 Δ' = Some (false, l ↦∗ vl)%I →
  envs_delete false i1 false Δ' = Δ'' →
  envs_lookup i2 Δ'' = Some (false, †l…n')%I →
  envs_delete false i2 false Δ'' = Δ''' →
  n' = length vl →
  envs_entails Δ''' (WP fill K (Lit LitPoison) @ E {{ Φ }}) →
  envs_entails Δ (WP fill K (Free (Lit $ LitInt n) (Lit $ LitLoc l)) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal; intros ? -> ?? <- ? <- -> HΔ. rewrite -pgl_wp_bind.
  rewrite into_laterN_env_sound /=. do 2 (rewrite envs_lookup_sound //=).
  rewrite HΔ. iIntros "(↦ & † & wp)". iApply (wp_free with "[$↦ $† //]")=>//.
  iNext. by iIntros.
Qed.

Lemma tac_wp_read K Δ Δ' E i l v Φ :
  ↑naN ⊆ E →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_entails Δ' (WP fill K (of_val v) @ E {{ Φ }}) →
  envs_entails Δ (WP fill K (Read (Lit $ LitLoc l)) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal. intros Hmask ?? HΔ. rewrite -pgl_wp_bind.
  rewrite into_laterN_env_sound envs_lookup_split //= HΔ. iIntros "[↦ →wp]".
  by iApply (wp_read with "↦").
Qed.

Lemma tac_wp_write K Δ Δ' Δ'' E i l v e v' Φ :
  IntoVal e v' → ↑non_atomic_cell_map.naN ⊆ E →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, (l ↦ v)%I) →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Lit LitPoison) @ E {{ Φ }}) →
  envs_entails Δ (WP fill K (Write (Lit $ LitLoc l) e) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal; intros <- ?? Hi Hsimpl HΦ. rewrite -pgl_wp_bind.
  rewrite into_laterN_env_sound /=.
  rewrite envs_simple_replace_singleton_sound //=.
  iIntros "[↦ →env]". iApply (wp_write with "↦")=>//.
  iNext. iIntros "↦". iApply HΦ. by iApply "→env".
Qed.

End heap.

(** Surface tactics for the heap-side rules. *)
Tactic Notation "wp_alloc" ident(l) "as" constr(H) constr(Hf) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | Alloc _ => eapply (tac_wp_alloc K _ _ _ H Hf)
    end);
    [try fast_done                    (* 0 < n *)
    |tc_solve                          (* IntoLaters *)
    |let sz := fresh "sz" in
     let Hsz := fresh "Hsz" in
     intros l sz Hsz; eexists; split;
       [reduction.pm_reflexivity || fail "wp_alloc: name" l "not fresh"
       |simpl; try wp_value_head]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_free" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | Free _ _ => eapply (tac_wp_free K)
    end);
    [try fast_done                    (* mask *)
    |try fast_done                    (* n = length vl *)
    |tc_solve                          (* IntoLaters *)
    |let l := match goal with |- _ = Some (_, (?l ↦∗ _)%I) => l end in
     iAssumptionCore || fail "wp_free: cannot find" l "↦∗ ?"
    |reduction.pm_reflexivity
    |let l := match goal with |- _ = Some (_, (†?l…_)%I) => l end in
     iAssumptionCore || fail "wp_free: cannot find †" l "… ?"
    |reduction.pm_reflexivity
    |try fast_done                    (* n' = length vl *)
    |simpl; try wp_value_head]
  | _ => fail "wp_free: not a 'wp'"
  end.

Tactic Notation "wp_read" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | Read _ => eapply (tac_wp_read K)
    end);
    [try fast_done                    (* mask *)
    |tc_solve                          (* IntoLaters *)
    |let l := match goal with |- _ = Some (_, (?l ↦ _)%I) => l end in
     iAssumptionCore || fail "wp_read: cannot find" l "↦ ?"
    |simpl; try wp_value_head]
  | _ => fail "wp_read: not a 'wp'"
  end.

Tactic Notation "wp_write" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | Write _ _ => eapply (tac_wp_write K)
    end);
    [tc_solve                          (* IntoVal *)
    |try fast_done                    (* mask *)
    |tc_solve                          (* IntoLaters *)
    |let l := match goal with |- _ = Some (_, (?l ↦ _)%I) => l end in
     iAssumptionCore || fail "wp_write: cannot find" l "↦ ?"
    |reduction.pm_reflexivity
    |simpl; try first [wp_pure (Seq (Lit LitPoison) _)|wp_value_head]]
  | _ => fail "wp_write: not a 'wp'"
  end.
