From lrust.lang.lib Require Import memcpy.
From lrust.lang Require Import heap.
From lrust.typing Require Export type own product sum shr_bor uniq_bor uniq_util int bool.
From lrust.typing Require Import uninit type_context programs freeable_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.

Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section pcell.
  Context `{!typeG Σ}.

  Program Definition pcell_ty n : type (pcellₛ n) :=
    {| ty_size := n;
      ty_gho x _ _ _ := ⌜ length x = n ⌝;
      ty_gho_pers  x _ _ _ := ⌜ length x = n ⌝;
      ty_phys (cell_ids: ~~ (pcellₛ n)) _ := pad (FCell <$> cell_ids) n ;
      ty_lfts := [];
      ty_E := [];
     |}%I.
  Next Obligation. move => n v tid. by rewrite length_pad. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move => *. iIntros "?". auto. Qed.
  Next Obligation. move => *. iIntros "?". auto. Qed.
  Next Obligation.
      intros n κ x n0 d g tid ξ R Hin. simpl in Hin. set_solver.
  Qed.
  Next Obligation. move => *. by iIntros "?". Qed.
  
  Global Instance pcell_send n: Send (pcell_ty n).
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. simpl in H.
       rewrite H. trivial.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance pcell_sync n: Sync (pcell_ty n).
  Proof. split; trivial. split; iSplit; done. Qed.
End pcell.

Section points_to.
  Context `{!typeG Σ}.

  Program Definition cell_points_to_ty {𝔄} (ty: type 𝔄) : type (trackedₛ (pcellₛ (ty.(ty_size)) * 𝔄)) := 
    {| ty_size := 0%nat;
      ty_lfts := ty.(ty_lfts);
      ty_E := ty.(ty_E);
      ty_gho x d g tid := 
        [S(d') := d] (cells_points_to_fancy_value_vec x.1 (ty.(ty_phys) x.2 tid))%I ∗ ▷ (ty.(ty_gho) x.2 d' g tid) ;
      ty_gho_pers x d g tid := 
        [S(d') := d] ⌜ length x.1 = ty_size ty ⌝ ∗ ▷ (ty.(ty_gho_pers) (snd x) d' g tid) ;
      ty_phys _ _ := [];
    |}%I.
  Next Obligation. move => 𝔄 tyA v tid //=. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' v tid ??//=.
    iIntros "H".
    destruct d => //=.
    destruct d' => //=; first lia.
    iDestruct "H" as "[H↦ Hgho]".
    iFrame "H↦".
    iDestruct (ty.(ty_gho_depth_mono) with "Hgho") as "[$ Hwand]" => //; first lia.
    iIntros "[$ Hgho] !>".
    by iApply "Hwand".
  Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' v tid ??//=.
    iIntros "H".
    destruct d => //=.
    destruct d' => //=; first lia.
    iDestruct "H" as "[$ H]".
    iNext.
    iDestruct (ty.(ty_gho_pers_depth_mono) _ _ d' g' with "H") as "?" => //; lia.
  Qed.
  Next Obligation.
    intros 𝔄 ty κ x n0 d g tid ξ R Hin.
    iIntros "#CTX #Incl #GhoPers'".
    destruct d as [|d']; first by done.
    iDestruct "GhoPers'" as "[% GhoPers]".
    simpl in Hin.
    iDestruct (ty_guard_proph _ ty _ _ (n0+1) _ _ _ ξ R Hin with "CTX Incl GhoPers") as "#L".
    iApply (bi.laterN_le (S (d' * (g + 1)))). { lia. }
    iNext. iNext. iIntros "#A #B".
    leaf_goal laters to (n0 + 1 + d' * (g + 1)). { lia. }
    iApply "L".
      - leaf_goal laters to n0. { lia. } iFrame "A".
      - iApply (guards_transitive_additive with "B []"). leaf_by_sep.
        simpl. iIntros "[C D]". iNext. iFrame. iIntros. iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 ty x d g tid. iIntros "A". destruct d as [|d']; first by done.
    iDestruct "A" as "[A1 A2]".
    iDestruct (cells_points_to_fancy_vec_length_eq with "A1") as "%".
    rewrite (ty_size_eq ty) in H.
    iSplit => //.
    iApply ty_gho_pers_impl. iFrame.
  Qed.

  Global Instance cell_points_to_send {𝔄} (ty: type 𝔄) :
      Send ty → Send (cell_points_to_ty ty).
  Proof.
    intros [Hphys Hgho]. split; trivial.
    intros tid tid' x d g G H κs d0 Hineq TG TH.
    iIntros "LFT UNIQ TIME Hg H Gg G Hgho #⧖o".
    destruct d => //=.
    iDestruct "Hgho" as "(Hown&Hgho)".
    iModIntro. iNext. iModIntro.
    iPoseProof (Hgho with "LFT UNIQ TIME Hg H Gg G Hgho ⧖o") as "X"; first lia.
    iApply (step_fupdN_wand with "X"). iIntros ">X".
    iDestruct "X" as (x' off) "[gho [#⧖off [%Habs [G H]]]]".
    rewrite (Hphys tid tid' (x.2) x'); last by done.
    iExists (x.1, x'), (off). iModIntro. iFrame. iFrame "#". iPureIntro. simpl.
    rewrite Habs. trivial.
  Qed.
  
  Global Instance cell_points_to_sync {𝔄} (ty: type 𝔄) :
      Sync ty → Sync (cell_points_to_ty ty).
  Proof.
      move=> HSync tid tid' x d g. split => //=. split.
      + iSplit.
         - iIntros "Hgho".
           destruct d => //=.
           iDestruct "Hgho" as "(Hown&Hgho)".
           pose proof (sync_change_tid tid tid' (snd x) d g) as [-> [Hgho Hghopers]].
           iFrame "%".
           iFrame.
           iApply (Hgho with "Hgho").
         - iIntros "Hgho".
           destruct d => //=.
           iDestruct "Hgho" as "(Hown&Hgho)".
           pose proof (sync_change_tid tid tid' (snd x) d g) as [-> [Hgho Hghopers]].
           iFrame "%".
           iFrame.
           iApply (Hgho with "Hgho").
       + destruct d => //=.
         pose proof (sync_change_tid tid tid' (snd x) d g) as [_ [Hgho Hghopers]].
         rewrite Hghopers. trivial.
  Qed.

End points_to.

Section typing.

  Context `{!typeG Σ}.

  Definition PCellFromOwn : val :=
    (λ: ["p"], "p")%V.

  Lemma typed_pcell_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PCellFromOwn [p]) (λ v, +[v ◁ own_ptr (ty_size ty) (prod_ty (pcell_ty (ty_size ty)) (cell_points_to_ty ty))]) (λ post '-[(l, x)], λ mask π, ∀ (cell_ids : list positive), post -[(l, (cell_ids, (cell_ids, x)))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[l x][]].
    iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "(#Hd & Hown & %Hphys)".
    simpl in Hphys.
    inversion Hphys; subst pl.
    destruct d => //=.
    iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    iApply wp_fupd.
    wp_bind p.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "£ #Hd'".
    wp_rec.
    iMod (cell_alloc2 with "Hl") as "[%γs [% H↦]]".
    set cl := ((l, (λ γ, [γ]) <$> γs) : cloc).
    change l with cl.1. change (app [] <$> γs) with cl.2.
    rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
    iDestruct "H↦" as "[Hchain Htail]".
    rewrite heap_complete_mapsto_vec_eq.
    rewrite (ty.(ty_size_eq)) in H.
    iExists -[(l, (γs, (γs, x)))].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iModIntro.
      iSplitL => //.
      iExists _, _.
      iFrame "Hd'".
      do 2 iSplit => //=.
      rewrite Nat.add_0_r app_nil_r pad_length'.
      2: by rewrite length_fmap -H.
      iFrame.
      iNext.
      iSplit => //.
      unfold cl.
      rewrite heap_complete_mapsto_fancy_val_vec_eq'.
      iFrame.
      iNext.
      iDestruct (ty.(ty_gho_depth_mono) with "Hgho") as "($ & ?)"; lia.
    - iApply (proph_obs_impl with "Obs").
      intros π Hpost.
      apply Hpost.
  Qed.

  Definition PCell2Own : val :=
    (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma typed_pcell_to_own {𝔄} (perm pcell : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[pcell ◁ own_ptr (ty_size ty) (pcell_ty (ty_size ty)); perm ◁ own_ptr 0 (cell_points_to_ty ty)] (PCell2Own [pcell; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty]) (λ post '-[(l, γs); (_, (γs', x))], λ mask π, γs = γs' ∧ post -[(l, x)] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[l γs] [[l' [γs' x]] []]].
    iDestruct "TY" as "(Hpcell & Hperm & _)".
    iDestruct "Hpcell" as (pl d Heval) "(#Hd & Hown & %Hphys)".
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hown' & %Hphys')".
    simpl in Hphys, Hphys'.
    inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    destruct d => //.
    destruct d' => //=.
    iDestruct "Hown" as "(H↦ & Hfree & >%Hlen)".
    iDestruct "Hown'" as "(_ & _ & Hown)".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    rewrite /PCell2Own.
    wp_bind pcell.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "£ #Hd''".
    wp_rec.
    iDestruct "£" as "[£1 [£2 £3]]".
    destruct d' => /=.
    { by iMod (lc_fupd_elim_later with "£2 Hown"). }
    iClear "£1 £2 £3".
    rewrite pad_length'.
    2: by rewrite length_fmap.
    iDestruct "Hown" as "[H↦' Hgho]".
    rewrite -heap_complete_mapsto_fancy_val_vec_eq'.
    iExists -[(l, x)].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iMod (heap_delete_cell with "H↦ H↦'") as "H↦".
      iModIntro.
      iSplit => //.
      iExists _, (S (S d')).
      do 2 iSplit => //=.
      iSplitL => //.
      iFrame.
      iDestruct (ty.(ty_gho_depth_mono) with "Hgho") as "($ & ?)"; lia.
    - iApply (proph_obs_impl with "Obs").
      intros π' Hpost.
      apply Hpost.
  Qed.

  Definition PCellBorrow : val :=
    (λ: ["pcell_ref"; "perm_ref"], "pcell_ref")%V.

  Lemma typed_pcell_borrow {𝔄} κ (pcell_ref perm_ref : path) (ty : type 𝔄) E L I :
    (* lctx_lft_alive E L κ → *)
    typed_instr E L I +[pcell_ref ◁ shr_bor κ (pcell_ty (ty_size ty)); perm_ref ◁ shr_bor κ (cell_points_to_ty ty)] (PCellBorrow [pcell_ref; perm_ref]) (λ v, +[v ◁ shr_bor κ ty]) (λ post '-[(l, γs); (_, (γs', x))], λ mask π, γs = γs' ∧ post -[(cloc_flat_insert l γs, x)] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    destruct vπl as [[l γs] [[l' [γs' x]] []]].
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d Heval) "(#Hd & #Hshr & %Hphys)".
    simpl in Hphys.
    inversion Hphys; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hshr' & %Hphys')".
    simpl in Hphys'.
    inversion Hphys'; subst pl'.
    (* destruct d' => //=. *)
    rewrite /PCellBorrow.
    wp_bind pcell_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    destruct (decide (d ≤ d')) as [Hd | Hd'].
    - iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
      destruct d => //.
      iSimpl in "Hshr".
      destruct d' as [ | [ | d']] => //=.
      { iDestruct "Hshr'" as "(_ & _ & Hfalse)".
        rewrite /advance_credits /=.
        iIntros "(£ & _) #Hd''".
        wp_rec.
        by iMod (lc_fupd_elim_later with "£ Hfalse"). }
      iIntros "H£ #Hd''".
      wp_rec.
      iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
      iDestruct "Hshr'" as "(_ & #Hshr' & (H&Hpers))".
      iExists -[(cloc_flat_insert l γs, x)].
      rewrite /tctx_elt_interp/ty_own/=.
      iFrame.
      iSplitL.
      { iCombine "H Hpers" as "H".
        rewrite !Nat.add_1_r -!bi.later_laterN.
        iMod (lc_fupd_add_laterN _ _ _ (S (S d'))  with "[H£] [H]") as "H".
        { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
        { iIntros "!> !>". iExact "H". }
        iDestruct "H" as "[%Hlen #Hgho]".
        rewrite pad_length'.
        2: by rewrite length_fmap.
        iModIntro.
        iSplit => //.
        - iExists _, (S (S (S d'))).
          iSplit => //.
          iFrame "#" => /=.
          iSplit => //.
          iSplitR; last iSplitL.
          + iDestruct "Hshr" as "(H↦shared1 & _ & _)".
            iDestruct (guards_weaken_rhs_sep_l with "Hshr'") as "H↦shared2 ".
            iDestruct (lguards_weaken_later with "H↦shared1") as "H↦shared1'".
            1: instantiate (1 := S (S (S d'))); lia.
            iDestruct (guard_cloc_combine_fancy' with "H↦shared1' H↦shared2") as "H↦shared3".
            simpl.
            iApply (lguards_weaken_later with "H↦shared3").
            lia.
          + iDestruct (guards_weaken_rhs_sep_r with "Hshr'") as "Hghoshared".
            iDestruct (guards_later_absorb_1 with "Hghoshared") as "Hghoshared1".
            iApply (guards_transitive_left with "Hghoshared1").
            leaf_by_sep.
            iApply ty.(ty_gho_depth_mono); lia.
          + repeat iNext.
            iApply (ty.(ty_gho_pers_depth_mono) with "Hgho") => //; lia.
      }
      iApply (proph_obs_impl with "Obs").
      intros π [? Hpost].
      apply Hpost.
    - iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
      destruct d => //.
      iSimpl in "Hshr".
      destruct d' as [ | [ | d']] => //=.
      { iDestruct "Hshr'" as "(_ & _ & Hfalse)".
        rewrite /advance_credits /=.
        iIntros "(£ & _) #Hd''".
        wp_rec.
        by iMod (lc_fupd_elim_later with "£ Hfalse"). }
      iIntros "H£ #Hd''".
      wp_rec.
      iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
      iDestruct "Hshr'" as "(_ & #Hshr' & (H&Hpers))".
      iExists -[(cloc_flat_insert l γs, x)].
      rewrite /tctx_elt_interp/ty_own/=.
      iFrame.
      iSplitL.
      { iCombine "H Hpers" as "H".
        rewrite !Nat.add_1_r -!bi.later_laterN.
        iMod (lc_fupd_add_laterN _ _ _ (S (S d'))  with "[H£] [H]") as "H".
        { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
        { iIntros "!> !>". iExact "H". }
        iDestruct "H" as "[%Hlen #Hgho]".
        rewrite pad_length'.
        2: by rewrite length_fmap.
        iModIntro.
        iSplit => //.
        - iExists _, (S (S d)).
          iSplit => //.
          iFrame "#" => /=.
          iSplit => //.
          iSplitR; last iSplitL.
          + iDestruct "Hshr" as "(H↦shared1 & _ & _)".
            iDestruct (guards_weaken_rhs_sep_l with "Hshr'") as "H↦shared2 ".
            iDestruct (lguards_weaken_later with "H↦shared2") as "H↦shared2'".
            1: instantiate (1 := S (S d)); lia.
            iDestruct (guard_cloc_combine_fancy' with "H↦shared1 H↦shared2'") as "H↦shared3".
            simpl.
            iApply (lguards_weaken_later with "H↦shared3").
            lia.
          + iDestruct (guards_weaken_rhs_sep_r with "Hshr'") as "Hghoshared".
            iDestruct (guards_later_absorb_1 with "Hghoshared") as "Hghoshared1".
            rewrite !Nat.add_1_r.
            iDestruct (lguards_weaken_later with "Hghoshared1") as "Hghoshared2".
            1: instantiate (1 := S (S (S d))); lia.
            iApply (guards_transitive_left with "Hghoshared2").
            leaf_by_sep.
            iApply ty.(ty_gho_depth_mono); lia.
          + repeat iNext.
            iApply (ty.(ty_gho_pers_depth_mono) with "Hgho") => //; lia.
      }
      iApply (proph_obs_impl with "Obs").
      intros π [? Hpost].
      apply Hpost.
  Qed.

  Definition PCellMutBorrow : val :=
    (λ: ["pcell_ref"; "perm_mut_ref"], "pcell_ref")%V.

  Lemma typed_pcell_mut_borrow {𝔄} κ (pcell_ref perm_mut_ref : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[pcell_ref ◁ shr_bor κ (pcell_ty (ty_size ty)); perm_mut_ref ◁ &uniq{κ} (cell_points_to_ty ty)] (PCellMutBorrow [pcell_ref; perm_mut_ref]) (λ v, +[v ◁ &uniq{κ} ty]) (λ post '-[(cl, γs); bor], λ mask π, let '(cl', (γs', x), ξi, d, g, idx) := bor in γs = γs' ∧ ∀ bor',
    uniq_bor_current bor' = x →
    uniq_bor_future bor' π = snd (uniq_bor_future bor π) →
    (uniq_bor_future bor π).1 = γs →
    (uniq_bor_loc bor') = cloc_flat_insert cl γs →
    post -[bor'] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [u []]].
    destruct u as [[[[[cl' [γs' x]] ξi] d] g] ξidx].
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d' Heval) "(#Hd & Hcell_shr & %Hphys)".
    destruct d' => //.
    simpl in Hphys.
    inversion Hphys; subst pl.
    iDestruct "Hperm" as (pl' d'' Heval') "(#Hd' & Huniq & %Hphys')".
    simpl in Hphys'.
    inversion Hphys'; subst pl'.
    iDestruct "Huniq" as "[#Incl [%Hineq [UniqBody [#PtBase #Pers]]]]".
    iSimpl in "Hcell_shr".
    iDestruct "Hcell_shr" as "[#Hcell_shr #[_ Hlen]]".
    rewrite /PCellMutBorrow.
    wp_bind pcell_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_mut_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [trivial |]; iIntros "⧗".
    destruct d'' as [ | ] => //=; first lia.
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Alv Incl'") as "G2".
      wp_rec. repeat wp_seq.
      leaf_open "G2" with "L" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    destruct d.
    { by wp_rec. }
    iDestruct "UniqBody" as "(ξVo & £saved  & ξTok & #ξBor)".
    set ξ := PrVar ((listₛ positiveₛ * 𝔄)%ST ↾ prval_to_inh (@vπ (listₛ positiveₛ * 𝔄) (γs, x))) ξi.
    destruct cl' as [l' [ | ]] eqn:?.
    2: {
      iMod (llftl_bor_idx_acc_guarded with "LFT ξBor ξTok Alv L") as "[Hown Hclose]"; [solve_ndisj|..].
      wp_rec.
      iDestruct "Hown" as "(%&%&%&?&?&?&Hfalse)".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hfalse") as "%Hfalse".
      by simpl in Hfalse. }
    wp_rec.

    change 2 with (1 + 1).
    iDestruct "⧗" as "(⧗ & ⧗')".
    iDestruct (guards_transitive_right with "Alv Hcell_shr") as "Hcell_shr'".
    iMod (guards_extract_persistent_later with "Hcell_shr' L []") as "Hlen'".
    3: {
      iIntros "H".
      iDestruct (heap_fancy_mapsto_cells_length with "H") as "H".
      rewrite length_pad.
      iExact "H".
    }
    1: apply _.
    1: done.
    destruct (decide (d' ≤ d'')) as [Hd' | Hd''].
    {

    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd'") as "(Hd'' & £)"; [solve_ndisj|..].
    iDestruct "£" as "[£ [£1' £1]]".


    rewrite !Nat.add_1_r -!bi.later_laterN.
    iMod (lc_fupd_add_laterN  with "[£] Hlen'") as "[L %Hlen']".
    { iApply (lc_weaken with "£"). nia. }

    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".

    iMod (uniq_body_transform (cell_points_to_ty ty) ty (γs, x) x (S d) g ξi ξidx κ tid cl' (cloc_flat_insert cl γs) _ _ (pair_with_cell_idsₛ (ty_size ty) γs) with "LFT PROPH UNIQ [⧗' £1'] HguardsK H1 [ξTok ξVo £saved]") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
    { iIntros "[gho pt]".
      iMod (lc_fupd_elim_later with "£1' gho") as "gho".
      iDestruct "gho" as "[H↦ gho]".
      iModIntro.
      iSplitL "gho".
      iDestruct (ty_gho_depth_mono _ _ _ (S d) g with "gho") as "[gho _]". { lia. } { lia. }
      done.
      simpl.
      rewrite -(ty.(ty_size_eq) x tid).
      iDestruct "Pers" as "[%Hlen Hgho_pers]".
      rewrite pad_length'.
      2: by rewrite length_fmap.


      iDestruct (heap_complete_mapsto_fancy_val_vec_eq'' _ cl with "H↦") as "H↦".
      { rewrite ty.(ty_size_eq) in Hlen. by rewrite Hlen' -Hlen. }
      iFrame.
      iIntros (x2 d2 g2) "[gho [pt2 ⧖2]]".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗' ⧖2") as "⧖2'". { solve_ndisj. }
      iModIntro. iExists (S d2), g2.
      replace (length (ty_phys ty x tid)) with (length (ty_phys ty x2 tid)).
      2: { repeat rewrite ty_size_eq. done. }
      simpl.
      rewrite heap_complete_mapsto_fancy_val_vec_eq''.
      iFrame. iApply (persistent_time_receipt_mono with "⧖2'"). lia.
      rewrite ty.(ty_size_eq) in Hlen.
      by rewrite Hlen' - Hlen.
    }
    { iFrame. simpl.
      rewrite Heqc.
      iEval (setoid_rewrite (heap_complete_mapsto_fancy_empty l')).
      iFrame "ξBor". }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iModIntro.
    iExists -[((cloc_flat_insert cl γs), x, ζi, (S d), g, ζidx)].
    iFrame "L". iFrame "UniqBody". iFrame "Incl".
    iSplit. 
    - iExists _, _.
      iSplit => //.
      iFrame.
      iSplit => //.
      iSplitR; first (iPureIntro; lia).
      iDestruct "Pers" as "(%Hlen & #Pers')".
      iSplitR.
      rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
      rewrite pad_length'.
      2: by rewrite length_fmap.
      rewrite heap_complete_mapsto_combine.
      iApply (lguards_weaken_later with "Hcell_shr"); first lia.
      by rewrite Hlen Hlen'.
      iRight.  iNext.
      iApply (ty_gho_pers_depth_mono  with "Pers'"); lia.
    - iCombine "Obs Obs2" as "Obs3".
      iApply (proph_obs_impl with "Obs3"). intros π [[_ Ha] Hb].
      apply Ha; intuition.
      + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      + unfold uniq_bor_future, uniq_bor_loc. simpl. rewrite Hb. trivial.
    }
    {

    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd") as "(Hd'' & £)"; [solve_ndisj|..].
    iDestruct "£" as "[£ [£1' £1]]".


    rewrite !Nat.add_1_r -!bi.later_laterN.
    iMod (lc_fupd_add_laterN  with "[£] Hlen'") as "[L %Hlen']".
    { iApply (lc_weaken with "£"). nia. }

    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".

    iMod (uniq_body_transform (cell_points_to_ty ty) ty (γs, x) x (S d) g ξi ξidx κ tid cl' (cloc_flat_insert cl γs) _ _ (pair_with_cell_idsₛ _ γs) with "LFT PROPH UNIQ [⧗' £1'] HguardsK H1 [ξTok ξVo £saved]") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
    { iIntros "[gho pt]".
      iMod (lc_fupd_elim_later with "£1' gho") as "gho".
      iDestruct "gho" as "[H↦ gho]".
      iModIntro.
      iSplitL "gho".
      iDestruct (ty_gho_depth_mono _ _ _ (S d) g with "gho") as "[gho _]". { lia. } { lia. }
      done.
      simpl.
      rewrite -(ty.(ty_size_eq) x tid).
      iDestruct "Pers" as "[%Hlen Hgho_pers]".
      rewrite pad_length'.
      2: by rewrite length_fmap.


      iDestruct (heap_complete_mapsto_fancy_val_vec_eq'' _ cl with "H↦") as "H↦".
      { rewrite ty.(ty_size_eq) in Hlen. by rewrite Hlen' -Hlen. }
      iFrame.
      iIntros (x2 d2 g2) "[gho [pt2 ⧖2]]".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗' ⧖2") as "⧖2'". { solve_ndisj. }
      iModIntro. iExists (S d2), g2.
      replace (length (ty_phys ty x tid)) with (length (ty_phys ty x2 tid)).
      2: { repeat rewrite ty_size_eq. done. }
      simpl.
      rewrite heap_complete_mapsto_fancy_val_vec_eq''.
      iFrame. iApply (persistent_time_receipt_mono with "⧖2'"). lia.
      rewrite ty.(ty_size_eq) in Hlen.
      by rewrite Hlen' - Hlen.
    }
    { iFrame. simpl.
      rewrite Heqc.
      iEval (setoid_rewrite (heap_complete_mapsto_fancy_empty l')).
      iFrame "ξBor". }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iModIntro.
    iExists -[((cloc_flat_insert cl γs), x, ζi, (S d), g, ζidx)].
    iFrame "L". iFrame "UniqBody". iFrame "Incl".
    iSplit.
    - iExists _, _.
      iSplit => //.
      iFrame.
      iSplit => //.
      iSplitR; first (iPureIntro; lia).
      iDestruct "Pers" as "(%Hlen & #Pers')".
      iSplitR.
      rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
      rewrite pad_length'.
      2: by rewrite length_fmap.
      rewrite heap_complete_mapsto_combine.
      iApply (lguards_weaken_later with "Hcell_shr"); first lia.
      by rewrite Hlen Hlen'.
      iRight.  iNext.
      iApply (ty_gho_pers_depth_mono  with "Pers'"); lia.
    - iCombine "Obs Obs2" as "Obs3".
      iApply (proph_obs_impl with "Obs3"). intros π [[_ Ha] Hb].
      apply Ha; intuition.
      + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      + unfold uniq_bor_future, uniq_bor_loc. simpl. rewrite Hb. trivial.
    }
  Qed.

End typing.

