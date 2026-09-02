import CPD.Existence

/-!
# Theorem 1: existence under QC and M-C (§6.1)

This file proves **Theorem 1**, in three parts. The construction throughout
follows Algorithm 3 (the greedy algorithm) and Appendix C's coalition-optimal
equilibrium (COE) partitions from `COE.lean`: at each step, pick a coalition
attaining the maximum of the residual coalition-payoff set `max 𝒲_{R_t}`, and
show (using the pooling and merging lemmas of `Existence.lean`) that the
resulting partition is coalition-proof.

* **Theorem 1** (existence): if the message mapping is complete (M-C) and `v̄`
  is quasiconcave (QC), a coalition-proof PBE exists (`one_existence`), by
  exhibiting a COE partition.
* **Theorem 1(i)** (no halt): if in addition `v̄` is strictly quasiconcave
  (QC*), a greedy partition exists and every greedy partition is a
  coalition-proof PBE partition (`one_noHalt`); the full "no run of the
  greedy algorithm halts" form is proved separately in `GreedyPrefix.lean`.
* **Theorem 1(ii)** (essential uniqueness): if the game is generic, any two
  coalition-proof PBE partitions have the same length, cells, and payoffs
  (`one_unique`).
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ### Helper lemmas (private) -/

/-- Transport a strategy along an equality of games, preserving evidence and beliefs. -/
private lemma strategy_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) (s : Strategy g₁) :
    ∃ s' : Strategy g₂, s'.evidence = s.evidence ∧
      ∀ m, s'.coalitionBelief m = s.coalitionBelief m := by
  subst h; exact ⟨s, rfl, fun _ => rfl⟩

/-- Transport a coalition along an equality of games, preserving cell and payoff. -/
private lemma coalition_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) (K : g₁.Coalition) :
    ∃ K' : g₂.Coalition, K'.C = K.C ∧ K'.w = K.w := by
  subst h; exact ⟨K, rfl, rfl⟩

/-- Coalition-payoff sets agree for equal games. -/
private lemma coalitionPayoffs_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) :
    g₁.coalitionPayoffs = g₂.coalitionPayoffs := by
  subst h; rfl

/-
QC* implies QC.
-/
private lemma qcStar_qc (hQCs : G.QCStar) : G.QC := by
  intro μ hμ μ' hμ' l hl;
  by_cases h : μ = μ';
  · simp +decide [ h, ← add_mul ];
  · exact le_of_lt ( hQCs μ hμ μ' hμ' h l hl )

/-
QC is inherited by restricted games.
-/
private lemma qc_restrict {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hQC : G.QC) : (G.restrict S hne hsub).QC := by
  intro μ hμ μ' hμ' l hl;
  convert hQC μ (simplexOn_mono hsub hμ) μ' (simplexOn_mono hsub hμ') l hl using 1

/-
M-C is inherited by restricted games.
-/
private lemma mc_restrict {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hMC : G.MC) : (G.restrict S hne hsub).MC := by
  intro m hm m' hm'
  obtain ⟨m'', hm'', hm''_eq⟩ := hMC m (by
  exact G.restrictMsgSpace_subset hsub hm) m' (by
  exact G.restrictMsgSpace_subset hsub hm');
  refine' ⟨ m'', _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff, DisclosureGame.canSend ];
  · simp_all +decide [ DisclosureGame.preimageFull, DisclosureGame.restrictMsgSpace ];
    obtain ⟨ a, ha, ha' ⟩ := hm; specialize hm''_eq a; simp_all +decide [ preimage ] ;
    grind +qlia;
  · simp_all +decide [ DisclosureGame.preimageFull, DisclosureGame.preimageSet ];
    simp_all +decide [ preimage ];
    grind +splitImp

/-
The conditional prior on a subset `C ⊆ S` is unchanged when passing to `G|_S`.
-/
private lemma restrict_condPrior_eq {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    {C : Finset T} (hCS : C ⊆ S) :
    (G.restrict S hne hsub).condPrior C = G.condPrior C := by
  unfold DisclosureGame.condPrior;
  funext θ; by_cases hθC : θ ∈ C <;> simp +decide [ hθC ] ;
  simp +decide [ DisclosureGame.condPrior, DisclosureGame.priorMeasure, DisclosureGame.restrict, hθC ];
  rw [ ← Finset.sum_div _ _ _, div_div_div_cancel_right₀ ];
  · rw [ if_pos ( hCS hθC ), Finset.sum_congr rfl fun x hx => if_pos ( hCS hx ) ];
  · exact ne_of_gt ( G.priorMeasure_pos hne hsub )

/-
The coalition-payoff set has a greatest element.
-/
private lemma exists_isGreatest_cp (H : DisclosureGame T Msg) :
    ∃ w, IsGreatest H.coalitionPayoffs w := by
  apply_rules [ IsCompact.exists_isGreatest, DisclosureGame.isCompact_coalitionPayoffs, DisclosureGame.coalitionPayoffs_nonempty ]

/-
**Maximal cell.** Under QC and M-C there is a coalition attaining the greatest
coalition payoff such that removing its cell cannot raise the residual maximum.
-/
lemma exists_max_cell (H : DisclosureGame T Msg) (hQC : H.QC) (hMC : H.MC) :
    ∃ K : H.Coalition, IsGreatest H.coalitionPayoffs K.w ∧
      ∀ (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ) (w' : ℝ),
        IsGreatest (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs w' → w' ≤ K.w := by
  obtain ⟨K, hK⟩ : ∃ K : Coalition H, IsGreatest H.coalitionPayoffs K.w ∧ ∀ K' : Coalition H, IsGreatest H.coalitionPayoffs K'.w → K'.C.card ≤ K.C.card := by
    obtain ⟨w, hw⟩ : ∃ w, IsGreatest H.coalitionPayoffs w := by
      convert exists_isGreatest_cp H;
    obtain ⟨K, hK⟩ : ∃ K : Coalition H, K.w = w := by
      exact hw.1;
    -- Let $N$ be the maximum cardinality of a coalition attaining $w$.
    obtain ⟨N, hN⟩ : ∃ N, N ∈ Set.image (fun K : Coalition H => K.C.card) {K : Coalition H | IsGreatest H.coalitionPayoffs K.w} ∧ ∀ n ∈ Set.image (fun K : Coalition H => K.C.card) {K : Coalition H | IsGreatest H.coalitionPayoffs K.w}, n ≤ N := by
      apply_rules [ Set.exists_max_image ];
      · exact Set.Finite.subset ( Set.toFinite ( Finset.image ( fun s : Finset T => s.card ) ( Finset.powerset H.Θ ) ) ) ( Set.image_subset_iff.mpr fun K hK => Finset.mem_image.mpr ⟨ K.C, Finset.mem_powerset.mpr K.C_subset, rfl ⟩ );
      · exact ⟨ _, ⟨ K, by simpa [ hK ] using hw, rfl ⟩ ⟩;
    rcases hN.1 with ⟨ K, hK, rfl ⟩ ; exact ⟨ K, hK, fun K' hK' => hN.2 _ <| Set.mem_image_of_mem _ hK' ⟩ ;
  by_contra h_contra;
  obtain ⟨Kt, hKt⟩ : ∃ Kt : Coalition H, K.C ⊂ Kt.C ∧ Kt.w = K.w ∧ H.vbar (H.condPrior K.C) = K.w ∧ H.vbar (H.condPrior Kt.C) = K.w := by
    have := merging hQC hMC H.Θ_nonempty (subset_rfl);
    grind +suggestions;
  exact not_lt_of_ge ( hK.2 Kt ( by simpa [ hKt.2.1 ] using hK.1 ) ) ( Finset.card_lt_card hKt.1 )

/-
Single-cell COE partition when the maximal cell exhausts `Θ`.
-/
private lemma single_cell_coe (H : DisclosureGame T Msg) (K : H.Coalition)
    (hempty : H.Θ \ K.C = ∅) (hmax : IsGreatest H.coalitionPayoffs K.w) :
    ∃ P : Partition H, P.IsCOE := by
  refine' ⟨ _, _ ⟩;
  refine' ⟨ 1, fun _ => K.C, _, _, _, _, fun _ => K.σ, fun _ => K.w, fun _ => _, fun _ => K.payoff ⟩ <;> simp +decide [ Fin.eq_zero ];
  exact fun x hx => by_contra fun hx' => Finset.notMem_empty x ( hempty ▸ Finset.mem_sdiff.mpr ⟨ hx, hx' ⟩ );
  convert K.exclusive;
  ext; simp [thetaStep, DisclosureGame.preimageSet, DisclosureGame.preimageSetFull];
  exact fun _ => ⟨ fun h => K.C_subset h, fun h => Classical.not_not.1 fun h' => Finset.notMem_empty _ ( hempty ▸ Finset.mem_sdiff.2 ⟨ h, h' ⟩ ) ⟩;
  intro t; fin_cases t; simp +decide [ Partition.IsCOE ] ;
  convert hmax using 1;
  convert coalitionPayoffs_of_eq _;
  convert DisclosureGame.restrict_self;
  ext; simp +decide [ thetaStep ] ;
  exact ⟨ fun h => K.C_subset h, fun h => Classical.not_not.1 fun h' => Finset.notMem_empty _ ( hempty ▸ Finset.mem_sdiff.2 ⟨ h, h' ⟩ ) ⟩

/-
Construct the prepended partition (structure only), with cells/payoffs and
residuals matched index-by-index to `K` (at level 0) and `P'` (at later levels).
-/
private lemma exists_prependP (H : DisclosureGame T Msg) (K : H.Coalition)
    (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ)
    (P' : Partition (H.restrict (H.Θ \ K.C) hne hsub)) :
    ∃ P : Partition H, P.card = P'.card + 1 ∧
      (∀ t : Fin P.card, (t : ℕ) = 0 → thetaStep P.C t = H.Θ ∧ P.w t = K.w) ∧
      (∀ (t : Fin P.card) (j : Fin P'.card), (t : ℕ) = (j : ℕ) + 1 →
        thetaStep P.C t = thetaStep P'.C j ∧ P.w t = P'.w j) := by
  refine' ⟨ _, _, _, _ ⟩;
  use P'.card + 1;
  exact fun t => Fin.cases K.C ( fun j => P'.C j ) t;
  all_goals norm_num [ Fin.forall_fin_succ, Fin.exists_fin_succ, thetaStep ];
  exact ⟨ K.C_nonempty, fun i => P'.C_nonempty i ⟩;
  exact ⟨ fun i hi => Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( P'.C_subset i hx' ) |>.2 hx, fun i => ⟨ Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( P'.C_subset i hx ) |>.2 hx', fun j hj => P'.C_disjoint i j hj ⟩ ⟩;
  exact ⟨ K.C_subset, fun i => P'.C_subset i |> Finset.Subset.trans <| Finset.sdiff_subset ⟩;
  rotate_left;
  exact fun t => Fin.cases K.σ ( fun j => ( strategy_of_eq ( restrict_restrict hne hsub ( P'.C_nonempty j ) ( P'.C_subset j ) ) ( P'.σ j ) ).choose ) t;
  exact fun t => Fin.cases K.w ( fun j => P'.w j ) t;
  all_goals norm_num [ Fin.forall_fin_succ, Fin.exists_fin_succ, Finset.ext_iff, Set.ext_iff ] at *;
  · constructor;
    · convert K.exclusive using 1;
      simp +decide [ Finset.ext_iff, Set.ext_iff, DisclosureGame.preimageSet, DisclosureGame.preimageSetFull ];
      intro a ha; constructor <;> intro h <;> contrapose! ha <;> simp_all +decide [ Fin.exists_fin_succ, Finset.ext_iff, Set.ext_iff ] ;
      · exact False.elim ( ha ( K.C_subset ( h.elim ( fun h => h ) fun ⟨ i, hi ⟩ => P'.C_subset i hi |> fun h => by aesop ) ) );
      · intro m hm; specialize ha 0; simp_all +decide [ Fin.cases ] ;
        intro hm';
        have := K.exclusive; simp_all +decide [ Finset.ext_iff, Set.ext_iff, DisclosureGame.preimageSet, DisclosureGame.preimageSetFull ] ;
        exact ha ( this ( Finset.mem_filter.mpr ⟨ h, ⟨ m, by aesop ⟩ ⟩ ) );
    · intro i;
      have := P'.exclusive i;
      convert this using 1;
      ext; simp [preimageSet];
      constructor <;> intro h;
      · obtain ⟨ ⟨ j, hj₁, hj₂ ⟩, hj₃ ⟩ := h;
        rcases j with ⟨ _ | j, hj ⟩ <;> simp_all +decide [ Fin.ext_iff, thetaStep ];
        refine' ⟨ ⟨ ⟨ j, by linarith ⟩, _, _ ⟩, _ ⟩;
        · exact Nat.le_of_succ_le_succ hj₁;
        · exact hj₂;
        · convert hj₃ using 1;
          grind +suggestions;
      · refine' ⟨ ⟨ Fin.succ i, _, _ ⟩, _ ⟩ <;> simp_all +decide [ thetaStep ];
        · obtain ⟨ ⟨ j, hj₁, hj₂ ⟩, hj₃ ⟩ := h;
          exact this ( by
            exact Finset.mem_filter.mpr ⟨ Finset.mem_biUnion.mpr ⟨ j, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj₁ ⟩, hj₂ ⟩, hj₃ ⟩ );
        · convert h.2 using 1;
          grind;
  · refine' ⟨ K.payoff, _ ⟩;
    intro i m hm
    have := P'.payoff i m
    simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    grind;
  · intro a;
    constructor;
    · rintro ( ha | ⟨ i, ha ⟩ ) <;> [ exact K.C_subset ha; exact P'.C_subset i ha |> fun h => hsub h ];
    · intro ha
      by_cases haK : a ∈ K.C;
      · exact Or.inl haK;
      · have := P'.cover_eq;
        replace this := Finset.ext_iff.mp this a; aesop;
  · intro i j hij; simp +decide [ Fin.ext hij ] ;
  · intro θ hθ;
    by_cases hθK : θ ∈ K.C;
    · exact Finset.mem_biUnion.mpr ⟨ ⟨ 0, Nat.succ_pos _ ⟩, Finset.mem_univ _, by simpa using hθK ⟩;
    · have := P'.cover_eq;
      replace this := Finset.ext_iff.mp this θ; simp_all +decide [ Finset.mem_biUnion ] ;
      exact ⟨ Fin.succ this.choose, this.choose_spec ⟩

/-
The prepended partition is COE.
-/
private lemma prepend_isCOE (H : DisclosureGame T Msg) (K : H.Coalition)
    (hmax : IsGreatest H.coalitionPayoffs K.w)
    (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ)
    (hbound : ∀ w', IsGreatest (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs w' → w' ≤ K.w)
    (P' : Partition (H.restrict (H.Θ \ K.C) hne hsub)) (hP' : P'.IsCOE)
    (P : Partition H) (hcard : P.card = P'.card + 1)
    (h0 : ∀ t : Fin P.card, (t : ℕ) = 0 → thetaStep P.C t = H.Θ ∧ P.w t = K.w)
    (hsucc : ∀ (t : Fin P.card) (j : Fin P'.card), (t : ℕ) = (j : ℕ) + 1 →
        thetaStep P.C t = thetaStep P'.C j ∧ P.w t = P'.w j) :
    P.IsCOE := by
  intro t
  by_cases ht : t.val = 0;
  · simp_all +decide [ Partition.stepPayoffs ];
    convert hmax using 1;
    exact coalitionPayoffs_of_eq ( restrict_self );
  · obtain ⟨j, hj⟩ : ∃ j : Fin P'.card, t.val = j.val + 1 := by
      exact ⟨ ⟨ t - 1, by omega ⟩, by simp +decide [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ht ) ] ⟩;
    obtain ⟨h_stepPayoffs, h_monotone⟩ := hP' j;
    refine' ⟨ _, _ ⟩;
    · convert h_stepPayoffs using 1;
      · unfold Partition.stepPayoffs; simp +decide [ hsucc t j hj ] ;
        grind +suggestions;
      · exact hsucc t j hj |>.2;
    · by_cases hj0 : j.val = 0;
      · have h_stepPayoffs : P'.stepPayoffs j = (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs := by
          have h_stepPayoffs : thetaStep P'.C j = (H.restrict (H.Θ \ K.C) hne hsub).Θ := by
            have := P'.cover_eq;
            simp +decide [ hj0, thetaStep ];
            convert this.symm using 1;
            grind;
          unfold Partition.stepPayoffs; simp +decide [ h_stepPayoffs ] ;
          grind +suggestions;
        grind;
      · obtain ⟨j', hj'⟩ : ∃ j' : Fin P'.card, j.val = j'.val + 1 := by
          exact ⟨ ⟨ j - 1, by omega ⟩, by simp +decide [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hj0 ) ] ⟩;
        grind

/-- Prepend a maximal cell to a COE partition of the residual game. -/
private lemma prepend_coe (H : DisclosureGame T Msg) (K : H.Coalition)
    (hmax : IsGreatest H.coalitionPayoffs K.w)
    (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ)
    (hbound : ∀ w', IsGreatest (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs w' → w' ≤ K.w)
    (P' : Partition (H.restrict (H.Θ \ K.C) hne hsub)) (hP' : P'.IsCOE) :
    ∃ P : Partition H, P.IsCOE := by
  obtain ⟨P, hcard, h0, hsucc⟩ := exists_prependP H K hne hsub P'
  exact ⟨P, prepend_isCOE H K hmax hne hsub hbound P' hP' P hcard h0 hsucc⟩

/-
**Existence of a COE partition** under QC and M-C, for any disclosure game.
-/
lemma exists_coePartition (H : DisclosureGame T Msg) (hQC : H.QC) (hMC : H.MC) :
    ∃ P : Partition H, P.IsCOE := by
  -- By induction on the cardinality of Θ.
  induction' n : H.Θ.card using Nat.strong_induction_on with k ih generalizing H;
  obtain ⟨ K, hKmax, hbound ⟩ := exists_max_cell H hQC hMC;
  by_cases hempty : H.Θ \ K.C = ∅;
  · exact single_cell_coe H K hempty hKmax;
  · obtain ⟨hne, hsub⟩ : (H.Θ \ K.C).Nonempty ∧ (H.Θ \ K.C) ⊆ H.Θ := by
      exact ⟨ Finset.nonempty_of_ne_empty hempty, Finset.sdiff_subset ⟩;
    have hcard : (H.restrict (H.Θ \ K.C) hne hsub).Θ.card < k := by
      convert Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ hsub, ?_ ⟩ ) using 1;
      · exact n.symm;
      · simp_all +decide [ Finset.ext_iff ];
        exact Finset.not_disjoint_iff.mpr ⟨ _, K.C_nonempty.choose_spec |> fun h => Finset.mem_of_subset K.C_subset h, K.C_nonempty.choose_spec ⟩;
    exact ih _ hcard _ ( qc_restrict hne hsub hQC ) ( mc_restrict hne hsub hMC ) rfl |> fun ⟨ P, hP ⟩ => prepend_coe H K hKmax hne hsub ( hbound hne hsub ) P hP

/-
The cell at step `t` of a partition, viewed as a coalition of the residual game.
-/
private lemma cell_coalition (P : Partition G) (t : Fin P.card) :
    ∃ K : (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t))
        (P.thetaStep_subset t)).Coalition,
      K.C = P.C t ∧ K.w = P.w t := by
  obtain ⟨K, hK⟩ : ∃ K : Coalition (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)), K.C = P.C t ∧ K.w = P.w t := by
    have h_eq : (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)).restrict (P.C t) (P.C_nonempty t) (by
    exact Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by rfl ⟩ ) |> Finset.Subset.trans <| Finset.Subset.refl _;) = G.restrict (P.C t) (P.C_nonempty t) (P.C_subset t) := by
      exact restrict_restrict _ _ _ _
    obtain ⟨σ', hσ'⟩ := strategy_of_eq h_eq.symm (P.σ t);
    refine' ⟨ ⟨ P.C t, _, _, σ', _, P.w t, _ ⟩, rfl, rfl ⟩ <;> simp_all +decide [ DisclosureGame.Coalition ];
    · convert P.exclusive t using 1;
    · exact P.payoff t
  generalize_proofs at *; (
  use K)

/-
If a cell attains the residual maximum, its pooling value equals its payoff.
-/
private lemma cell_vbar (hQC : G.QC) (hMC : G.MC) (P : Partition G) (t : Fin P.card)
    (hmax : IsGreatest (P.stepPayoffs t) (P.w t)) :
    G.vbar (G.condPrior (P.C t)) = P.w t := by
  obtain ⟨ K, hKC, hKw ⟩ := cell_coalition P t;
  have hK_max : IsGreatest (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)).coalitionPayoffs K.w := by
    convert hmax using 1;
  convert coalition_attains_max (qc_restrict (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t) hQC) (mc_restrict (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t) hMC) K hK_max using 1;
  · rw [ restrict_condPrior_eq ];
    · rw [ hKC, DisclosureGame.vbar, DisclosureGame.vbar ];
      rw [ DisclosureGame.restrict_V ];
    · exact K.C_subset;
  · exact hKw.symm

/-
**No merging up under genericity.** Removing a cell attaining the maximum cannot
raise the residual maximum.
-/
private lemma no_merge_up (hQC : G.QC) (hMC : G.MC) (hGen : G.Generic)
    {Θt : Finset T} (hΘne : Θt.Nonempty) (hΘsub : Θt ⊆ G.Θ)
    (K : (G.restrict Θt hΘne hΘsub).Coalition)
    (hw : IsGreatest (G.restrict Θt hΘne hΘsub).coalitionPayoffs K.w)
    (hne' : (Θt \ K.C).Nonempty) (hsub' : (Θt \ K.C) ⊆ G.Θ) {w' : ℝ}
    (hw' : IsGreatest (G.restrict (Θt \ K.C) hne' hsub').coalitionPayoffs w') :
    w' ≤ K.w := by
  by_contra h;
  obtain ⟨Kt, hKt⟩ := merging hQC hMC hΘne hΘsub K hw hne' hw' (not_le.mp h);
  have := hGen ( show K.C.Nonempty ∧ K.C ⊆ G.Θ from ⟨ K.C_nonempty, Finset.Subset.trans K.C_subset hΘsub ⟩ ) ( show Kt.C.Nonempty ∧ Kt.C ⊆ G.Θ from ⟨ Finset.Nonempty.mono hKt.1.subset K.C_nonempty, Finset.Subset.trans Kt.C_subset hΘsub ⟩ ) ; simp_all +decide [ Finset.ssubset_def ] ;

/-- The `ℕ`-indexed residual `R_n := ⋃_{(s:ℕ) ≥ n} C_s`. -/
private noncomputable def Rn (P : Partition G) (n : ℕ) : Finset T :=
  (Finset.univ.filter (fun s : Fin P.card => n ≤ (s : ℕ))).biUnion P.C

private lemma thetaStep_eq_Rn (P : Partition G) (t : Fin P.card) :
    thetaStep P.C t = Rn P (t : ℕ) := by
  ext; simp [thetaStep, Rn]

private lemma Rn_zero (P : Partition G) : Rn P 0 = G.Θ := by
  unfold Rn; simp +decide [ P.cover_eq ] ;

private lemma Rn_nonempty_iff (P : Partition G) (n : ℕ) :
    (Rn P n).Nonempty ↔ n < P.card := by
  constructor <;> intro hn;
  · obtain ⟨ θ, hθ ⟩ := hn;
    obtain ⟨ s, hs, hθ ⟩ := Finset.mem_biUnion.mp hθ;
    exact lt_of_le_of_lt ( Finset.mem_filter.mp hs |>.2 ) ( Fin.is_lt s );
  · exact ⟨ _, Finset.mem_biUnion.mpr ⟨ ⟨ n, hn ⟩, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_rfl ⟩, Finset.mem_coe.mpr ( P.C_nonempty ⟨ n, hn ⟩ |> Classical.choose_spec ) ⟩ ⟩

private lemma Rn_succ (P : Partition G) {n : ℕ} (h : n < P.card) :
    Rn P (n + 1) = Rn P n \ P.C ⟨n, h⟩ := by
  refine' Finset.Subset.antisymm _ _;
  · intro x hx; simp_all +decide [ Rn ] ;
    obtain ⟨ a, ha₁, ha₂ ⟩ := hx; refine' ⟨ ⟨ a, le_of_lt ha₁, ha₂ ⟩, _ ⟩ ; intro ha₃; have := P.C_disjoint a ⟨ n, h ⟩ ; simp_all +decide [ Fin.ext_iff ] ;
    exact Finset.disjoint_left.mp ( this ( ne_of_gt ha₁ ) ) ha₂ ha₃;
  · intro x hx; simp_all +decide [ Rn ] ;
    obtain ⟨ ⟨ a, ha₁, ha₂ ⟩, ha₃ ⟩ := hx; exact ⟨ a, lt_of_le_of_ne ha₁ ( Ne.symm <| by rintro rfl; exact ha₃ ha₂ ), ha₂ ⟩ ;

/-
For a greedy partition under genericity, each payoff equals the residual maximum.
-/
private lemma greedy_w_eq_stepMax (hQC : G.QC) (hMC : G.MC) (hGen : G.Generic)
    (P : Partition G) (hg : P.IsGreedy) (t : Fin P.card) : P.w t = P.stepMax t := by
  induction' t with t ih;
  induction' t using Nat.strong_induction_on with t ih generalizing P;
  have := hg ⟨ t, ih ⟩;
  refine' this.unique ⟨ _, fun w hw => _ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · exact P.isGreatest_stepMax ⟨ t, ih ⟩ |>.1;
    · exact P.greedyLower_le_stepMax ⟨ t, ih ⟩;
    · intro t' ht'
      obtain ⟨K, hKC, hKw⟩ := cell_coalition P t';
      have h_ne : (thetaStep P.C t' \ K.C).Nonempty := by
        convert thetaStep_nonempty ⟨ t, ih ⟩ ( P.C_nonempty ⟨ t, ih ⟩ ) using 1;
        rw [ hKC, thetaStep_eq_Rn, thetaStep_eq_Rn ];
        rw [ ← ht', Rn_succ ]
      have h_sub : (thetaStep P.C t' \ K.C) ⊆ G.Θ := by
        exact Finset.sdiff_subset.trans ( P.thetaStep_subset t' )
      have h_w : IsGreatest (G.restrict (thetaStep P.C t' \ K.C) h_ne h_sub).coalitionPayoffs (P.stepMax ⟨t, ih⟩) := by
        convert P.isGreatest_stepMax ⟨ t, ih ⟩ using 1;
        convert coalitionPayoffs_of_eq _ using 2;
        congr! 1;
        rw [ hKC, thetaStep_eq_Rn, thetaStep_eq_Rn ];
        exact Rn_succ P ( by linarith ) ▸ by aesop;
      have h_no_merge_up : ∀ w', IsGreatest (G.restrict (thetaStep P.C t' \ K.C) h_ne h_sub).coalitionPayoffs w' → w' ≤ K.w := by
        apply no_merge_up;
        · exact hQC;
        · exact hMC;
        · exact hGen;
        · convert P.isGreatest_stepMax t' using 1;
          rw [ hKw, ‹∀ m < t, ∀ ( P : G.Partition ), P.IsGreedy → ∀ ( ih : m < P.card ), P.w ⟨ m, ih ⟩ = P.stepMax ⟨ m, ih ⟩ › _ ( by linarith ) _ hg ( by linarith ) ];
      exact le_trans ( h_no_merge_up _ h_w ) ( by linarith );
  · exact P.isGreatest_stepMax ⟨ t, ih ⟩ |>.2 hw.1

/-- Under QC, M-C and genericity, every greedy partition is COE. -/
private lemma greedy_isCOE (hQC : G.QC) (hMC : G.MC) (hGen : G.Generic)
    (P : Partition G) (hg : P.IsGreedy) : P.IsCOE := by
  intro t
  refine ⟨?_, ?_⟩
  · have h := greedy_w_eq_stepMax hQC hMC hGen P hg t
    rw [h]; exact P.isGreatest_stepMax t
  · intro t' ht'
    exact (hg t).1.2.2 t' ht'

/-
If two COE partitions share the residual at level `n`, their `n`-th cells and
payoffs coincide (under genericity).
-/
private lemma coe_cell_match (hQC : G.QC) (hMC : G.MC) (hGen : G.Generic)
    (P P' : Partition G) (hP : P.IsCOE) (hP' : P'.IsCOE) {n : ℕ}
    (hres : Rn P n = Rn P' n) (hPlt : n < P.card) (hP'lt : n < P'.card) :
    P.C ⟨n, hPlt⟩ = P'.C ⟨n, hP'lt⟩ ∧ P.w ⟨n, hPlt⟩ = P'.w ⟨n, hP'lt⟩ := by
  have h_stepPayoffs_eq : P.stepPayoffs ⟨n, hPlt⟩ = P'.stepPayoffs ⟨n, hP'lt⟩ := by
    convert coalitionPayoffs_of_eq _;
    congr! 1;
  have h_payoff_eq : P.w ⟨n, hPlt⟩ = P'.w ⟨n, hP'lt⟩ := by
    exact IsGreatest.unique ( hP ⟨ n, hPlt ⟩ |>.1 ) ( h_stepPayoffs_eq ▸ hP' ⟨ n, hP'lt ⟩ |>.1 );
  have h_cell_eq : G.vbar (G.condPrior (P.C ⟨n, hPlt⟩)) = G.vbar (G.condPrior (P'.C ⟨n, hP'lt⟩)) := by
    convert h_payoff_eq using 1;
    · convert cell_vbar hQC hMC P ⟨ n, hPlt ⟩ ( hP ⟨ n, hPlt ⟩ |>.1 ) using 1;
    · apply cell_vbar;
      · exact hQC;
      · exact hMC;
      · exact hP' ⟨ n, hP'lt ⟩ |>.1;
  have := hGen ( show P.C ⟨ n, hPlt ⟩ ∈ { C : Finset T | C.Nonempty ∧ C ⊆ G.Θ } from ⟨ P.C_nonempty _, P.C_subset _ ⟩ ) ( show P'.C ⟨ n, hP'lt ⟩ ∈ { C : Finset T | C.Nonempty ∧ C ⊆ G.Θ } from ⟨ P'.C_nonempty _, P'.C_subset _ ⟩ ) ; aesop;

/-
Two COE partitions have the same residuals at every level (under genericity).
-/
private lemma coe_residual_eq (hQC : G.QC) (hMC : G.MC) (hGen : G.Generic)
    (P P' : Partition G) (hP : P.IsCOE) (hP' : P'.IsCOE) (n : ℕ) :
    Rn P n = Rn P' n := by
  induction' n with n ih;
  · rw [ DisclosureGame.Rn_zero, DisclosureGame.Rn_zero ];
  · by_cases hn : n < P.card <;> by_cases hn' : n < P'.card;
    · rw [ Rn_succ P hn, Rn_succ P' hn', ih ];
      rw [ coe_cell_match hQC hMC hGen P P' hP hP' ih hn hn' |>.1 ];
    · have := Rn_nonempty_iff P n; have := Rn_nonempty_iff P' n; simp_all +decide ;
      linarith;
    · simp_all +decide [ Rn_nonempty_iff ];
      have h_empty : Rn P n = ∅ := by
        exact Finset.eq_empty_of_forall_notMem fun x hx => by have := Rn_nonempty_iff P n; exact this.mp ⟨ x, hx ⟩ |> not_lt_of_ge hn;
      simp_all +decide [ Finset.ext_iff ];
      simp_all +decide [ Rn ];
      grind;
    · rw [ show Rn P ( n + 1 ) = ∅ from Finset.not_nonempty_iff_eq_empty.mp ( by simpa using Rn_nonempty_iff P ( n + 1 ) |>.not.mpr ( by linarith ) ), show Rn P' ( n + 1 ) = ∅ from Finset.not_nonempty_iff_eq_empty.mp ( by simpa using Rn_nonempty_iff P' ( n + 1 ) |>.not.mpr ( by linarith ) ) ]

/-- Essential uniqueness for COE partitions under genericity. -/
private lemma coe_unique (hQC : G.QC) (hMC : G.MC) (hGen : G.Generic)
    (P P' : Partition G) (hP : P.IsCOE) (hP' : P'.IsCOE) :
    P.card = P'.card ∧
      ∀ (t : Fin P.card) (t' : Fin P'.card), (t : ℕ) = (t' : ℕ) →
        P.C t = P'.C t' ∧ P.w t = P'.w t' := by
  have hcard : P.card = P'.card := by
    have hiff : ∀ n : ℕ, n < P.card ↔ n < P'.card := by
      intro n
      rw [← Rn_nonempty_iff P n, ← Rn_nonempty_iff P' n,
        coe_residual_eq hQC hMC hGen P P' hP hP' n]
    rcases lt_trichotomy P.card P'.card with h | h | h
    · exact absurd ((hiff P.card).mpr h) (lt_irrefl _)
    · exact h
    · exact absurd ((hiff P'.card).mp h) (lt_irrefl _)
  refine ⟨hcard, ?_⟩
  intro t t' htt'
  have hPlt : (t : ℕ) < P.card := t.isLt
  have hP'lt : (t : ℕ) < P'.card := by have := t'.isLt; omega
  have hmatch := coe_cell_match hQC hMC hGen P P' hP hP'
    (coe_residual_eq hQC hMC hGen P P' hP hP' (t : ℕ)) hPlt hP'lt
  have ht : t = (⟨(t : ℕ), hPlt⟩ : Fin P.card) := by ext; rfl
  have ht' : t' = (⟨(t : ℕ), hP'lt⟩ : Fin P'.card) := by ext; exact htt'.symm
  rw [ht, ht']
  exact hmatch

/-! ### Theorem 1 -/

/-- **Theorem 1** (existence): under M-C and QC a coalition-proof PBE
partition (equivalently, a coalition-proof PBE) exists. -/
theorem one_existence (hMC : G.MC) (hQC : G.QC) :
    ∃ P : Partition G, P.IsCPPBEPartition := by
  obtain ⟨P, hP⟩ := exists_coePartition G hQC hMC
  exact ⟨P, hP.isCPPBEPartition⟩

/-- **Theorem 1(i)** (no halt): under M-C and QC*, a greedy partition exists
(the greedy algorithm never halts), and every greedy partition is a
coalition-proof PBE partition. -/
theorem one_noHalt (hMC : G.MC) (hQCs : G.QCStar) :
    (∃ P : Partition G, P.IsGreedy) ∧
      (∀ P : Partition G, P.IsGreedy → P.IsCPPBEPartition) := by
  have hQC : G.QC := qcStar_qc hQCs
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hP⟩ := exists_coePartition G hQC hMC
    exact ⟨P, hP.isGreedy⟩
  · intro P hg
    exact P.cppbe_characterization.mpr hg

/-- **Theorem 1(ii)** (essential uniqueness): under M-C, QC and genericity,
any two coalition-proof PBE partitions have the same length, cells, and
payoffs. -/
theorem one_unique (hMC : G.MC) (hQC : G.QC) (hGen : G.Generic)
    (P P' : Partition G) (hP : P.IsCPPBEPartition) (hP' : P'.IsCPPBEPartition) :
    P.card = P'.card ∧
      ∀ (t : Fin P.card) (t' : Fin P'.card), (t : ℕ) = (t' : ℕ) →
        P.C t = P'.C t' ∧ P.w t = P'.w t' := by
  have hPg : P.IsGreedy := P.cppbe_characterization.mp hP
  have hP'g : P'.IsGreedy := P'.cppbe_characterization.mp hP'
  exact coe_unique hQC hMC hGen P P'
    (greedy_isCOE hQC hMC hGen P hPg) (greedy_isCOE hQC hMC hGen P' hP'g)

end DisclosureGame

end CPD