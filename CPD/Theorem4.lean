import CPD.CheapTalk

/-!
# Theorem 4 and the Pure-Cheap-Talk Corollary

Formalizes Section 6.3 of the paper: under message completeness (M-C) and
cheap-talk copies (M-CT), a coalition-proof PBE exists, via the closure game
of `CheapTalk`. If in addition every message is available to every type, the
equilibrium is essentially unique and coincides with the Lipnowski–Ravid pure
cheap-talk value.

* `four_existence` — **Theorem 4**: M-C and M-CT together give existence of
  a coalition-proof PBE.
* `pure_ct` — **Corollary 1**: if every message is available to every type
  (`P(m) = Θ`) and `|𝓜| ≥ n := |Θ|`, a coalition-proof PBE exists and is
  essentially unique: every coalition-proof PBE partition is the single cell
  `Θ` with payoff `v̄^qc(μ⁰)`.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ### Generic transport helpers (fresh private copies) -/

lemma t4_strategy_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) (s : Strategy g₁) :
    ∃ s' : Strategy g₂, s'.evidence = s.evidence ∧
      ∀ m, s'.coalitionBelief m = s.coalitionBelief m := by
  subst h; exact ⟨s, rfl, fun _ => rfl⟩

private lemma t4_coalition_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) (K : g₁.Coalition) :
    ∃ K' : g₂.Coalition, K'.C = K.C ∧ K'.w = K.w := by
  subst h; exact ⟨K, rfl, rfl⟩

lemma t4_coalitionPayoffs_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) :
    g₁.coalitionPayoffs = g₂.coalitionPayoffs := by
  subst h; rfl

/-! ### Restriction inheritance -/

private lemma t4_restrict_MC {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hMC : G.MC) : (G.restrict S hne hsub).MC := by
  intros m hm m' hm';
  obtain ⟨ m'', hm'', hm''_eq ⟩ := hMC m ( DisclosureGame.restrictMsgSpace_subset hsub hm ) m' ( DisclosureGame.restrictMsgSpace_subset hsub hm' );
  refine' ⟨ m'', _, _ ⟩ <;> simp_all +decide [ DisclosureGame.restrictMsgSpace, DisclosureGame.canSend ];
  · simp_all +decide [ Finset.ext_iff, DisclosureGame.preimageFull ];
    obtain ⟨ a, ha, ha' ⟩ := hm; obtain ⟨ b, hb, hb' ⟩ := hm'; specialize hm''_eq a; simp_all +decide [ preimage ] ;
    grind;
  · unfold DisclosureGame.preimageFull at *; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
    simp_all +decide [ preimage ];
    grind +splitImp

private lemma t4_restrict_QC {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hQC : G.QC) : (G.restrict S hne hsub).QC := by
  intro μ hμ μ' hμ' l hl
  exact hQC μ (simplexOn_mono hsub hμ) μ' (simplexOn_mono hsub hμ') l hl

private lemma t4_restrict_MCT {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hMCT : G.MCT) : (G.restrict S hne hsub).MCT := by
  intros m hm
  have h_card_le : (G.Θ).card ≤ ((G.𝓜).filter (fun m' => G.canSend m' = G.canSend m)).card := by
    convert hMCT m _;
    exact G.restrictMsgSpace_subset hsub hm;
  refine' le_trans _ ( Finset.card_mono _ );
  convert h_card_le.trans' ( Finset.card_le_card hsub ) using 1;
  intro m' hm'
  simp_all +decide [ DisclosureGame.restrictMsgSpace, DisclosureGame.canSend ];
  simp_all +decide [ Finset.ext_iff, DisclosureGame.preimageFull ];
  simp_all +decide [ preimage ];
  simp_all +decide [ Finset.Nonempty ];
  exact ⟨ by obtain ⟨ a, ha, ha' ⟩ := hm; exact ⟨ a, ha, hm'.2 a ( hsub ha ) |>.2 ha' ⟩, fun a ha => hm'.2 a ( hsub ha ) ⟩

/-! ### Envelope bounds relating `v̄`, `v̲`, `v_min`, `v̄^qc` -/

private lemma t4_vMin_le_vlow {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.vMin ≤ G.vlow μ := by
  apply csInf_le;
  · exact G.vlow_lowerSemicontinuousOn.bddBelow_of_isCompact ( isCompact_simplexOn _ );
  · exact Set.mem_image_of_mem _ hμ

lemma t4_vbar_le_qcClosure {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.vbar μ ≤ G.qcClosure μ := by
  have h_qcClosure_ge_vbar : μ ∈ convexHull ℝ (G.vbarUpperLevel (G.vbar μ)) := by
    exact subset_convexHull ℝ _ ⟨ hμ, le_rfl ⟩;
  rw [ ← qcClosure_upperLevel ] at * ; aesop;

/-! ### Closure-game vs. original-game coalition payoffs -/

/-
Every coalition of `G|_S` is a coalition of `G^qc|_S` (the closure game has a
larger payoff correspondence), so its payoff is also a closure-game payoff.
-/
private lemma t4_coalitionPayoffs_subset {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ) :
    (G.restrict S hne hsub).coalitionPayoffs ⊆
      (G.closureGame.restrict S hne hsub).coalitionPayoffs := by
  rintro _ ⟨ K, rfl ⟩;
  refine' ⟨ ⟨ K.C, K.C_nonempty, K.C_subset, ⟨ K.σ.σ, K.σ.mem ⟩, K.exclusive, K.w, _ ⟩, rfl ⟩;
  intro m hm
  have hν_mem : K.σ.coalitionBelief m ∈ simplexOn G.Θ := by
    convert zeroExt_mem_simplex ( K.C_subset.trans hsub ) ( K.σ.belief_mem_simplex hm ) using 1;
  have hK_w : K.w ∈ Set.Icc (G.vlow (K.σ.coalitionBelief m)) (G.vbar (K.σ.coalitionBelief m)) := by
    have := K.payoff m hm;
    convert this using 1;
    exact DisclosureGame.V_eq_Icc hν_mem ▸ rfl;
  exact ⟨ t4_vMin_le_vlow hν_mem |> le_trans <| hK_w.1, t4_vbar_le_qcClosure hν_mem |> le_trans hK_w.2 ⟩

/-- The upper envelope of the restricted closure game is `v̄^qc`. -/
private lemma t4_closure_restrict_vbar {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    {ν : T → ℝ} (hν : ν ∈ simplexOn G.Θ) :
    (G.closureGame.restrict S hne hsub).vbar ν = G.qcClosure ν := by
  unfold DisclosureGame.vbar
  rw [restrict_V, closureGame_V, csSup_Icc (vMin_le_qcClosure hν)]

/-
The greatest closure-game payoff on `S` is realized by a coalition of `G|_S`
(via cheap-talk realization), under M-C and M-CT.
-/
private lemma t4_max_realizable {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hMC : G.MC) (hMCT : G.MCT) {w : ℝ}
    (hw : IsGreatest (G.closureGame.restrict S hne hsub).coalitionPayoffs w) :
    w ∈ (G.restrict S hne hsub).coalitionPayoffs := by
  have := hw.1;
  obtain ⟨ K, rfl ⟩ := this;
  -- By `isGreatest_coalitionPayoffs_iff` and `hw`, we get `IsGreatest poolingPayoffs w`, hence `w ∈ poolingPayoffs`.
  obtain ⟨mbar, hmbar⟩ : ∃ mbar ∈ (G.restrict S hne hsub).𝓜, K.w = (G.closureGame.restrict S hne hsub).vbar ((G.closureGame.restrict S hne hsub).condPrior ((G.closureGame.restrict S hne hsub).canSend mbar)) := by
    have h_pooling : IsGreatest (G.closureGame.restrict S hne hsub).poolingPayoffs K.w := by
      have h_pooling : (G.closureGame.restrict S hne hsub).QC := by
        grind +suggestions;
      convert isGreatest_coalitionPayoffs_iff h_pooling ( t4_restrict_MC hne hsub ( closureGame_MC hMC ) ) |>.1 hw;
    obtain ⟨ mbar, hmbar ⟩ := h_pooling.1;
    exact ⟨ mbar, hmbar.1, hmbar.2.symm ⟩;
  -- By `condPrior_canSend_restrict`, we have `(G.closureGame.restrict S hne hsub).condPrior ((G.closureGame.restrict S hne hsub).canSend mbar) = G.condPrior (G.canSend mbar ∩ S)`.
  have h_condPrior : (G.closureGame.restrict S hne hsub).condPrior ((G.closureGame.restrict S hne hsub).canSend mbar) = G.condPrior (G.canSend mbar ∩ S) := by
    apply DisclosureGame.Partition.condPrior_canSend_restrict;
  obtain ⟨ K0, hK0 ⟩ := ct_realization hMCT hne hsub ( show mbar ∈ G.restrictMsgSpace S from hmbar.1 );
  have h_vbar : (G.closureGame.restrict S hne hsub).vbar (G.condPrior (G.canSend mbar ∩ S)) = G.qcClosure (G.condPrior (G.canSend mbar ∩ S)) := by
    apply t4_closure_restrict_vbar;
    have h_condPrior_mem_simplex : ∀ {C : Finset T}, C.Nonempty → C ⊆ G.Θ → G.condPrior C ∈ simplexOn G.Θ := by
      intros C hC hC_sub
      have h_condPrior_mem_simplex : G.condPrior C ∈ simplexOn C := by
        exact G.condPrior_mem_simplex hC hC_sub;
      exact simplexOn_mono hC_sub h_condPrior_mem_simplex;
    apply h_condPrior_mem_simplex;
    · exact hK0.1 ▸ K0.C_nonempty;
    · exact Finset.inter_subset_right.trans hsub;
  exact ⟨ K0, by aesop ⟩

/-
The greatest coalition payoff agrees between `G|_S` and `G^qc|_S`.
-/
private lemma t4_isGreatest_closure_iff {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hMC : G.MC) (hMCT : G.MCT) {w : ℝ} :
    IsGreatest (G.restrict S hne hsub).coalitionPayoffs w ↔
      IsGreatest (G.closureGame.restrict S hne hsub).coalitionPayoffs w := by
  constructor <;> intro hw;
  · obtain ⟨hw₁, hw₂⟩ := hw;
    refine' ⟨ _, fun x hx => _ ⟩;
    · exact t4_coalitionPayoffs_subset hne hsub hw₁;
    · obtain ⟨wB, hwB⟩ : ∃ wB, IsGreatest (G.closureGame.restrict S hne hsub).coalitionPayoffs wB := by
        apply_rules [ isCompact_coalitionPayoffs, IsCompact.exists_isGreatest ];
        exact ⟨ _, hx ⟩;
      have := t4_max_realizable hne hsub hMC hMCT hwB;
      exact le_trans ( hwB.2 hx ) ( hw₂ this );
  · refine' ⟨ t4_max_realizable hne hsub hMC hMCT hw, fun x hx => _ ⟩;
    exact hw.2 ( t4_coalitionPayoffs_subset hne hsub hx )

/-! ### Maximal cell -/

private lemma t4_exists_isGreatest_cp (H : DisclosureGame T Msg) :
    ∃ w, IsGreatest H.coalitionPayoffs w := by
  apply_rules [ IsCompact.exists_isGreatest, DisclosureGame.isCompact_coalitionPayoffs,
    DisclosureGame.coalitionPayoffs_nonempty ]

/-
Maximal cell for a quasiconcave, message-complete game (re-derivation of the
Theorem 1 maximal-cell lemma using the public `merging` lemma).
-/
private lemma t4_qc_max_cell (H : DisclosureGame T Msg) (hQC : H.QC) (hMC : H.MC) :
    ∃ K : H.Coalition, IsGreatest H.coalitionPayoffs K.w ∧
      ∀ (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ) (w' : ℝ),
        IsGreatest (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs w' → w' ≤ K.w := by
  obtain ⟨K, hK⟩ : ∃ K : Coalition H, IsGreatest H.coalitionPayoffs K.w ∧ ∀ K' : Coalition H, K'.w = K.w → K'.C.card ≤ K.C.card := by
    obtain ⟨w, hw⟩ : ∃ w, IsGreatest H.coalitionPayoffs w := by
      apply t4_exists_isGreatest_cp;
    obtain ⟨K, hK⟩ : ∃ K : Coalition H, K.w = w ∧ ∀ K' : Coalition H, K'.w = w → K'.C.card ≤ K.C.card := by
      apply Classical.byContradiction
      intro h_no_max_card;
      have h_finite : Set.Finite {K : Finset T | ∃ K' : Coalition H, K'.w = w ∧ K = K'.C} := by
        exact Set.toFinite _;
      have h_max_card : ∃ K ∈ {K : Finset T | ∃ K' : Coalition H, K'.w = w ∧ K = K'.C}, ∀ K' ∈ {K : Finset T | ∃ K' : Coalition H, K'.w = w ∧ K = K'.C}, K.card ≥ K'.card := by
        apply_rules [ Set.exists_max_image ];
        exact ⟨ _, ⟨ hw.1.choose, hw.1.choose_spec, rfl ⟩ ⟩;
      obtain ⟨ K, ⟨ K', hK', rfl ⟩, hK ⟩ := h_max_card; exact h_no_max_card ⟨ K', hK', fun K'' hK'' => hK _ ⟨ K'', hK'', rfl ⟩ ⟩ ;
    exact ⟨ K, by simpa only [ hK.1 ] using hw, by simpa only [ hK.1 ] using hK.2 ⟩;
  refine' ⟨ K, hK.1, _ ⟩;
  intro hne hsub w' hw'
  by_contra hlt;
  obtain ⟨Kt, hKt⟩ : ∃ Kt : Coalition H, K.C ⊂ Kt.C ∧ Kt.w = K.w := by
    have := @merging T Msg;
    obtain ⟨K', hK'⟩ : ∃ K' : Coalition (H.restrict H.Θ H.Θ_nonempty subset_rfl), K'.C = K.C ∧ K'.w = K.w := by
      grind +suggestions;
    contrapose! this;
    grind +suggestions;
  exact not_lt_of_ge ( hK.2 Kt hKt.2 ) ( Finset.card_lt_card hKt.1 )

/-- A maximal coalition of the closure game has payoff `v̄^qc` of its cell. -/
private lemma t4_closure_attains (H : DisclosureGame T Msg) (hMC : H.MC)
    (Kq : H.closureGame.Coalition) (hKqmax : IsGreatest H.closureGame.coalitionPayoffs Kq.w) :
    Kq.w = H.qcClosure (H.condPrior Kq.C) := by
  have hsub : Kq.C ⊆ H.Θ := Kq.C_subset
  have hmem : H.condPrior Kq.C ∈ simplexOn H.Θ :=
    simplexOn_mono hsub (H.condPrior_mem_simplex Kq.C_nonempty hsub)
  have hattains := coalition_attains_max (closureGame_QC) (closureGame_MC hMC) Kq hKqmax
  rw [← hattains]
  convert closureGame_vbar hmem using 2

/-
**Maximal cell under M-C and M-CT.** There is a coalition attaining the
greatest coalition payoff of `H` whose removal cannot raise the residual maximum.
-/
private lemma t4_g_max_cell (H : DisclosureGame T Msg) (hMC : H.MC) (hMCT : H.MCT) :
    ∃ K : H.Coalition, IsGreatest H.coalitionPayoffs K.w ∧
      ∀ (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ) (w' : ℝ),
        IsGreatest (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs w' → w' ≤ K.w := by
  obtain ⟨Kq, hKqmax, hqbound⟩ := t4_qc_max_cell H.closureGame (closureGame_QC) (closureGame_MC hMC);
  obtain ⟨m, hm, hcs⟩ := (pooling_dominance (DisclosureGame.closureGame_QC) (DisclosureGame.closureGame_MC hMC) Kq).1;
  obtain ⟨ K0, hK0C, hK0w ⟩ := CPD.DisclosureGame.ct_realization hMCT H.Θ_nonempty ( subset_rfl ) ( show m ∈ H.restrictMsgSpace H.Θ from by
                                                                                                            simp +decide [ DisclosureGame.restrictMsgSpace ];
                                                                                                            have := H.cover; simp_all +decide [ Set.ext_iff ] ; );
  obtain ⟨K, hKC, hKw⟩ := t4_coalition_of_eq (restrict_self : H.restrict H.Θ H.Θ_nonempty subset_rfl = H) K0; use K; simp_all +decide [ Finset.inter_eq_left.mpr ( show H.canSend m ⊆ H.Θ from Finset.filter_subset _ _ ) ] ;
  refine' ⟨ _, _ ⟩;
  · convert t4_isGreatest_closure_iff H.Θ_nonempty ( subset_rfl ) hMC hMCT |>.mpr _ using 1;
    · exact t4_coalitionPayoffs_of_eq ( by simp +decide [ restrict_self ] );
    · convert t4_coalitionPayoffs_of_eq ( restrict_self : H.closureGame.restrict H.Θ H.Θ_nonempty subset_rfl = H.closureGame ) ▸ hKqmax using 1;
      rw [ t4_closure_attains H hMC Kq hKqmax, hcs.symm ];
      rw [ Finset.inter_eq_left.mpr ( show H.canSend m ⊆ H.Θ from Finset.filter_subset _ _ ) ];
  · intro hne w' hw'
    have hKqw : Kq.w = H.qcClosure (H.condPrior Kq.C) := by
      exact t4_closure_attains H hMC Kq hKqmax
    have hKqw' : K.w = H.qcClosure (H.condPrior (Kq.C ∩ H.Θ)) := by
      exact hKw
    have hKqw'' : Kq.w = K.w := by
      rw [ hKqw, hKqw', show Kq.C ∩ H.Θ = Kq.C from Finset.inter_eq_left.mpr <| by
                          exact hcs ▸ Finset.filter_subset _ _ ]
    have hKqw''' : w' ≤ K.w := by
      convert hqbound hne w' _ using 1;
      · exact hKqw''.symm;
      · convert t4_isGreatest_closure_iff ( show ( H.Θ \ Kq.C ).Nonempty from hne ) ( show ( H.Θ \ Kq.C ) ⊆ H.Θ from Finset.sdiff_subset ) ( show H.MC from hMC ) ( show H.MCT from hMCT ) |>.1 hw' using 1
    exact hKqw'''.trans (by
    exact hKqw'.le)

/-! ### Generic COE construction (fresh private copies, no QC needed) -/

lemma t4_single_cell_coe (H : DisclosureGame T Msg) (K : H.Coalition)
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
  convert t4_coalitionPayoffs_of_eq _;
  convert DisclosureGame.restrict_self;
  ext; simp +decide [ thetaStep ] ;
  exact ⟨ fun h => K.C_subset h, fun h => Classical.not_not.1 fun h' => Finset.notMem_empty _ ( hempty ▸ Finset.mem_sdiff.2 ⟨ h, h' ⟩ ) ⟩

lemma t4_exists_prependP (H : DisclosureGame T Msg) (K : H.Coalition)
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
  exact fun t => Fin.cases K.σ ( fun j => ( t4_strategy_of_eq ( restrict_restrict hne hsub ( P'.C_nonempty j ) ( P'.C_subset j ) ) ( P'.σ j ) ).choose ) t;
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

lemma t4_prepend_isCOE (H : DisclosureGame T Msg) (K : H.Coalition)
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
    exact t4_coalitionPayoffs_of_eq ( restrict_self );
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

lemma t4_prepend_coe (H : DisclosureGame T Msg) (K : H.Coalition)
    (hmax : IsGreatest H.coalitionPayoffs K.w)
    (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ)
    (hbound : ∀ w', IsGreatest (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs w' → w' ≤ K.w)
    (P' : Partition (H.restrict (H.Θ \ K.C) hne hsub)) (hP' : P'.IsCOE) :
    ∃ P : Partition H, P.IsCOE := by
  obtain ⟨P, hcard, h0, hsucc⟩ := t4_exists_prependP H K hne hsub P'
  exact ⟨P, t4_prepend_isCOE H K hmax hne hsub hbound P' hP' P hcard h0 hsucc⟩

/-- **Existence of a COE partition under M-C and M-CT.** -/
private lemma t4_exists_coe (H : DisclosureGame T Msg) (hMC : H.MC) (hMCT : H.MCT) :
    ∃ P : Partition H, P.IsCOE := by
  induction' n : H.Θ.card using Nat.strong_induction_on with k ih generalizing H;
  obtain ⟨ K, hKmax, hbound ⟩ := t4_g_max_cell H hMC hMCT;
  by_cases hempty : H.Θ \ K.C = ∅;
  · exact t4_single_cell_coe H K hempty hKmax;
  · obtain ⟨hne, hsub⟩ : (H.Θ \ K.C).Nonempty ∧ (H.Θ \ K.C) ⊆ H.Θ :=
      ⟨ Finset.nonempty_of_ne_empty hempty, Finset.sdiff_subset ⟩;
    have hcard : (H.restrict (H.Θ \ K.C) hne hsub).Θ.card < k := by
      convert Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ hsub, ?_ ⟩ ) using 1;
      · exact n.symm;
      · simp_all +decide [ Finset.ext_iff ];
        exact Finset.not_disjoint_iff.mpr ⟨ _, K.C_nonempty.choose_spec |> fun h => Finset.mem_of_subset K.C_subset h, K.C_nonempty.choose_spec ⟩;
    exact ih _ hcard _ ( t4_restrict_MC hne hsub hMC ) ( t4_restrict_MCT hne hsub hMCT ) rfl
      |> fun ⟨ P, hP ⟩ => t4_prepend_coe H K hKmax hne hsub ( hbound hne hsub ) P hP

/-- **Theorem 4.** If the message mapping is complete (M-C) and has cheap-talk
copies (M-CT), then a coalition-proof PBE exists. -/
theorem four_existence (hMC : G.MC) (hMCT : G.MCT) :
    ∃ P : Partition G, P.IsCPPBEPartition := by
  obtain ⟨P, hP⟩ := t4_exists_coe G hMC hMCT
  exact ⟨P, hP.isCPPBEPartition⟩

/-! ### The pure-cheap-talk corollary -/

private lemma t4_pure_MC (hpure : ∀ m ∈ G.𝓜, G.canSend m = G.Θ) : G.MC := by
  intro m hm m' hm'
  use m;
  grind

private lemma t4_pure_MCT (hpure : ∀ m ∈ G.𝓜, G.canSend m = G.Θ)
    (hcard : G.Θ.card ≤ G.𝓜.card) : G.MCT := by
  refine' fun m hm => le_trans hcard _;
  rw [ Finset.filter_true_of_mem fun m' hm' => by rw [ hpure m' hm', hpure m hm ] ]

/-
Under purity, every type can send every message: `M θ = 𝓜`.
-/
private lemma t4_pure_M_eq (hpure : ∀ m ∈ G.𝓜, G.canSend m = G.Θ) {θ : T} (hθ : θ ∈ G.Θ) :
    G.M θ = G.𝓜 := by
  refine' Finset.Subset.antisymm _ _;
  · exact G.M_subset θ hθ;
  · intro m hm; specialize hpure m hm; simp_all +decide [ DisclosureGame.canSend, DisclosureGame.preimageFull ] ;
    replace hpure := Finset.ext_iff.mp hpure θ; simp_all +decide [ preimage ] ;
    grind

/-
Under purity, every coalition's cell is all of `Θ` (since `M θ = 𝓜`, the
evidence preimage is the whole type space).
-/
private lemma t4_pure_coalition_C (hpure : ∀ m ∈ G.𝓜, G.canSend m = G.Θ)
    (K : G.Coalition) : K.C = G.Θ := by
  refine' Finset.Subset.antisymm K.C_subset _;
  intro θ hθ;
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ ∈ K.σ.evidence, m₀ ∈ G.𝓜 := by
    have := K.preimage_eq;
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ G.preimageSetFull K.σ.evidence, True := by
      exact ⟨ Classical.choose ( K.C_nonempty ), this.symm ▸ Classical.choose_spec ( K.C_nonempty ), trivial ⟩;
    obtain ⟨ m₀, hm₀ ⟩ := mem_preimageSet.mp hθ₀.1;
    exact ⟨ hm₀.choose, hm₀.choose_spec.2, G.M_subset _ m₀ hm₀.choose_spec.1 ⟩;
  have hpre := K.preimage_eq;
  have hm₀θ : m₀ ∈ G.M θ := by
    have hθ_can : θ ∈ G.canSend m₀ := by rw [ hpure m₀ hm₀.2 ]; exact hθ;
    simp only [ DisclosureGame.canSend, DisclosureGame.preimageFull ] at hθ_can;
    obtain ⟨-, m', hm'⟩ := mem_preimage.mp hθ_can;
    have hm'_eq : m' = m₀ := Finset.mem_singleton.mp ( Finset.mem_inter.mp hm' ).2;
    exact hm'_eq ▸ ( Finset.mem_inter.mp hm' ).1;
  rw [ ← hpre ];
  exact mem_preimageSet.mpr ⟨ hθ, ⟨ m₀, Finset.mem_coe.mpr hm₀θ, hm₀.1 ⟩ ⟩

/-
Under purity, the value `v̄^qc(μ⁰)` is the greatest coalition payoff.
-/
private lemma t4_pure_isGreatest (hpure : ∀ m ∈ G.𝓜, G.canSend m = G.Θ)
    (hcard : G.Θ.card ≤ G.𝓜.card) :
    IsGreatest G.coalitionPayoffs (G.qcClosure G.μ0) := by
  constructor;
  · obtain ⟨m₀, hm₀⟩ : ∃ m₀ ∈ G.𝓜, True := by
      exact Exists.elim ( Finset.card_pos.mp ( pos_of_gt ( lt_of_lt_of_le ( Finset.card_pos.mpr G.Θ_nonempty ) hcard ) ) ) fun m hm => ⟨ m, hm, trivial ⟩;
    obtain ⟨K0, hK0⟩ : ∃ K0 : (G.restrict G.Θ G.Θ_nonempty (subset_refl G.Θ)).Coalition, K0.w = G.qcClosure G.μ0 := by
      have := ct_realization ( t4_pure_MCT hpure hcard ) G.Θ_nonempty ( subset_refl G.Θ ) ( show m₀ ∈ G.restrictMsgSpace G.Θ from ?_ );
      · grind +suggestions;
      · simp +decide [ DisclosureGame.restrictMsgSpace, hm₀.1 ];
        have := G.cover; simp_all +decide [ Set.ext_iff ] ;
    obtain ⟨K, hK⟩ : ∃ K : Coalition G, K.C = K0.C ∧ K.w = K0.w := by
      convert t4_coalition_of_eq ( restrict_self : G.restrict G.Θ G.Θ_nonempty ( subset_refl G.Θ ) = G ) K0 using 1;
    exact ⟨ K, by aesop ⟩;
  · intro x hx;
    obtain ⟨K', hK'⟩ := hx;
    -- By `t4_pure_coalition_C hpure K'`, `K'.C = G.Θ`.
    have hK'_C : K'.C = G.Θ := by
      exact t4_pure_coalition_C hpure K';
    -- Transport `K'` along `restrict_self.symm` via `t4_coalition_of_eq` to `K'' : Coalition (G.restrict G.Θ G.Θ_nonempty subset_rfl)` with `K''.C = K'.C = G.Θ` and `K''.w = K'.w`.
    obtain ⟨K'', hK''⟩ : ∃ K'' : (G.restrict G.Θ G.Θ_nonempty subset_rfl).Coalition, K''.C = K'.C ∧ K''.w = K'.w := by
      grind +suggestions;
    have := coalition_w_le_qcClosure G.Θ_nonempty ( subset_rfl ) K'';
    rw [ hK''.1, hK'_C ] at this; rw [ DisclosureGame.condPrior_self ] at this; linarith;

/-
Under purity, every cell of a partition equals its residual type set.
-/
private lemma t4_pure_cell_eq_step (hpure : ∀ m ∈ G.𝓜, G.canSend m = G.Θ)
    (P : Partition G) (t : Fin P.card) : P.C t = thetaStep P.C t := by
  refine' subset_antisymm _ _;
  · exact Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_rfl ⟩ );
  · have := P.exclusive t; simp_all +decide [ DisclosureGame.preimageSet ] ;
    refine' fun θ hθ => this ( Finset.mem_filter.mpr ⟨ hθ, _ ⟩ );
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ P.C t, θ₀ ∈ G.preimageSetFull (P.σ t).evidence := by
      have h_subset : P.C t ⊆ G.preimageSetFull (P.σ t).evidence := by
        apply coalitionStrategy_subset_preimage (P.C_nonempty t) (P.C_subset t) (P.σ t);
      exact Exists.elim ( P.C_nonempty t ) fun x hx => ⟨ x, hx, h_subset hx ⟩;
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ ∈ (P.σ t).evidence, m₀ ∈ G.M θ₀ := by
      simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.mem_preimageSet ];
      exact ⟨ hθ₀.2.2.choose, hθ₀.2.2.choose_spec.2, hθ₀.2.2.choose_spec.1 ⟩;
    have hMθ : G.M θ = G.𝓜 := by
      apply t4_pure_M_eq;
      · exact hpure;
      · exact P.thetaStep_subset t hθ;
    exact ⟨ m₀, hMθ.symm ▸ G.M_subset _ ( P.C_subset _ hθ₀.1 ) hm₀.2, hm₀.1 ⟩

private lemma t4_pure_card_one (hpure : ∀ m ∈ G.𝓜, G.canSend m = G.Θ)
    (P : Partition G) : P.card = 1 := by
  by_contra h_contra; have h_card_ge_two : 2 ≤ P.card := by
    rcases n : P.card with ( _ | _ | n ) <;> simp_all +decide;
    cases P;
    cases ‹ℕ› <;> simp_all +decide;
    exact absurd ( ‹G.Θ ⊆ Finset.univ.biUnion _› ( Classical.choose_spec G.Θ_nonempty ) ) ( by simp +decide [ Finset.notMem_empty ] );
  -- By `t4_pure_cell_eq_step hpure P i`, `P.C i = thetaStep P.C i = (Finset.univ.filter (fun s => i ≤ s)).biUnion P.C`. Since `i = 0 ≤ j`, `P.C j ⊆ P.C i` (via `Finset.subset_biUnion_of_mem`).
  have h_subset : P.C (Fin.mk 1 (by omega)) ⊆ P.C (Fin.mk 0 (by omega)) := by
    have h_subset : P.C (Fin.mk 1 (by omega)) ⊆ thetaStep P.C (Fin.mk 0 (by omega)) := by
      exact Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simp +decide ⟩ );
    convert h_subset using 1;
    convert t4_pure_cell_eq_step hpure P ⟨ 0, by linarith ⟩ using 1;
  exact Finset.disjoint_left.mp ( P.C_disjoint _ _ ( by simp +decide ) ) ( P.C_nonempty _ |> Classical.choose_spec ) ( h_subset ( P.C_nonempty _ |> Classical.choose_spec ) )

/-- **Corollary 1** (pure cheap talk). If `P(m) = Θ` for every `m` and
`|𝓜| ≥ n := |Θ|`, then a coalition-proof PBE exists and is essentially
unique: every coalition-proof PBE partition is the single cell `Θ` with
payoff `v̄^qc(μ⁰)`. -/
theorem pure_ct (hpure : ∀ m ∈ G.𝓜, G.canSend m = G.Θ) (hcard : G.Θ.card ≤ G.𝓜.card) :
    (∃ P : Partition G, P.IsCPPBEPartition) ∧
      (∀ P : Partition G, P.IsCPPBEPartition →
        P.card = 1 ∧ (∀ t, P.C t = G.Θ) ∧ (∀ t, P.w t = G.qcClosure G.μ0)) := by
  refine' ⟨ _, fun P hP => _ ⟩;
  · exact ⟨_, (four_existence (t4_pure_MC hpure) (t4_pure_MCT hpure hcard)).choose_spec⟩
  · -- By definition of `IsCPPBEPartition`, we know that `P` is greedy.
    have hP_greedy : P.IsGreedy := by
      exact P.isGreedy_of_isCPPBEPartition hP;
    have hP_card : P.card = 1 := by
      apply t4_pure_card_one hpure P;
    refine' ⟨ hP_card, _, _ ⟩;
    · intro t;
      have hP_cover : G.Θ = Finset.univ.biUnion P.C := by
        exact P.cover_eq;
      convert t4_pure_cell_eq_step hpure P t;
      unfold thetaStep; simp +decide [ Finset.ext_iff ] ;
      grind;
    · intro t
      have hP_stepPayoffs : P.stepPayoffs t = G.coalitionPayoffs := by
        convert t4_coalitionPayoffs_of_eq _;
        convert restrict_self;
        convert P.cover_eq.symm using 1;
        ext; simp [thetaStep];
        grind
      have hP_greedyConstraint : P.greedyConstraint t = {w | w ∈ G.coalitionPayoffs ∧ P.greedyLower t ≤ w} := by
        simp +decide [ Partition.greedyConstraint, hP_stepPayoffs ];
        grind
      have hP_greedyLower : P.greedyLower t ≤ G.qcClosure G.μ0 := by
        have hP_stepMax : P.stepMax t = G.qcClosure G.μ0 := by
          have := t4_pure_isGreatest hpure hcard;
          exact IsGreatest.csSup_eq ( by simpa only [ hP_stepPayoffs ] using this );
        exact hP_stepMax ▸ P.greedyLower_le_stepMax t
      have hP_greedyMax : IsGreatest (P.stepPayoffs t) (G.qcClosure G.μ0) := by
        convert t4_pure_isGreatest hpure hcard using 1
      have hP_greedyMax_eq : P.w t = G.qcClosure G.μ0 := by
        apply IsGreatest.unique (hP_greedy t);
        simp_all +decide [ IsGreatest, mem_upperBounds ]
      exact hP_greedyMax_eq

end DisclosureGame

end CPD
