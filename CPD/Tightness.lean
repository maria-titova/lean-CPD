import CPD.CheapTalk
import CPD.Betweenness

/-!
# Non-Existence and the Two-Type Existence Theorem

Formalizes Proposition 5 and Theorem 6, which delimit the existence theory.
First, a minimal three-type non-existence example: a
disclosure game whose payoff correspondence is single-valued, concave, and
continuous — and which still satisfies cheap-talk copies (M-CT) once
augmented with copies of each message — yet admits **no** coalition-proof
PBE. Second, the two-type existence theorem: whenever `|Θ| = 2`, a
coalition-proof PBE always exists, so the non-existence example is minimal
in the number of types.

The example games are pinned down by existential statements listing their
defining fields explicitly, since checking the disclosure-game envelope
axioms for an explicitly given payoff correspondence `V` is routine but
lengthy proof work.

* `nonexistence` — the base three-type example, no coalition-proof PBE.
* `nonexistence_mct` — the same non-existence persists once the message
  mapping is augmented with cheap-talk copies (M-CT).
* `binary_existence` — `|Θ| = 2` always admits a coalition-proof PBE.
-/

open Set Topology
open scoped Classical

namespace CPD

/-- The value function of the non-existence example (types `0,1,2` stand for
the paper's `1,2,3`): `v(μ) = min{μ₁ + 0.9 μ₃, −0.1 μ₁ + 1.1 μ₂ + 0.9 μ₃}` —
a minimum of two affine maps, hence concave and continuous. -/
noncomputable def nonexistenceV (μ : Fin 3 → ℝ) : ℝ :=
  min (μ 0 + 0.9 * μ 2) (-0.1 * μ 0 + 1.1 * μ 1 + 0.9 * μ 2)

/-- `nonexistenceV` is continuous (a min of two affine maps). -/
lemma continuous_nonexistenceV : Continuous nonexistenceV := by
  unfold nonexistenceV
  fun_prop

/-- Upper hemicontinuity of the single-valued correspondence `μ ↦ {f μ}` for a
continuous `f`. -/
lemma uhc_singleton_of_continuous {T : Type*} [Fintype T]
    (f : (T → ℝ) → ℝ) (hf : Continuous f) (D : Set (T → ℝ)) :
    UpperHemicontinuousOn (fun μ => ({f μ} : Set ℝ)) D := by
  intro μ hμ U hU hsub
  have hmem : f μ ∈ U := hsub rfl
  refine ⟨f ⁻¹' U, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds ((hU.preimage hf).mem_nhds hmem)
  · intro μ' hμ'
    simpa using hμ'

namespace DisclosureGame

/-- **The non-existence example game** (base game, two messages `a = 0`, `b = 1`). -/
noncomputable def nonexistenceGame : DisclosureGame (Fin 3) (Fin 2) where
  Θ := Finset.univ
  𝓜 := Finset.univ
  Θ_nonempty := Finset.univ_nonempty
  𝓜_nonempty := Finset.univ_nonempty
  M := fun θ => if θ = 0 then {0, 1} else if θ = 1 then {0} else {1}
  M_subset := by intro θ _ x _; exact Finset.mem_univ x
  M_nonempty := by intro θ _; fin_cases θ <;> decide
  cover := by
    ext m; simp only [Finset.coe_univ, Set.mem_univ, true_iff, Set.mem_iUnion,
      Finset.mem_coe, exists_prop]
    fin_cases m
    · exact ⟨0, Finset.mem_univ _, by decide⟩
    · exact ⟨0, Finset.mem_univ _, by decide⟩
  μ0 := fun _ => 1 / 3
  μ0_mem := by
    refine ⟨fun a => by norm_num, ?_, fun a ha => absurd (Finset.mem_univ a) ha⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  μ0_fullSupport := by intro θ _; norm_num
  V := fun μ => {nonexistenceV μ}
  V_nonempty := fun μ _ => ⟨_, rfl⟩
  V_isCompact := fun μ _ => isCompact_singleton
  V_ordConnected := fun μ _ => ordConnected_singleton
  V_uhc := uhc_singleton_of_continuous nonexistenceV continuous_nonexistenceV _

@[simp] lemma nonexistenceGame_Θ : nonexistenceGame.Θ = Finset.univ := rfl
@[simp] lemma nonexistenceGame_𝓜 : nonexistenceGame.𝓜 = Finset.univ := rfl
@[simp] lemma nonexistenceGame_μ0 (θ : Fin 3) : nonexistenceGame.μ0 θ = 1 / 3 := rfl
@[simp] lemma nonexistenceGame_V (μ : Fin 3 → ℝ) :
    nonexistenceGame.V μ = {nonexistenceV μ} := rfl

lemma nonexistenceGame_M0 : nonexistenceGame.M 0 = ({0, 1} : Finset (Fin 2)) := rfl
lemma nonexistenceGame_M1 : nonexistenceGame.M 1 = ({0} : Finset (Fin 2)) := rfl
lemma nonexistenceGame_M2 : nonexistenceGame.M 2 = ({1} : Finset (Fin 2)) := rfl

/-- `v̄ = nonexistenceV` for the example game. -/
@[simp] lemma nonexistenceGame_vbar (μ : Fin 3 → ℝ) :
    nonexistenceGame.vbar μ = nonexistenceV μ := by
  simp [DisclosureGame.vbar]

/-- `v̲ = nonexistenceV` for the example game. -/
@[simp] lemma nonexistenceGame_vlow (μ : Fin 3 → ℝ) :
    nonexistenceGame.vlow μ = nonexistenceV μ := by
  simp [DisclosureGame.vlow]

/-! ### Coalition analysis of the base example -/

/-- On the edge `μ₂ = 0`, the value is `min{x, 1.1-1.2x} ≤ 1/2`. -/
private lemma nonexistenceV_le_half_edge2 {μ : Fin 3 → ℝ}
    (hμ : μ ∈ simplexOn (Finset.univ : Finset (Fin 3))) (h2 : μ 2 = 0) :
    nonexistenceV μ ≤ 1 / 2 := by
  have hsum : μ 0 + μ 1 + μ 2 = 1 := by
    have := hμ.2.1; rwa [Fin.sum_univ_three] at this
  have h0 : 0 ≤ μ 0 := hμ.1 0
  have h1 : 0 ≤ μ 1 := hμ.1 1
  unfold nonexistenceV
  rw [min_le_iff]
  rcases le_or_gt (μ 0) (1 / 2) with h | h
  · left; rw [h2]; nlinarith
  · right; rw [h2]; nlinarith

/-
`P(a) = {0,1}`.
-/
private lemma ne_canSend0 : nonexistenceGame.canSend 0 = ({0, 1} : Finset (Fin 3)) := by
  ext θ; fin_cases θ <;> simp +decide [ DisclosureGame.canSend, DisclosureGame.preimageFull, preimage, nonexistenceGame ];

/-
`P(b) = {0,2}`.
-/
private lemma ne_canSend1 : nonexistenceGame.canSend 1 = ({0, 2} : Finset (Fin 3)) := by
  ext θ; fin_cases θ <;> simp +decide [ DisclosureGame.canSend, DisclosureGame.preimageFull, preimage, nonexistenceGame ];

/-
`v(μ⁰_{0,1}) = 1/2`.
-/
private lemma ne_vlow_condPrior01 :
    nonexistenceGame.vlow (nonexistenceGame.condPrior ({0, 1} : Finset (Fin 3))) = 1 / 2 := by
  convert nonexistenceGame_vlow _ using 1;
  unfold nonexistenceV; norm_num [ nonexistenceGame ];
  simp +decide [ DisclosureGame.condPrior, DisclosureGame.priorMeasure ]; ring; norm_num;

/-
`v(μ⁰_{0,2}) = 2/5`.
-/
private lemma ne_vlow_condPrior02 :
    nonexistenceGame.vlow (nonexistenceGame.condPrior ({0, 2} : Finset (Fin 3))) = 2 / 5 := by
  unfold nonexistenceGame nonexistenceV;
  unfold DisclosureGame.vlow DisclosureGame.condPrior; norm_num [ Fin.sum_univ_three, DisclosureGame.priorMeasure ];
  simp +decide; norm_num

/-
A coalition that never uses message `a` (`0`) pools `{0,2}` on `b`, paying `2/5`.
-/
private lemma coalition_bOnly_w (K : Coalition nonexistenceGame)
    (h0 : (0 : Fin 2) ∉ K.σ.evidence) : K.w = 2 / 5 := by
  convert Set.mem_singleton_iff.mp ( K.payoff 1 _ ) using 1;
  · unfold nonexistenceV; ring;
    -- By definition of $K$, we know that $K.C = \{0, 2\}$.
    have hC : K.C = {0, 2} := by
      have h_evidence : K.σ.evidence = {1} := by
        apply Set.eq_singleton_iff_nonempty_unique_mem.mpr;
        obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ K.C, θ₀ ∈ nonexistenceGame.preimageSetFull K.σ.evidence := by
          exact ⟨ _, K.C_nonempty.choose_spec, K.preimage_eq.symm ▸ K.C_nonempty.choose_spec ⟩;
        simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
        exact hθ₀.2.mono fun x hx => hx.2;
      rw [ ← K.preimage_eq ];
      simp +decide [ h_evidence, DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
    have h_sigma_0_1 : K.σ.σ 0 1 = 1 := by
      have h_sigma0 : K.σ.σ 0 0 = 0 := by
        contrapose! h0; simp_all +decide [ Strategy.evidence, Strategy.msgSupport ];
        exact Or.inl ( lt_of_le_of_ne ( K.σ.mem 0 ( by simp +decide [ hC ] ) |>.1 0 ) ( Ne.symm h0 ) );
      have := K.σ.mem 0 ( by simp +decide [ hC ] ); simp_all +decide [ simplexOn ];
    have h_sigma_2_1 : K.σ.σ 2 1 = 1 := by
      have h_sigma_2_1 : K.σ.σ 2 ∈ simplexOn (nonexistenceGame.M 2) := by
        exact K.σ.mem 2 ( by simp +decide [ hC ] );
      have := h_sigma_2_1.2.1; simp_all +decide [ Fin.sum_univ_three ];
    unfold Strategy.coalitionBelief; norm_num [ h_sigma_0_1, h_sigma_2_1, hC ];
    unfold Strategy.belief Strategy.onPathProb; norm_num [ Fin.sum_univ_three, h_sigma_0_1, h_sigma_2_1, hC ];
    unfold zeroExt; norm_num [ Finset.sum_pair, h_sigma_0_1, h_sigma_2_1, hC ];
    simp +decide [ Finset.sum_pair, h_sigma_0_1, h_sigma_2_1, DisclosureGame.condPrior, DisclosureGame.priorMeasure ]; ring; norm_num;
  · have h_evidence : K.σ.evidence.Nonempty := by
      obtain ⟨ θ, hθ ⟩ := K.C_nonempty;
      have := coalitionStrategy_subset_preimage ( hne := K.C_nonempty ) ( hsub := K.C_subset ) ( s := K.σ ); simp_all +decide [ DisclosureGame.preimageSetFull ];
      have := this hθ; simp_all +decide [ DisclosureGame.preimageSet ];
      exact this.mono fun x hx => hx.2;
    grind +suggestions

/-
Every coalition of the base example pays at most `1/2`.
-/
private lemma coalition_w_le_half (K : Coalition nonexistenceGame) : K.w ≤ 1 / 2 := by
  by_cases h0 : (0 : Fin 2) ∈ K.σ.evidence;
  · have h_payoff : K.w = nonexistenceV (zeroExt K.C (K.σ.belief 0)) := by
      convert Set.mem_singleton_iff.mp ( K.payoff 0 h0 ) using 1;
    refine' h_payoff ▸ nonexistenceV_le_half_edge2 _ _;
    · apply_rules [ DisclosureGame.zeroExt_mem_simplex, K.σ.belief_mem_simplex ];
      exact Finset.subset_univ _;
    · by_cases h2 : 2 ∈ K.C <;> simp_all +decide [ zeroExt ];
      have := K.σ.mem 2 ( by simp +decide [ h2 ] ); simp_all +decide [ simplexOn ];
      unfold Strategy.belief; simp +decide [ this, h2 ];
  · rw [ coalition_bOnly_w K h0 ]; norm_num

/-- The payoff `1/2` is attainable (pool `{0,1}` on message `a`). -/
private lemma half_mem_coalitionPayoffs :
    (1 : ℝ) / 2 ∈ nonexistenceGame.coalitionPayoffs := by
  have h := Partition.vlow_condPrior_canSend_mem_coalitionPayoffs nonexistenceGame
    (m := (0 : Fin 2)) (by simp)
  rw [ne_canSend0, ne_vlow_condPrior01] at h
  exact h

/-
The only coalition paying `1/2` has cell `{0,1}`.
-/
-- Larger heartbeat budget: this finite-case coalition analysis is elaboration-heavy.
set_option maxHeartbeats 1600000 in
private lemma coalition_w_half_cell (K : Coalition nonexistenceGame)
    (hw : K.w = 1 / 2) : K.C = ({0, 1} : Finset (Fin 3)) := by
  by_cases h0 : (0 : Fin 2) ∈ K.σ.evidence;
  · have h1 : 1 ∈ K.C := by
      have h1 : K.w = nonexistenceV (zeroExt K.C (K.σ.coalitionBelief 0)) := by
        convert Set.mem_singleton_iff.mp ( K.payoff 0 h0 ) using 1;
        congr! 1;
        ext θ; simp [Strategy.coalitionBelief];
        unfold zeroExt; aesop;
      have h1 : zeroExt K.C (K.σ.coalitionBelief 0) 2 = 0 := by
        unfold zeroExt; simp +decide [ h0, Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
        unfold zeroExt; simp +decide [ h0, Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
        have := K.σ.mem 2; simp_all +decide [ simplexOn ];
      have h1 : zeroExt K.C (K.σ.coalitionBelief 0) 0 = 1 / 2 ∧ zeroExt K.C (K.σ.coalitionBelief 0) 1 = 1 / 2 := by
        unfold nonexistenceV at *; norm_num at *;
        have h1 : zeroExt K.C (K.σ.coalitionBelief 0) 0 + zeroExt K.C (K.σ.coalitionBelief 0) 1 + zeroExt K.C (K.σ.coalitionBelief 0) 2 = 1 := by
          have h1 : zeroExt K.C (K.σ.coalitionBelief 0) ∈ simplexOn (Finset.univ : Finset (Fin 3)) := by
            apply_rules [ DisclosureGame.zeroExt_mem_simplex, K.σ.belief_mem_simplex ];
            · exact Finset.subset_univ _;
            · exact Finset.Subset.refl _;
          have := h1.2.1; simp_all +decide [ Fin.sum_univ_three ];
        grind;
      unfold zeroExt at h1; aesop;
    have h2 : 2 ∉ K.C := by
      intro h2
      have h_payoff : K.w = nonexistenceV (zeroExt K.C (K.σ.belief 0)) := by
        convert Set.mem_singleton_iff.mp ( K.payoff 0 h0 ) using 1
      have h_mu : zeroExt K.C (K.σ.belief 0) 2 = 0 := by
        have h_sigma20 : K.σ.σ 2 0 = 0 := by
          have := K.σ.mem 2 ( by simp +decide [ h2 ] ); simp_all +decide [ simplexOn ];
        simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb, zeroExt ]
      have h_nonexistenceV : nonexistenceV (zeroExt K.C (K.σ.belief 0)) = 1 / 2 := by
        linarith
      have h_contra : zeroExt K.C (K.σ.belief 0) 0 = 1 / 2 := by
        unfold nonexistenceV at h_nonexistenceV; norm_num at h_nonexistenceV;
        have h_sum : zeroExt K.C (K.σ.belief 0) 0 + zeroExt K.C (K.σ.belief 0) 1 + zeroExt K.C (K.σ.belief 0) 2 = 1 := by
          have h_sum : ∀ μ ∈ simplexOn (Finset.univ : Finset (Fin 3)), μ 0 + μ 1 + μ 2 = 1 := by
            intro μ hμ; have := hμ.2.1; simp_all +decide [ Fin.sum_univ_three ];
          apply_rules [ DisclosureGame.zeroExt_mem_simplex, K.σ.belief_mem_simplex ];
          exact Finset.subset_univ _;
        cases min_cases ( zeroExt K.C ( K.σ.belief 0 ) 0 + 9 / 10 * zeroExt K.C ( K.σ.belief 0 ) 2 ) ( - ( 1 / 10 * zeroExt K.C ( K.σ.belief 0 ) 0 ) + 11 / 10 * zeroExt K.C ( K.σ.belief 0 ) 1 + 9 / 10 * zeroExt K.C ( K.σ.belief 0 ) 2 ) <;> linarith
      have h_contra' : zeroExt K.C (K.σ.belief 0) 1 = 1 / 2 := by
        have h_contra' : zeroExt K.C (K.σ.belief 0) 0 + zeroExt K.C (K.σ.belief 0) 1 + zeroExt K.C (K.σ.belief 0) 2 = 1 := by
          have h_contra' : ∑ θ ∈ Finset.univ, zeroExt K.C (K.σ.belief 0) θ = 1 := by
            have h_contra' : zeroExt K.C (K.σ.belief 0) ∈ simplexOn (Finset.univ : Finset (Fin 3)) := by
              apply_rules [ DisclosureGame.zeroExt_mem_simplex, K.σ.belief_mem_simplex ];
              exact Finset.subset_univ _
            exact h_contra'.2.1.trans ( by simp +decide [ Fin.sum_univ_three ] )
          generalize_proofs at *;
          rwa [ Fin.sum_univ_three ] at h_contra';
        linarith
      have h_contra'' : K.σ.σ 0 1 = 0 := by
        have := K.σ.mem 1 ( by simp +decide [ h1 ] ); simp_all +decide [ simplexOn ];
        unfold zeroExt at *; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
        split_ifs at h_contra <;> norm_num at *;
        rw [ div_eq_iff ] at h_contra h_contra' <;> norm_num at *;
        · unfold DisclosureGame.condPrior at *; simp_all +decide [ DisclosureGame.priorMeasure ];
          have := K.σ.mem 0 ( by simp +decide [ * ] ); simp_all +decide [ simplexOn ];
          nlinarith [ show ( K.C.card : ℝ ) ≥ 1 by exact_mod_cast Finset.card_pos.mpr ⟨ 0, by assumption ⟩, div_mul_cancel₀ ( 3⁻¹ : ℝ ) ( show ( K.C.card : ℝ ) * 3⁻¹ ≠ 0 by exact mul_ne_zero ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr ⟨ 0, by assumption ⟩ ) <| by norm_num ) ];
        · intro h; norm_num [ h ] at h_contra';
        · intro h; norm_num [ h ] at *;
      have h_contra''' : 1 ∉ K.σ.evidence := by
        intro h1
        have h_payoff : K.w = nonexistenceV (zeroExt K.C (K.σ.belief 1)) := by
          convert Set.mem_singleton_iff.mp ( K.payoff 1 h1 ) using 1
        have h_mu : zeroExt K.C (K.σ.belief 1) = fun θ => if θ = 2 then 1 else 0 := by
          have h_mu : ∀ θ, θ ≠ 2 → K.σ.σ θ 1 = 0 := by
            intro θ hθ; fin_cases θ <;> simp_all +decide;
            have := K.σ.mem 1 ( by simp +decide [ * ] ); simp_all +decide [ simplexOn ];
          ext θ; simp [zeroExt, Strategy.belief, Strategy.onPathProb];
          split_ifs <;> simp_all +decide [ Fin.sum_univ_three ];
          rw [ Finset.sum_eq_single 2 ] <;> simp_all +decide [ Finset.sum_ite ];
          unfold DisclosureGame.condPrior; simp +decide [ DisclosureGame.priorMeasure ];
          have := K.σ.mem 2 ( by simp +decide [ h2 ] ); simp_all +decide [ simplexOn ];
          exact ⟨ Finset.Nonempty.ne_empty ⟨ 2, h2 ⟩, by linarith ⟩
        have h_nonexistenceV : nonexistenceV (zeroExt K.C (K.σ.belief 1)) = 9 / 10 := by
          unfold nonexistenceV; norm_num [ h_mu ];
          norm_num [ Fin.ext_iff ]
        norm_num [ h_payoff, h_mu, h_nonexistenceV ] at hw;
        grind +suggestions
      exact h_contra''' (by
      have := K.preimage_eq.symm ▸ h2; simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
      simp_all +decide [ nonexistenceGame ])
    have h0 : 0 ∈ K.C := by
      have := K.preimage_eq.symm; simp_all +decide [ DisclosureGame.preimageSetFull ];
      simp_all +decide [ DisclosureGame.preimageSet ];
      exact ⟨ 0, by simp +decide [ nonexistenceGame_M0 ], h0 ⟩
    have hC : K.C = {0, 1} := by
      grind +suggestions
    exact hC;
  · exact absurd hw ( by rw [ coalition_bOnly_w K h0 ]; norm_num )

/-
Skeptical payoffs are at most `1/2`.
-/
private lemma skeptical_le_half (θ : Fin 3) : nonexistenceGame.skeptical θ ≤ 1 / 2 := by
  refine' csSup_le _ _ <;> norm_num;
  · fin_cases θ <;> simp +decide [ nonexistenceGame ];
  · intro b hb
    cases' hb with hb0 hb1;
    · obtain ⟨μ, hμ⟩ : ∃ μ ∈ nonexistenceGame.feasibleBeliefs 0, IsMinOn nonexistenceGame.vlow (nonexistenceGame.feasibleBeliefs 0) μ ∧ nonexistenceGame.skepticalInner 0 = nonexistenceGame.vlow μ := by
        apply DisclosureGame.exists_isMinOn_vlow_feasibleBeliefs; simp +decide [ nonexistenceGame ];
      have hμ_le : nonexistenceGame.vlow μ ≤ nonexistenceGame.vlow (nonexistenceGame.condPrior (nonexistenceGame.canSend 0)) := by
        apply hμ.right.left;
        convert nonexistenceGame.condPrior_canSend_mem_polytope ( show 0 ∈ nonexistenceGame.𝓜 from by simp +decide [ nonexistenceGame ] ) using 1;
        exact nonexistenceGame.feasibleBeliefs_eq_polytope ( by simp +decide [ nonexistenceGame ] );
      exact hb0.2 ▸ hμ.2.2 ▸ hμ_le.trans ( by rw [ ne_canSend0, ne_vlow_condPrior01 ] );
    · -- By `exists_isMinOn_vlow_feasibleBeliefs`, get `μ ∈ feasibleBeliefs 1` with `IsMinOn vlow (feasibleBeliefs 1) μ` and `skepticalInner 1 = vlow μ`.
      obtain ⟨μ, hμ⟩ : ∃ μ ∈ nonexistenceGame.feasibleBeliefs 1, IsMinOn nonexistenceGame.vlow (nonexistenceGame.feasibleBeliefs 1) μ ∧ nonexistenceGame.skepticalInner 1 = nonexistenceGame.vlow μ := by
        apply exists_isMinOn_vlow_feasibleBeliefs; simp [nonexistenceGame];
      -- The point `condPrior (canSend 1)` lies in `feasibleBeliefs 1` (by `condPrior_canSend_mem_polytope` together with `feasibleBeliefs_eq_polytope`).
      have h_condPrior1 : nonexistenceGame.condPrior (nonexistenceGame.canSend 1) ∈ nonexistenceGame.feasibleBeliefs 1 := by
        convert nonexistenceGame.condPrior_canSend_mem_polytope _ using 1;
        · convert nonexistenceGame.feasibleBeliefs_eq_polytope _ using 1;
          exact Finset.mem_univ _;
        · exact Finset.mem_univ _;
      -- Since `μ` minimises `vlow` on `feasibleBeliefs 1`, `vlow μ ≤ vlow (condPrior (canSend 1))`.
      have h_vlow_le : nonexistenceGame.vlow μ ≤ nonexistenceGame.vlow (nonexistenceGame.condPrior (nonexistenceGame.canSend 1)) := by
        exact hμ.2.1 h_condPrior1;
      linarith [ ne_vlow_condPrior02, show nonexistenceGame.vlow ( nonexistenceGame.condPrior ( nonexistenceGame.canSend 1 ) ) = 2 / 5 by rw [ ne_canSend1, ne_vlow_condPrior02 ] ]

/-
In the residual one-type game on `{2}`, the only coalition payoff is `9/10`.
-/
private lemma residual_singleton (hne : ({2} : Finset (Fin 3)).Nonempty)
    (hsub : ({2} : Finset (Fin 3)) ⊆ nonexistenceGame.Θ) {w : ℝ}
    (hw : w ∈ (nonexistenceGame.restrict {2} hne hsub).coalitionPayoffs) :
    w = 9 / 10 := by
  obtain ⟨K, hK⟩ : ∃ K : Coalition (DisclosureGame.restrict nonexistenceGame {2} hne hsub), K.w = w :=
    hw
  -- Since $K$ is a coalition in the residual game on $\{2\}$, we have $K.C = \{2\}$.
  have hC : K.C = {2} := by
    exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨ K.C_nonempty, fun x hx => by have := K.C_subset; aesop ⟩;
  -- Since $K$ is a coalition in the residual game on $\{2\}$, we have $K.σ.σ 2 1 = 1$.
  have hσ21 : K.σ.σ 2 1 = 1 := by
    have hσ21 : ∀ m, m ≠ 1 → K.σ.σ 2 m = 0 := by
      intro m hm; have := K.σ.mem 2; simp_all +decide [ DisclosureGame.M ];
      fin_cases m <;> tauto;
    have := K.σ.mem 2; simp_all +decide [ Fin.sum_univ_two ];
  -- Since $K$ is a coalition in the residual game on $\{2\}$, we have $K.σ.coalitionBelief 1 2 = 1$.
  have hcoalitionBelief12 : K.σ.coalitionBelief 1 2 = 1 := by
    unfold Strategy.coalitionBelief; simp +decide [ hσ21 ];
    unfold Strategy.belief; simp +decide [ hσ21 ];
    unfold Strategy.onPathProb; simp +decide [ hσ21, hC ];
    unfold zeroExt; simp +decide [ hσ21 ];
    repeat unfold DisclosureGame.condPrior; simp +decide [ DisclosureGame.priorMeasure ];
  have hcoalitionBelief1 : K.σ.coalitionBelief 1 0 = 0 ∧ K.σ.coalitionBelief 1 1 = 0 := by
    unfold Strategy.coalitionBelief; simp +decide [ hσ21 ];
    unfold zeroExt; simp +decide [ hC ];
  have := K.payoff 1 ?_ <;> norm_num at *;
  · unfold nonexistenceV at this; norm_num [ hcoalitionBelief1, hcoalitionBelief12 ] at this; linarith;
  · simp +decide [ Strategy.evidence, hC ];
    simp +decide [ Strategy.msgSupport, hσ21 ]

/-- **Proposition 5**, base game. There
is a disclosure game with three types (uniform prior), two messages `a = 0`,
`b = 1`, message mapping `M(1) = {a,b}`, `M(2) = {a}`, `M(3) = {b}`, and
single-valued `V = {nonexistenceV}`, admitting **no** coalition-proof PBE. -/
theorem nonexistence :
    ∃ G : DisclosureGame (Fin 3) (Fin 2),
      G.Θ = Finset.univ ∧ G.𝓜 = Finset.univ ∧
      G.M 0 = ({0, 1} : Finset (Fin 2)) ∧
      G.M 1 = ({0} : Finset (Fin 2)) ∧
      G.M 2 = ({1} : Finset (Fin 2)) ∧
      (∀ θ, G.μ0 θ = 1 / 3) ∧
      (∀ μ, G.V μ = {nonexistenceV μ}) ∧
      ∀ P : Partition G, ¬ P.IsCPPBEPartition := by
  refine ⟨nonexistenceGame, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro P hP
  classical
  have hgreedy : P.IsGreedy := P.cppbe_characterization.mp hP
  have hmono : Antitone P.w := P.antitone_of_isGreedy hgreedy
  -- a cell containing type `2`
  have h2 : (2 : Fin 3) ∈ nonexistenceGame.Θ := by simp
  rw [P.cover_eq] at h2
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h2
  obtain ⟨t2, ht2⟩ := h2
  have hcard : 0 < P.card := by have := t2.isLt; omega
  set t0 : Fin P.card := ⟨0, hcard⟩ with ht0
  have ht0val : (t0 : ℕ) = 0 := rfl
  -- `R_0 = Θ`
  have hfilter0 : (Finset.univ.filter (fun s => t0 ≤ s)) = (Finset.univ : Finset (Fin P.card)) := by
    apply Finset.filter_true_of_mem
    intro s _; rw [Fin.le_def]; exact Nat.zero_le _
  have hR0 : thetaStep P.C t0 = nonexistenceGame.Θ := by
    unfold thetaStep; rw [hfilter0]; exact P.cover_eq.symm
  -- stepPayoffs at 0 equals the coalition payoffs of the full game
  have hgame0 :
      nonexistenceGame.restrict (thetaStep P.C t0)
        (thetaStep_nonempty t0 (P.C_nonempty t0)) (P.thetaStep_subset t0) = nonexistenceGame :=
    (Partition.restrict_eq_of_eq hR0 _ _ nonexistenceGame.Θ_nonempty subset_rfl).trans restrict_self
  have hstep0 : P.stepPayoffs t0 = nonexistenceGame.coalitionPayoffs := by
    unfold Partition.stepPayoffs; rw [hgame0]
  -- `w_0 = 1/2`
  have hw0 : P.w t0 = 1 / 2 := by
    have hge : IsGreatest (P.greedyConstraint t0) (1 / 2) := by
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hstep0]; exact half_mem_coalitionPayoffs
      · unfold Partition.greedyLower
        apply Finset.sup'_le
        intro θ _; exact skeptical_le_half θ
      · intro t' ht'; exfalso; rw [ht0val] at ht'; omega
      · rintro w ⟨hwstep, -, -⟩
        rw [hstep0] at hwstep
        obtain ⟨K, rfl⟩ := hwstep
        exact coalition_w_le_half K
    exact IsGreatest.unique (hgreedy t0) hge
  -- cell at step 0 is `{0,1}`
  have hexcl0 : nonexistenceGame.preimageSetFull (P.σ t0).evidence ⊆ P.C t0 := by
    have h := P.exclusive t0
    rw [hR0] at h; exact h
  have hcell : P.C t0 = ({0, 1} : Finset (Fin 3)) := by
    have hK : (⟨P.C t0, P.C_nonempty t0, P.C_subset t0, P.σ t0, hexcl0, P.w t0,
        P.payoff t0⟩ : Coalition nonexistenceGame).w = 1 / 2 := hw0
    exact coalition_w_half_cell _ hK
  -- `t2 ≠ 0`
  have ht2ne : t2 ≠ t0 := by
    intro h; rw [h, hcell] at ht2
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht2
    rcases ht2 with h' | h' <;> exact absurd (congrArg Fin.val h') (by norm_num)
  -- `R_{t2} = {2}`
  have hR2 : thetaStep P.C t2 = ({2} : Finset (Fin 3)) := by
    apply Finset.Subset.antisymm
    · intro θ hθ
      simp only [thetaStep, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and] at hθ
      obtain ⟨s, hts, hθs⟩ := hθ
      have hst0 : s ≠ t0 := by
        intro h; subst h
        exact ht2ne (le_antisymm hts (by rw [Fin.le_def, ht0val]; exact Nat.zero_le _))
      have hθnot : θ ∉ P.C t0 := Finset.disjoint_left.mp (P.C_disjoint s t0 hst0) hθs
      rw [hcell] at hθnot
      have hθΘ : θ ∈ nonexistenceGame.Θ := P.C_subset s hθs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hθnot ⊢
      fin_cases θ <;> simp_all
    · intro θ hθ
      rw [Finset.mem_singleton] at hθ; subst hθ
      simp only [thetaStep, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨t2, le_rfl, ht2⟩
  -- `w_{t2} = 9/10`
  have hw2 : P.w t2 = 9 / 10 := by
    have hmem := P.w_mem_stepPayoffs t2
    unfold Partition.stepPayoffs at hmem
    rw [Partition.restrict_eq_of_eq hR2 _ _ (Finset.singleton_nonempty _)
      (Finset.subset_univ _)] at hmem
    exact residual_singleton _ _ hmem
  -- contradiction: `9/10 = w_{t2} ≤ w_0 = 1/2`
  have hle : P.w t2 ≤ P.w t0 := hmono (by rw [Fin.le_def, ht0val]; exact Nat.zero_le _)
  rw [hw0, hw2] at hle; norm_num at hle

/-! ## The cheap-talk-copy variant -/

/-- **The M-CT variant** with four copies of each message: `a`-copies `{0,1,2,3}`,
`b`-copies `{4,5,6,7}`. -/
noncomputable def mctGame : DisclosureGame (Fin 3) (Fin 8) where
  Θ := Finset.univ
  𝓜 := Finset.univ
  Θ_nonempty := Finset.univ_nonempty
  𝓜_nonempty := Finset.univ_nonempty
  M := fun θ => if θ = 0 then Finset.univ else if θ = 1 then {0, 1, 2, 3} else {4, 5, 6, 7}
  M_subset := by intro θ _ x _; exact Finset.mem_univ x
  M_nonempty := by intro θ _; fin_cases θ <;> decide
  cover := by
    ext m; simp only [Finset.coe_univ, Set.mem_univ, true_iff, Set.mem_iUnion,
      Finset.mem_coe, exists_prop]
    exact ⟨0, Finset.mem_univ _, by simp⟩
  μ0 := fun _ => 1 / 3
  μ0_mem := by
    refine ⟨fun a => by norm_num, ?_, fun a ha => absurd (Finset.mem_univ a) ha⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  μ0_fullSupport := by intro θ _; norm_num
  V := fun μ => {nonexistenceV μ}
  V_nonempty := fun μ _ => ⟨_, rfl⟩
  V_isCompact := fun μ _ => isCompact_singleton
  V_ordConnected := fun μ _ => ordConnected_singleton
  V_uhc := uhc_singleton_of_continuous nonexistenceV continuous_nonexistenceV _

@[simp] lemma mctGame_Θ : mctGame.Θ = Finset.univ := rfl
@[simp] lemma mctGame_𝓜 : mctGame.𝓜 = Finset.univ := rfl
@[simp] lemma mctGame_μ0 (θ : Fin 3) : mctGame.μ0 θ = 1 / 3 := rfl
@[simp] lemma mctGame_V (μ : Fin 3 → ℝ) : mctGame.V μ = {nonexistenceV μ} := rfl

lemma mctGame_M0 : mctGame.M 0 = (Finset.univ : Finset (Fin 8)) := rfl
lemma mctGame_M1 : mctGame.M 1 = ({0, 1, 2, 3} : Finset (Fin 8)) := rfl
lemma mctGame_M2 : mctGame.M 2 = ({4, 5, 6, 7} : Finset (Fin 8)) := rfl

@[simp] lemma mctGame_vbar (μ : Fin 3 → ℝ) : mctGame.vbar μ = nonexistenceV μ := by
  simp [DisclosureGame.vbar]
@[simp] lemma mctGame_vlow (μ : Fin 3 → ℝ) : mctGame.vlow μ = nonexistenceV μ := by
  simp [DisclosureGame.vlow]

/-
`v̄ = nonexistenceV` is quasiconcave on the mct game.
-/
private lemma mct_QC : mctGame.QC := by
  intro μ hμ μ' hμ' l hl;
  simp +decide [ mctGame_vbar, nonexistenceV ];
  constructor <;> contrapose! hl <;> norm_num at *;
  · intro hl_pos; nlinarith [ hμ.1 0, hμ.1 1, hμ.1 2, hμ'.1 0, hμ'.1 1, hμ'.1 2, Fin.sum_univ_three μ, Fin.sum_univ_three μ' ];
  · exact fun h => by nlinarith [ hμ.1 0, hμ.1 1, hμ.1 2, hμ'.1 0, hμ'.1 1, hμ'.1 2, Fin.sum_univ_three μ, Fin.sum_univ_three μ' ];

/-
M-CT holds: every message has at least `3` copies with the same preimage.
-/
private lemma mct_MCT : mctGame.MCT := by
  unfold DisclosureGame.MCT;
  unfold mctGame
  simp +decide [ DisclosureGame.canSend ];
  simp +decide [ DisclosureGame.preimageFull ];
  simp +decide [ preimage ];
  simp +decide [ Finset.Nonempty ]

/-
`P(a-copy) = {0,1}` for each a-copy `m ∈ {0,1,2,3}`.
-/
private lemma mct_canSend_a {m : Fin 8} (hm : m ∈ ({0, 1, 2, 3} : Finset (Fin 8))) :
    mctGame.canSend m = ({0, 1} : Finset (Fin 3)) := by
  ext θ; fin_cases θ <;> simp +decide [ mctGame, DisclosureGame.canSend, DisclosureGame.preimageFull, preimage ] at hm ⊢;
  · exact ⟨ m, by aesop ⟩;
  · rcases hm with ( rfl | rfl | rfl | rfl ) <;> simp +decide

/-
`P(b-copy) = {0,2}` for each b-copy `m ∈ {4,5,6,7}`.
-/
private lemma mct_canSend_b {m : Fin 8} (hm : m ∈ ({4, 5, 6, 7} : Finset (Fin 8))) :
    mctGame.canSend m = ({0, 2} : Finset (Fin 3)) := by
  fin_cases m <;> simp +decide [ mctGame, DisclosureGame.canSend, DisclosureGame.preimageFull, preimage ] at hm ⊢;
  · simp +decide [ Finset.Nonempty ];
  · simp +decide [ Finset.ext_iff, Set.ext_iff ];
    simp +decide [ Fin.forall_fin_succ ];
  · simp +decide [ Finset.ext_iff ];
    simp +decide [ Fin.forall_fin_succ ];
  · simp +decide [ Finset.ext_iff ];
    simp +decide [ Fin.forall_fin_succ ]

/-- QC pooling bound: every coalition pays at most `v(μ⁰_C)`. -/
private lemma mct_coalition_w_le_v (K : Coalition mctGame) :
    K.w ≤ nonexistenceV (mctGame.condPrior K.C) := by
  rw [← mctGame_vbar]
  have key := coalition_w_le_vbar_condPrior (G := mctGame) mct_QC
    (R := mctGame.Θ) mctGame.Θ_nonempty subset_rfl
  rw [restrict_self] at key
  exact key K

/-
A coalition of the mct game that never uses an a-copy pools `⊆ {0,2}` on b-copies,
paying at most `2/5`.
-/
private lemma mct_bOnly_le (K : Coalition mctGame)
    (h0 : ∀ m ∈ ({0, 1, 2, 3} : Finset (Fin 8)), m ∉ K.σ.evidence) : K.w ≤ 2 / 5 := by
  refine' le_trans ( mct_coalition_w_le_v K ) _;
  by_cases h1 : 1 ∈ K.C;
  · have := K.σ.mem 1 h1; simp_all +decide [ mctGame_M1, mctGame_M2 ];
    simp_all +decide [ Fin.sum_univ_eight, Strategy.evidence, Strategy.msgSupport ];
    grind +suggestions;
  · have h2 : 0 ∈ K.C := by
      have h2 : K.σ.evidence.Nonempty := by
        obtain ⟨ θ, hθ ⟩ := K.C_nonempty; have := coalitionStrategy_subset_preimage ( hne := K.C_nonempty ) ( hsub := K.C_subset ) ( s := K.σ ); simp_all +decide [ DisclosureGame.preimageSetFull ];
        have := this hθ; simp_all +decide [ DisclosureGame.preimageSet ];
        exact this.mono fun x hx => hx.2;
      have := K.preimage_eq.symm; simp_all +decide [ DisclosureGame.preimageSetFull ];
      simp_all +decide [ mctGame, DisclosureGame.canSend, DisclosureGame.preimageSet ];
    by_cases h3 : 2 ∈ K.C <;> simp_all +decide [ Finset.ext_iff ];
    · rw [ show K.C = { 0, 2 } from ?_ ];
      · unfold nonexistenceV mctGame; norm_num [ DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
        simp +decide; norm_num;
      · ext x; fin_cases x <;> simp_all +decide;
    · rw [ show K.C = { 0 } by ext x; fin_cases x <;> simp +decide [ * ] ]; norm_num [ mctGame, nonexistenceV, DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
      norm_num [ Fin.ext_iff ]

/-
Every coalition of the mct game pays at most `1/2`.
-/
private lemma mct_coalition_w_le_half (K : Coalition mctGame) : K.w ≤ 1 / 2 := by
  by_cases h : ∃ m ∈ ({0, 1, 2, 3} : Finset (Fin 8)), m ∈ K.σ.evidence;
  · obtain ⟨ m, hm₁, hm₂ ⟩ := h;
    have h_mu : K.σ.coalitionBelief m 2 = 0 := by
      rw [ DisclosureGame.restrict_coalitionBelief_eq ];
      have := K.σ.mem 2; simp_all +decide [ mctGame_M2 ];
      grind;
    convert nonexistenceV_le_half_edge2 _ h_mu using 1;
    · exact Set.mem_singleton_iff.mp ( K.payoff m hm₂ );
    · apply_rules [ DisclosureGame.zeroExt_mem_simplex, K.σ.belief_mem_simplex ];
      exact Finset.subset_univ _;
  · exact le_trans ( mct_bOnly_le K fun m hm => fun hm' => h ⟨ m, hm, hm' ⟩ ) ( by norm_num )

/-
The payoff `1/2` is attainable in the mct game.
-/
private lemma mct_half_mem : (1 : ℝ) / 2 ∈ mctGame.coalitionPayoffs := by
  have := Partition.vlow_condPrior_canSend_mem_coalitionPayoffs mctGame ( m := ( 0 : Fin 8 ) ) ( by simp +decide ); simp_all +decide;
  convert this using 1;
  unfold nonexistenceV; rw [ mct_canSend_a ( by decide ) ]; norm_num [ mctGame, DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
  decide

/-
The only coalition of the mct game paying `1/2` has cell `{0,1}`.
-/
-- Larger heartbeat budget: this finite-case coalition analysis is elaboration-heavy.
set_option maxHeartbeats 1600000 in
private lemma mct_coalition_w_half_cell (K : Coalition mctGame)
    (hw : K.w = 1 / 2) : K.C = ({0, 1} : Finset (Fin 3)) := by
  by_cases h0 : ∃ m ∈ ({0, 1, 2, 3} : Finset (Fin 8)), m ∈ K.σ.evidence;
  · obtain ⟨ m, hm₁, hm₂ ⟩ := h0
    have h_mu : K.σ.coalitionBelief m 2 = 0 := by
      rw [ DisclosureGame.restrict_coalitionBelief_eq ];
      have := K.σ.mem 2; simp_all +decide [ mctGame_M2 ];
      grind
    have h_nonexistenceV : nonexistenceV (zeroExt K.C (K.σ.coalitionBelief m)) = 1 / 2 := by
      have := K.payoff m hm₂; simp_all +decide [ mctGame_V ];
      unfold nonexistenceV at *; norm_num at *;
      unfold Strategy.coalitionBelief at *; simp_all +decide [ Strategy.belief, Strategy.onPathProb, zeroExt ];
    have h_eq : zeroExt K.C (K.σ.coalitionBelief m) 0 = 1 / 2 ∧ zeroExt K.C (K.σ.coalitionBelief m) 1 = 1 / 2 := by
      unfold nonexistenceV at h_nonexistenceV; norm_num at h_nonexistenceV;
      have h_eq : zeroExt K.C (K.σ.coalitionBelief m) 0 + zeroExt K.C (K.σ.coalitionBelief m) 1 + zeroExt K.C (K.σ.coalitionBelief m) 2 = 1 := by
        have h_eq : zeroExt K.C (K.σ.coalitionBelief m) ∈ simplexOn (Finset.univ : Finset (Fin 3)) := by
          apply_rules [ DisclosureGame.zeroExt_mem_simplex, K.σ.belief_mem_simplex ];
          · exact Finset.subset_univ _;
          · exact Finset.Subset.refl _
        generalize_proofs at *; (
        have := h_eq.2.1; simp_all +decide [ Fin.sum_univ_three ];);
      unfold zeroExt at *; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
      grind
    have h_eq' : K.σ.σ 0 m = K.σ.σ 1 m := by
      simp_all +decide [ DisclosureGame.restrict_coalitionBelief_eq, zeroExt ];
      grind
    have h_eq'' : ∀ m ∈ ({0, 1, 2, 3} : Finset (Fin 8)), K.σ.σ 0 m = K.σ.σ 1 m := by
      intro m hm; by_cases hm' : m ∈ K.σ.evidence <;> simp_all +decide [ zeroExt ];
      · have h_mu : K.σ.coalitionBelief m 2 = 0 := by
          rw [ DisclosureGame.restrict_coalitionBelief_eq ];
          have := K.σ.mem 2; simp_all +decide [ mctGame_M2 ];
          grind
        have h_nonexistenceV : nonexistenceV (zeroExt K.C (K.σ.coalitionBelief m)) = 1 / 2 := by
          have := K.payoff m hm'; simp_all +decide [ mctGame_V ];
          unfold nonexistenceV at *; norm_num at *;
          unfold zeroExt; simp +decide [ h_mu ];
          grind
        have h_eq : zeroExt K.C (K.σ.coalitionBelief m) 0 = 1 / 2 ∧ zeroExt K.C (K.σ.coalitionBelief m) 1 = 1 / 2 := by
          unfold nonexistenceV at h_nonexistenceV; norm_num at h_nonexistenceV;
          have h_sum : zeroExt K.C (K.σ.coalitionBelief m) 0 + zeroExt K.C (K.σ.coalitionBelief m) 1 + zeroExt K.C (K.σ.coalitionBelief m) 2 = 1 := by
            have h_sum : ∀ μ ∈ simplexOn (Finset.univ : Finset (Fin 3)), μ 0 + μ 1 + μ 2 = 1 := by
              intro μ hμ; have := hμ.2.1; simp_all +decide [ Fin.sum_univ_three ];
            apply_rules [ DisclosureGame.zeroExt_mem_simplex, K.σ.belief_mem_simplex ];
            · exact Finset.subset_univ _;
            · exact Finset.Subset.refl _;
          unfold zeroExt at *; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
          grind
        have h_eq' : K.σ.σ 0 m = K.σ.σ 1 m := by
          unfold zeroExt at h_eq; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
          unfold zeroExt at h_eq; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
          unfold mctGame at *; simp_all +decide [ DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
          grind
        exact h_eq';
      · have := K.σ.mem 1; simp_all +decide [ mctGame_M1 ];
        unfold Strategy.evidence at hm'; simp_all +decide [ Strategy.msgSupport, Strategy.onPathProb_pos_iff_mem_evidence ];
        have := K.σ.mem 0; simp_all +decide [ mctGame_M0 ];
        grind
    have h_eq''' : ∑ m ∈ ({0, 1, 2, 3} : Finset (Fin 8)), K.σ.σ 0 m = 1 := by
      have := K.σ.mem 1 ( by
        unfold zeroExt at *; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
        split_ifs at h_eq <;> norm_num at h_eq; aesop ( simp_config := { decide := true } ); ); simp_all +decide [ mctGame_M1 ];
      rw [ ← this.2.1, Fin.sum_univ_eight ]; simp +decide [ this.2.2 ]; ring!;
    have h_eq'''' : ∀ m ∈ ({4, 5, 6, 7} : Finset (Fin 8)), K.σ.σ 0 m = 0 := by
      intro m hm
      have := K.σ.mem 0; simp_all +decide [ mctGame_M0 ];
      by_cases h0 : 0 ∈ K.C <;> simp_all +decide [ Fin.sum_univ_eight ];
      · grind +qlia;
      · unfold zeroExt at *; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
    have h_eq''''' : ∀ m ∈ ({4, 5, 6, 7} : Finset (Fin 8)), m ∉ K.σ.evidence := by
      intro m hm; intro hm'; have := K.σ.mem 1; simp_all +decide [ mctGame_M1 ];
      have h_mu : K.σ.coalitionBelief m 0 = 0 ∧ K.σ.coalitionBelief m 1 = 0 := by
        unfold Strategy.coalitionBelief; simp +decide [ Strategy.belief, Strategy.onPathProb, zeroExt ];
        grind +suggestions
      have h_nonexistenceV : nonexistenceV (zeroExt K.C (K.σ.coalitionBelief m)) = 9 / 10 := by
        unfold nonexistenceV; norm_num [ h_mu, zeroExt ];
        have h_mu : K.σ.coalitionBelief m 2 = 1 := by
          have h_mu : K.σ.coalitionBelief m ∈ simplexOn (Finset.univ : Finset (Fin 3)) := by
            apply_rules [ DisclosureGame.zeroExt_mem_simplex, K.σ.belief_mem_simplex ];
            exact Finset.subset_univ _;
          have := h_mu.2.1; simp_all +decide [ Fin.sum_univ_three ];
        have := K.preimage_eq.symm; simp_all +decide [ DisclosureGame.preimageSetFull ];
        simp +decide [ mctGame, DisclosureGame.preimageSet ] at this ⊢;
        exact fun h => False.elim <| h ⟨ m, by aesop ⟩
      norm_num [ hw ] at h_nonexistenceV;
      have := K.payoff m hm'; simp_all +decide [ mctGame_V ];
      unfold zeroExt at *; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
      unfold zeroExt at *; simp_all +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb ];
      norm_num at this
    have h_eq'''''' : K.C = ({0, 1} : Finset (Fin 3)) := by
      have h_eq'''''' : K.C = mctGame.preimageSetFull K.σ.evidence := by
        exact K.preimage_eq.symm
      rw [h_eq''''''];
      simp +decide [ mctGame, DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
      simp +decide [ Finset.Nonempty, Set.Nonempty ] at *;
      grind +splitImp
    exact h_eq'''''';
  · exact absurd hw ( by linarith [ mct_bOnly_le K fun m hm => fun hm' => h0 ⟨ m, hm, hm' ⟩ ] )

/-
Skeptical payoffs of the mct game are at most `1/2`.
-/
private lemma mct_skeptical_le_half (θ : Fin 3) : mctGame.skeptical θ ≤ 1 / 2 := by
  refine' csSup_le _ _ <;> norm_num;
  · fin_cases θ <;> simp +decide [ mctGame ];
  · intro m hm
    have h_upper_bound : mctGame.skepticalInner m ≤ nonexistenceV (mctGame.condPrior (mctGame.canSend m)) := by
      obtain ⟨μ, hμ⟩ : ∃ μ ∈ mctGame.feasibleBeliefs m, IsMinOn mctGame.vlow (mctGame.feasibleBeliefs m) μ ∧ mctGame.skepticalInner m = mctGame.vlow μ := by
        apply DisclosureGame.exists_isMinOn_vlow_feasibleBeliefs; simp +decide [ mctGame ];
      convert hμ.2.1 ( mctGame.condPrior_canSend_mem_polytope ( show m ∈ mctGame.𝓜 from by simp +decide [ mctGame ] ) |> fun h => mctGame.feasibleBeliefs_eq_polytope ( by simp +decide [ mctGame ] ) ▸ h ) using 1; aesop;
    refine' le_trans h_upper_bound _;
    fin_cases m <;> simp +decide [ mct_canSend_a, mct_canSend_b, mctGame_vlow ] at hm ⊢;
    all_goals unfold nonexistenceV; norm_num [ mctGame, DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
    all_goals norm_num [ Fin.ext_iff ];

/-
In the residual one-type mct game on `{2}`, the only coalition payoff is `9/10`.
-/
private lemma mct_residual_singleton (hne : ({2} : Finset (Fin 3)).Nonempty)
    (hsub : ({2} : Finset (Fin 3)) ⊆ mctGame.Θ) {w : ℝ}
    (hw : w ∈ (mctGame.restrict {2} hne hsub).coalitionPayoffs) :
    w = 9 / 10 := by
  obtain ⟨ K, rfl ⟩ := hw;
  -- Since K is a coalition in the residual game, its type space is {2}. Therefore, K.C must be {2}.
  have hK_C : K.C = {2} := by
    exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨ K.C_nonempty, fun x hx => by have := K.C_subset; aesop ⟩;
  -- Since K is a coalition in the residual game, its evidence is nonempty. Let m be an element of K.σ.evidence.
  obtain ⟨m, hm⟩ : ∃ m, m ∈ K.σ.evidence := by
    have := K.C_nonempty; simp_all +decide [ Finset.ext_iff ];
    obtain ⟨ θ, hθ ⟩ := this; have := K.preimage_eq.symm ▸ hθ; simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
    exact this.imp fun x hx => hx.2;
  have hcoalitionBelief : K.σ.coalitionBelief m = fun θ => if θ = 2 then 1 else 0 := by
    ext θ; simp [Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb, zeroExt];
    simp +decide [ hK_C, DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
    split_ifs <;> simp_all +decide [ Strategy.evidence, Strategy.msgSupport ];
    linarith;
  have := K.payoff m hm; simp_all +decide [ nonexistenceV ];
  norm_num

/-- **Proposition 5**, cheap-talk
variant. Non-existence persists when the example is augmented with
cheap-talk copies (four copies of each message: `a`-copies `{0,1,2,3}`,
`b`-copies `{4,5,6,7}`), so the game additionally satisfies cheap-talk
copies (M-CT). -/
theorem nonexistence_mct :
    ∃ G : DisclosureGame (Fin 3) (Fin 8),
      G.Θ = Finset.univ ∧ G.𝓜 = Finset.univ ∧
      G.M 0 = (Finset.univ : Finset (Fin 8)) ∧
      G.M 1 = ({0, 1, 2, 3} : Finset (Fin 8)) ∧
      G.M 2 = ({4, 5, 6, 7} : Finset (Fin 8)) ∧
      (∀ θ, G.μ0 θ = 1 / 3) ∧
      (∀ μ, G.V μ = {nonexistenceV μ}) ∧
      G.MCT ∧
      ∀ P : Partition G, ¬ P.IsCPPBEPartition := by
  refine ⟨mctGame, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, mct_MCT, ?_⟩
  intro P hP
  classical
  have hgreedy : P.IsGreedy := P.cppbe_characterization.mp hP
  have hmono : Antitone P.w := P.antitone_of_isGreedy hgreedy
  have h2 : (2 : Fin 3) ∈ mctGame.Θ := by simp
  rw [P.cover_eq] at h2
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h2
  obtain ⟨t2, ht2⟩ := h2
  have hcard : 0 < P.card := by have := t2.isLt; omega
  set t0 : Fin P.card := ⟨0, hcard⟩ with ht0
  have ht0val : (t0 : ℕ) = 0 := rfl
  have hfilter0 : (Finset.univ.filter (fun s => t0 ≤ s)) = (Finset.univ : Finset (Fin P.card)) := by
    apply Finset.filter_true_of_mem
    intro s _; rw [Fin.le_def]; exact Nat.zero_le _
  have hR0 : thetaStep P.C t0 = mctGame.Θ := by
    unfold thetaStep; rw [hfilter0]; exact P.cover_eq.symm
  have hgame0 :
      mctGame.restrict (thetaStep P.C t0)
        (thetaStep_nonempty t0 (P.C_nonempty t0)) (P.thetaStep_subset t0) = mctGame :=
    (Partition.restrict_eq_of_eq hR0 _ _ mctGame.Θ_nonempty subset_rfl).trans restrict_self
  have hstep0 : P.stepPayoffs t0 = mctGame.coalitionPayoffs := by
    unfold Partition.stepPayoffs; rw [hgame0]
  have hw0 : P.w t0 = 1 / 2 := by
    have hge : IsGreatest (P.greedyConstraint t0) (1 / 2) := by
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hstep0]; exact mct_half_mem
      · unfold Partition.greedyLower
        apply Finset.sup'_le
        intro θ _; exact mct_skeptical_le_half θ
      · intro t' ht'; exfalso; rw [ht0val] at ht'; omega
      · rintro w ⟨hwstep, -, -⟩
        rw [hstep0] at hwstep
        obtain ⟨K, rfl⟩ := hwstep
        exact mct_coalition_w_le_half K
    exact IsGreatest.unique (hgreedy t0) hge
  have hexcl0 : mctGame.preimageSetFull (P.σ t0).evidence ⊆ P.C t0 := by
    have h := P.exclusive t0
    rw [hR0] at h; exact h
  have hcell : P.C t0 = ({0, 1} : Finset (Fin 3)) := by
    have hK : (⟨P.C t0, P.C_nonempty t0, P.C_subset t0, P.σ t0, hexcl0, P.w t0,
        P.payoff t0⟩ : Coalition mctGame).w = 1 / 2 := hw0
    exact mct_coalition_w_half_cell _ hK
  have ht2ne : t2 ≠ t0 := by
    intro h; rw [h, hcell] at ht2
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht2
    rcases ht2 with h' | h' <;> exact absurd (congrArg Fin.val h') (by norm_num)
  have hR2 : thetaStep P.C t2 = ({2} : Finset (Fin 3)) := by
    apply Finset.Subset.antisymm
    · intro θ hθ
      simp only [thetaStep, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and] at hθ
      obtain ⟨s, hts, hθs⟩ := hθ
      have hst0 : s ≠ t0 := by
        intro h; subst h
        exact ht2ne (le_antisymm hts (by rw [Fin.le_def, ht0val]; exact Nat.zero_le _))
      have hθnot : θ ∉ P.C t0 := Finset.disjoint_left.mp (P.C_disjoint s t0 hst0) hθs
      rw [hcell] at hθnot
      have hθΘ : θ ∈ mctGame.Θ := P.C_subset s hθs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hθnot ⊢
      fin_cases θ <;> simp_all
    · intro θ hθ
      rw [Finset.mem_singleton] at hθ; subst hθ
      simp only [thetaStep, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨t2, le_rfl, ht2⟩
  have hw2 : P.w t2 = 9 / 10 := by
    have hmem := P.w_mem_stepPayoffs t2
    unfold Partition.stepPayoffs at hmem
    rw [Partition.restrict_eq_of_eq hR2 _ _ (Finset.singleton_nonempty _)
      (Finset.subset_univ _)] at hmem
    exact mct_residual_singleton _ _ hmem
  have hle : P.w t2 ≤ P.w t0 := hmono (by rw [Fin.le_def, ht0val]; exact Nat.zero_le _)
  rw [hw0, hw2] at hle; norm_num at hle

variable {T Msg : Type*} [Fintype T] [Fintype Msg] {G : DisclosureGame T Msg}

/-- A one-type game admits a COE partition (its single cell is the whole type space). -/
private lemma one_type_coe (H : DisclosureGame T Msg) (hcard : H.Θ.card = 1) :
    ∃ P : Partition H, P.IsCOE := by
  obtain ⟨w, hw⟩ := IsCompact.exists_isGreatest (isCompact_coalitionPayoffs H)
    (coalitionPayoffs_nonempty H)
  obtain ⟨K, hKw⟩ := hw.1
  have hCsub : K.C ⊆ H.Θ := K.C_subset
  have hCΘ : H.Θ \ K.C = ∅ := by
    have hcardC : K.C.card = 1 := le_antisymm (hcard ▸ Finset.card_le_card hCsub)
      (Finset.card_pos.mpr K.C_nonempty)
    have : K.C = H.Θ := Finset.eq_of_subset_of_card_le hCsub (by rw [hcard, hcardC])
    rw [this, Finset.sdiff_self]
  exact t4_single_cell_coe H K hCΘ (hKw ▸ hw)

/-
In a one-type residual game, every coalition payoff is at most `v̄` of the
residual conditional prior (all posteriors equal that prior).
-/
private lemma binary_res_le_vbar {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (hRcard : R.card = 1) (K' : Coalition (G.restrict R hne hsub)) :
    K'.w ≤ G.vbar (G.condPrior R) := by
  -- By `K'.payoff`, `K'.w ∈ G.V (K'.σ.coalitionBelief m)` (using `restrict_V`).
  obtain ⟨m, hm⟩ : ∃ m, m ∈ K'.σ.evidence := by
    obtain ⟨ θ, hθ ⟩ := K'.C_nonempty; have := K'.preimage_eq.symm ▸ hθ; simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
    exact this.2.imp fun x hx => by aesop;
  have h_ver : K'.w ∈ G.V (K'.σ.coalitionBelief m) := by
    convert K'.payoff m hm using 1
  generalize_proofs at *; (
  -- By `restrict_coalitionBelief_eq`, `K'.σ.coalitionBelief m = condPrior R` (both are distributions supported on the single-element set `R`).
  have h_coalitionBelief : K'.σ.coalitionBelief m = G.condPrior R := by
    have h_coalitionBelief : ∀ μ ∈ simplexOn R, μ = G.condPrior R := by
      obtain ⟨ η, rfl ⟩ := Finset.card_eq_one.mp hRcard; simp +decide [ DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
      intro μ hμ₁ hμ₂ hμ₃; ext a; by_cases ha : a = η <;> simp_all +decide [ DisclosureGame.condPrior ];
      simp_all +decide [ Finset.sum_eq_single η, DisclosureGame.priorMeasure ];
      rw [ div_self ( ne_of_gt ( G.μ0_fullSupport η ( hsub ( by simp +decide ) ) ) ) ]
    generalize_proofs at *; (
    apply_rules [ DisclosureGame.zeroExt_mem_simplex, K'.σ.belief_mem_simplex ])
  generalize_proofs at *; (
  rw [ h_coalitionBelief ] at h_ver; exact DisclosureGame.le_vbar ( G.condPrior_mem_simplex hne hsub |> fun h => simplexOn_mono hsub h ) h_ver;))

/-- Two closed sets covering `[a,b]`, one containing `a`, the other `b`, meet. -/
private lemma icc_cover_meet {a b : ℝ} (hab : a ≤ b) {u v : Set ℝ}
    (hu : IsClosed u) (hv : IsClosed v) (hcover : Set.Icc a b ⊆ u ∪ v)
    (hau : a ∈ u) (hbv : b ∈ v) : ∃ c ∈ Set.Icc a b, c ∈ u ∧ c ∈ v := by
  by_contra h
  push_neg at h
  have hpc : IsPreconnected (Set.Icc a b) := isPreconnected_Icc
  have key := hpc uᶜ vᶜ hu.isOpen_compl hv.isOpen_compl
  have hc2 : Set.Icc a b ⊆ uᶜ ∪ vᶜ := by
    intro x hx
    rcases em (x ∈ u) with hxu | hxu
    · right; intro hxv; exact (h x hx hxu) hxv
    · left; exact hxu
  have ha' : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb' : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have hnv : (Set.Icc a b ∩ vᶜ).Nonempty := ⟨a, ha', fun hav => (h a ha' hau) hav⟩
  have hnu : (Set.Icc a b ∩ uᶜ).Nonempty := ⟨b, hb', fun hbu => (h b hb' hbu) hbv⟩
  obtain ⟨x, hx, hxu, hxv⟩ := key hc2 hnu hnv
  rcases hcover hx with h1 | h1
  · exact hxu h1
  · exact hxv h1

/-- The segment belief with weight `c` at `θ'` and `1-c` at `θ`. -/
private noncomputable def binQ (θ θ' : T) (c : ℝ) : T → ℝ :=
  fun x => if x = θ' then c else if x = θ then 1 - c else 0

private lemma continuous_binQ (θ θ' : T) : Continuous (fun c : ℝ => binQ θ θ' c) := by
  apply continuous_pi; intro x; unfold binQ; split_ifs <;> fun_prop

private lemma binQ_mem_simplex {θ θ' : T} (hdist : θ ≠ θ') (hΘ : G.Θ = {θ, θ'})
    {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) : binQ θ θ' c ∈ simplexOn G.Θ := by
  unfold binQ; simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
  rw [ Finset.card_filter ]; aesop

private lemma binQ_one {θ θ' : T} (hθ'Θ : θ' ∈ G.Θ) (hdist : θ ≠ θ') :
    binQ θ θ' 1 = G.condPrior ({θ'} : Finset T) := by
  ext x
  unfold binQ
  by_cases hx : x = θ'
  · subst hx
    rw [if_pos rfl, condPrior_of_mem (Finset.mem_singleton_self x)]
    have hpos : 0 < G.μ0 x := G.μ0_fullSupport x hθ'Θ
    simp only [DisclosureGame.priorMeasure, Finset.sum_singleton]
    exact (div_self (ne_of_gt hpos)).symm
  · rw [if_neg hx, condPrior_of_not_mem (by simpa using hx)]
    by_cases hx2 : x = θ
    · rw [if_pos hx2]; ring
    · rw [if_neg hx2]

private lemma binQ_prior {θ θ' : T} (hθΘ : θ ∈ G.Θ) (hθ'Θ : θ' ∈ G.Θ) (hdist : θ ≠ θ')
    (hΘ : G.Θ = {θ, θ'}) : binQ θ θ' (G.μ0 θ') = G.condPrior G.Θ := by
  -- Start by expanding the definition of `binQ` (a nested `if` expression). This simplifies the LHS for the main goal `binQ θ θ' (G.μ0 θ') = G.condPrior G.Θ`.
  ext a
  unfold binQ
  simp at *;
  have hsum : G.μ0 θ + G.μ0 θ' = 1 := by
    have hsum : ∑ a ∈ G.Θ, G.μ0 a = 1 := by
      convert G.μ0_mem.2.1 using 1;
      exact Finset.sum_subset ( Finset.subset_univ _ ) fun x hx₁ hx₂ => by have := G.μ0_mem.2.2 x; aesop;
    rw [ ← hsum, hΘ, Finset.sum_pair hdist ];
  unfold DisclosureGame.condPrior; simp +decide [ hΘ, hsum.symm ];
  unfold DisclosureGame.priorMeasure; simp +decide [ hΘ, hsum ];
  grind

/-
A singleton coalition realizing any payoff in `V(δ_η)`, when `η` is the sole
sender of some message `m`.
-/
private lemma binary_singleton_coalition {η : T} {m : Msg} (hcs : G.canSend m = ({η} : Finset T))
    {w : ℝ} (hw : w ∈ G.V (G.condPrior ({η} : Finset T))) :
    ∃ K : Coalition G, K.C = ({η} : Finset T) ∧ K.w = w := by
  have hηΘ : η ∈ G.Θ := by
    have hη_in_canSend : η ∈ G.canSend m := hcs.symm ▸ Finset.mem_singleton_self _
    rw [DisclosureGame.canSend, DisclosureGame.preimageFull] at hη_in_canSend
    exact (mem_preimage.mp hη_in_canSend).1
  generalize_proofs at *; (
  have hmMη : m ∈ G.M η := by
    replace hcs := Finset.ext_iff.mp hcs η; simp_all +decide [ DisclosureGame.canSend, DisclosureGame.preimageSetFull ];
    unfold DisclosureGame.preimageFull at hcs; simp_all +decide [ DisclosureGame.preimageSet, preimage ];
    obtain ⟨ x, hx ⟩ := hcs; aesop;
  generalize_proofs at *; (
  refine' ⟨ ⟨ { η }, _, _, _, _, w, _ ⟩, rfl, rfl ⟩ <;> norm_num [ hηΘ, hmMη ];
  use fun _ => fun m' => if m' = m then 1 else 0;
  all_goals norm_num [ DisclosureGame.restrict, DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
  grind +suggestions;
  · simp_all +decide [ Finset.ext_iff, DisclosureGame.canSend ];
    simp_all +decide [ DisclosureGame.preimageFull, Set.Nonempty ];
    simp_all +decide [ preimage, Strategy.evidence, Strategy.msgSupport ];
    exact Or.inr fun a => by specialize hcs a; aesop;
  · intro m' hm'
    have hm'_eq_m : m' = m := by
      unfold Strategy.evidence at hm'; simp_all +decide [ Strategy.msgSupport, Strategy.onPathProb_pos_iff_mem_evidence ];
      split_ifs at hm' <;> simp_all +decide [ ne_of_gt ]
    generalize_proofs at *; (
    convert hw using 1
    simp [Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb, zeroExt];
    congr! 1
    generalize_proofs at *; (
    ext x; simp [Strategy.belief, Strategy.onPathProb, zeroExt, DisclosureGame.condPrior, DisclosureGame.priorMeasure]; split_ifs <;> simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
    rw [ div_self ( ne_of_gt ( G.μ0_fullSupport η hηΘ ) ), div_one ]))))

/-
**Full-Θ coalition construction.** With `θ'` (and `θ`) both able to send `m₀`,
and a segment belief `binQ θ θ' c` (`c ∈ [μ⁰θ', 1]`) at which `w₁` is feasible,
plus `w₁ ∈ V(δ_θ)` (realized by the singleton `{θ}` coalition `K₁`), there is a
coalition on all of `Θ` paying `w₁`.
-/
-- Larger heartbeat budget: constructing and verifying the pooling coalition is heavy.
set_option maxHeartbeats 1000000 in
private lemma binary_theta_coalition {θ θ' : T} (hθΘ : θ ∈ G.Θ) (hθ'Θ : θ' ∈ G.Θ)
    (hdist : θ ≠ θ') (hΘ : G.Θ = {θ, θ'}) {m₀ : Msg} (hcs : G.canSend m₀ = G.Θ)
    (K₁ : Coalition G) (hK₁C : K₁.C = ({θ} : Finset T)) (w₁ : ℝ)
    (hVθ : w₁ ∈ G.V (G.condPrior ({θ} : Finset T))) (hK₁w : K₁.w = w₁)
    {c : ℝ} (hc : c ∈ Set.Icc (G.μ0 θ') 1) (hcV : w₁ ∈ G.V (binQ θ θ' c)) :
    ∃ K : Coalition G, K.C = G.Θ ∧ K.w = w₁ := by
  -- Assume $m_0$ is not in the evidence of $K_1$, hence $K_1.σ.σ θ m_0 = 0$.
  have h_not_evidence : m₀ ∉ K₁.σ.evidence := by
    intro hm₀;
    have := K₁.exclusive ( show θ' ∈ G.preimageSetFull K₁.σ.evidence from by
                            simp +decide [ DisclosureGame.canSend, DisclosureGame.preimageSetFull ] at *;
                            simp +decide [ DisclosureGame.preimageSet, DisclosureGame.preimageFull ] at *;
                            replace hcs := Finset.ext_iff.mp hcs θ'; simp_all +decide [ preimage ];
                            obtain ⟨ m, hm ⟩ := hcs; use m; aesop; ); simp_all +decide [ Finset.subset_iff ];
  -- Define the new strategy $\tau$.
  obtain ⟨τ, hτ⟩ : ∃ τ : Strategy (G.restrict G.Θ G.Θ_nonempty subset_rfl), (∀ m, τ.σ θ m = ((G.μ0 θ') * (1 - c) / (G.μ0 θ * c)) * (if m = m₀ then 1 else 0) + (1 - ((G.μ0 θ') * (1 - c) / (G.μ0 θ * c))) * K₁.σ.σ θ m) ∧ (∀ m, τ.σ θ' m = if m = m₀ then 1 else 0) := by
    refine' ⟨ _, _, _ ⟩;
    constructor;
    rotate_left;
    use fun θ m => if θ = θ' then if m = m₀ then 1 else 0 else if θ = θ then (G.μ0 θ' * (1 - c) / (G.μ0 θ * c)) * (if m = m₀ then 1 else 0) + (1 - (G.μ0 θ' * (1 - c) / (G.μ0 θ * c))) * K₁.σ.σ θ m else 0;
    all_goals simp +decide [ hΘ, DisclosureGame.restrict ];
    · aesop;
    · refine' ⟨ ⟨ _, _, _ ⟩, _, _ ⟩;
      · intro m; split_ifs <;> norm_num;
        · refine' add_nonneg _ _;
          · exact div_nonneg ( mul_nonneg ( le_of_lt ( G.μ0_fullSupport θ' hθ'Θ ) ) ( sub_nonneg.2 hc.2 ) ) ( mul_nonneg ( le_of_lt ( G.μ0_fullSupport θ hθΘ ) ) ( hc.1.trans' ( le_of_lt ( G.μ0_fullSupport θ' hθ'Θ ) ) ) );
          · refine' mul_nonneg _ _;
            · rw [ sub_nonneg, div_le_iff₀ ];
              · have h_sum : G.μ0 θ + G.μ0 θ' = 1 := by
                  have := G.μ0_mem.2.1; simp_all +decide [ Finset.sum_pair ];
                  rw [ ← this, ← Finset.sum_subset ( Finset.subset_univ { θ, θ' } ) ] <;> simp +decide [ *, Finset.sum_pair ];
                  exact fun x hx₁ hx₂ => G.μ0_mem.2.2 x |> fun h => by have := G.μ0_fullSupport x; aesop;
                nlinarith [ hc.1, hc.2, G.μ0_fullSupport θ hθΘ, G.μ0_fullSupport θ' hθ'Θ ];
              · exact mul_pos ( G.μ0_fullSupport θ hθΘ ) ( lt_of_lt_of_le ( G.μ0_fullSupport θ' hθ'Θ ) hc.1 );
            · exact K₁.σ.mem θ ( by aesop ) |>.1 m;
        · refine' mul_nonneg _ _;
          · rw [ sub_nonneg, div_le_iff₀ ];
            · have h_sum : G.μ0 θ + G.μ0 θ' = 1 := by
                have := G.μ0_mem.2.1; simp_all +decide [ Finset.sum_pair ];
                rw [ ← this, ← Finset.sum_subset ( Finset.subset_univ { θ, θ' } ) ] <;> simp +decide [ * ];
                intro x hx hx'; have := G.μ0_mem.2.2 x; simp_all +decide [ Finset.ext_iff ];
              nlinarith [ hc.1, hc.2, G.μ0_fullSupport θ hθΘ, G.μ0_fullSupport θ' hθ'Θ ];
            · exact mul_pos ( G.μ0_fullSupport θ hθΘ ) ( lt_of_lt_of_le ( G.μ0_fullSupport θ' hθ'Θ ) hc.1 );
          · exact K₁.σ.mem θ ( by aesop ) |>.1 m;
      · have := K₁.σ.mem θ; simp_all +decide [ Strategy.belief, Strategy.onPathProb_pos_iff_mem_evidence ];
        simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
        rw [ ← Finset.mul_sum _ _ _, this.2.1 ]; ring;
      · intro a ha; split_ifs <;> simp_all +decide [ Strategy.evidence, Strategy.msgSupport ];
        · simp_all +decide [ Finset.ext_iff, DisclosureGame.canSend ];
          specialize hcs θ; simp_all +decide [ DisclosureGame.preimageFull ];
          simp_all +decide [ preimage ];
        · exact Or.inr ( by have := K₁.σ.mem θ; simp_all +decide [ Strategy.onPathProb_pos_iff_mem_evidence ] );
      · exact fun _ => by split_ifs <;> norm_num;
      · intro m hm hnm; simp_all +decide [ DisclosureGame.canSend ];
        simp_all +decide [ Finset.ext_iff, DisclosureGame.preimageFull ];
        specialize hcs θ'; simp_all +decide [ preimage ];
  refine' ⟨ ⟨ G.Θ, G.Θ_nonempty, subset_rfl, τ, _, w₁, _ ⟩, rfl, rfl ⟩;
  · exact fun x hx => by simp +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ] at hx ⊢; aesop;
  · intro m hm; by_cases hm' : m = m₀ <;> simp_all +decide [ Strategy.evidence, Strategy.msgSupport, Strategy.onPathProb_pos_iff_mem_evidence ];
    · convert hcV using 1;
      congr! 1;
      ext x; simp +decide [ Strategy.coalitionBelief, Strategy.belief, Strategy.onPathProb, zeroExt ];
      by_cases hx : x = θ <;> by_cases hx' : x = θ' <;> simp +decide [ *, Finset.sum_pair, binQ ];
      · grind;
      · rw [ show K₁.σ.σ θ m₀ = 0 from le_antisymm h_not_evidence ( by have := K₁.σ.mem θ; simp_all +decide [ Strategy.onPathProb_pos_iff_mem_evidence ] ) ]; simp +decide [ *, DisclosureGame.condPrior ]; ring;
        by_cases hc : c = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        · exact absurd ‹G.μ0 θ' ≤ 0› ( not_le_of_gt ( G.μ0_fullSupport θ' ( by simp +decide [ hΘ ] ) ) );
        · field_simp;
          rw [ div_eq_iff ] <;> ring;
          · grind;
          · simp +decide [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( G.μ0_fullSupport θ ( by simp +decide [ hΘ ] ) ), ne_of_gt ( G.μ0_fullSupport θ' ( by simp +decide [ hΘ ] ) ) ];
            exact ne_of_gt ( Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( by aesop ) ) ( by aesop ) );
      · rw [ show K₁.σ.σ θ m₀ = 0 from le_antisymm h_not_evidence ( by have := K₁.σ.mem θ; aesop ) ]; simp +decide [ *, DisclosureGame.condPrior ]; ring;
        by_cases hc : c = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        · exact Or.inr ( le_antisymm ‹_› ( G.μ0_mem.1 _ ) );
        · by_cases h : G.μ0 θ = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
          · exact absurd h ( ne_of_gt ( G.μ0_fullSupport θ ( by simp +decide [ hΘ ] ) ) );
          · simp +decide [ DisclosureGame.priorMeasure, h, hx, hx', Finset.sum_pair, hdist ];
            rw [ ← mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( add_pos ( G.μ0_fullSupport θ ( by simp +decide [ hΘ ] ) ) ( G.μ0_fullSupport θ' ( by simp +decide [ hΘ ] ) ) ) ), one_mul, mul_inv_cancel₀ ( ne_of_gt ( G.μ0_fullSupport θ' ( by simp +decide [ hΘ ] ) ) ) ];
    · convert hVθ using 1;
      congr! 1;
      ext x; simp +decide [ *, DisclosureGame.restrict_coalitionBelief_eq, DisclosureGame.condPrior ];
      split_ifs <;> simp_all +decide [ DisclosureGame.priorMeasure ];
      grind

/-
A singleton-cell coalition's belief at any on-path message is the point mass.
-/
private lemma coalition_singleton_belief {η : T} (K : Coalition G) (hKC : K.C = ({η} : Finset T))
    {m : Msg} (hm : m ∈ K.σ.evidence) :
    K.σ.coalitionBelief m = G.condPrior ({η} : Finset T) := by
  apply Eq.symm; exact (by
    have h_singleton : ∀ μ ∈ simplexOn ({η} : Finset T), μ = G.condPrior ({η} : Finset T) := by
      intro μ hμ; ext x; by_cases hx : x = η <;> simp_all +decide [ DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
      rw [ div_self ( ne_of_gt ( G.μ0_fullSupport η ( by have := K.C_subset; aesop ) ) ) ]; have := hμ.2.1; rw [ Finset.sum_eq_single η ] at this <;> aesop;
    generalize_proofs at *; (
    apply Eq.symm; exact (by
      have h_mem : K.σ.coalitionBelief m ∈ simplexOn ({η} : Finset T) := by
        convert DisclosureGame.zeroExt_mem_simplex ( show K.C ⊆ K.C from Finset.Subset.refl _ ) ( K.σ.belief_mem_simplex hm ) using 1
        generalize_proofs at *; (
        rw [ hKC ])
      generalize_proofs at *; exact h_singleton _ h_mem)))

/-- Topological key step of the two-type existence theorem. If the greatest
coalition payoff `w₁` is not attained by a full-Θ coalition and is attained
by the singleton `{θ}`, then `v̄(δ_{θ'}) ≤ w₁` for the other type `θ'`. -/
private lemma binary_vbar_key {θ θ' : T} (hθΘ : θ ∈ G.Θ) (hθ'Θ : θ' ∈ G.Θ)
    (hdist : θ ≠ θ') (hΘ : G.Θ = {θ, θ'})
    (w₁ : ℝ) (hw₁ : IsGreatest G.coalitionPayoffs w₁)
    (hno : ¬ ∃ K : Coalition G, K.C = G.Θ ∧ K.w = w₁)
    (K₁ : Coalition G) (hK₁C : K₁.C = {θ}) (hK₁w : K₁.w = w₁) :
    G.vbar (G.condPrior ({θ'} : Finset T)) ≤ w₁ := by
  classical
  by_contra hgt
  push_neg at hgt
  have ha1 : G.μ0 θ' ≤ 1 :=
    le_trans (Finset.single_le_sum (fun x _ => G.μ0_mem.1 x) (Finset.mem_univ θ'))
      (le_of_eq G.μ0_mem.2.1)
  -- Step 2: a message `m₀ ∈ M θ'` with `canSend m₀ = Θ`.
  obtain ⟨m₀, hm₀M, hcs⟩ : ∃ m₀, m₀ ∈ G.M θ' ∧ G.canSend m₀ = G.Θ := by
    obtain ⟨m₀, hm₀⟩ := G.M_nonempty θ' hθ'Θ
    refine ⟨m₀, hm₀, ?_⟩
    have hθ'cs : θ' ∈ G.canSend m₀ := by
      simp only [DisclosureGame.canSend, DisclosureGame.preimageFull, mem_preimage]
      exact ⟨hθ'Θ, m₀, Finset.mem_inter.mpr ⟨hm₀, Finset.mem_singleton_self _⟩⟩
    have hcssub : G.canSend m₀ ⊆ G.Θ := Finset.filter_subset _ _
    by_contra hcsne
    have hθnotcs : θ ∉ G.canSend m₀ := by
      intro hθcs
      apply hcsne
      apply Finset.Subset.antisymm hcssub
      rw [hΘ]; intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hsingle : G.canSend m₀ = ({θ'} : Finset T) := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hxΘ := hcssub hx; rw [hΘ] at hxΘ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxΘ ⊢
        rcases hxΘ with rfl | rfl
        · exact absurd hx hθnotcs
        · rfl
      · intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact hθ'cs
    obtain ⟨K, _, hKw⟩ := binary_singleton_coalition hsingle
      (vbar_mem (simplexOn_mono (Finset.singleton_subset_iff.mpr hθ'Θ)
        (G.condPrior_mem_simplex (Finset.singleton_nonempty _)
          (Finset.singleton_subset_iff.mpr hθ'Θ))))
    have hle := hw₁.2 ⟨K, rfl⟩
    rw [hKw] at hle
    exact absurd hle (not_le.mpr hgt)
  -- Step 1: `w₁ ∈ V(δ_θ)` from the singleton coalition `K₁`.
  have hVθ : w₁ ∈ G.V (G.condPrior ({θ} : Finset T)) := by
    obtain ⟨m, hm⟩ : ∃ m, m ∈ K₁.σ.evidence := by
      have hθpre : θ ∈ G.preimageSetFull K₁.σ.evidence := by
        rw [K₁.preimage_eq, hK₁C]; exact Finset.mem_singleton_self θ
      rw [DisclosureGame.preimageSetFull, mem_preimageSet] at hθpre
      obtain ⟨m, hmint⟩ := hθpre.2
      exact ⟨m, hmint.2⟩
    have hb := coalition_singleton_belief K₁ hK₁C hm
    have hp := K₁.payoff m hm
    rw [hb] at hp
    rwa [hK₁w] at hp
  -- Step 3: the covering argument.
  set a := G.μ0 θ' with ha_def
  have hsimp : ∀ c ∈ Set.Icc a 1, binQ θ θ' c ∈ simplexOn G.Θ := by
    intro c hc
    exact binQ_mem_simplex hdist hΘ
      ⟨le_trans (le_of_lt (G.μ0_fullSupport θ' hθ'Θ)) hc.1, hc.2⟩
  have hcont : ContinuousOn (fun c : ℝ => binQ θ θ' c) (Set.Icc a 1) :=
    (continuous_binQ θ θ').continuousOn
  have hmaps : Set.MapsTo (fun c : ℝ => binQ θ θ' c) (Set.Icc a 1) (simplexOn G.Θ) := hsimp
  have husc : UpperSemicontinuousOn (fun c : ℝ => G.vbar (binQ θ θ' c)) (Set.Icc a 1) :=
    (vbar_upperSemicontinuousOn (G := G)).comp hcont hmaps
  have hlsc : LowerSemicontinuousOn (fun c : ℝ => G.vlow (binQ θ θ' c)) (Set.Icc a 1) :=
    (vlow_lowerSemicontinuousOn (G := G)).comp hcont hmaps
  set u : Set ℝ := Set.Icc a 1 ∩ {c | w₁ ≤ G.vbar (binQ θ θ' c)} with hu_def
  set v : Set ℝ := Set.Icc a 1 ∩ {c | G.vlow (binQ θ θ' c) ≤ w₁} with hv_def
  have hu_closed : IsClosed u := by
    obtain ⟨V', hV'c, hV'E⟩ := (upperSemicontinuousOn_iff_preimage_Ici.mp husc) w₁
    have : u = Set.Icc a 1 ∩ V' := by rw [hu_def, ← hV'E]; rfl
    rw [this]; exact isClosed_Icc.inter hV'c
  have hv_closed : IsClosed v := by
    obtain ⟨V', hV'c, hV'E⟩ := (lowerSemicontinuousOn_iff_preimage_Iic.mp hlsc) w₁
    have : v = Set.Icc a 1 ∩ V' := by rw [hv_def, ← hV'E]; rfl
    rw [this]; exact isClosed_Icc.inter hV'c
  have hcover : Set.Icc a 1 ⊆ v ∪ u := by
    intro c hc
    have hmem := hmaps hc
    by_cases h : w₁ ≤ G.vbar (binQ θ θ' c)
    · exact Or.inr ⟨hc, h⟩
    · push_neg at h
      exact Or.inl ⟨hc, le_of_lt (lt_of_le_of_lt (G.vlow_le hmem (vbar_mem hmem)) h)⟩
  have hav : a ∈ v := by
    refine ⟨⟨le_refl a, ha1⟩, ?_⟩
    change G.vlow (binQ θ θ' a) ≤ w₁
    rw [ha_def, binQ_prior hθΘ hθ'Θ hdist hΘ]
    have hmem : G.vlow (G.condPrior (G.canSend m₀)) ∈ G.coalitionPayoffs :=
      Partition.vlow_condPrior_canSend_mem_coalitionPayoffs G (G.M_subset θ' hθ'Θ hm₀M)
    rw [← hcs]; exact hw₁.2 hmem
  have h1u : (1 : ℝ) ∈ u := by
    refine ⟨⟨ha1, le_refl 1⟩, ?_⟩
    change w₁ ≤ G.vbar (binQ θ θ' 1)
    rw [binQ_one hθ'Θ hdist]; exact le_of_lt hgt
  obtain ⟨c, hcIcc, hcv, hcu⟩ := icc_cover_meet ha1 hv_closed hu_closed hcover hav h1u
  have hμc : binQ θ θ' c ∈ simplexOn G.Θ := hsimp c hcIcc
  have hVc : w₁ ∈ G.V (binQ θ θ' c) := by
    rw [V_eq_Icc hμc]; exact ⟨hcv.2, hcu.2⟩
  rw [ha_def] at hcIcc
  exact hno (binary_theta_coalition hθΘ hθ'Θ hdist hΘ hcs K₁ hK₁C w₁ hVθ hK₁w hcIcc hVc)

/-- Crux of the two-type existence theorem. For `|Θ| = 2`, when the greatest
coalition payoff `w₁` is not attained by any full-Θ coalition, removing a
max singleton cell cannot raise the residual maximum above `w₁`. -/
private lemma binary_residual_bound (h2 : G.Θ.card = 2) (w₁ : ℝ)
    (hw₁ : IsGreatest G.coalitionPayoffs w₁)
    (hno : ¬ ∃ K : Coalition G, K.C = G.Θ ∧ K.w = w₁)
    (K₁ : Coalition G) (hK₁w : K₁.w = w₁)
    (hne : (G.Θ \ K₁.C).Nonempty) (hsub : (G.Θ \ K₁.C) ⊆ G.Θ) (w' : ℝ)
    (hw' : IsGreatest (G.restrict (G.Θ \ K₁.C) hne hsub).coalitionPayoffs w') :
    w' ≤ w₁ := by
  -- `K₁.C` is a singleton `{θ}`
  have hK₁CΘ : K₁.C ≠ G.Θ := fun h => hno ⟨K₁, h, hK₁w⟩
  have hK₁card1 : K₁.C.card = 1 := by
    have hle : K₁.C.card ≤ 2 := h2 ▸ Finset.card_le_card K₁.C_subset
    have hpos : 1 ≤ K₁.C.card := Finset.card_pos.mpr K₁.C_nonempty
    have hne2 : K₁.C.card ≠ 2 :=
      fun h => hK₁CΘ (Finset.eq_of_subset_of_card_le K₁.C_subset (by omega))
    omega
  obtain ⟨θ, hθ⟩ := Finset.card_eq_one.mp hK₁card1
  have hRcard : (G.Θ \ K₁.C).card = 1 := by
    have hsum : (G.Θ \ K₁.C).card + K₁.C.card = 2 := by
      rw [← h2]; exact Finset.card_sdiff_add_card_eq_card K₁.C_subset
    omega
  obtain ⟨θ', hθ'⟩ := Finset.card_eq_one.mp hRcard
  have hθΘ : θ ∈ G.Θ := K₁.C_subset (hθ ▸ Finset.mem_singleton_self θ)
  have hθ'mem : θ' ∈ G.Θ \ K₁.C := hθ' ▸ Finset.mem_singleton_self θ'
  have hθ'Θ : θ' ∈ G.Θ := (Finset.mem_sdiff.mp hθ'mem).1
  have hdist : θ ≠ θ' := by
    intro h; subst h
    exact (Finset.mem_sdiff.mp hθ'mem).2 (hθ ▸ Finset.mem_singleton_self θ)
  have hΘset : G.Θ = {θ, θ'} := by
    have hu := Finset.sdiff_union_of_subset K₁.C_subset
    rw [hθ', hθ] at hu
    rw [← hu]; ext a
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  -- residual max `w'` is realized by some coalition
  obtain ⟨K', hK'⟩ := hw'.1
  have hle1 : K'.w ≤ G.vbar (G.condPrior (G.Θ \ K₁.C)) :=
    binary_res_le_vbar hne hsub hRcard K'
  have hle2 : G.vbar (G.condPrior (G.Θ \ K₁.C)) ≤ w₁ := by
    rw [hθ']
    exact binary_vbar_key hθΘ hθ'Θ hdist hΘset w₁ hw₁ hno K₁ hθ hK₁w
  rw [← hK']
  exact le_trans hle1 hle2

/-- A max cell for `|Θ| = 2` whose removal cannot raise the residual maximum. -/
private lemma binary_max_cell (h2 : G.Θ.card = 2) :
    ∃ K : Coalition G, IsGreatest G.coalitionPayoffs K.w ∧
      ∀ (hne : (G.Θ \ K.C).Nonempty) (hsub : (G.Θ \ K.C) ⊆ G.Θ) (w' : ℝ),
        IsGreatest (G.restrict (G.Θ \ K.C) hne hsub).coalitionPayoffs w' → w' ≤ K.w := by
  obtain ⟨w₁, hw₁⟩ := IsCompact.exists_isGreatest (isCompact_coalitionPayoffs G)
    (coalitionPayoffs_nonempty G)
  by_cases hΘc : ∃ K : Coalition G, K.C = G.Θ ∧ K.w = w₁
  · obtain ⟨K, hCΘ, hKw⟩ := hΘc
    refine ⟨K, by rw [hKw]; exact hw₁, ?_⟩
    intro hne hsub w' hw'
    exact absurd hne (by rw [hCΘ, Finset.sdiff_self]; exact Finset.not_nonempty_empty)
  · obtain ⟨K₁, hK₁w⟩ := hw₁.1
    refine ⟨K₁, by rw [hK₁w]; exact hw₁, ?_⟩
    intro hne hsub w' hw'
    rw [hK₁w]
    exact binary_residual_bound h2 w₁ hw₁ hΘc K₁ hK₁w hne hsub w' hw'

/-- **Theorem 6.** If
`|Θ| = 2`, every disclosure game admits a coalition-proof PBE. -/
theorem binary_existence (h2 : G.Θ.card = 2) :
    ∃ P : Partition G, P.IsCPPBEPartition := by
  obtain ⟨K, hKmax, hbound⟩ := binary_max_cell h2
  by_cases hempty : G.Θ \ K.C = ∅
  · obtain ⟨P, hP⟩ := t4_single_cell_coe G K hempty hKmax
    exact ⟨P, hP.isCPPBEPartition⟩
  · have hne : (G.Θ \ K.C).Nonempty := Finset.nonempty_of_ne_empty hempty
    have hsub : (G.Θ \ K.C) ⊆ G.Θ := Finset.sdiff_subset
    have hres1 : (G.restrict (G.Θ \ K.C) hne hsub).Θ.card = 1 := by
      rw [restrict_Θ]
      have hsum : (G.Θ \ K.C).card + K.C.card = 2 := by
        rw [← h2]; exact Finset.card_sdiff_add_card_eq_card K.C_subset
      have hpos : 1 ≤ (G.Θ \ K.C).card := Finset.card_pos.mpr hne
      have hCpos : 1 ≤ K.C.card := Finset.card_pos.mpr K.C_nonempty
      omega
    obtain ⟨Pres, hPres⟩ := one_type_coe _ hres1
    obtain ⟨P, hP⟩ := t4_prepend_coe G K hKmax hne hsub (hbound hne hsub) Pres hPres
    exact ⟨P, hP.isCPPBEPartition⟩

end DisclosureGame

end CPD
