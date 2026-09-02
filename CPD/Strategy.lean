import CPD.Game

/-!
# Sender strategies, evidence, and induced beliefs  (§2: Strategies)

A **sender strategy** `σ : Θ → Δ𝓜` with `supp σ(·|θ) ⊆ M(θ)`, its **evidence**
`X(σ) := ⋃_θ supp σ(·|θ)`, the **on-path probability** `p_σ(m)`, and the
**induced belief** `μ_σ(·|m)` obtained from `σ` by Bayes' rule.
-/

open Set

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg] {G : DisclosureGame T Msg}

/-- **§2 (Strategies).** A **sender strategy** `σ : Θ → Δ𝓜` with
`supp σ(·|θ) ⊆ M(θ)`. -/
structure Strategy (G : DisclosureGame T Msg) where
  /-- For each type, a probability distribution over messages, `σ(·|θ)`. -/
  σ : T → Msg → ℝ
  /-- For `θ ∈ Θ`, `σ(·|θ)` is a distribution supported inside `M θ`. -/
  mem : ∀ θ ∈ G.Θ, σ θ ∈ simplexOn (G.M θ)

namespace Strategy

variable (s : Strategy G)

/-
`σ(·|θ) ∈ Δ𝓜`.
-/
lemma mem_msgSimplex {θ : T} (hθ : θ ∈ G.Θ) : s.σ θ ∈ simplexOn G.𝓜 := by
  have h_sub : ∀ a ∉ G.𝓜, s.σ θ a = 0 := by
    exact fun a ha => s.mem θ hθ |>.2.2 a ( fun h => ha <| G.M_subset θ hθ h );
  exact ⟨ fun a ↦ ( s.mem θ hθ ).1 a, ( s.mem θ hθ ).2.1, h_sub ⟩

/-- **§2 (Strategies).** The support of `σ(·|θ)`. -/
def msgSupport (θ : T) : Set Msg := simplexSupport (s.σ θ)

/-- **§2 (Strategies).** The **evidence** of `σ`:
`X(σ) := ⋃_{θ ∈ Θ} supp σ(·|θ)`. -/
def evidence : Set Msg := ⋃ θ ∈ G.Θ, s.msgSupport θ

/-- **§2 (Strategies).** The on-path probability
`p_σ(m) := ∑_{θ ∈ Θ} μ⁰(θ) σ(m|θ)`. -/
noncomputable def onPathProb (m : Msg) : ℝ := ∑ θ ∈ G.Θ, G.μ0 θ * s.σ θ m

/-- **§2 (Strategies).** On-path messages are exactly the evidence. -/
lemma onPathProb_pos_iff_mem_evidence (m : Msg) :
    0 < s.onPathProb m ↔ m ∈ s.evidence := by
  constructor <;> intro h;
  · contrapose! h;
    refine' Finset.sum_nonpos fun θ hθ => mul_nonpos_of_nonneg_of_nonpos ( G.μ0_mem.1 θ ) _;
    exact le_of_not_gt fun hm => h <| Set.mem_iUnion₂.2 ⟨ θ, hθ, hm ⟩;
  · obtain ⟨ θ, hθ ⟩ := Set.mem_iUnion₂.mp h;
    refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => mul_nonneg ( le_of_lt ( G.μ0_fullSupport x ‹_› ) ) ( s.mem x ‹_› |>.1 m ) ) ( Finset.mem_coe.mpr hθ.1 ) );
    exact mul_pos ( G.μ0_fullSupport θ hθ.1 ) hθ.2

/-- **§2 (Strategies).** The induced (Bayesian) belief
`μ_σ(θ|m) := μ⁰(θ) σ(m|θ) / p_σ(m)`. -/
noncomputable def belief (m : Msg) : T → ℝ :=
  fun θ => G.μ0 θ * s.σ θ m / s.onPathProb m

/-- **§2 (Strategies).** The induced belief is a probability distribution in
`Δ Θ`. -/
lemma belief_mem_simplex {m : Msg} (hm : m ∈ s.evidence) :
    s.belief m ∈ simplexOn G.Θ := by
  refine' ⟨ _, _, _ ⟩;
  · intro θ; by_cases hθ : θ ∈ G.Θ <;> simp_all +decide [ Strategy.belief ] ;
    · exact div_nonneg ( mul_nonneg ( G.μ0_fullSupport θ hθ |> le_of_lt ) ( s.mem θ hθ |>.1 m ) ) ( Finset.sum_nonneg fun _ _ => mul_nonneg ( G.μ0_fullSupport _ ‹_› |> le_of_lt ) ( s.mem _ ‹_› |>.1 _ ) );
    · have := G.μ0_mem.2.2 θ hθ; aesop;
  · have h_sum : ∑ θ, G.μ0 θ * s.σ θ m = s.onPathProb m := by
      rw [ ← Finset.sum_subset ( Finset.subset_univ G.Θ ) ];
      · rfl;
      · intro x _ hx; have := G.μ0_mem.2.2 x hx; aesop;
    unfold Strategy.belief;
    rw [ ← Finset.sum_div, h_sum, div_self ( ne_of_gt ( onPathProb_pos_iff_mem_evidence s m |>.2 hm ) ) ];
  · intro θ hθ
    have h_zero : G.μ0 θ = 0 := by
      exact G.μ0_mem.2.2 θ hθ;
    unfold Strategy.belief; aesop;

end Strategy

end CPD