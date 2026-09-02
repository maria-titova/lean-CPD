import CPD.Simplex

/-!
# Disclosure games  (§2: Model)

A **disclosure game** `G = (Θ, 𝓜, M, μ⁰, V)` (**Definition 1**): finite
non-empty type space `Θ` and message space `𝓜`, a message mapping `M`, a
full-support prior `μ⁰`, and a payoff correspondence `V : ΔΘ ⇉ ℝ` that is
upper hemicontinuous with non-empty compact interval values (**Assumption
1**, conditions (A1)–(A4)).  The upper and lower envelopes `v̄(μ) := max V(μ)`
and `v̲(μ) := min V(μ)` are defined here, and the envelope properties used
throughout the paper (`V(μ) = [v̲(μ), v̄(μ)]`, `v̄` upper semicontinuous, `v̲`
lower semicontinuous) are derived from (A4).
-/

open Set Topology

namespace CPD

/-- **Upper hemicontinuity** (open-set definition) of `V : ΔΘ ⇉ ℝ` on `D`. -/
def UpperHemicontinuousOn {T : Type*} [Fintype T] (V : (T → ℝ) → Set ℝ)
    (D : Set (T → ℝ)) : Prop :=
  ∀ μ ∈ D, ∀ U : Set ℝ, IsOpen U → V μ ⊆ U →
    ∃ W ∈ 𝓝[D] μ, ∀ μ' ∈ W, V μ' ⊆ U

/-- **Definition 1** (disclosure game): `G = (Θ, 𝓜, M, μ⁰, V)`, satisfying
Assumption 1 (A1)–(A4). -/
structure DisclosureGame (T Msg : Type*) [Fintype T] [Fintype Msg] where
  /-- The finite type space `Θ`. -/
  Θ : Finset T
  /-- The finite message space `𝓜`. -/
  𝓜 : Finset Msg
  /-- `Θ` is non-empty. -/
  Θ_nonempty : Θ.Nonempty
  /-- `𝓜` is non-empty. -/
  𝓜_nonempty : 𝓜.Nonempty
  /-- The message mapping `M : Θ → 2^𝓜 ∖ {∅}`. -/
  M : T → Finset Msg
  /-- Each feasible set is a subset of `𝓜`. -/
  M_subset : ∀ θ ∈ Θ, M θ ⊆ 𝓜
  /-- Each feasible set is non-empty. -/
  M_nonempty : ∀ θ ∈ Θ, (M θ).Nonempty
  /-- The cover condition (A3): `𝓜 = ⋃_{θ ∈ Θ} M θ`. -/
  cover : (𝓜 : Set Msg) = ⋃ θ ∈ Θ, (M θ : Set Msg)
  /-- The prior `μ⁰`. -/
  μ0 : T → ℝ
  /-- `μ⁰ ∈ Δ Θ`. -/
  μ0_mem : μ0 ∈ simplexOn Θ
  /-- `μ⁰` has full support (A2). -/
  μ0_fullSupport : ∀ θ ∈ Θ, 0 < μ0 θ
  /-- The payoff correspondence `V : Δ Θ ⇉ ℝ`. -/
  V : (T → ℝ) → Set ℝ
  /-- `V` has non-empty values. -/
  V_nonempty : ∀ μ ∈ simplexOn Θ, (V μ).Nonempty
  /-- `V` has compact values. -/
  V_isCompact : ∀ μ ∈ simplexOn Θ, IsCompact (V μ)
  /-- `V` has interval (order-connected) values. -/
  V_ordConnected : ∀ μ ∈ simplexOn Θ, (V μ).OrdConnected
  /-- `V` is upper hemicontinuous (A4). -/
  V_uhc : UpperHemicontinuousOn V (simplexOn Θ)

namespace DisclosureGame

variable {T Msg : Type*} [Fintype T] [Fintype Msg] (G : DisclosureGame T Msg)

/-- The upper envelope `v̄(μ) := max V(μ)`. -/
noncomputable def vbar (μ : T → ℝ) : ℝ := sSup (G.V μ)

/-- The lower envelope `v̲(μ) := min V(μ)`. -/
noncomputable def vlow (μ : T → ℝ) : ℝ := sInf (G.V μ)

variable {G}

/-- **Envelope property (§2).** `v̄(μ) = max V(μ)`: the upper envelope is
attained. -/
lemma vbar_mem {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) : G.vbar μ ∈ G.V μ := by
  apply_rules [ IsCompact.sSup_mem ];
  · exact G.V_isCompact μ hμ;
  · exact G.V_nonempty μ hμ

/-- **Envelope property (§2).** `v̲(μ) = min V(μ)`: the lower envelope is
attained. -/
lemma vlow_mem {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) : G.vlow μ ∈ G.V μ := by
  convert ( IsCompact.sInf_mem ?_ ?_ );
  exacts [ inferInstance, inferInstance, G.V_isCompact μ hμ, G.V_nonempty μ hμ ]

/-
`v̄(μ)` is an upper bound of `V(μ)`.
-/
lemma le_vbar {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) {x : ℝ} (hx : x ∈ G.V μ) :
    x ≤ G.vbar μ := by
  exact le_csSup ( by exact ( G.V_isCompact μ hμ ).bddAbove ) hx

/-
`v̲(μ)` is a lower bound of `V(μ)`.
-/
lemma vlow_le {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) {x : ℝ} (hx : x ∈ G.V μ) :
    G.vlow μ ≤ x := by
  exact csInf_le ( G.V_isCompact μ hμ |> IsCompact.bddBelow ) hx

/-- **Envelope interval (§2).** `V(μ) = [v̲(μ), v̄(μ)]`. -/
lemma V_eq_Icc {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.V μ = Set.Icc (G.vlow μ) (G.vbar μ) := by
  apply Set.Subset.antisymm;
  · exact fun x hx => ⟨ G.vlow_le hμ hx, G.le_vbar hμ hx ⟩;
  · exact fun x hx => G.V_ordConnected μ hμ |>.out ( vlow_mem hμ ) ( vbar_mem hμ ) hx

/-- **Envelope semicontinuity, upper (§2).** `v̄` is upper semicontinuous on
`Δ Θ`. -/
lemma vbar_upperSemicontinuousOn :
    UpperSemicontinuousOn G.vbar (simplexOn G.Θ) := by
  intro μ hμ y hy
  obtain ⟨U, hU_open, hU_superset⟩ : ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (G.vlow μ) (G.vbar μ) ⊆ U ∧ ∀ x ∈ U, x < y := by
    exact ⟨ Set.Iio y, isOpen_Iio, fun x hx => hx.2.trans_lt hy, fun x hx => hx ⟩
  generalize_proofs at *; (
  -- By upper hemicontinuity of `V`, obtain a neighborhood `W` of `μ` in `Δ Θ` such that `V(x') ⊆ U` for all `x' ∈ W`.
  obtain ⟨W, hW⟩ : ∃ W ∈ 𝓝[simplexOn G.Θ] μ, ∀ x' ∈ W, G.V x' ⊆ U := by
    have := G.V_uhc μ hμ U hU_open ( by rw [ V_eq_Icc hμ ] ; exact hU_superset.1 ) ; aesop;
  generalize_proofs at *; (
  filter_upwards [ hW.1, self_mem_nhdsWithin ] with x' hx' hx'' using hU_superset.2 _ ( hW.2 x' hx' ( vbar_mem ( show x' ∈ simplexOn G.Θ from hx'' ) ) )))

/-- **Envelope semicontinuity, lower (§2).** `v̲` is lower semicontinuous on
`Δ Θ`. -/
lemma vlow_lowerSemicontinuousOn :
    LowerSemicontinuousOn G.vlow (simplexOn G.Θ) := by
  intro μ hμ y hy;
  -- By the upper hemicontinuity of $V$, there exists a neighborhood $W$ of $\mu$ such that $V(x') \subseteq (y, \infty)$ for all $x' \in W$.
  obtain ⟨W, hW⟩ : ∃ W ∈ nhdsWithin μ (simplexOn G.Θ), ∀ x' ∈ W, G.V x' ⊆ Set.Ioi y := by
    apply G.V_uhc μ hμ (Set.Ioi y) isOpen_Ioi;
    exact fun x hx => lt_of_lt_of_le hy ( G.vlow_le hμ hx );
  filter_upwards [ hW.1, self_mem_nhdsWithin ] with x' hx' hx'';
  exact lt_of_lt_of_le ( hW.2 x' hx' ( G.vlow_mem hx'' ) ) ( le_rfl )

end DisclosureGame

end CPD