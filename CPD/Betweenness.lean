import CPD.Theorem4

/-!
# Betweenness (Definition 15)

Let `G = (Θ, 𝓜, M, μ⁰, V)` be a disclosure game with upper envelope `v̄` (and
lower envelope `v̲`). `v̄` satisfies **betweenness (B)** if for all beliefs
`μ, μ' ∈ ΔΘ` and `λ ∈ (0,1)` the value `v̄(λμ + (1-λ)μ')` lies between `v̄(μ)`
and `v̄(μ')`; it satisfies **strict betweenness (B*)** if, in addition, the
value is *strictly* between whenever `v̄(μ) ≠ v̄(μ')`. This is Definition 15 of
§6.2 (Betweenness).

The file also proves inheritance under restriction and the quasiconcavity and
conditional-prior bounds used by Theorems 2, 3, and 6 and Proposition 5.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ## Definitions: betweenness and strict betweenness -/

variable (G) in
/-- **Definition 15 (B).** `v̄` satisfies *betweenness*: for all `μ, μ' ∈ ΔΘ`
and `λ ∈ (0,1)`, `v̄(λμ + (1-λ)μ')` lies between `v̄(μ)` and `v̄(μ')`. -/
def Betweenness : Prop :=
  ∀ μ ∈ simplexOn G.Θ, ∀ μ' ∈ simplexOn G.Θ, ∀ l : ℝ, l ∈ Set.Ioo (0 : ℝ) 1 →
    min (G.vbar μ) (G.vbar μ') ≤ G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ) ∧
      G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ) ≤ max (G.vbar μ) (G.vbar μ')

variable (G) in
/-- **Definition 15 (B*).** `v̄` satisfies *strict betweenness*: it satisfies B
and the value is strictly between `v̄(μ)` and `v̄(μ')` whenever
`v̄(μ) ≠ v̄(μ')`. -/
def StrictBetweenness : Prop :=
  G.Betweenness ∧
    ∀ μ ∈ simplexOn G.Θ, ∀ μ' ∈ simplexOn G.Θ, G.vbar μ ≠ G.vbar μ' →
      ∀ l : ℝ, l ∈ Set.Ioo (0 : ℝ) 1 →
        min (G.vbar μ) (G.vbar μ') < G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ) ∧
          G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ) < max (G.vbar μ) (G.vbar μ')

/-! ## Elementary consequences -/

/-- The lower inequality of betweenness is exactly quasiconcavity. -/
lemma Betweenness.qc (hB : G.Betweenness) : G.QC := by
  intro μ hμ μ' hμ' l hl
  exact (hB μ hμ μ' hμ' l hl).1

/-- Strict betweenness implies quasiconcavity. -/
lemma StrictBetweenness.qc (hB : G.StrictBetweenness) : G.QC :=
  hB.1.qc

/-- Betweenness is inherited by restricted games. -/
lemma restrict_Betweenness {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hB : G.Betweenness) : (G.restrict S hne hsub).Betweenness := by
  intro μ hμ μ' hμ' l hl
  exact hB μ (simplexOn_mono hsub hμ) μ' (simplexOn_mono hsub hμ') l hl

/-- Strict betweenness is inherited by restricted games. -/
lemma restrict_StrictBetweenness {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hB : G.StrictBetweenness) : (G.restrict S hne hsub).StrictBetweenness := by
  refine ⟨restrict_Betweenness hne hsub hB.1, ?_⟩
  intro μ hμ μ' hμ' hne' l hl
  exact hB.2 μ (simplexOn_mono hsub hμ) μ' (simplexOn_mono hsub hμ') hne' l hl

/-- Under quasiconcavity, the quasiconcave closure of `v̄` agrees with `v̄` on the
simplex (since `v̄` is then already upper semicontinuous and quasiconcave). -/
lemma qcClosure_eq_vbar_of_QC (hQC : G.QC) {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.qcClosure μ = G.vbar μ := by
  refine le_antisymm ?_ (t4_vbar_le_qcClosure hμ)
  have hconv : Convex ℝ (G.vbarUpperLevel (G.qcClosure μ)) :=
    vbar_superlevel_convex hQC (G.qcClosure μ)
  have hmem : μ ∈ {ν | ν ∈ simplexOn G.Θ ∧ G.qcClosure μ ≤ G.qcClosure ν} := ⟨hμ, le_refl _⟩
  rw [qcClosure_superlevel_eq_convexHull] at hmem
  rw [hconv.convexHull_eq] at hmem
  exact hmem.2

/-- **MC-free pooling bound.** Under quasiconcavity, every coalition `(C, σ, w)`
of a restricted game satisfies `w ≤ v̄(μ⁰_C)`. -/
lemma coalition_w_le_vbar_condPrior (hQC : G.QC) {R : Finset T} (hne : R.Nonempty)
    (hsub : R ⊆ G.Θ) (K : Coalition (G.restrict R hne hsub)) :
    K.w ≤ G.vbar (G.condPrior K.C) := by
  have h := coalition_w_le_qcClosure hne hsub K
  have hmem : G.condPrior K.C ∈ simplexOn G.Θ :=
    simplexOn_mono (K.C_subset.trans hsub)
      (G.condPrior_mem_simplex K.C_nonempty (K.C_subset.trans hsub))
  rwa [qcClosure_eq_vbar_of_QC hQC hmem] at h

/-! ## Conditional beliefs in restricted games -/

/-
**Restricted coalition belief, in terms of the full prior.** For a strategy
`s` of a restricted game `G|_S`, the (zero-extended) coalition belief after a
message `m` is the Bayesian posterior computed directly with the *full* prior
`G.μ0`; the `priorMeasure S` normalizer cancels between numerator and
denominator.
-/
lemma restrict_coalitionBelief_eq {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (s : Strategy (G.restrict S hne hsub)) (m : Msg) (θ : T) :
    s.coalitionBelief m θ
      = if θ ∈ S then G.μ0 θ * s.σ θ m / (∑ θ' ∈ S, G.μ0 θ' * s.σ θ' m) else 0 := by
  by_cases hθ : θ ∈ S <;> simp +decide [ hθ, Strategy.coalitionBelief ];
  · simp +decide [ zeroExt, Strategy.belief, Strategy.onPathProb, condPrior_of_mem hθ, priorMeasure_pos hne hsub, ne_of_gt ];
    rw [ if_pos hθ, div_mul_eq_mul_div, div_div ];
    rw [ Finset.mul_sum _ _ _ ];
    exact congr_arg _ ( Finset.sum_congr rfl fun x hx => by rw [ condPrior_of_mem hx ] ; rw [ div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ ( ne_of_gt ( priorMeasure_pos hne hsub ) ) ] );
  · exact if_neg hθ

end DisclosureGame

end CPD
