import Mathlib

/-!
# Kakutani's fixed-point theorem  (the one external mathematical input)

Kakutani's fixed-point theorem is not in mathlib.  It is the single external
mathematical input of this entire development: every other result is proved
from mathlib's foundational axioms alone.  The classical statement is
recorded as `KakutaniProperty E` and asserted as `axiom kakutani` for
finite-dimensional real normed spaces `E`.  The axiom is consumed in exactly
one place, the proof of `CPD.DisclosureGame.exists_PBE` (**Lemma K.4**, PBE
existence).
-/

open Set

namespace CPD

/-- **Kakutani's fixed-point theorem**, as a property of a real topological
vector space `E`: for every non-empty compact convex `K ⊆ E` and every
correspondence `Φ : E → Set E` with non-empty convex values, `Φ x ⊆ K` for
`x ∈ K`, and closed graph, there is a fixed point `x ∈ K` with `x ∈ Φ x`. -/
def KakutaniProperty (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop :=
  ∀ (K : Set E) (Φ : E → Set E),
    K.Nonempty → IsCompact K → Convex ℝ K →
    (∀ x ∈ K, (Φ x).Nonempty) →
    (∀ x ∈ K, Convex ℝ (Φ x)) →
    (∀ x ∈ K, Φ x ⊆ K) →
    IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ Φ p.1} →
    ∃ x ∈ K, x ∈ Φ x

/-- **Kakutani's fixed-point theorem** (the one external mathematical input
of this development), asserted for finite-dimensional real normed spaces. -/
axiom kakutani (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : KakutaniProperty E

/-- The ambient finite-dimensional real coordinate space of the fixed-point
argument: `ℝ^{Θ×𝓜} × ℝ^{𝓜×Θ} × ℝ^{𝓜}`, encoding `(σ, μ, r)`. -/
abbrev FixedPointSpace (T Msg : Type*) : Type _ :=
  (T → Msg → ℝ) × (Msg → T → ℝ) × (Msg → ℝ)

end CPD
