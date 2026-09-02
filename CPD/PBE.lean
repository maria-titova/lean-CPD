import CPD.Feasible

/-!
# Perfect Bayesian Equilibrium  (§4: Perfect Bayesian Equilibrium)

This file defines `argmaxOn r S`, the set `argmax_{m∈S} r(m)`, and formalizes
**Definition 7** (PBE). The predicate `Supports σ μ r` packages its four
conditions: feasible beliefs, Bayesian updating on path, payoff-compatible
receiver payoffs, and sequential rationality. The predicate `IsPBE σ` is the
existential form of the same definition.
-/

open Set

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-- `argmax_{m ∈ S} r(m)`. -/
def argmaxOn (r : Msg → ℝ) (S : Finset Msg) : Set Msg :=
  {m | m ∈ S ∧ ∀ m' ∈ S, r m' ≤ r m}

omit [Fintype T] [Fintype Msg] in
@[simp] lemma mem_argmaxOn {r : Msg → ℝ} {S : Finset Msg} {m : Msg} :
    m ∈ argmaxOn r S ↔ m ∈ S ∧ ∀ m' ∈ S, r m' ≤ r m := Iff.rfl

/-- **Definition 7** (PBE): `(μ, r)` supports `σ` as a PBE, via the four
conditions: feasible beliefs, Bayesian updating on path, payoff
compatibility, and sequential rationality. -/
structure Supports (s : Strategy G) (μ : Msg → T → ℝ) (r : Msg → ℝ) : Prop where
  /-- `μ : 𝓜 → ΔΘ` is a belief system. -/
  belief_system : ∀ m ∈ G.𝓜, μ m ∈ simplexOn G.Θ
  /-- (1) beliefs are feasible: `μ(·|m) ∈ 𝓕(m)`. -/
  feasible : ∀ m ∈ G.𝓜, μ m ∈ G.feasibleBeliefs m
  /-- (2) beliefs are Bayesian on path: `μ(·|m) = μ_σ(·|m)`. -/
  bayesian : ∀ m ∈ s.evidence, μ m = s.belief m
  /-- (3) `r(m) ∈ V(μ(·|m))`. -/
  payoff_compat : ∀ m ∈ G.𝓜, r m ∈ G.V (μ m)
  /-- (4) sequential rationality: `supp σ(·|θ) ⊆ argmax_{m∈M(θ)} r(m)`. -/
  seq_optimal : ∀ θ ∈ G.Θ, s.msgSupport θ ⊆ argmaxOn r (G.M θ)

variable (G) in
/-- **Definition 7** (PBE), existential form: `σ` is a PBE strategy if some
`(μ, r)` supports it. -/
def IsPBE (s : Strategy G) : Prop :=
  ∃ (μ : Msg → T → ℝ) (r : Msg → ℝ), Supports s μ r

end DisclosureGame

namespace Strategy

variable {G : DisclosureGame T Msg}

/-- **Consistency of conditions (1)–(2)**: for `m ∈ X(σ)`, `μ_σ(·|m) ∈ 𝓕(m)`. -/
lemma belief_mem_feasibleBeliefs (s : Strategy G) {m : Msg}
    (hm : m ∈ s.evidence) : s.belief m ∈ G.feasibleBeliefs m :=
  ⟨s, hm, rfl⟩

end Strategy

end CPD
