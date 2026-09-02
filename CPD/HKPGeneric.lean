import CPD.EvidenceGame
import CPD.BetweennessGeneric

/-!
# Genericity in evidence games (Corollary 2)

An evidence game has `V` single-valued and `v̄` satisfying betweenness (B), so
the genericity uniqueness result for betweenness games (`btw_generic_unique`)
applies: under genericity, all coalition-proof PBE partitions share cells and
payoffs. Composing with `hkp_cppbe` (**Proposition 10**: a truth-leaning
equilibrium strategy is a coalition-proof PBE strategy), every truth-leaning
equilibrium and every coalition-proof PBE induce the same cells and the same
payoffs.

* `hkp_generic` (**Corollary 2**): in a generic evidence game, a truth-leaning
  equilibrium is associated with a coalition-proof PBE partition `Q`, and `Q`
  has the same cells and payoffs as every coalition-proof PBE partition.

(The receiver's-optimal-commitment clause of the paper corollary is an
external attribution to HKP's Theorem 1 and is not formalized, as with
Proposition 10.)

Proved modulo Kakutani (through both `hkp_cppbe` and `btw_generic_unique`).
-/

open Set Topology

namespace CPD

variable {T : Type*} [Fintype T]

namespace DisclosureGame

variable {G : DisclosureGame T T}

/-- **Corollary 2.** In a generic evidence game, a truth-leaning
equilibrium `(s, μ, r)` is associated with a coalition-proof PBE partition `Q`,
and `Q` has the same cells and payoffs as every coalition-proof PBE partition of
`G`. Hence every truth-leaning equilibrium and every coalition-proof PBE induce
the same cells and payoffs. -/
theorem hkp_generic (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    (hB : G.Betweenness) (hGen : G.Generic)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) (hnorm : ∀ θ ∉ G.Θ, s.σ θ = 0) :
    ∃ Q : Partition G, Q.IsCPPBEPartition ∧ Q.AssociatedWith s ∧
      ∀ P : Partition G, P.IsCPPBEPartition →
        Q.card = P.card ∧
        ∀ (t : Fin Q.card) (t' : Fin P.card), (t : ℕ) = (t' : ℕ) →
          Q.C t = P.C t' ∧ Q.w t = P.w t' := by
  obtain ⟨Q, hQ, hQassoc⟩ := hkp_cppbe hev hSV hB h hnorm
  exact ⟨Q, hQ, hQassoc, fun P hP => btw_generic_unique hSV hB hGen Q P hQ hP⟩

end DisclosureGame

end CPD
