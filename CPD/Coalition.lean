import CPD.Restriction

/-!
# Coalitions  (§3: Coalitions and Partitions)

A **coalition strategy** on a non-empty `C ⊆ Θ` is a sender strategy of the
restricted game `G|_C`; its **coalition-induced belief**
`μ^{C,σ}(·|m) := ι_C(μ_σ(·|m))` is the zero-extension of `μ_σ(·|m)` to `Θ`.
A **coalition** `(C, σ, w)` of `G` (**Definition 2**) satisfies conditions
(C1)–(C4): `C` non-empty, `σ` a coalition strategy on `C`, exclusivity of the
evidence, and a common payoff `w`.  The reverse inclusion `C ⊆ M⁻¹(X(σ))`
holds automatically, so `M⁻¹(X(σ)) = C`.  **Remark 1** (coalitions exist):
every disclosure game admits a coalition.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace Strategy

variable {g : DisclosureGame T Msg}

/-- The **coalition-induced belief** `μ^{C,σ}(·|m) := ι_C(μ_σ(·|m))`. -/
noncomputable def coalitionBelief (s : Strategy g) (m : Msg) : T → ℝ :=
  DisclosureGame.zeroExt g.Θ (s.belief m)

end Strategy

namespace DisclosureGame

variable (G : DisclosureGame T Msg)

/-- The **preimage of a set of messages `X` relative to `S`**:
`M⁻¹_S(X) := {θ ∈ S | M(θ) ∩ X ≠ ∅}`, for `X : Set Msg`. -/
noncomputable def preimageSet (S : Finset T) (X : Set Msg) : Finset T :=
  S.filter (fun θ => ((G.M θ : Set Msg) ∩ X).Nonempty)

/-- `M⁻¹(X) := M⁻¹_Θ(X)`, the set-preimage relative to the full type space. -/
noncomputable def preimageSetFull (X : Set Msg) : Finset T := G.preimageSet G.Θ X

variable {G}

lemma mem_preimageSet {S : Finset T} {X : Set Msg} {θ : T} :
    θ ∈ G.preimageSet S X ↔ θ ∈ S ∧ ((G.M θ : Set Msg) ∩ X).Nonempty := by
  unfold CPD.DisclosureGame.preimageSet; simp +decide [ Set.ext_iff ] ;

/-
**The reverse inclusion `C ⊆ M⁻¹(X(σ))`** holds automatically.
-/
lemma coalitionStrategy_subset_preimage {C : Finset T} (hne : C.Nonempty)
    (hsub : C ⊆ G.Θ) (s : Strategy (G.restrict C hne hsub)) :
    C ⊆ G.preimageSetFull s.evidence := by
  intro θ hθ
  have h_mem : ∃ m ∈ (G.M θ : Set Msg), m ∈ s.evidence := by
    have h_mem : ∃ m, 0 < s.σ θ m := by
      have := s.mem θ;
      simp_all +decide [ simplexOn ];
      exact not_forall_not.mp fun h => by have := this.2.1 ▸ Finset.sum_nonpos fun m _ => le_of_not_gt fun hm => h m hm; norm_num at this;
    obtain ⟨ m, hm ⟩ := h_mem; use m; simp_all +decide [ Strategy.evidence ] ;
    exact ⟨ by exact Classical.not_not.1 fun hnm => hm.ne' <| s.mem θ hθ |>.2.2 _ <| by aesop, θ, hθ, hm ⟩;
  exact Finset.mem_filter.mpr ⟨ hsub hθ, by obtain ⟨ m, hm₁, hm₂ ⟩ := h_mem; exact ⟨ m, hm₁, hm₂ ⟩ ⟩

variable (G) in
/-- **Definition 2** (coalition): `(C, σ, w)` of `G`, satisfying (C1) `C`
non-empty, (C2) `σ` a coalition strategy on `C`, (C3) evidence exclusive to
`C`, (C4) common payoff `w`. -/
structure Coalition where
  /-- The coalition `C ⊆ Θ` (C1). -/
  C : Finset T
  /-- `C` is non-empty (C1). -/
  C_nonempty : C.Nonempty
  /-- `C ⊆ Θ`. -/
  C_subset : C ⊆ G.Θ
  /-- `σ` is a coalition strategy on `C` (C2). -/
  σ : Strategy (G.restrict C C_nonempty C_subset)
  /-- Exclusivity of the evidence (C3): `M⁻¹(X(σ)) ⊆ C`. -/
  exclusive : G.preimageSetFull σ.evidence ⊆ C
  /-- The common payoff `w`. -/
  w : ℝ
  /-- `w ∈ V(μ^{C,σ}(·|m))` for every `m ∈ X(σ)` (C4). -/
  payoff : ∀ m ∈ σ.evidence, w ∈ G.V (σ.coalitionBelief m)

namespace Coalition

variable (K : Coalition G)

/-
**`M⁻¹(X(σ)) = C`** for a coalition (C3 equivalence).
-/
lemma preimage_eq : G.preimageSetFull K.σ.evidence = K.C := by
  exact Finset.Subset.antisymm K.exclusive ( coalitionStrategy_subset_preimage K.C_nonempty K.C_subset K.σ )

end Coalition

/-- **Remark 1** (coalitions exist): every disclosure game admits a
coalition. -/
theorem exists_coalition : Nonempty (Coalition G) := by
  obtain ⟨m, hm⟩ : ∃ m : Msg, m ∈ G.𝓜 := by
    exact G.𝓜_nonempty;
  have h_nonempty : ∃ θ : T, θ ∈ G.Θ ∧ m ∈ G.M θ := by
    have := G.cover.subset ( Set.mem_of_mem_of_subset hm ( Set.Subset.refl _ ) ) ; aesop;
  -- Let $C := G.canSend m$.
  set C : Finset T := G.preimageFull {m} with hC_def;
  -- Define the strategy σ on `G.restrict C C_nonempty C_subset` by σ.σ := fun _θ => (fun a => if a = m then (1:ℝ) else 0) (the point mass δ_{m} for every type).
  obtain ⟨σ, hσ⟩ : ∃ σ : Strategy (G.restrict C (by
  exact ⟨ h_nonempty.choose, Finset.mem_filter.mpr ⟨ h_nonempty.choose_spec.1, ⟨ m, Finset.mem_inter.mpr ⟨ h_nonempty.choose_spec.2, Finset.mem_singleton_self _ ⟩ ⟩ ⟩ ⟩) (by
  exact Finset.filter_subset _ _)), σ.evidence = {m} := by
    all_goals generalize_proofs at *;
    refine' ⟨ ⟨ fun θ => fun a => if a = m then 1 else 0, _ ⟩, _ ⟩ <;> simp +decide [ *, Strategy.evidence ];
    all_goals norm_num [ Set.ext_iff, Strategy.msgSupport ];
    · simp +decide [ DisclosureGame.preimageFull ];
      simp +decide [ preimage ];
      grind;
    · grind +suggestions
  generalize_proofs at *;
  -- Let $w$ be a common payoff for the coalition.
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w ∈ G.V (σ.coalitionBelief m) := by
    apply G.V_nonempty;
    apply zeroExt_mem_simplex;
    · assumption;
    · apply Strategy.belief_mem_simplex;
      grind;
  refine' ⟨ ⟨ C, _, _, σ, _, w, _ ⟩ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  simp +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageFull ];
  simp +decide [ preimage, DisclosureGame.preimageSet ];
  exact fun x hx hx' => ⟨ hx, ⟨ m, by aesop ⟩ ⟩

end DisclosureGame

end CPD