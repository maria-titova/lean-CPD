import CPD.Strategy

/-!
# Preimages, forced types, conditional priors, restricted games  (§2: Useful notation, Restricted games)

* the **preimage** `M⁻¹_S(X) := {θ ∈ S | M(θ) ∩ X ≠ ∅}`, with `M⁻¹(X)` the full
  version, `P(m) := M⁻¹({m})` and the **forced** types `F(m) := {θ | M(θ)={m}}`;
* the **prior measure** `μ⁰(C)`, the **conditional prior** `μ⁰_C`;
* the **restricted message space** `𝓜_S`, the **zero-extension** `ι_S`, and the
  **restricted game** `G|_S`.  **Lemma K.2** (restriction): `G|_Θ = G`, and
  restriction is transitive, `(G|_S)|_{S'} = G|_{S'}`.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

/-! ## Preimages and forced types -/

/-- The **preimage of `X` relative to `S`**: `M⁻¹_S(X) := {θ ∈ S | M(θ)∩X ≠ ∅}`. -/
noncomputable def preimage (M : T → Finset Msg) (S : Finset T) (X : Finset Msg) : Finset T :=
  S.filter (fun θ => (M θ ∩ X).Nonempty)

omit [Fintype T] [Fintype Msg] in
lemma mem_preimage {M : T → Finset Msg} {S : Finset T} {X : Finset Msg} {θ : T} :
    θ ∈ preimage M S X ↔ θ ∈ S ∧ (M θ ∩ X).Nonempty := by
  unfold preimage; aesop;

omit [Fintype Msg] in
/-- Upper hemicontinuity restricts to subsets. -/
lemma UpperHemicontinuousOn.mono {V : (T → ℝ) → Set ℝ} {D D' : Set (T → ℝ)}
    (h : UpperHemicontinuousOn V D) (hsub : D' ⊆ D) :
    UpperHemicontinuousOn V D' := by
  intro μ hμ U hU hVU;
  -- Apply the hypothesis `h` to obtain the neighborhood `W` in `D`.
  obtain ⟨W, hW₁, hW₂⟩ := h μ (hsub hμ) U hU hVU;
  refine' ⟨ W ∩ D', _, _ ⟩ <;> simp_all +decide [ Set.inter_assoc, Set.subset_inter_iff ];
  exact ⟨ nhdsWithin_mono _ hsub hW₁, self_mem_nhdsWithin ⟩

namespace DisclosureGame

variable (G : DisclosureGame T Msg)

/-- `M⁻¹(X) := M⁻¹_Θ(X)`. -/
noncomputable def preimageFull (X : Finset Msg) : Finset T := preimage G.M G.Θ X

/-- `P(m) := M⁻¹({m})`, the types that can send `m`. -/
noncomputable def canSend (m : Msg) : Finset T := G.preimageFull {m}

/-- `F(m) := {θ ∈ Θ | M(θ) = {m}}`, the types *forced* to send `m`. -/
noncomputable def forced (m : Msg) : Finset T := G.Θ.filter (fun θ => G.M θ = {m})

/-- The **prior measure** `μ⁰(C) := ∑_{θ∈C} μ⁰(θ)`. -/
noncomputable def priorMeasure (C : Finset T) : ℝ := ∑ θ ∈ C, G.μ0 θ

/-- The **conditional prior** `μ⁰_C(θ) := μ⁰(θ)·𝟙(θ∈C) / μ⁰(C)`. -/
noncomputable def condPrior (C : Finset T) : T → ℝ :=
  fun θ => G.μ0 θ * (if θ ∈ C then 1 else 0) / G.priorMeasure C

variable {G}

/-
**`μ⁰(C) > 0`** for non-empty `C ⊆ Θ`.
-/
lemma priorMeasure_pos {C : Finset T} (hC : C.Nonempty) (hCΘ : C ⊆ G.Θ) :
    0 < G.priorMeasure C := by
  exact Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( hCΘ hx ) ) hC

/-
For `θ ∈ C`, `μ⁰_C(θ) = μ⁰(θ) / μ⁰(C)`.
-/
lemma condPrior_of_mem {C : Finset T} {θ : T} (hθ : θ ∈ C) :
    G.condPrior C θ = G.μ0 θ / G.priorMeasure C := by
  unfold DisclosureGame.condPrior; aesop;

/-
For `θ ∉ C`, `μ⁰_C(θ) = 0`.
-/
lemma condPrior_of_not_mem {C : Finset T} {θ : T} (hθ : θ ∉ C) :
    G.condPrior C θ = 0 := by
  unfold CPD.DisclosureGame.condPrior;
  simp +decide [ hθ ]

/-
**`μ⁰_C ∈ Δ C`.**
-/
lemma condPrior_mem_simplex {C : Finset T} (hC : C.Nonempty) (hCΘ : C ⊆ G.Θ) :
    G.condPrior C ∈ simplexOn C := by
  -- Show that `G.condPrior C` is nonnegative.
  have h_nonneg : ∀ θ, 0 ≤ G.condPrior C θ := by
    intro θ; unfold CPD.DisclosureGame.condPrior; split_ifs <;> simp +decide [ *, div_nonneg, Finset.sum_nonneg, G.μ0_mem.1 ] ;
    exact div_nonneg ( G.μ0_mem.1 θ ) ( Finset.sum_nonneg fun _ _ => G.μ0_mem.1 _ );
  refine' ⟨ h_nonneg, _, _ ⟩;
  · -- Show that `G.condPrior C` sums to 1.
    have h_sum : ∑ a, G.condPrior C a = ∑ a ∈ C, G.μ0 a / G.priorMeasure C := by
      rw [ ← Finset.sum_subset ( Finset.subset_univ C ) ];
      · exact Finset.sum_congr rfl fun x hx => by rw [ condPrior_of_mem hx ] ;
      · exact fun x _ hx => condPrior_of_not_mem hx;
    rw [ h_sum, ← Finset.sum_div _ _ _, div_eq_iff ] <;> linarith [ priorMeasure_pos hC hCΘ, show G.priorMeasure C = ∑ a ∈ C, G.μ0 a from rfl ];
  · exact fun a a_1 ↦ condPrior_of_not_mem a_1

/-
The conditional prior has full support on `C`.
-/
lemma condPrior_pos {C : Finset T} (hC : C.Nonempty) (hCΘ : C ⊆ G.Θ) {θ : T}
    (hθ : θ ∈ C) : 0 < G.condPrior C θ := by
  rw [ condPrior_of_mem hθ ];
  exact div_pos ( G.μ0_fullSupport θ ( hCΘ hθ ) ) ( priorMeasure_pos hC hCΘ )

/-
**The conditional prior has support exactly `C`.**
-/
lemma simplexSupport_condPrior {C : Finset T} (hC : C.Nonempty) (hCΘ : C ⊆ G.Θ) :
    simplexSupport (G.condPrior C) = (C : Set T) := by
  ext θ; by_cases hθ : θ ∈ C <;> simp_all +decide [ condPrior_of_mem, condPrior_of_not_mem ] ;
  exact div_pos ( G.μ0_fullSupport θ ( hCΘ hθ ) ) ( priorMeasure_pos hC hCΘ )

/-! ## Restricted message space and zero-extension embedding -/

variable (G)

/-- The **restricted message space** `𝓜_S := ⋃_{θ∈S} M(θ)`. -/
noncomputable def restrictMsgSpace (S : Finset T) : Finset Msg := S.biUnion G.M

variable {G}

@[simp] lemma coe_restrictMsgSpace (S : Finset T) :
    (G.restrictMsgSpace S : Set Msg) = ⋃ θ ∈ S, (G.M θ : Set Msg) := by
  simp [restrictMsgSpace]

lemma restrictMsgSpace_subset {S : Finset T} (hS : S ⊆ G.Θ) :
    G.restrictMsgSpace S ⊆ G.𝓜 := by
  exact Finset.biUnion_subset.mpr fun θ hθ => G.M_subset θ ( hS hθ )

variable (G)

/-- The **zero-extension embedding** `ι_S : ΔS → ΔΘ`. -/
noncomputable def zeroExt (S : Finset T) (ν : T → ℝ) : T → ℝ :=
  fun θ => if θ ∈ S then ν θ else 0

variable {G}

lemma zeroExt_eq_self {S : Finset T} {ν : T → ℝ} (hν : ν ∈ simplexOn S) :
    zeroExt S ν = ν := by
  ext θ; by_cases hθ : θ ∈ S <;> simp_all +decide [ zeroExt ] ;

lemma zeroExt_mem_simplex {S Θ : Finset T} (h : S ⊆ Θ) {ν : T → ℝ}
    (hν : ν ∈ simplexOn S) : zeroExt S ν ∈ simplexOn Θ := by
  grind +suggestions

omit [Fintype T] in
/-- The zero-extension embedding `ι_S` is continuous. -/
lemma continuous_zeroExt (S : Finset T) :
    Continuous (zeroExt S : (T → ℝ) → (T → ℝ)) := by
  convert continuous_pi fun θ => ?_ using 1;
  by_cases h : θ ∈ S <;> simp +decide [ h, zeroExt ];
  · exact continuous_apply θ;
  · exact continuous_const

/-! ## The restricted game -/

variable (G)

/-- **§2 (Restricted games).** The **restricted game** `G|_S` on a
non-empty `S ⊆ Θ`. -/
noncomputable def restrict (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ) :
    DisclosureGame T Msg where
  Θ := S
  𝓜 := G.restrictMsgSpace S
  Θ_nonempty := hne
  𝓜_nonempty := Finset.Nonempty.biUnion hne (fun θ hθ => G.M_nonempty θ (hsub hθ))
  M := G.M
  M_subset := fun θ hθ => Finset.subset_biUnion_of_mem G.M hθ
  M_nonempty := fun θ hθ => G.M_nonempty θ (hsub hθ)
  cover := by simp [restrictMsgSpace]
  μ0 := G.condPrior S
  μ0_mem := condPrior_mem_simplex hne hsub
  μ0_fullSupport := fun θ hθ => condPrior_pos hne hsub hθ
  V := G.V
  V_nonempty := fun μ hμ => G.V_nonempty μ (simplexOn_mono hsub hμ)
  V_isCompact := fun μ hμ => G.V_isCompact μ (simplexOn_mono hsub hμ)
  V_ordConnected := fun μ hμ => G.V_ordConnected μ (simplexOn_mono hsub hμ)
  V_uhc := G.V_uhc.mono (simplexOn_mono hsub)

variable {G}

@[simp] lemma restrict_Θ (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ) :
    (G.restrict S hne hsub).Θ = S := rfl

@[simp] lemma restrict_M (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ) :
    (G.restrict S hne hsub).M = G.M := rfl

@[simp] lemma restrict_V (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ) :
    (G.restrict S hne hsub).V = G.V := rfl

@[simp] lemma restrict_μ0 (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ) :
    (G.restrict S hne hsub).μ0 = G.condPrior S := rfl

@[simp] lemma restrict_𝓜 (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ) :
    (G.restrict S hne hsub).𝓜 = G.restrictMsgSpace S := rfl

/-
Extensionality for disclosure games.
-/
lemma ext' {g₁ g₂ : DisclosureGame T Msg}
    (hΘ : g₁.Θ = g₂.Θ) (h𝓜 : g₁.𝓜 = g₂.𝓜) (hM : g₁.M = g₂.M)
    (hμ : g₁.μ0 = g₂.μ0) (hV : g₁.V = g₂.V) : g₁ = g₂ := by
  cases g₁ ; cases g₂ ; simp_all +decide [ DisclosureGame ]

/-
`μ⁰(Θ) = 1`.
-/
lemma priorMeasure_self : G.priorMeasure G.Θ = 1 := by
  convert G.μ0_mem.2.1;
  refine' Finset.sum_subset _ _ <;> simp +contextual [ G.μ0_mem.2.2 ]

/-
`μ⁰_Θ = μ⁰`.
-/
lemma condPrior_self : G.condPrior G.Θ = G.μ0 := by
  ext θ; by_cases hθ : θ ∈ G.Θ <;> simp_all +decide [ condPrior ] ;
  · rw [ priorMeasure_self, div_one ];
  · exact Eq.symm ( G.μ0_mem.2.2 θ hθ )

/-- **Lemma K.2** (restriction): `G|_Θ = G`. -/
lemma restrict_self : G.restrict G.Θ G.Θ_nonempty subset_rfl = G := by
  refine' ext' _ _ _ _ _ <;> simp +decide [ DisclosureGame.restrict ];
  · convert G.cover.symm using 1;
    simp +decide [ Finset.ext_iff, Set.ext_iff ];
    simp +decide [ DisclosureGame.restrictMsgSpace, Finset.mem_biUnion ];
  · exact condPrior_self

/-- **Lemma K.2** (restriction is transitive): `(G|_S)|_{S'} = G|_{S'}`. -/
lemma restrict_restrict {S S' : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hne' : S'.Nonempty) (hsub' : S' ⊆ S) :
    (G.restrict S hne hsub).restrict S' hne' hsub' =
      G.restrict S' hne' (hsub'.trans hsub) := by
  refine' ext' _ _ _ _ _ <;> simp +decide [ DisclosureGame.restrict ];
  · simp +decide [ DisclosureGame.restrictMsgSpace ];
  · ext θ; by_cases hθ : θ ∈ S' <;> simp_all +decide [ DisclosureGame.condPrior ] ;
    rw [ if_pos ( hsub' hθ ), div_div, mul_comm ];
    congr! 1;
    unfold DisclosureGame.priorMeasure; simp +decide [ Finset.sum_mul _ _ _ ] ;
    rw [ Finset.sum_congr rfl fun x hx => by rw [ DisclosureGame.condPrior_of_mem ( hsub' hx ) ] ] ; ring!;
    exact Finset.sum_congr rfl fun x hx => by rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( priorMeasure_pos hne hsub ) ), mul_one ] ;

end DisclosureGame

end CPD
