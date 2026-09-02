import CPD.Betweenness

/-!
# Ranking level sets under plain betweenness — axiom-free core (Lemma E.1)

This module isolates the *axiom-free* geometric machinery behind **Lemma E.1
(btw-order)**: point/convex-set separation (`proper_separation`, a
Rockafellar Thm. 11.3-style proper separating hyperplane for two disjoint
non-empty convex sets), convexity of sub/super level sets of `v̄` under
betweenness (B), the level-component extraction lemma, and the generalized
ranking construction (`btw_order_aux`). It imports only `CPD.Betweenness`
(which does not depend on the `kakutani` axiom), so these results can be
developed independently of the fixed-point machinery. `CPD.BetweennessOrder`
consumes `btw_order_aux` to prove the public `btw_order`, and the whole
development underlies **Theorem 3** (plain betweenness ⇒ a coalition-proof
PBE exists), the paper's hardest existence result.

**The ranking construction.** Fix a level `y` of `v̄` on a convex `F ⊆ ΔΘ`.
Two proper separators split `F` into strictly-below / level / strictly-above
pieces: `a = fp + cp` separates `{v̄ ≤ y} ∩ F` from `{v̄ > y} ∩ F`, and
`b = fm + cm` separates `{v̄ < y} ∩ F` from `{v̄ ≥ y} ∩ F`. Level points `x`
satisfy `a x ≤ 0 ≤ b x`; ranking is primarily by the pencil coordinate
`pencilLam x = b(x)/(b(x) - a(x)) ∈ [0,1]` (descending), with ties on the
pencil hyperplane broken by recursion on the strictly smaller affine
dimension of the tie slice (`pencilRel`, `btw_order_aux_rank`). `rankRel` is
the single-separator special case used when no strictly-below point exists.
-/

open Set Topology
open scoped Classical
open scoped Pointwise

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

/-- Boundary case of the point/convex-set separation core: a non-empty convex
set `C` in `ℝ^Θ` not containing the origin, but with the origin in its closure
(a relative-boundary point).  There is a linear functional `≤ 0` on `C` and
strictly negative somewhere on `C`.  This is the supporting-hyperplane content of
Rockafellar Thm. 11.3, obtained by separating the origin from the (relatively
open, non-empty) intrinsic interior of `C` inside the linear span of `C`. -/
private lemma sep_point_bdry {C : Set (T → ℝ)} (hC : Convex ℝ C) (hCne : C.Nonempty)
    (h0 : (0 : T → ℝ) ∉ C) (h0cl : (0 : T → ℝ) ∈ closure C) :
    ∃ F : (T → ℝ) →ₗ[ℝ] ℝ, (∀ x ∈ C, F x ≤ 0) ∧ (∃ x ∈ C, F x < 0) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ C, True :=
    ⟨hCne.some, hCne.choose_spec, trivial⟩
  set W := Submodule.span ℝ (Set.image (fun c => c - x₀) C) with hW_def
  have hW_closed : IsClosed (W : Set (T → ℝ)) := W.closed_of_finiteDimensional
  have hC_subset_W : C ⊆ W := by
    have hx₀_in_W : x₀ ∈ W := by
      have h0_eq : 0 ∈ (fun c => c + x₀) '' W := by
        have h0_eq : closure C ⊆ (fun c => c + x₀) '' W := by
          refine' closure_minimal _ _;
          · exact fun x hx => ⟨ x - x₀, Submodule.subset_span ( Set.mem_image_of_mem _ hx ), by simp +decide ⟩;
          · convert hW_closed.preimage ( show Continuous fun c : T → ℝ => c - x₀ from continuous_id.sub continuous_const ) using 1 ; ext ; aesop;
        exact h0_eq h0cl;
      obtain ⟨ w, hw, hw' ⟩ := h0_eq; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
    exact fun c hc => by simpa using Submodule.add_mem _ ( Submodule.subset_span ( Set.mem_image_of_mem _ hc ) ) hx₀_in_W;
  set C' : Set W := W.subtype ⁻¹' C with hC'_def
  have hC'_convex : Convex ℝ C' := hC.linear_preimage _
  have hC'_nonempty : C'.Nonempty := ⟨ ⟨ x₀, hC_subset_W hx₀.1 ⟩, hx₀.1 ⟩
  have hC'_interior_nonempty : (interior C').Nonempty := by
    have hC'_vectorSpan : vectorSpan ℝ C' = ⊤ := by
      have hC'_vectorSpan : Submodule.map W.subtype (vectorSpan ℝ C') = W := by
        refine' le_antisymm _ _;
        · simp +decide [ Submodule.map_le_iff_le_comap, Submodule.span_le ];
        · rw [ Submodule.span_le ];
          rintro _ ⟨ c, hc, rfl ⟩;
          refine' ⟨ ⟨ c, hC_subset_W hc ⟩ - ⟨ x₀, hC_subset_W hx₀.1 ⟩, _, _ ⟩ <;> simp +decide [ hc, hx₀.1 ];
          exact Submodule.subset_span ⟨ ⟨ c, hC_subset_W hc ⟩, hc, ⟨ x₀, hC_subset_W hx₀.1 ⟩, hx₀.1, rfl ⟩;
      exact Submodule.map_injective_of_injective ( Submodule.injective_subtype W ) ( by aesop );
    have hC'_interior_nonempty : affineSpan ℝ C' = ⊤ :=
      (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (↥W) (↥W)
        hC'_nonempty).mpr hC'_vectorSpan
    convert hC'_convex.interior_nonempty_iff_affineSpan_eq_top.mpr hC'_interior_nonempty;
  obtain ⟨g, hg⟩ : ∃ g : W →L[ℝ] ℝ, ∀ a ∈ interior C', g a < g 0 := by
    have h0_not_in_C' : (0 : W) ∉ C' := by aesop;
    have := @geometric_hahn_banach_open_point;
    convert this ( show Convex ℝ ( interior C' ) from hC'_convex.interior ) ( isOpen_interior ) ( show ( 0 : W ) ∉ interior C' from fun h => h0_not_in_C' <| interior_subset h ) using 1;
  have hC'_le_zero : ∀ a ∈ C', g a ≤ 0 := by
    have hC'_le_zero : C' ⊆ closure (interior C') := by
      rw [ hC'_convex.closure_interior_eq_closure_of_nonempty_interior hC'_interior_nonempty ];
      exact subset_closure;
    intro a ha
    have h_closure : g a ≤ g 0 := by
      have h_closure : a ∈ closure (interior C') := hC'_le_zero ha;
      rw [ mem_closure_iff_seq_limit ] at h_closure;
      exact le_of_tendsto_of_tendsto' ( g.continuous.continuousAt.tendsto.comp h_closure.choose_spec.2 ) tendsto_const_nhds fun n => le_of_lt ( hg _ ( h_closure.choose_spec.1 n ) );
    convert h_closure using 1 ; aesop;
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ ∈ interior C', g a₀ < 0 :=
    Exists.elim hC'_interior_nonempty fun x hx => ⟨ x, hx, by simpa using hg x hx ⟩;
  obtain ⟨ F, hF ⟩ := g.exists_extend;
  refine' ⟨ F.toContinuousLinearMap, _, _ ⟩ <;> simp_all +decide [ funext_iff, LinearMap.ext_iff ];
  · exact fun x hx => hF x ( hC_subset_W hx ) ▸ hC'_le_zero x ( hC_subset_W hx ) hx;
  · exact ⟨ a₀, by simpa using interior_subset ha₀.1, by simpa [ hF _ a₀.2 ] using ha₀.2 ⟩

/-- Point/convex-set separation core: a non-empty convex set `C` in `ℝ^Θ` not
containing the origin admits a linear functional `≤ 0` on `C`, strictly negative
somewhere on `C`. -/
private lemma sep_point_ext {C : Set (T → ℝ)} (hC : Convex ℝ C) (hCne : C.Nonempty)
    (h0 : (0 : T → ℝ) ∉ C) :
    ∃ F : (T → ℝ) →ₗ[ℝ] ℝ, (∀ x ∈ C, F x ≤ 0) ∧ (∃ x ∈ C, F x < 0) := by
  by_cases hcl : (0 : T → ℝ) ∈ closure C
  · exact sep_point_bdry hC hCne h0 hcl
  · obtain ⟨f, u, hfu, hb⟩ :=
      geometric_hahn_banach_point_closed hC.closure isClosed_closure hcl
    have hf0 : f (0 : T → ℝ) = 0 := map_zero f
    refine ⟨-(f.toLinearMap), ?_, ?_⟩
    · intro x hx
      have hxu : u < f x := hb x (subset_closure hx)
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
      rw [hf0] at hfu; linarith
    · obtain ⟨x, hx⟩ := hCne
      refine ⟨x, hx, ?_⟩
      have hxu : u < f x := hb x (subset_closure hx)
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
      rw [hf0] at hfu; linarith

/-- **Lemma E.1 tool: proper separation.** Non-empty disjoint convex subsets
of `ℝ^Θ` admit a *proper* affine separation: `h ≤ 0` on `A₁`, `h ≥ 0` on `A₂`,
and `h` not identically zero on `A₁ ∪ A₂`. (Rockafellar, Thm. 11.3; the sets
are neither open nor compact in general.) -/
lemma proper_separation {A₁ A₂ : Set (T → ℝ)}
    (h1 : A₁.Nonempty) (h2 : A₂.Nonempty) (hd : Disjoint A₁ A₂)
    (hc1 : Convex ℝ A₁) (hc2 : Convex ℝ A₂) :
    ∃ (f : (T → ℝ) →ₗ[ℝ] ℝ) (c : ℝ),
      (∀ x ∈ A₁, f x + c ≤ 0) ∧ (∀ x ∈ A₂, 0 ≤ f x + c) ∧
      (∃ x ∈ A₁ ∪ A₂, f x + c ≠ 0) := by
  set C : Set (T → ℝ) := A₁ - A₂ with hC
  have hCconv : Convex ℝ C := hc1.sub hc2
  have hCne : C.Nonempty := h1.sub h2
  have h0 : (0 : T → ℝ) ∉ C := by
    rintro ⟨a, ha, b, hb, hab⟩
    exact (hd.ne_of_mem ha hb) (by rw [sub_eq_zero] at hab; exact hab)
  obtain ⟨F, hFle, x0, hx0C, hx0lt⟩ := sep_point_ext hCconv hCne h0
  have hpair : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, F a₁ ≤ F a₂ := by
    intro a₁ ha₁ a₂ ha₂
    have hmem : (a₁ - a₂) ∈ C := ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    have := hFle _ hmem; simp only [map_sub] at this; linarith
  have hbdd : BddAbove (F '' A₁) := by
    obtain ⟨a₂, ha₂⟩ := h2
    exact ⟨F a₂, by rintro _ ⟨a₁, ha₁, rfl⟩; exact hpair a₁ ha₁ a₂ ha₂⟩
  have hne' : (F '' A₁).Nonempty := h1.image _
  set s : ℝ := sSup (F '' A₁) with hs
  refine ⟨F, -s, ?_, ?_, ?_⟩
  · intro x hx
    have : F x ≤ s := le_csSup hbdd ⟨x, hx, rfl⟩; linarith
  · intro x hx
    have : s ≤ F x := csSup_le hne' (by rintro _ ⟨a₁, ha₁, rfl⟩; exact hpair a₁ ha₁ x hx)
    linarith
  · obtain ⟨a, ha, b, hb, hab⟩ := hx0C
    have hlt : F a < F b := by
      have hx : F x0 < 0 := hx0lt
      rw [← hab, map_sub] at hx; linarith
    have ha_le : F a ≤ s := le_csSup hbdd ⟨a, ha, rfl⟩
    have hs_le : s ≤ F b := csSup_le hne' (by rintro _ ⟨a₁, ha₁, rfl⟩; exact hpair a₁ ha₁ b hb)
    by_cases hA : F a + -s = 0
    · exact ⟨b, Or.inr hb, by intro h; apply absurd hlt; push_neg; linarith⟩
    · exact ⟨a, Or.inl ha, hA⟩

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-- Under betweenness, sub-level sets of `v̄` are convex (public version of the
`private` `btwc_sublevel_convex` from `BetweennessCore`). -/
lemma vbar_sublevel_convex (hB : G.Betweenness) (c : ℝ) :
    Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} := by
  intro μ hμ ν hν a b ha hb hab
  by_cases ha0 : a = 0
  · simp_all [show b = 1 by linarith]
  · by_cases hb0 : b = 0
    · simp_all [show a = 1 by linarith]
    · have hbt := hB μ hμ.1 ν hν.1 a ⟨lt_of_le_of_ne ha (Ne.symm ha0),
        by linarith [show 0 < b by positivity]⟩
      refine ⟨⟨fun x => add_nonneg (mul_nonneg ha (hμ.1.1 x)) (mul_nonneg hb (hν.1.1 x)),
        by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ.1.2.1, hν.1.2.1, hab], ?_⟩, ?_⟩
      · intro x hx; simp [hμ.1.2.2 x hx, hν.1.2.2 x hx]
      · have hb' : (1 : ℝ) - a = b := by linarith
        have := hbt.2
        rw [hb'] at this
        exact le_trans this (max_le hμ.2 hν.2)

/-- Finite betweenness (upper bound) for a `Fin n` family: `v̄` of a convex
combination is bounded above by the common upper bound `c` of the pieces. -/
lemma vbar_convexCombo_le (hB : G.Betweenness) {n : ℕ} (a : Fin n → ℝ)
    (μs : Fin n → (T → ℝ)) (hμ : ∀ z, μs z ∈ simplexOn G.Θ)
    (ha : ∀ z, 0 ≤ a z) (hsum : ∑ z, a z = 1) {c : ℝ} (hc : ∀ z, G.vbar (μs z) ≤ c) :
    G.vbar (fun θ => ∑ z, a z * μs z θ) ≤ c := by
  have h_convex : Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} :=
    vbar_sublevel_convex hB c
  have h_mem : (∑ z, a z • μs z) ∈ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} :=
    h_convex.sum_mem (fun z _ => ha z) hsum (fun z _ => ⟨hμ z, hc z⟩)
  have := h_mem.2
  convert this using 2
  funext θ; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-
Under betweenness, the strict super-level set `{μ ∈ simplex | c < v̄ μ}` is
convex.
-/
lemma vbar_superlevel_strict_convex (hB : G.Betweenness) (c : ℝ) :
    Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ c < G.vbar μ} := by
  intro μ hμ ν hν a b ha hb hab;
  refine' ⟨ _, _ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · exact fun x => add_nonneg ( mul_nonneg ha ( hμ.1.1 x ) ) ( mul_nonneg hb ( hν.1.1 x ) );
    · simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hμ.1.2, hν.1.2, hab ];
    · intro θ hθ; simp +decide [ hμ.1.2.2 θ hθ, hν.1.2.2 θ hθ ] ;
  · by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> simp_all +decide [ ← eq_sub_iff_add_eq' ];
    have := hB μ ⟨ hμ.1.1, hμ.1.2.1, hμ.1.2.2 ⟩ ν ⟨ hν.1.1, hν.1.2.1, hν.1.2.2 ⟩ a ⟨ lt_of_le_of_ne ha ( Ne.symm ha0 ), lt_of_le_of_ne hb ( Ne.symm <| by aesop ) ⟩;
    exact lt_of_lt_of_le ( lt_min hμ.2 hν.2 ) this.1

/-
Betweenness "upper bound" existence: if `μ̄` is on the level set `{v̄ = y}` and
is a strictly-positive finite convex combination of points all of value `≤ y`,
then at least one component actually sits on the level set.
-/
lemma exists_level_component (hB : G.Betweenness) (y : ℝ) {μbar : T → ℝ}
    (hbar : G.vbar μbar = y) {n : ℕ} (a : Fin n → ℝ) (μs : Fin n → (T → ℝ))
    (hpos : ∀ z, 0 < a z) (hsum : ∑ z, a z = 1)
    (hmem : ∀ z, μs z ∈ simplexOn G.Θ ∧ G.vbar (μs z) ≤ y)
    (hcomb : μbar = fun θ => ∑ z, a z * μs z θ) :
    ∃ z, G.vbar (μs z) = y := by
  rcases n with ( _ | n ) <;> simp_all +decide;
  -- Since $\sum z, a z = 1$, there must exist some $z$ such that $G.vbar (μs z) = y$.
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Fin (n + 1), ∀ z : Fin (n + 1), G.vbar (μs z) ≤ G.vbar (μs z₀) := by
    simpa using Finset.exists_max_image Finset.univ ( fun z => G.vbar ( μs z ) ) ⟨ 0, Finset.mem_univ 0 ⟩;
  have h_le : G.vbar (fun θ => ∑ z, a z * μs z θ) ≤ G.vbar (μs z₀) := by
    apply vbar_convexCombo_le hB a μs (fun z => (hmem z).left) (fun z => (hpos z).le) hsum (c := G.vbar (μs z₀)) (fun z => hz₀ z);
  exact ⟨ z₀, by linarith [ hmem z₀ ] ⟩

/-- Convexity of the simplex `Δ Θ`. -/
lemma simplexOn_convex' (S : Finset T) : Convex ℝ (simplexOn S) := by
  intro x hx y hy a b ha hb hab
  exact ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)),
    by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hx.2.1, hy.2.1, hab],
    fun i hi => by simp [hx.2.2 i hi, hy.2.2 i hi]⟩

/-- Under betweenness, the strict sub-level set `{μ ∈ simplex | v̄ μ < c}` is
convex (quasiconvexity of `v̄`). -/
lemma vbar_sublevel_strict_convex (hB : G.Betweenness) (c : ℝ) :
    Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ < c} := by
  intro μ hμ ν hν a b ha hb hab
  by_cases ha0 : a = 0
  · simp_all [show b = 1 by linarith]
  · by_cases hb0 : b = 0
    · simp_all [show a = 1 by linarith]
    · have hbt := hB μ hμ.1 ν hν.1 a ⟨lt_of_le_of_ne ha (Ne.symm ha0),
        by linarith [show 0 < b by positivity]⟩
      refine ⟨⟨fun x => add_nonneg (mul_nonneg ha (hμ.1.1 x)) (mul_nonneg hb (hν.1.1 x)),
        by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ.1.2.1, hν.1.2.1, hab], ?_⟩, ?_⟩
      · intro x hx; simp [hμ.1.2.2 x hx, hν.1.2.2 x hx]
      · have hb' : (1 : ℝ) - a = b := by linarith
        have := hbt.2
        rw [hb'] at this
        exact lt_of_le_of_lt this (max_lt hμ.2 hν.2)

/-- **Affine dimension drops across a hyperplane slice.** If a linear functional
`f` is non-constant on `F` (witnessed by `a b ∈ F` with `f a ≠ f b`), then the
affine dimension of the slice `F ∩ {f = t}` is strictly smaller than that of `F`.
This is the measure that makes the induction in `btw_order_aux_rank` well-founded. -/
lemma vectorSpan_hyperplane_finrank_lt (F : Set (T → ℝ)) (f : (T → ℝ) →ₗ[ℝ] ℝ) (t : ℝ)
    (a b : T → ℝ) (ha : a ∈ F) (hb : b ∈ F) (hfab : f a ≠ f b) :
    Module.finrank ℝ (vectorSpan ℝ (F ∩ {x | f x = t})) < Module.finrank ℝ (vectorSpan ℝ F) := by
  have hsub : vectorSpan ℝ (F ∩ {x | f x = t}) ≤ (LinearMap.ker f) ⊓ vectorSpan ℝ F := by
    rw [vectorSpan, Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    refine ⟨?_, vsub_mem_vectorSpan ℝ hp.1 hq.1⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, vsub_eq_sub]
    have h1 : f p = t := hp.2
    have h2 : f q = t := hq.2
    simp_all
  have hlt : (LinearMap.ker f) ⊓ vectorSpan ℝ F < vectorSpan ℝ F := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have hmem : (a - b) ∈ vectorSpan ℝ F := vsub_mem_vectorSpan ℝ ha hb
    rw [← heq] at hmem
    have h0 : f (a - b) = 0 := LinearMap.mem_ker.mp hmem.1
    rw [map_sub] at h0
    exact hfab (sub_eq_zero.mp h0)
  calc Module.finrank ℝ (vectorSpan ℝ (F ∩ {x | f x = t}))
      ≤ Module.finrank ℝ ((LinearMap.ker f) ⊓ vectorSpan ℝ F : Submodule ℝ (T → ℝ)) :=
        Submodule.finrank_mono hsub
    _ < Module.finrank ℝ (vectorSpan ℝ F) := Submodule.finrank_lt_finrank_of_lt hlt

/-- **Lemma E.1 construction: the single-separator ranking relation.** Rank
primarily by the affine separator `f` (descending), breaking ties on the fibre
`{f = f a}` with the recursively supplied slice order `σ (f a)`. -/
def rankRel (f : (T → ℝ) →ₗ[ℝ] ℝ) (σ : ℝ → (T → ℝ) → (T → ℝ) → Prop)
    (a b : T → ℝ) : Prop :=
  f b < f a ∨ (f a = f b ∧ σ (f a) a b)

section Rank

variable (f : (T → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (σ : ℝ → (T → ℝ) → (T → ℝ) → Prop)
  (y : ℝ) (F : Set (T → ℝ))

/-
Completeness of `rankRel` on the level set of `F`, from completeness of each
slice order.
-/
lemma rankRel_complete
    (hσ : ∀ t, ∀ x ∈ F ∩ {x | f x = t}, G.vbar x = y →
      ∀ x' ∈ F ∩ {x | f x = t}, G.vbar x' = y → σ t x x' ∨ σ t x' x) :
    ∀ x ∈ F, G.vbar x = y → ∀ x' ∈ F, G.vbar x' = y →
      rankRel f σ x x' ∨ rankRel f σ x' x := by
  intro x hx hx' x' hx'' hx''';
  by_cases h : f x = f x';
  · cases hσ ( f x ) x ⟨ hx, rfl ⟩ hx' x' ⟨ hx'', h.symm ⟩ hx''' <;> simp_all +decide [ rankRel ];
  · cases lt_or_gt_of_ne h <;> tauto

/-
Transitivity of `rankRel` on the level set of `F`, from transitivity of each
slice order.
-/
lemma rankRel_trans
    (hσ : ∀ t, ∀ x ∈ F ∩ {x | f x = t}, G.vbar x = y →
      ∀ x' ∈ F ∩ {x | f x = t}, G.vbar x' = y →
      ∀ x'' ∈ F ∩ {x | f x = t}, G.vbar x'' = y → σ t x x' → σ t x' x'' → σ t x x'') :
    ∀ x ∈ F, G.vbar x = y → ∀ x' ∈ F, G.vbar x' = y → ∀ x'' ∈ F, G.vbar x'' = y →
      rankRel f σ x x' → rankRel f σ x' x'' → rankRel f σ x x'' := by
  unfold rankRel at *;
  grind

/-
Strict-improvement property (iii) for `rankRel`: moving from `x` on the level
set toward a strictly-higher-value point `u`, while staying on the level set,
strictly improves the rank.
-/
lemma rankRel_iii
    (hle : ∀ x ∈ F, G.vbar x ≤ y → f x + c ≤ 0)
    (hge : ∀ x ∈ F, y < G.vbar x → 0 ≤ f x + c)
    (hσ : ∀ t, ∀ x ∈ F ∩ {x | f x = t}, G.vbar x = y →
      ∀ u ∈ F ∩ {x | f x = t}, y < G.vbar u → ∀ α ∈ Set.Ioo (0 : ℝ) 1,
        (fun θ => α * x θ + (1 - α) * u θ) ∈ F ∩ {x | f x = t} →
        G.vbar (fun θ => α * x θ + (1 - α) * u θ) = y →
          σ t (fun θ => α * x θ + (1 - α) * u θ) x ∧
          ¬ σ t x (fun θ => α * x θ + (1 - α) * u θ)) :
    ∀ x ∈ F, G.vbar x = y → ∀ u ∈ F, y < G.vbar u → ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      (fun θ => α * x θ + (1 - α) * u θ) ∈ F →
      G.vbar (fun θ => α * x θ + (1 - α) * u θ) = y →
        rankRel f σ (fun θ => α * x θ + (1 - α) * u θ) x ∧
        ¬ rankRel f σ x (fun θ => α * x θ + (1 - α) * u θ) := by
  intro x hx hx' u hu hu' α hα hα' hα'';
  have h_linear : f (fun θ => α * x θ + (1 - α) * u θ) = α * f x + (1 - α) * f u := by
    convert f.map_add ( α • x ) ( ( 1 - α ) • u ) using 1 ; norm_num [ f.map_smul ];
  by_cases hfx : f x < f u;
  · simp +decide [ rankRel, hfx ];
    exact ⟨ Or.inl <| by nlinarith [ hα.1, hα.2 ], by nlinarith [ hα.1, hα.2 ], fun h => by nlinarith [ hα.1, hα.2 ] ⟩;
  · have hfx_eq : f x = f u := by
      grind;
    have hfx_eq : f x = -c := by
      linarith [ hle x hx ( by linarith ), hge u hu ( by linarith ) ];
    have hfx_eq : f (fun θ => α * x θ + (1 - α) * u θ) = -c := by
      grind;
    specialize hσ ( -c ) x ⟨ hx, by aesop ⟩ hx' u ⟨ hu, by aesop ⟩ hu' α hα ⟨ hα', by aesop ⟩ hα'' ; simp_all +decide [ rankRel ]

/-
Decomposition property (iv) for `rankRel`, given the slice decomposition
property and the alignment fact `halign`.
-/
lemma rankRel_decomp
    (hσ : ∀ t, ∀ μbar ∈ F ∩ {x | f x = t}, G.vbar μbar = y →
      ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
      (∀ z, 0 < a z) → (∑ z, a z = 1) →
      (∀ z, μs z ∈ F ∩ {x | f x = t} ∧ G.vbar (μs z) ≤ y) →
      (μbar = fun θ => ∑ z, a z * μs z θ) →
        ∃ z, (μs z ∈ F ∩ {x | f x = t} ∧ G.vbar (μs z) = y) ∧ σ t (μs z) μbar)
    (halign : ∀ μbar ∈ F, G.vbar μbar = y →
      ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
      (∀ z, 0 < a z) → (∑ z, a z = 1) →
      (∀ z, μs z ∈ F ∧ G.vbar (μs z) ≤ y) →
      (μbar = fun θ => ∑ z, a z * μs z θ) →
        ∃ z0, G.vbar (μs z0) = y ∧ ∀ w, f (μs w) ≤ f (μs z0)) :
    ∀ μbar ∈ F, G.vbar μbar = y → ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
      (∀ z, 0 < a z) → (∑ z, a z = 1) →
      (∀ z, μs z ∈ F ∧ G.vbar (μs z) ≤ y) →
      (μbar = fun θ => ∑ z, a z * μs z θ) →
        ∃ z, (μs z ∈ F ∧ G.vbar (μs z) = y) ∧ rankRel f σ (μs z) μbar := by
  intro μbar hμbarF hμbary n a μs hpos hsum hmem hcomb
  obtain ⟨z0, hz0, hz0max⟩ := halign μbar hμbarF hμbary n a μs hpos hsum hmem hcomb
  set M := f (μs z0)
  have hfμ : f μbar = ∑ z, a z * f (μs z) := by
    convert f.pi_apply_eq_sum_univ μbar using 1;
    convert f.pi_apply_eq_sum_univ ( ∑ z, a z • μs z ) using 1;
    · simp +decide [ map_sum, map_smul ];
    · simp +decide [ hcomb, Finset.sum_apply, Pi.smul_apply ]
  have hle_M : f μbar ≤ M := by
    rw [ hfμ ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left ( hz0max _ ) ( le_of_lt ( hpos _ ) ) ) ( by simp +decide [ ← Finset.sum_mul, hsum ] );
  by_cases hM : f μbar = M;
  · -- Since $f μbar = M$, we have $f (μs z) = M$ for all $z$.
    have hall : ∀ z, f (μs z) = M := by
      intro z
      by_contra hneq;
      have hsum_pos : ∑ z, a z * (M - f (μs z)) = 0 := by
        simp +decide [ mul_sub, ← Finset.sum_mul _ _ _, hsum, hM ];
        linarith;
      exact absurd hsum_pos ( ne_of_gt ( lt_of_lt_of_le ( mul_pos ( hpos z ) ( sub_pos.mpr ( lt_of_le_of_ne ( hz0max z ) hneq ) ) ) ( Finset.single_le_sum ( fun z _ => mul_nonneg ( le_of_lt ( hpos z ) ) ( sub_nonneg.mpr ( hz0max z ) ) ) ( Finset.mem_univ z ) ) ) );
    specialize hσ M μbar ⟨ hμbarF, hM ⟩ hμbary n a μs hpos hsum ( fun z => ⟨ ⟨ hmem z |>.1, by simp +decide [ hall z ] ⟩, hmem z |>.2 ⟩ ) hcomb ; simp_all +decide [ rankRel ] ;
  · exact ⟨ z0, ⟨ hmem z0 |>.1, hz0 ⟩, Or.inl ( lt_of_le_of_ne hle_M hM ) ⟩

end Rank

/-!
## The two-separator pencil ranking (sound replacement for the single separator)

A single-separator alignment lemma is **false** under plain betweenness (the
Möbius/plateau wedge counterexample): on a full-dimensional level "wedge" the
unique proper separator is not co-monotone with `v̄`, so any single-separator
ranking is unsound.

The sound construction, vindicated by that very wedge, is the **two-separator
pencil**.  On a convex `F ⊆ ΔΘ` with level height `y` we take two proper
separators
* `a = fp + cp`  separating `{v̄ ≤ y} ∩ F` (`a ≤ 0`) from `{v̄ > y} ∩ F` (`a ≥ 0`);
* `b = fm + cm`  separating `{v̄ < y} ∩ F` (`b ≤ 0`) from `{v̄ ≥ y} ∩ F` (`b ≥ 0`).

For a level point `x` one then has `a x ≤ 0 ≤ b x`; for a strictly-below point
`p` **both** `a p ≤ 0` and `b p ≤ 0`; for a strictly-above point `u` both
`a u ≥ 0` and `b u ≥ 0`.  Ranking is primarily by the *pencil coordinate*
`pencilLam x = b x / (b x - a x) ∈ [0,1]` (descending), ties broken by the
inductive slice order on the pencil hyperplane `{pencilVal t = 0}` where
`pencilVal t = t·a + (1-t)·b` (an affine functional whose zero-slice, when
non-constant on `F`, has strictly smaller `vectorSpan` dimension).
-/

/-- **Lemma E.1 construction: the pencil coordinate.** Pencil coordinate of
`x` from the two separators `a = fp + cp`, `b = fm + cm`: for a level point
(`a x ≤ 0 ≤ b x`) it lies in `[0,1]`; the degenerate point `a x = b x = 0` is
sent to the top value `1`. -/
noncomputable def pencilLam (fp fm : (T → ℝ) →ₗ[ℝ] ℝ) (cp cm : ℝ) (x : T → ℝ) : ℝ :=
  if (fm x + cm) - (fp x + cp) = 0 then 1
  else (fm x + cm) / ((fm x + cm) - (fp x + cp))

/-- **Lemma E.1 construction: the pencil functional.** Affine pencil
functional at parameter `t`: `pencilVal t x = t·(a x) + (1-t)·(b x)` where
`a = fp + cp`, `b = fm + cm`. -/
def pencilVal (fp fm : (T → ℝ) →ₗ[ℝ] ℝ) (cp cm : ℝ) (t : ℝ) (x : T → ℝ) : ℝ :=
  t * (fp x + cp) + (1 - t) * (fm x + cm)

/-- **Lemma E.1 construction: the two-separator pencil ranking.** Rank
primarily by `pencilLam` (descending), breaking ties on the pencil hyperplane
`{pencilVal t = 0}` (with `t = pencilLam a`) using the recursively supplied
slice order `σ (pencilLam a)`. -/
def pencilRel (fp fm : (T → ℝ) →ₗ[ℝ] ℝ) (cp cm : ℝ)
    (σ : ℝ → (T → ℝ) → (T → ℝ) → Prop) (a b : T → ℝ) : Prop :=
  pencilLam fp fm cp cm b < pencilLam fp fm cp cm a ∨
    (pencilLam fp fm cp cm a = pencilLam fp fm cp cm b ∧
      σ (pencilLam fp fm cp cm a) a b)

section Pencil

variable (fp fm : (T → ℝ) →ₗ[ℝ] ℝ) (cp cm : ℝ)
  (σ : ℝ → (T → ℝ) → (T → ℝ) → Prop) (y : ℝ) (F : Set (T → ℝ))

/-
On a level point (`a x ≤ 0 ≤ b x`) the pencil coordinate lies in `[0,1]`.
-/
lemma pencilLam_mem_Icc {x : T → ℝ} (ha : fp x + cp ≤ 0) (hb : 0 ≤ fm x + cm) :
    pencilLam fp fm cp cm x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold pencilLam;
  split_ifs <;> [ exact ⟨ by norm_num, by norm_num ⟩ ; exact ⟨ div_nonneg ( by linarith ) ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ) ⟩ ]

/-
The defining property of the pencil coordinate: at its own parameter, the
affine pencil functional vanishes on a level point.
-/
lemma pencilVal_self {x : T → ℝ} (ha : fp x + cp ≤ 0) (hb : 0 ≤ fm x + cm) :
    pencilVal fp fm cp cm (pencilLam fp fm cp cm x) x = 0 := by
  unfold pencilVal pencilLam; by_cases h : ( fm x + cm ) - ( fp x + cp ) = 0 <;> simp +decide [ h ] ; ring;
  · linarith;
  · grind +revert

/-
The affine pencil functional is affine along a two-point combination.
-/
lemma pencilVal_affine_combo (t α : ℝ) (x u : T → ℝ) :
    pencilVal fp fm cp cm t (fun θ => α * x θ + (1 - α) * u θ)
      = α * pencilVal fp fm cp cm t x + (1 - α) * pencilVal fp fm cp cm t u := by
  unfold pencilVal; ring;
  rw [ show ( fun θ => α * x θ - α * u θ + u θ ) = α • x - α • u + u by ext; simp +decide [ sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm ] ] ; rw [ map_add, map_sub ] ; ring;
  rw [ map_add, map_sub, map_smul, map_smul ] ; ring;
  rw [ show fm ( α • x ) = α • fm x by rw [ LinearMap.map_smul ] ] ; rw [ show fm ( α • u ) = α • fm u by rw [ LinearMap.map_smul ] ] ; norm_num ; ring;

/-
The affine pencil functional is affine along a finite convex combination.
-/
lemma pencilVal_sum_combo (t : ℝ) {n : ℕ} (a : Fin n → ℝ) (μs : Fin n → (T → ℝ))
    (hsum : ∑ z, a z = 1) :
    pencilVal fp fm cp cm t (fun θ => ∑ z, a z * μs z θ)
      = ∑ z, a z * pencilVal fp fm cp cm t (μs z) := by
  unfold pencilVal;
  rw [ show ( fun θ => ∑ z, a z * μs z θ ) = ∑ z, a z • μs z from ?_ ];
  · simp +decide [ mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib, hsum ];
    simp +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hsum ];
  · ext θ; simp +decide [ Finset.sum_apply, Pi.smul_apply ] ;

/-
On a level point, `0 ≤ pencilVal t` implies `t ≤ pencilLam` (for `t ≤ 1`).
-/
lemma le_pencilLam_of_pencilVal_nonneg {x : T → ℝ} {t : ℝ}
    (ha : fp x + cp ≤ 0) (hb : 0 ≤ fm x + cm) (ht : t ≤ 1)
    (h : 0 ≤ pencilVal fp fm cp cm t x) : t ≤ pencilLam fp fm cp cm x := by
  unfold pencilLam;
  split_ifs <;> simp_all +decide [ pencilVal ];
  rw [ le_div_iff₀ ] <;> cases lt_or_gt_of_ne ‹_› <;> nlinarith

/-
On a level point, `0 < pencilVal t` implies `t < pencilLam`.
-/
lemma lt_pencilLam_of_pencilVal_pos {x : T → ℝ} {t : ℝ}
    (ha : fp x + cp ≤ 0) (hb : 0 ≤ fm x + cm)
    (h : 0 < pencilVal fp fm cp cm t x) : t < pencilLam fp fm cp cm x := by
  unfold pencilLam pencilVal at *;
  split_ifs <;> [ nlinarith; rw [ lt_div_iff₀ ] <;> nlinarith ];
  rw [ lt_div_iff₀ ] <;> cases lt_or_gt_of_ne ‹_› <;> nlinarith

/-
Completeness of `pencilRel` on the level set of `F`.
-/
lemma pencilRel_complete
    (hlep : ∀ x ∈ F, G.vbar x ≤ y → fp x + cp ≤ 0)
    (hgem : ∀ x ∈ F, y ≤ G.vbar x → 0 ≤ fm x + cm)
    (hgood : ∀ z ∈ F, G.vbar z = y →
      ∃ p ∈ F, ∃ q ∈ F,
        (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) p
          ≠ (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) q)
    (hσ : ∀ t, (∃ p ∈ F, ∃ q ∈ F, (t • fp + (1 - t) • fm) p ≠ (t • fp + (1 - t) • fm) q) →
      ∀ x ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x = y →
      ∀ x' ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x' = y →
        σ t x x' ∨ σ t x' x) :
    ∀ x ∈ F, G.vbar x = y → ∀ x' ∈ F, G.vbar x' = y →
      pencilRel fp fm cp cm σ x x' ∨ pencilRel fp fm cp cm σ x' x := by
  intro x hx hx' x' hx'' hx''';
  by_cases h : pencilLam fp fm cp cm x = pencilLam fp fm cp cm x';
  · specialize hσ (pencilLam fp fm cp cm x) (hgood x hx hx') x ⟨hx, by
      exact pencilVal_self fp fm cp cm ( hlep x hx ( le_of_eq hx' ) ) ( hgem x hx ( le_of_eq hx'.symm ) )⟩ hx' x' ⟨hx'', by
      rw [ h ];
      exact pencilVal_self fp fm cp cm ( hlep x' hx'' ( le_of_eq hx''' ) ) ( hgem x' hx'' ( le_of_eq hx'''.symm ) )⟩ hx''';
    unfold pencilRel; aesop;
  · cases lt_or_gt_of_ne h <;> simp +decide [ *, pencilRel ]

/-
Transitivity of `pencilRel` on the level set of `F`.
-/
lemma pencilRel_trans
    (hlep : ∀ x ∈ F, G.vbar x ≤ y → fp x + cp ≤ 0)
    (hgem : ∀ x ∈ F, y ≤ G.vbar x → 0 ≤ fm x + cm)
    (hgood : ∀ z ∈ F, G.vbar z = y →
      ∃ p ∈ F, ∃ q ∈ F,
        (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) p
          ≠ (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) q)
    (hσ : ∀ t, (∃ p ∈ F, ∃ q ∈ F, (t • fp + (1 - t) • fm) p ≠ (t • fp + (1 - t) • fm) q) →
      ∀ x ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x = y →
      ∀ x' ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x' = y →
      ∀ x'' ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x'' = y →
      σ t x x' → σ t x' x'' → σ t x x'') :
    ∀ x ∈ F, G.vbar x = y → ∀ x' ∈ F, G.vbar x' = y → ∀ x'' ∈ F, G.vbar x'' = y →
      pencilRel fp fm cp cm σ x x' → pencilRel fp fm cp cm σ x' x'' →
        pencilRel fp fm cp cm σ x x'' := by
  intro x hx hx' x' hx' hx'' x'' hx'' hx''' hx'''';
  cases hx'''';
  · grind +locals;
  · cases' ‹pencilLam fp fm cp cm x = pencilLam fp fm cp cm x' ∧ σ ( pencilLam fp fm cp cm x ) x x'› with h₁ h₂;
    cases' em ( pencilLam fp fm cp cm x'' = pencilLam fp fm cp cm x ) with h₃ h₃;
    · have h_pencilVal_zero : pencilVal fp fm cp cm (pencilLam fp fm cp cm x) x = 0 ∧ pencilVal fp fm cp cm (pencilLam fp fm cp cm x) x' = 0 ∧ pencilVal fp fm cp cm (pencilLam fp fm cp cm x) x'' = 0 := by
        exact ⟨ pencilVal_self _ _ _ _ ( hlep _ hx ( by linarith ) ) ( hgem _ hx ( by linarith ) ), by simpa [ h₁ ] using pencilVal_self _ _ _ _ ( hlep _ hx' ( by linarith ) ) ( hgem _ hx' ( by linarith ) ), by simpa [ h₃ ] using pencilVal_self _ _ _ _ ( hlep _ hx'' ( by linarith ) ) ( hgem _ hx'' ( by linarith ) ) ⟩;
      grind +locals;
    · cases lt_or_gt_of_ne h₃ <;> intro h₄ <;> cases h₄ <;> first | linarith | tauto;

/-
Strict-improvement property (iii) for `pencilRel`: moving from a level point
`x` toward a strictly-above point `u`, staying on the level set, strictly
improves the pencil rank.
-/
lemma pencilRel_iii
    (hlep : ∀ x ∈ F, G.vbar x ≤ y → fp x + cp ≤ 0)
    (hgep : ∀ x ∈ F, y < G.vbar x → 0 ≤ fp x + cp)
    (hlem : ∀ x ∈ F, G.vbar x < y → fm x + cm ≤ 0)
    (hgem : ∀ x ∈ F, y ≤ G.vbar x → 0 ≤ fm x + cm)
    (hgood : ∀ z ∈ F, G.vbar z = y →
      ∃ p ∈ F, ∃ q ∈ F,
        (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) p
          ≠ (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) q)
    (hσ : ∀ t, (∃ p ∈ F, ∃ q ∈ F, (t • fp + (1 - t) • fm) p ≠ (t • fp + (1 - t) • fm) q) →
      ∀ x ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x = y →
      ∀ u ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, y < G.vbar u →
      ∀ α ∈ Set.Ioo (0 : ℝ) 1,
        (fun θ => α * x θ + (1 - α) * u θ) ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0} →
        G.vbar (fun θ => α * x θ + (1 - α) * u θ) = y →
          σ t (fun θ => α * x θ + (1 - α) * u θ) x ∧
          ¬ σ t x (fun θ => α * x θ + (1 - α) * u θ)) :
    ∀ x ∈ F, G.vbar x = y → ∀ u ∈ F, y < G.vbar u → ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      (fun θ => α * x θ + (1 - α) * u θ) ∈ F →
      G.vbar (fun θ => α * x θ + (1 - α) * u θ) = y →
        pencilRel fp fm cp cm σ (fun θ => α * x θ + (1 - α) * u θ) x ∧
        ¬ pencilRel fp fm cp cm σ x (fun θ => α * x θ + (1 - α) * u θ) := by
  intro x hxF hxy u huF huy α hα hmF hmy;
  -- Let $t = \text{pencilLam} \, fp \, fm \, cp \, cm \, x$.
  set t := pencilLam fp fm cp cm x with ht_def;
  -- By definition of $t$, we know that $t \leq \text{pencilLam} \, fp \, fm \, cp \, cm \, m$.
  have ht_le : t ≤ pencilLam fp fm cp cm (fun θ => α * x θ + (1 - α) * u θ) := by
    apply le_pencilLam_of_pencilVal_nonneg;
    · exact hlep _ hmF ( le_of_eq hmy );
    · exact hgem _ hmF ( by linarith );
    · exact pencilLam_mem_Icc _ _ _ _ ( hlep x hxF ( by linarith ) ) ( hgem x hxF ( by linarith ) ) |>.2;
    · have ht_le : 0 ≤ pencilVal fp fm cp cm t u := by
        have ht_le : 0 ≤ t ∧ t ≤ 1 := by
          apply pencilLam_mem_Icc;
          · exact hlep x hxF hxy.le;
          · exact hgem x hxF hxy.ge;
        exact add_nonneg ( mul_nonneg ht_le.1 ( hgep u huF huy ) ) ( mul_nonneg ( sub_nonneg.2 ht_le.2 ) ( hgem u huF huy.le ) );
      rw [ pencilVal_affine_combo ];
      rw [ pencilVal_self ];
      · nlinarith [ hα.1, hα.2 ];
      · exact hlep x hxF hxy.le;
      · exact hgem x hxF ( by linarith );
  rcases eq_or_lt_of_le ht_le with ht_eq | ht_lt;
  · have hVu0 : pencilVal fp fm cp cm t u = 0 := by
      have hVm : pencilVal fp fm cp cm t (fun θ => α * x θ + (1 - α) * u θ) = 0 := by
        rw [ ht_eq, pencilVal_self ];
        · exact hlep _ hmF ( le_of_eq hmy );
        · exact hgem _ hmF ( by linarith );
      have hVm : pencilVal fp fm cp cm t (fun θ => α * x θ + (1 - α) * u θ) = (1 - α) * pencilVal fp fm cp cm t u := by
        convert pencilVal_affine_combo fp fm cp cm t α x u using 1;
        simp +zetaDelta at *;
        exact Or.inr ( pencilVal_self fp fm cp cm ( hlep x hxF ( le_of_eq hxy ) ) ( hgem x hxF ( le_of_eq hxy.symm ) ) );
      grind;
    specialize hσ t (hgood x hxF hxy) x ⟨hxF, ?_⟩ hxy u ⟨huF, ?_⟩ huy α hα ⟨hmF, ?_⟩ hmy;
    · exact pencilVal_self _ _ _ _ ( hlep x hxF ( le_of_eq hxy ) ) ( hgem x hxF ( le_of_eq hxy.symm ) );
    · exact hVu0;
    · grind +suggestions;
    · unfold pencilRel; aesop;
  · unfold pencilRel;
    grind

/-
Decomposition property (iv) for `pencilRel`: every positive finite convex
decomposition of a level point `μbar` into pieces of value `≤ y` contains a
level piece ranked at least `μbar`.
-/
lemma pencilRel_decomp
    (hlep : ∀ x ∈ F, G.vbar x ≤ y → fp x + cp ≤ 0)
    (hgep : ∀ x ∈ F, y < G.vbar x → 0 ≤ fp x + cp)
    (hlem : ∀ x ∈ F, G.vbar x < y → fm x + cm ≤ 0)
    (hgem : ∀ x ∈ F, y ≤ G.vbar x → 0 ≤ fm x + cm)
    (hgood : ∀ z ∈ F, G.vbar z = y →
      ∃ p ∈ F, ∃ q ∈ F,
        (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) p
          ≠ (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) q)
    (hσ : ∀ t, (∃ p ∈ F, ∃ q ∈ F, (t • fp + (1 - t) • fm) p ≠ (t • fp + (1 - t) • fm) q) →
      ∀ μbar ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar μbar = y →
      ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
      (∀ z, 0 < a z) → (∑ z, a z = 1) →
      (∀ z, μs z ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0} ∧ G.vbar (μs z) ≤ y) →
      (μbar = fun θ => ∑ z, a z * μs z θ) →
        ∃ z, (μs z ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0} ∧ G.vbar (μs z) = y) ∧
          σ t (μs z) μbar) :
    ∀ μbar ∈ F, G.vbar μbar = y → ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
      (∀ z, 0 < a z) → (∑ z, a z = 1) →
      (∀ z, μs z ∈ F ∧ G.vbar (μs z) ≤ y) →
      (μbar = fun θ => ∑ z, a z * μs z θ) →
        ∃ z, (μs z ∈ F ∧ G.vbar (μs z) = y) ∧ pencilRel fp fm cp cm σ (μs z) μbar := by
  intro μbar hμbarF hμbary n a μs hpos hsum hmem hcomb;
  by_cases hn : n = 0;
  · aesop;
  · -- Let's set `t := pencilLam .. μbar` and derive the necessary inequalities.
    set t := pencilLam fp fm cp cm μbar
    have ht0 : 0 ≤ t := by
      apply (pencilLam_mem_Icc fp fm cp cm (hlep μbar hμbarF (le_of_eq hμbary)) (hgem μbar hμbarF (le_of_eq hμbary.symm))).left
    have ht1 : t ≤ 1 := by
      apply (pencilLam_mem_Icc (fp := fp) (fm := fm) (cp := cp) (cm := cm) (x := μbar) (hlep μbar hμbarF (le_of_eq hμbary)) (hgem μbar hμbarF (le_of_eq hμbary.symm))).right
    have hself : pencilVal fp fm cp cm t μbar = 0 := by
      apply pencilVal_self;
      · exact hlep μbar hμbarF hμbary.le;
      · exact hgem μbar hμbarF hμbary.ge
    have hkey : ∑ z, a z * pencilVal fp fm cp cm t (μs z) = 0 := by
      rw [ ← hself, hcomb, pencilVal_sum_combo ] ; aesop ( simp_config := { singlePass := true } ) ;
    obtain ⟨z0, hz0⟩ : ∃ z0, ∀ z, pencilVal fp fm cp cm t (μs z) ≤ pencilVal fp fm cp cm t (μs z0) := by
      simpa using Finset.exists_max_image Finset.univ ( fun z => pencilVal fp fm cp cm t ( μs z ) ) ⟨ ⟨ 0, Nat.pos_of_ne_zero hn ⟩, Finset.mem_univ _ ⟩;
    by_cases hM : 0 < pencilVal fp fm cp cm t (μs z0);
    · -- Since $pencilVal fp fm cp cm t (μs z0) > 0$, we have $G.vbar (μs z0) = y$.
      have hz0_level : G.vbar (μs z0) = y := by
        by_contra h_contra;
        exact hM.not_ge ( by rw [ pencilVal ] ; nlinarith [ hlep ( μs z0 ) ( hmem z0 |>.1 ) ( hmem z0 |>.2 ), hlem ( μs z0 ) ( hmem z0 |>.1 ) ( lt_of_le_of_ne ( hmem z0 |>.2 ) h_contra ) ] );
      refine' ⟨ z0, ⟨ hmem z0 |>.1, hz0_level ⟩, Or.inl _ ⟩;
      apply lt_pencilLam_of_pencilVal_pos;
      · exact hlep _ ( hmem z0 |>.1 ) ( hz0_level.le );
      · exact hgem _ ( hmem z0 |>.1 ) ( by linarith );
      · exact hM;
    · -- Since $M \leq 0$, we have $pencilVal fp fm cp cm t (μs z) = 0$ for all $z$.
      have hallz : ∀ z, pencilVal fp fm cp cm t (μs z) = 0 := by
        intro z
        by_contra h_nonzero;
        have h_neg : ∑ z, a z * pencilVal fp fm cp cm t (μs z) < ∑ z, a z * 0 := by
          apply Finset.sum_lt_sum;
          · exact fun i _ => mul_le_mul_of_nonneg_left ( le_trans ( hz0 i ) ( le_of_not_gt hM ) ) ( le_of_lt ( hpos i ) );
          · exact ⟨ z, Finset.mem_univ _, mul_lt_mul_of_pos_left ( lt_of_le_of_ne ( le_trans ( hz0 z ) ( le_of_not_gt hM ) ) h_nonzero ) ( hpos z ) ⟩;
        simp +decide [ hkey ] at h_neg;
      specialize hσ t (hgood μbar hμbarF hμbary) μbar ⟨hμbarF, hself⟩ hμbary n a μs hpos hsum (fun z => ⟨⟨hmem z |>.1, hallz z⟩, hmem z |>.2⟩) hcomb;
      obtain ⟨ z, hz₁, hz₂ ⟩ := hσ;
      use z;
      grind +locals

/-
**Flat degeneracy is impossible when a strictly-below point exists.**
If `v̄` is continuous, both separators are nontrivial on `F` (`hsepp`, `hsepm`),
and there is a strictly-above point, then for every level point `z` the pencil
functional at `pencilLam z` is non-constant on `F`.  Equivalently, the pencil
coordinate never becomes globally constant (the wedge stays genuinely
two-dimensional), so the tie-slices always drop affine dimension.

Proof by contradiction on `t := pencilLam z`.  If `t • fp + (1-t) • fm` were
constant on `F`, then `pencilVal t ≡ 0` on `F` (it vanishes at `z` by
`pencilVal_self`).  Then:
* `t = 0` forces `fm + cm ≡ 0`, contradicting `hsepm`;
* `t = 1` forces `fp + cp ≡ 0`, contradicting `hsepp`;
* `t ∈ (0,1)`: the above point `u` has `fp u + cp = 0` and `fm u + cm = 0`
  (both nonneg, weighted to `0`), and `z` has `fp z + cp < 0` (else `pencilLam z`
  would be `1`).  Along the segment `w_α = α z + (1-α) u`, `fp w_α + cp = α (fp z
  + cp) < 0`, so every interior point is `≤ y` (else `hgep` gives `≥ 0`) and `≥ y`
  (betweenness), hence exactly `y`; letting `α → 0` and using continuity gives
  `v̄ u = y`, contradicting `y < v̄ u`.
-/
lemma pencil_hgood (husc : UpperSemicontinuousOn G.vbar (simplexOn G.Θ))
    (hconv : Convex ℝ F) (hFsub : F ⊆ simplexOn G.Θ)
    (hlep : ∀ x ∈ F, G.vbar x ≤ y → fp x + cp ≤ 0)
    (hlem : ∀ x ∈ F, G.vbar x < y → fm x + cm ≤ 0)
    (hgem : ∀ x ∈ F, y ≤ G.vbar x → 0 ≤ fm x + cm)
    (hsepp : ∃ w ∈ F, fp w + cp ≠ 0) (hsepm : ∃ w ∈ F, fm w + cm ≠ 0)
    (hbelow : ∃ w ∈ F, G.vbar w < y) :
    ∀ z ∈ F, G.vbar z = y →
      ∃ p ∈ F, ∃ q ∈ F,
        (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) p
          ≠ (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) q := by
  intro z hzF hzy
  set t := pencilLam fp fm cp cm z with ht
  by_contra hfold
  push_neg at hfold
  have hfull : ∀ x ∈ F, t * (fp x + cp) + (1 - t) * (fm x + cm) = 0 := by
    have hLz : t * (fp z + cp) + (1 - t) * (fm z + cm) = 0 := by
      have h := pencilVal_self fp fm cp cm (hlep z hzF (le_of_eq hzy))
        (hgem z hzF (le_of_eq hzy.symm))
      rw [ht]
      simpa [pencilVal] using h
    intro x hx
    have hLx : (t • fp + (1 - t) • fm) x = (t • fp + (1 - t) • fm) z :=
      hfold x hx z hzF
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hLx
    nlinarith [hLx, hLz]
  have ht0 : 0 ≤ t :=
    (pencilLam_mem_Icc fp fm cp cm (hlep z hzF (le_of_eq hzy))
      (hgem z hzF (le_of_eq hzy.symm))).1
  have ht1 : t ≤ 1 :=
    (pencilLam_mem_Icc fp fm cp cm (hlep z hzF (le_of_eq hzy))
      (hgem z hzF (le_of_eq hzy.symm))).2
  have ht0' : 0 < t := by
    by_contra ht
    have : t = 0 := le_antisymm (not_lt.mp ht) ht0
    obtain ⟨q, hqF, hq⟩ := hsepm
    specialize hfull q hqF
    rw [this] at hfull
    simp at hfull
    exact hq hfull
  have ht1' : t < 1 := by
    by_contra ht
    have : t = 1 := le_antisymm ht1 (not_lt.mp ht)
    obtain ⟨q, hqF, hq⟩ := hsepp
    specialize hfull q hqF
    rw [this] at hfull
    simp at hfull
    exact hq hfull
  obtain ⟨w, hwF, hwy⟩ := hbelow
  have haw0 : fp w + cp = 0 := by
    nlinarith [hfull w hwF, hlep w hwF (le_of_lt hwy), hlem w hwF hwy]
  have hbw0 : fm w + cm = 0 := by
    nlinarith [hfull w hwF, hlep w hwF (le_of_lt hwy), hlem w hwF hwy]
  have hbzero : ∀ q ∈ F, fm q + cm = 0 := by
    intro q hqF
    let s : ℕ → (T → ℝ) := fun n θ => (1 / (n + 2 : ℝ)) * q θ +
      (1 - 1 / (n + 2 : ℝ)) * w θ
    have hsF : ∀ n, s n ∈ F := by
      intro n
      apply hconv hqF hwF
      · positivity
      · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hden : (0 : ℝ) < (n : ℝ) + 2 := by linarith
        have hone : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
        exact sub_nonneg.mpr ((div_le_one hden).mpr hone)
      · ring
    have hsconv : Filter.Tendsto s Filter.atTop (nhds w) := by
      rw [tendsto_pi_nhds]
      intro θ
      exact (by
        exact le_trans (Filter.Tendsto.add
          (Filter.Tendsto.mul
            (tendsto_const_nhds.div_atTop
              (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
            tendsto_const_nhds)
          (Filter.Tendsto.mul
            (tendsto_const_nhds.sub
              (tendsto_const_nhds.div_atTop
                (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)))
            tendsto_const_nhds)) (by norm_num))
    have hswithin : Filter.Tendsto s Filter.atTop (nhdsWithin w (simplexOn G.Θ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hsconv, Filter.Eventually.of_forall fun n => hFsub (hsF n)⟩
    have hev : ∀ᶠ n in Filter.atTop, G.vbar (s n) < y :=
      (husc w (hFsub hwF)) y hwy |>.filter_mono hswithin
    obtain ⟨n, hn⟩ := hev.exists
    have ha : fp (s n) + cp ≤ 0 := hlep (s n) (hsF n) (le_of_lt hn)
    have hb : fm (s n) + cm ≤ 0 := hlem (s n) (hsF n) hn
    have hb0 : fm (s n) + cm = 0 := by
      nlinarith [hfull (s n) (hsF n)]
    have hlin : fm (s n) = (1 / (n + 2 : ℝ)) * fm q +
        (1 - 1 / (n + 2 : ℝ)) * fm w := by
      change fm ((1 / (n + 2 : ℝ)) • q + (1 - 1 / (n + 2 : ℝ)) • w) = _
      rw [map_add, map_smul, map_smul]
      simp [smul_eq_mul]
    rw [hlin] at hb0
    have hnpos : 0 < (1 / (n + 2 : ℝ)) := by positivity
    nlinarith [hbw0]
  obtain ⟨q, hqF, hq⟩ := hsepm
  exact hq (hbzero q hqF)

end Pencil

/-- **Generalized ranking lemma**, bounded-rank form: strong induction on the
affine dimension `d = Module.finrank ℝ (vectorSpan ℝ F)`.  In the substantive
case (a level point and a strictly-above point both exist) it ranks the level
set by the **two-separator pencil** described above. -/
lemma btw_order_aux_rank (husc : UpperSemicontinuousOn G.vbar (simplexOn G.Θ))
    (hB : G.Betweenness) (y : ℝ) :
    ∀ d : ℕ, ∀ F : Set (T → ℝ), Module.finrank ℝ (vectorSpan ℝ F) = d →
      Convex ℝ F → F ⊆ simplexOn G.Θ →
    ∃ ord : (T → ℝ) → (T → ℝ) → Prop,
      (∀ x ∈ F, G.vbar x = y → ∀ x' ∈ F, G.vbar x' = y → ord x x' ∨ ord x' x) ∧
      (∀ x ∈ F, G.vbar x = y → ∀ x' ∈ F, G.vbar x' = y → ∀ x'' ∈ F, G.vbar x'' = y →
        ord x x' → ord x' x'' → ord x x'') ∧
      (∀ x ∈ F, G.vbar x = y → ∀ u ∈ F, y < G.vbar u → ∀ α ∈ Set.Ioo (0 : ℝ) 1,
        (fun θ => α * x θ + (1 - α) * u θ) ∈ F →
        G.vbar (fun θ => α * x θ + (1 - α) * u θ) = y →
          ord (fun θ => α * x θ + (1 - α) * u θ) x ∧
          ¬ ord x (fun θ => α * x θ + (1 - α) * u θ)) ∧
      (∀ μbar ∈ F, G.vbar μbar = y → ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
        (∀ z, 0 < a z) → (∑ z, a z = 1) →
        (∀ z, μs z ∈ F ∧ G.vbar (μs z) ≤ y) →
        (μbar = fun θ => ∑ z, a z * μs z θ) →
          ∃ z, (μs z ∈ F ∧ G.vbar (μs z) = y) ∧ ord (μs z) μbar) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro F hFd hconv hFsub
    by_cases hSne : ∃ x ∈ F, G.vbar x = y
    · by_cases hA2 : ∃ u ∈ F, y < G.vbar u
      · -- main separator case: a level point `x0` and a strictly-above point `u0` exist
        obtain ⟨x0, hx0F, hx0y⟩ := hSne
        obtain ⟨u0, hu0F, hu0y⟩ := hA2
        -- the `+` separator: {v̄ ≤ y} ∩ F  vs  {v̄ > y} ∩ F
        have hAne : (F ∩ {μ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ y}).Nonempty :=
          ⟨x0, hx0F, hFsub hx0F, le_of_eq hx0y⟩
        have hA2ne : (F ∩ {μ | μ ∈ simplexOn G.Θ ∧ y < G.vbar μ}).Nonempty :=
          ⟨u0, hu0F, hFsub hu0F, hu0y⟩
        have hdis : Disjoint (F ∩ {μ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ y})
            (F ∩ {μ | μ ∈ simplexOn G.Θ ∧ y < G.vbar μ}) := by
          rw [Set.disjoint_left]; rintro z ⟨_, _, hz1⟩ ⟨_, _, hz2⟩; linarith
        obtain ⟨fp, cp, hAle', hA2ge', hsep_ne⟩ := proper_separation hAne hA2ne hdis
          (hconv.inter (vbar_sublevel_convex hB y))
          (hconv.inter (vbar_superlevel_strict_convex hB y))
        have hlep : ∀ x ∈ F, G.vbar x ≤ y → fp x + cp ≤ 0 :=
          fun x hxF hxy => hAle' x ⟨hxF, hFsub hxF, hxy⟩
        have hgep : ∀ x ∈ F, y < G.vbar x → 0 ≤ fp x + cp :=
          fun x hxF hxy => hA2ge' x ⟨hxF, hFsub hxF, hxy⟩
        have hsepp : ∃ w ∈ F, fp w + cp ≠ 0 := by
          obtain ⟨w, hw, hwne⟩ := hsep_ne
          rcases hw with hw | hw <;> exact ⟨w, hw.1, hwne⟩
        by_cases hbelow : (F ∩ {μ | μ ∈ simplexOn G.Θ ∧ G.vbar μ < y}).Nonempty
        · -- **Below point exists**: two-separator pencil.  Flat degeneracy is
          -- ruled out (`pencil_hgood`), so all tie-slices drop affine dimension.
          have hA2ne' : (F ∩ {μ | μ ∈ simplexOn G.Θ ∧ y ≤ G.vbar μ}).Nonempty :=
            ⟨x0, hx0F, hFsub hx0F, le_of_eq hx0y.symm⟩
          have hdis' : Disjoint (F ∩ {μ | μ ∈ simplexOn G.Θ ∧ G.vbar μ < y})
              (F ∩ {μ | μ ∈ simplexOn G.Θ ∧ y ≤ G.vbar μ}) := by
            rw [Set.disjoint_left]; rintro z ⟨_, _, hz1⟩ ⟨_, _, hz2⟩; linarith
          obtain ⟨fm, cm, hle2, hge2, hsep_ne'⟩ := proper_separation hbelow hA2ne' hdis'
            (hconv.inter (vbar_sublevel_strict_convex hB y))
            (hconv.inter (vbar_superlevel_convex hB.qc y))
          have hlem : ∀ x ∈ F, G.vbar x < y → fm x + cm ≤ 0 :=
            fun x hxF hxy => hle2 x ⟨hxF, hFsub hxF, hxy⟩
          have hgem : ∀ x ∈ F, y ≤ G.vbar x → 0 ≤ fm x + cm :=
            fun x hxF hxy => hge2 x ⟨hxF, hFsub hxF, hxy⟩
          have hsepm : ∃ w ∈ F, fm w + cm ≠ 0 := by
            obtain ⟨w, hw, hwne⟩ := hsep_ne'
            rcases hw with hw | hw <;> exact ⟨w, hw.1, hwne⟩
          have hgood : ∀ z ∈ F, G.vbar z = y →
              ∃ p ∈ F, ∃ q ∈ F,
                (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) p
                  ≠ (pencilLam fp fm cp cm z • fp + (1 - pencilLam fp fm cp cm z) • fm) q :=
            pencil_hgood fp fm cp cm y F husc hconv hFsub hlep hlem hgem hsepp hsepm
              ⟨hbelow.some, hbelow.some_mem.1, hbelow.some_mem.2.2⟩
          have hslice_eq : ∀ t, F ∩ {x | pencilVal fp fm cp cm t x = 0}
              = F ∩ {x | (t • fp + (1 - t) • fm) x = -(t * cp + (1 - t) * cm)} := by
            intro t; ext x
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq, pencilVal,
              LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            constructor <;> rintro ⟨hxF, hx⟩ <;> exact ⟨hxF, by linarith⟩
          have hconv_slice : ∀ t, Convex ℝ (F ∩ {x | pencilVal fp fm cp cm t x = 0}) := by
            intro t; rw [hslice_eq t]
            exact hconv.inter ((convex_singleton _).linear_preimage (t • fp + (1 - t) • fm))
          classical
          have hσchoose : ∀ t : ℝ, ∃ ord : (T → ℝ) → (T → ℝ) → Prop,
              (∃ p ∈ F, ∃ q ∈ F, (t • fp + (1 - t) • fm) p ≠ (t • fp + (1 - t) • fm) q) →
              (∀ x ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x = y →
                ∀ x' ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x' = y →
                  ord x x' ∨ ord x' x) ∧
              (∀ x ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x = y →
                ∀ x' ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x' = y →
                ∀ x'' ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x'' = y →
                  ord x x' → ord x' x'' → ord x x'') ∧
              (∀ x ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar x = y →
                ∀ u ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, y < G.vbar u →
                ∀ α ∈ Set.Ioo (0 : ℝ) 1,
                (fun θ => α * x θ + (1 - α) * u θ) ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0} →
                G.vbar (fun θ => α * x θ + (1 - α) * u θ) = y →
                  ord (fun θ => α * x θ + (1 - α) * u θ) x ∧
                  ¬ ord x (fun θ => α * x θ + (1 - α) * u θ)) ∧
              (∀ μbar ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0}, G.vbar μbar = y →
                ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
                (∀ z, 0 < a z) → (∑ z, a z = 1) →
                (∀ z, μs z ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0} ∧ G.vbar (μs z) ≤ y) →
                (μbar = fun θ => ∑ z, a z * μs z θ) →
                  ∃ z, (μs z ∈ F ∩ {x | pencilVal fp fm cp cm t x = 0} ∧ G.vbar (μs z) = y) ∧
                    ord (μs z) μbar) := by
            intro t
            by_cases ht : ∃ p ∈ F, ∃ q ∈ F, (t • fp + (1 - t) • fm) p ≠ (t • fp + (1 - t) • fm) q
            · obtain ⟨p, hpF, q, hqF, hpq⟩ := ht
              have hdrop : Module.finrank ℝ (vectorSpan ℝ (F ∩ {x | pencilVal fp fm cp cm t x = 0})) < d := by
                rw [hslice_eq t]
                have := vectorSpan_hyperplane_finrank_lt F (t • fp + (1 - t) • fm)
                  (-(t * cp + (1 - t) * cm)) p q hpF hqF hpq
                rwa [hFd] at this
              obtain ⟨ord, hord⟩ := ih _ hdrop _ rfl (hconv_slice t) (fun x hx => hFsub hx.1)
              exact ⟨ord, fun _ => hord⟩
            · exact ⟨fun _ _ => True, fun ht' => absurd ht' ht⟩
          choose σ hσ using hσchoose
          refine ⟨pencilRel fp fm cp cm σ, ?_, ?_, ?_, ?_⟩
          · exact pencilRel_complete fp fm cp cm σ y F hlep hgem hgood
              (fun t ht => (hσ t ht).1)
          · exact pencilRel_trans fp fm cp cm σ y F hlep hgem hgood
              (fun t ht => (hσ t ht).2.1)
          · exact pencilRel_iii fp fm cp cm σ y F hlep hgep hlem hgem hgood
              (fun t ht => (hσ t ht).2.2.1)
          · exact pencilRel_decomp fp fm cp cm σ y F hlep hgep hlem hgem hgood
              (fun t ht => (hσ t ht).2.2.2)
        · -- **No strictly-below point**: every value-`≤ y` point of `F` is a level
          -- point, so the single `+` separator suffices (`rankRel fp`); the
          -- alignment property (iv) holds because all decomposition pieces are level.
          have hnb : ∀ x ∈ F, ¬ G.vbar x < y := fun x hxF h => hbelow ⟨x, hxF, hFsub hxF, h⟩
          have hfab : ∃ p ∈ F, ∃ q ∈ F, fp p ≠ fp q := by
            obtain ⟨w, hwF, hwne⟩ := hsepp
            rcases lt_or_gt_of_ne hwne with hlt | hgt
            · refine ⟨w, hwF, u0, hu0F, ?_⟩
              intro heq; have := hgep u0 hu0F hu0y; rw [heq] at hlt; linarith
            · refine ⟨w, hwF, x0, hx0F, ?_⟩
              intro heq; have := hlep x0 hx0F (le_of_eq hx0y); rw [heq] at hgt; linarith
          have hdrop : ∀ t : ℝ,
              Module.finrank ℝ (vectorSpan ℝ (F ∩ {x | fp x = t})) < d := by
            intro t
            obtain ⟨p, hpF, q, hqF, hpq⟩ := hfab
            have := vectorSpan_hyperplane_finrank_lt F fp t p q hpF hqF hpq
            rwa [hFd] at this
          choose σ hspec using (fun t : ℝ =>
            ih (Module.finrank ℝ (vectorSpan ℝ (F ∩ {x | fp x = t}))) (hdrop t)
              (F ∩ {x | fp x = t}) rfl (hconv.inter ((convex_singleton t).linear_preimage fp))
              (fun x hx => hFsub hx.1))
          refine ⟨rankRel fp σ, ?_, ?_, ?_, ?_⟩
          · exact rankRel_complete fp σ y F (fun t => (hspec t).1)
          · exact rankRel_trans fp σ y F (fun t => (hspec t).2.1)
          · exact rankRel_iii fp cp σ y F hlep hgep (fun t => (hspec t).2.2.1)
          · refine rankRel_decomp fp σ y F (fun t => (hspec t).2.2.2) ?_
            intro μbar hμbarF hμbary n a μs hpos hsum hmem hcomb
            have hlevel : ∀ z, G.vbar (μs z) = y := fun z =>
              le_antisymm (hmem z).2 (not_lt.mp (hnb (μs z) (hmem z).1))
            have hn : 0 < n := by
              rcases Nat.eq_zero_or_pos n with h | h
              · subst h; simp at hsum
              · exact h
            obtain ⟨z0, _, hz0max⟩ :=
              Finset.exists_max_image Finset.univ (fun z => fp (μs z)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
            exact ⟨z0, hlevel z0, fun w => hz0max w (Finset.mem_univ w)⟩
      · -- no point strictly above `y`: property (iii) is vacuous
        push_neg at hA2
        refine ⟨fun _ _ => True, ?_, ?_, ?_, ?_⟩
        · intro x _ _ x' _ _; exact Or.inl trivial
        · intro x _ _ x' _ _ x'' _ _ _ _; trivial
        · intro x _ _ u huF hu; exact absurd (hA2 u huF) (not_le.mpr hu)
        · intro μbar _ hμbary n a μs hpos hsum hmem hcomb
          obtain ⟨z, hz⟩ := exists_level_component hB y hμbary a μs hpos hsum
            (fun z => ⟨hFsub (hmem z).1, (hmem z).2⟩) hcomb
          exact ⟨z, ⟨(hmem z).1, hz⟩, trivial⟩
    · -- level set empty: everything is vacuous
      push_neg at hSne
      refine ⟨fun _ _ => True, ?_, ?_, ?_, ?_⟩
      · intro x hxF hxy; exact absurd hxy (hSne x hxF)
      · intro x hxF hxy; exact absurd hxy (hSne x hxF)
      · intro x hxF hxy; exact absurd hxy (hSne x hxF)
      · intro μbar hμbarF hμbary; exact absurd hμbary (hSne μbar hμbarF)

/-- **Generalized ranking lemma** (`lem:btw-order`, relativized to a convex
`F ⊆ Δ Θ`), proved by strong induction on the affine dimension
`Module.finrank ℝ (vectorSpan ℝ F)`. Writing the level slice `S_F = {x ∈ F | v̄ x = y}`,
it provides a complete transitive relation on `S_F` with the strict-improvement
property (i) and the decomposition property (ii), both relativized to `F`.
Specializing to `F = Δ Θ` yields `btw_order`. -/
lemma btw_order_aux (husc : UpperSemicontinuousOn G.vbar (simplexOn G.Θ))
    (hB : G.Betweenness) (y : ℝ) :
    ∀ F : Set (T → ℝ), Convex ℝ F → F ⊆ simplexOn G.Θ →
    ∃ ord : (T → ℝ) → (T → ℝ) → Prop,
      (∀ x ∈ F, G.vbar x = y → ∀ x' ∈ F, G.vbar x' = y → ord x x' ∨ ord x' x) ∧
      (∀ x ∈ F, G.vbar x = y → ∀ x' ∈ F, G.vbar x' = y → ∀ x'' ∈ F, G.vbar x'' = y →
        ord x x' → ord x' x'' → ord x x'') ∧
      (∀ x ∈ F, G.vbar x = y → ∀ u ∈ F, y < G.vbar u → ∀ α ∈ Set.Ioo (0 : ℝ) 1,
        (fun θ => α * x θ + (1 - α) * u θ) ∈ F →
        G.vbar (fun θ => α * x θ + (1 - α) * u θ) = y →
          ord (fun θ => α * x θ + (1 - α) * u θ) x ∧
          ¬ ord x (fun θ => α * x θ + (1 - α) * u θ)) ∧
      (∀ μbar ∈ F, G.vbar μbar = y → ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
        (∀ z, 0 < a z) → (∑ z, a z = 1) →
        (∀ z, μs z ∈ F ∧ G.vbar (μs z) ≤ y) →
        (μbar = fun θ => ∑ z, a z * μs z θ) →
          ∃ z, (μs z ∈ F ∧ G.vbar (μs z) = y) ∧ ord (μs z) μbar) := by
  intro F hconv hsub
  exact btw_order_aux_rank husc hB y (Module.finrank ℝ (vectorSpan ℝ F)) F rfl hconv hsub

end DisclosureGame

end CPD