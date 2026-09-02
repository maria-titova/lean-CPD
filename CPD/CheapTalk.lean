import CPD.Existence
import Mathlib

/-!
# Cheap Talk and the Quasiconcave Closure

Formalizes Section 6.3 of the paper. A message mapping has **cheap-talk
copies (M-CT)** (Definition 16) if every message belongs to a class of at
least `n := |Θ|` messages sharing its preimage. The **quasiconcave closure** `v̄^qc` of
the upper envelope `v̄` (Definition 17) is built from convex combinations of
belief-tuples indexed by `Θ`; it is the smallest quasiconcave function
dominating `v̄`. Its associated **closure game** `G^qc = (Θ, 𝓜, M, μ⁰, V^qc)`
is a disclosure game that inherits message completeness (M-C) from `G` and is
itself quasiconcave (Lemma F.1). Every coalition payoff of a restricted game
is bounded above by `v̄^qc` of its cell's conditional prior (Lemma F.2, the
qc-bound), and under M-CT this bound is achieved: a coalition can spread its
members across cheap-talk copies of a single message to realize
`v̄^qc(μ⁰_C)` exactly at the conditional prior (Lemma F.3, the
ct-realization).

* `MCT` — cheap-talk copies (Definition 16).
* `qcClosure` — the quasiconcave closure `v̄^qc` (Definition 17), and
  `closureGame` — the closure game `G^qc` (Lemma F.1).
* `closureGame_QC`, `closureGame_MC` — the closure game is quasiconcave and
  inherits M-C (Lemma F.1).
* `coalition_w_le_qcClosure` — the qc-bound (Lemma F.2).
* `ct_realization` — the ct-realization lemma (Lemma F.3).
-/

open Set Topology
open scoped Classical

set_option maxHeartbeats 1600000

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ## (M-CT) cheap-talk copies -/

variable (G) in
/-- **Definition 16** (cheap-talk copies, M-CT): for every `m ∈ 𝓜`, at least
`n := |Θ|` messages `m'` share the preimage `P(m')=P(m)`. -/
def MCT : Prop :=
  ∀ m ∈ G.𝓜, G.Θ.card ≤ (G.𝓜.filter (fun m' => G.canSend m' = G.canSend m)).card

/-! ## The quasiconcave closure -/

variable (G) in
/-- `v_min := min_{ΔΘ} v̲`, the lowest lower-envelope value. -/
noncomputable def vMin : ℝ := sInf (G.vlow '' simplexOn G.Θ)

variable (G) in
/-- The **constraint set** `K_μ`: pairs `(λ, p)` of a weight distribution
`λ ∈ ΔΘ` and beliefs `p θ₀ ∈ ΔΘ` (`θ₀` over the `n` elements of `Θ`) with
`μ = ∑_{θ₀} λ(θ₀)·p(θ₀)`. -/
def qcConstraint (μ : T → ℝ) : Set ((T → ℝ) × (T → T → ℝ)) :=
  {lp | lp.1 ∈ simplexOn G.Θ ∧ (∀ θ₀, lp.2 θ₀ ∈ simplexOn G.Θ) ∧
        (∀ θ, μ θ = ∑ θ₀ ∈ G.Θ, lp.1 θ₀ * lp.2 θ₀ θ)}

variable (G) in
/-- The **objective** `min_{θ₀∈Θ} v̄(p θ₀)`. -/
noncomputable def qcObjective (lp : (T → ℝ) × (T → T → ℝ)) : ℝ :=
  G.Θ.inf' G.Θ_nonempty (fun θ₀ => G.vbar (lp.2 θ₀))

variable (G) in
/-- **Definition 17** (quasiconcave closure `v̄^qc`): `v̄^qc(μ)` is the
supremum of the objective over the constraint set. -/
noncomputable def qcClosure (μ : T → ℝ) : ℝ :=
  sSup (G.qcObjective '' G.qcConstraint μ)

variable (G) in
/-- The upper level set `{ν ∈ ΔΘ | v̄(ν) ≥ y}`. -/
def vbarUpperLevel (y : ℝ) : Set (T → ℝ) :=
  {ν | ν ∈ simplexOn G.Θ ∧ y ≤ G.vbar ν}

/-! ## Private helpers (quasiconcave-closure analysis) -/

/-
The standard simplex on a `Finset` is convex.
-/
private lemma simplexOn_convex (S : Finset T) : Convex ℝ (simplexOn S) := by
  intro x hx y hy a b ha hb hab;
  refine' ⟨ fun θ => _, _, fun θ hθ => _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
  · nlinarith [ hx.1 θ, hy.1 θ ];
  · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hx.2.1, hy.2.1, hab ]

/-
`v_min ≤ v̲(μ)` for every belief `μ`.
-/
private lemma vMin_le_vlow {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.vMin ≤ G.vlow μ := by
  obtain ⟨ M, hM ⟩ := exists_bound_V G;
  exact csInf_le ⟨ -M, Set.forall_mem_image.2 fun ν hν => neg_le_of_abs_le ( hM ν hν _ ( vlow_mem hν ) ) ⟩ ⟨ μ, hμ, rfl ⟩

/-
The trivial representation `(μ, const μ)` lies in `K_μ`.
-/
private lemma qcConstraint_trivial_mem {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    ((μ, fun _ => μ) : (T → ℝ) × (T → T → ℝ)) ∈ G.qcConstraint μ := by
  refine' ⟨ hμ, fun _ => hμ, fun _ => _ ⟩;
  have := hμ.2.1;
  simp +decide [ ← Finset.sum_mul, this ];
  rw [ Finset.sum_subset ( Finset.subset_univ _ ) fun x _ hx => hμ.2.2 x hx ] ; simp +decide [ this ]

/-- `K_μ` is non-empty for `μ ∈ ΔΘ`. -/
private lemma qcConstraint_nonempty {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    (G.qcConstraint μ).Nonempty :=
  ⟨_, qcConstraint_trivial_mem hμ⟩

/-
`K_μ` is compact.
-/
private lemma qcConstraint_isCompact (μ : T → ℝ) : IsCompact (G.qcConstraint μ) := by
  refine' IsCompact.of_isClosed_subset _ _ _;
  exact ( simplexOn G.Θ ) ×ˢ Set.pi Set.univ fun _ => simplexOn G.Θ;
  · exact isCompact_simplexOn G.Θ |> IsCompact.prod <| isCompact_univ_pi fun _ => isCompact_simplexOn G.Θ;
  · refine' isClosed_of_closure_subset _;
    intro x hx;
    rw [ mem_closure_iff_seq_limit ] at hx;
    obtain ⟨ y, hy, hy' ⟩ := hx;
    refine' ⟨ _, _, _ ⟩;
    · have h_lim : Filter.Tendsto (fun n => y n |>.1) Filter.atTop (nhds x.1) := by
        exact continuousAt_fst.tendsto.comp hy';
      exact isClosed_simplexOn G.Θ |> fun h => h.mem_of_tendsto h_lim ( Filter.Eventually.of_forall fun n => hy n |>.1 );
    · intro θ₀
      have h_seq : Filter.Tendsto (fun n => (y n).2 θ₀) Filter.atTop (nhds (x.2 θ₀)) := by
        exact tendsto_pi_nhds.mp ( continuousAt_snd.tendsto.comp hy' ) θ₀;
      exact isClosed_simplexOn G.Θ |> fun h => h.mem_of_tendsto h_seq ( Filter.Eventually.of_forall fun n => hy n |>.2.1 θ₀ );
    · intro θ;
      have h_lim : Filter.Tendsto (fun n => ∑ θ₀ ∈ G.Θ, (y n).1 θ₀ * (y n).2 θ₀ θ) Filter.atTop (nhds (∑ θ₀ ∈ G.Θ, x.1 θ₀ * x.2 θ₀ θ)) := by
        exact tendsto_finset_sum _ fun _ _ => Filter.Tendsto.mul ( continuousAt_apply _ _ |> ContinuousAt.tendsto |> Filter.Tendsto.comp <| continuousAt_fst.tendsto.comp hy' ) ( continuousAt_apply _ _ |> ContinuousAt.tendsto |> Filter.Tendsto.comp <| continuousAt_apply _ _ |> ContinuousAt.tendsto |> Filter.Tendsto.comp <| continuousAt_snd.tendsto.comp hy' );
      exact tendsto_nhds_unique ( tendsto_const_nhds.congr fun n => by rw [ hy n |>.2.2 ] ) h_lim;
  · exact fun x hx => ⟨ hx.1, fun _ _ => hx.2.1 _ ⟩

/-
`min_{θ₀} v̄` is upper semicontinuous on the set of belief-tuples.
-/
private lemma qcObjective_upperSemicontinuousOn :
    UpperSemicontinuousOn G.qcObjective
      {lp : (T → ℝ) × (T → T → ℝ) | ∀ θ₀, lp.2 θ₀ ∈ simplexOn G.Θ} := by
  intro lp hlp y hy; contrapose! hy; simp_all +decide [ UpperSemicontinuousWithinAt ] ;
  contrapose! hy;
  -- Since $G.qcObjective lp < y$, there exists some $\theta_0 \in G.Θ$ such that $G.vbar (lp.2 \theta_0) < y$.
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ G.Θ, G.vbar (lp.2 θ₀) < y := by
    exact Exists.elim ( Finset.exists_mem_eq_inf' G.Θ_nonempty fun θ₀ => G.vbar ( lp.2 θ₀ ) ) fun x hx => ⟨ x, hx.1, hx.2.symm ▸ hy ⟩;
  -- Since $G.vbar$ is upper semicontinuous on $simplexOn G.Θ$, there exists a neighborhood $U$ of $lp.2 \theta_0$ such that $G.vbar (x) < y$ for all $x \in U$.
  obtain ⟨U, hU⟩ : ∃ U ∈ nhds (lp.2 θ₀), ∀ x ∈ U, x ∈ simplexOn G.Θ → G.vbar x < y := by
    have := G.vbar_upperSemicontinuousOn ( lp.2 θ₀ ) ( hlp θ₀ |>.1 |> fun h => ⟨ h, hlp θ₀ |>.2.1, hlp θ₀ |>.2.2 ⟩ ) y hθ₀.2; simp_all +decide [ UpperSemicontinuousWithinAt ] ;
    rw [ eventually_nhdsWithin_iff ] at this; simp_all +decide [ simplexOn ] ;
    exact ⟨ _, this, fun x hx hx' hx'' hx''' => this.self_of_nhds |> fun h => by aesop ⟩
  generalize_proofs at *; (
  -- Since $U$ is a neighborhood of $lp.2 \theta_0$, there exists a neighborhood $V$ of $lp$ such that for all $x \in V$, $x.2 \theta_0 \in U$.
  obtain ⟨V, hV⟩ : ∃ V ∈ nhds lp, ∀ x ∈ V, x.2 θ₀ ∈ U := by
    exact ⟨ { x : ( T → ℝ ) × ( T → T → ℝ ) | x.2 θ₀ ∈ U }, by exact ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun x : ( T → ℝ ) × ( T → T → ℝ ) => x.2 θ₀ ) lp from ContinuousAt.comp ( continuous_apply θ₀ |> Continuous.continuousAt ) continuousAt_snd ) hU.1, fun x hx => hx ⟩
  generalize_proofs at *; (
  filter_upwards [ self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hV.1 ] with x hx₁ hx₂ ; simp_all +decide [ qcObjective ] ;
  exact ⟨ θ₀, hθ₀.1, hU.2 _ ( hV.2 _ _ hx₂ ) ( hx₁ θ₀ |>.1 ) ( hx₁ θ₀ |>.2.1 ) ( hx₁ θ₀ |>.2.2 ) ⟩))

/-
The objective is bounded above on the constraint set.
-/
private lemma qcObjective_bddAbove (μ : T → ℝ) :
    BddAbove (G.qcObjective '' G.qcConstraint μ) := by
  have h_upper_semicontinuous : UpperSemicontinuousOn G.qcObjective (G.qcConstraint μ) := by
    refine' fun x hx => _;
    intro y hy;
    have := G.qcObjective_upperSemicontinuousOn x;
    exact this hx.2.1 |> fun h => h y hy |> fun h => h.filter_mono ( nhdsWithin_mono _ fun x hx => hx.2.1 );
  -- Apply the fact that an upper semicontinuous function on a compact set is bounded above.
  apply UpperSemicontinuousOn.bddAbove_of_isCompact (G.qcConstraint_isCompact μ) h_upper_semicontinuous

/-- Every objective value is at most the closure. -/
private lemma qcObjective_le_qcClosure {μ : T → ℝ} {lp : (T → ℝ) × (T → T → ℝ)}
    (h : lp ∈ G.qcConstraint μ) : G.qcObjective lp ≤ G.qcClosure μ :=
  le_csSup (qcObjective_bddAbove μ) ⟨lp, h, rfl⟩

/-
The supremum defining `v̄^qc` is attained.
-/
private lemma exists_qcObjective_eq_qcClosure {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    ∃ lp ∈ G.qcConstraint μ, G.qcObjective lp = G.qcClosure μ := by
  have h_upper_semicontinuous : UpperSemicontinuousOn G.qcObjective {lp : (T → ℝ) × (T → T → ℝ) | ∀ θ₀, lp.2 θ₀ ∈ simplexOn G.Θ} :=
    qcObjective_upperSemicontinuousOn
  obtain ⟨ lp, hlp ⟩ := UpperSemicontinuousOn.exists_isMaxOn ( qcConstraint_nonempty hμ ) ( qcConstraint_isCompact μ ) ( h_upper_semicontinuous.mono fun lp hlp => hlp.2.1 );
  refine' ⟨ lp, hlp.1, le_antisymm _ _ ⟩;
  · exact qcObjective_le_qcClosure hlp.1;
  · exact csSup_le ( Set.Nonempty.image _ ( qcConstraint_nonempty hμ ) ) ( Set.forall_mem_image.2 fun x hx => hlp.2 hx )

/-
An affinely independent finset of beliefs in `ΔΘ` has at most `|Θ|` points
(Carathéodory in the simplex's affine hull).
-/
private lemma affineIndep_simplex_card_le {t : Finset (T → ℝ)}
    (ht : (t : Set (T → ℝ)) ⊆ simplexOn G.Θ)
    (hai : AffineIndependent ℝ ((↑) : t → (T → ℝ))) : t.card ≤ G.Θ.card := by
  convert hai.card_le_card_of_subset_affineSpan _;
  convert rfl;
  convert Finset.card_image_of_injective _ ( show Function.Injective ( fun θ : T => Pi.single θ ( 1 : ℝ ) ) from ?_ );
  · intro θ₁ θ₂ h; replace h := congr_fun h θ₁; by_cases h' : θ₁ = θ₂ <;> simp_all +decide ;
  · intro x hx;
    have h_affine_comb : x = ∑ θ ∈ G.Θ, x θ • (Pi.single θ 1 : T → ℝ) := by
      ext θ; by_cases hθ : θ ∈ G.Θ <;> simp_all +decide [ Pi.single_apply ] ;
      exact ht hx |>.2.2 θ hθ;
    rw [h_affine_comb];
    refine' ⟨ _, _, _ ⟩;
    exact Pi.single ( Classical.choose ( Finset.card_pos.mp ( show 0 < Finset.card G.Θ from Finset.card_pos.mpr G.Θ_nonempty ) ) ) 1;
    · grind;
    · refine' ⟨ ∑ θ ∈ G.Θ, x θ • ( Pi.single θ 1 - Pi.single ( Classical.choose ( Finset.card_pos.mp ( show 0 < Finset.card G.Θ from Finset.card_pos.mpr G.Θ_nonempty ) ) ) 1 ), _, _ ⟩;
      · refine' Submodule.sum_mem _ fun θ hθ => Submodule.smul_mem _ _ _;
        refine' Submodule.subset_span _;
        exact ⟨ _, Finset.mem_image_of_mem _ hθ, _, Finset.mem_image_of_mem _ ( Classical.choose_spec ( Finset.card_pos.mp ( show 0 < Finset.card G.Θ from Finset.card_pos.mpr G.Θ_nonempty ) ) ), rfl ⟩;
      · ext θ; simp +decide [ Finset.sum_apply, Pi.single_apply ] ; ring;
        split_ifs <;> simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ] at *;
        · have := ht hx; simp +decide [ simplexOn ] at this;
          rw [ Finset.sum_subset ( Finset.subset_univ G.Θ ) ] <;> simp +decide [ this ];
          · exact fun h => False.elim <| h ‹_›;
          · exact this.2.2;
        · exact fun h => False.elim <| h ‹_›;
        · exact absurd ‹θ = Classical.choose _› ( by rintro rfl; exact absurd ( Classical.choose_spec ( Finset.card_pos.mp ( show 0 < Finset.card G.Θ from Finset.card_pos.mpr G.Θ_nonempty ) ) ) ‹_› );
        · tauto

/-
**Carathéodory in the simplex.** A point of `convexHull K` (with `K ⊆ ΔΘ`)
admits a representation `(λ, p) ∈ K_μ` with every `p θ₀ ∈ K` (`θ₀ ∈ Θ`).
-/
private lemma exists_qcConstraint_subset {K : Set (T → ℝ)} (hK : K ⊆ simplexOn G.Θ)
    {μ : T → ℝ} (hμ : μ ∈ convexHull ℝ K) :
    ∃ lp ∈ G.qcConstraint μ, ∀ θ₀ ∈ G.Θ, lp.2 θ₀ ∈ K := by
  obtain ⟨t, ht⟩ : ∃ t : Finset (T → ℝ), (t : Set (T → ℝ)) ⊆ K ∧ AffineIndependent ℝ ((↑) : t → (T → ℝ)) ∧ μ ∈ convexHull ℝ t := by
    rw [ convexHull_eq_union ] at hμ;
    aesop;
  obtain ⟨e, he_inj, he_image⟩ : ∃ e : (T → ℝ) → T, Set.InjOn e t ∧ ∀ x ∈ t, e x ∈ G.Θ := by
    obtain ⟨e, he⟩ : ∃ e : t ↪ G.Θ, True := by
      have h_card : t.card ≤ G.Θ.card := by
        apply affineIndep_simplex_card_le;
        · grind;
        · exact ht.2.1;
      simp +zetaDelta at *;
      have := Fintype.truncEquivFin t;
      obtain ⟨ e ⟩ := this;
      have := Fintype.truncEquivFin G.Θ;
      obtain ⟨ f ⟩ := Trunc.exists_rep this;
      exact ⟨ e.toEmbedding.trans ( Fin.castLEEmb ( by simpa using h_card ) |> fun h => h.trans f.symm.toEmbedding ) ⟩;
    refine' ⟨ fun x => if hx : x ∈ t then e ⟨ x, hx ⟩ else Classical.choose ( Finset.card_pos.mp ( Finset.card_pos.mpr G.Θ_nonempty ) ), _, _ ⟩ <;> simp +decide [ InjOn ];
    · simp +contextual [ e.injective.eq_iff ];
    · grind;
  obtain ⟨w, hw⟩ : ∃ w : (T → ℝ) → ℝ, (∀ x ∈ t, 0 ≤ w x) ∧ (∑ x ∈ t, w x = 1) ∧ μ = ∑ x ∈ t, w x • x := by
    rw [ mem_convexHull_iff_exists_fintype ] at ht;
    obtain ⟨ ι, x, w, z, hw₁, hw₂, hw₃, hw₄ ⟩ := ht.2.2; use fun x => ∑ i ∈ Finset.univ.filter ( fun i => z i = x ), w i; simp_all +decide [ Finset.sum_filter ] ;
    refine' ⟨ fun x hx => Finset.sum_nonneg fun i _ => by split_ifs <;> linarith [ hw₁ i ], _, _ ⟩;
    · rw [ ← hw₂, Finset.sum_comm ] ; aesop;
    · simp +decide [ ← hw₄, Finset.sum_comm, Finset.sum_smul ];
      exact Finset.sum_congr rfl fun i _ => by rw [ if_pos ( hw₃ i ) ] ;
  refine' ⟨ ⟨ fun θ₀ => ∑ x ∈ t.filter ( fun x => e x = θ₀ ), w x, fun θ₀ => if h : ∃ x ∈ t, e x = θ₀ then h.choose else Classical.choose ( show ∃ x ∈ K, True from ⟨ _, ht.1 ( Classical.choose_spec ( Finset.card_pos.mp ( by
                                                                                                                                              exact Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by rintro rfl; simp_all +decide ) ) ) ) ), trivial ⟩ ) ⟩, _, _ ⟩
  generalize_proofs at *;
  · refine' ⟨ _, _, _ ⟩;
    · refine' ⟨ _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_filter ];
      · exact fun a => Finset.sum_nonneg fun x hx => by split_ifs <;> linarith [ hw.1 x hx ] ;
      · rw [ ← hw.2.1, Finset.sum_comm ] ; aesop;
      · exact fun θ hθ => Finset.sum_eq_zero fun x hx => if_neg <| by rintro rfl; exact hθ <| he_image x hx;
    · intro θ₀;
      by_cases h : ∃ x ∈ t, e x = θ₀ <;> simp +decide [ h ];
      · have := h.choose_spec.1; have := h.choose_spec.2; simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] ;
        have := hK ( ht.1 ‹_› ) ; simp_all +decide [ simplexOn ] ;
      · grind +suggestions;
    · intro θ; simp +decide [ hw.2.2, Finset.sum_mul _ _ _ ] ;
      rw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun x hx => ⟨ e x, x ⟩ ) _ _ _ _ <;> simp +decide [ he_inj.eq_iff ];
      · exact fun x hx => ⟨ he_image x hx, hx ⟩;
      · grind;
      · intro x hx; split_ifs with h <;> simp_all +decide [ he_inj.eq_iff hx ] ;
        · have := h.choose_spec.2; have := he_inj ( h.choose_spec.1 ) hx; aesop;
        · exact False.elim ( h ⟨ x, hx, rfl ⟩ );
  · intro θ₀ hθ₀
    by_cases h : ∃ x ∈ t, e x = θ₀
    generalize_proofs at *;
    · grind;
    · grind

/-
The superlevel set of `v̄^qc` is the convex hull of the superlevel set of `v̄`.
-/
lemma qcClosure_superlevel_eq_convexHull (c : ℝ) :
    {μ | μ ∈ simplexOn G.Θ ∧ c ≤ G.qcClosure μ} = convexHull ℝ (G.vbarUpperLevel c) := by
  refine' Set.Subset.antisymm _ _;
  · intro μ hμ;
    obtain ⟨lp, hlp⟩ : ∃ lp ∈ G.qcConstraint μ, G.qcObjective lp = G.qcClosure μ := exists_qcObjective_eq_qcClosure hμ.left;
    -- For each `θ₀ ∈ G.Θ`, `G.qcObjective lp = G.Θ.inf' _ (fun θ₀ => G.vbar (lp.2 θ₀)) ≤ G.vbar (lp.2 θ₀)` (`Finset.inf'_le`), hence `c ≤ G.vbar (lp.2 θ₀)`, and `lp.2 θ₀ ∈ simplexOn G.Θ`, so `lp.2 θ₀ ∈ G.vbarUpperLevel c`.
    have hlp_upperLevel : ∀ θ₀ ∈ G.Θ, lp.2 θ₀ ∈ G.vbarUpperLevel c := by
      intro θ₀ hθ₀
      have hlp_le : c ≤ G.vbar (lp.2 θ₀) := by
        exact le_trans hμ.2 ( hlp.2 ▸ Finset.inf'_le _ hθ₀ )
      exact ⟨hlp.left.right.left θ₀, hlp_le⟩;
    -- Now `μ = G.Θ.centerMass lp.1 (fun θ₀ => lp.2 θ₀)`: since `lp.1 ∈ simplexOn G.Θ` we have `∑ θ₀ ∈ G.Θ, lp.1 θ₀ = 1` (extend to univ using vanishing off `G.Θ`, then `sum_eq_one`), so the centerMass is `∑ θ₀ ∈ G.Θ, lp.1 θ₀ • lp.2 θ₀`, which pointwise equals `∑ θ₀ ∈ G.Θ, lp.1 θ₀ * lp.2 θ₀ θ = μ θ` by the constraint.
    have hlp_centerMass : μ = G.Θ.centerMass lp.1 (fun θ₀ => lp.2 θ₀) := by
      ext θ; simp +decide [ Finset.centerMass, hlp.1.2.2 ] ;
      have := hlp.1.1; simp_all +decide [ simplexOn ] ;
      rw [ show ∑ a ∈ G.Θ, lp.1 a = 1 from by rw [ ← this.2.1, Finset.sum_subset ( Finset.subset_univ G.Θ ) fun x hx₁ hx₂ => this.2.2 x hx₂ ] ] ; norm_num;
    rw [hlp_centerMass];
    apply_rules [ Finset.centerMass_mem_convexHull ];
    · exact fun θ hθ => hlp.1.1.1 θ;
    · have := hlp.1.1;
      convert this.2;
      exact ⟨ fun h => ⟨ by simpa [ Finset.sum_subset ( Finset.subset_univ G.Θ ) fun x _ hx => this.2.2 x hx ] using this.2.1, fun x hx => this.2.2 x hx ⟩, fun h => by simp [ h.1, Finset.sum_subset ( Finset.subset_univ G.Θ ) fun x _ hx => h.2 x hx ] ⟩;
  · intro μ hμ
    have hμ_simplex : μ ∈ simplexOn G.Θ := by
      refine' convexHull_min _ _ hμ;
      · exact fun x hx => hx.1;
      · exact simplexOn_convex G.Θ
    have hμ_qcClosure : c ≤ G.qcClosure μ := by
      obtain ⟨lp, hlp⟩ := exists_qcConstraint_subset (fun ν hν => hν.1) hμ;
      refine' le_trans _ ( qcObjective_le_qcClosure hlp.1 );
      exact Finset.le_inf' _ _ fun θ₀ hθ₀ => hlp.2 θ₀ hθ₀ |>.2
    exact ⟨hμ_simplex, hμ_qcClosure⟩

/-
The superlevel set of `v̄` is compact.
-/
private lemma vbarUpperLevel_isCompact (c : ℝ) : IsCompact (G.vbarUpperLevel c) := by
  convert ( UpperSemicontinuousOn.isCompact_inter_preimage_Ici G.vbar_upperSemicontinuousOn ( CPD.isCompact_simplexOn G.Θ ) c ) using 1

/-- The superlevel set of `v̄` is closed. -/
private lemma vbarUpperLevel_isClosed (c : ℝ) : IsClosed (G.vbarUpperLevel c) :=
  (vbarUpperLevel_isCompact c).isClosed

/-- The superlevel sets of `v̄^qc` are closed. -/
private lemma qcClosure_superlevel_isClosed (c : ℝ) :
    IsClosed {μ | μ ∈ simplexOn G.Θ ∧ c ≤ G.qcClosure μ} := by
  have hPc : IsCompact (((simplexOn G.Θ) ×ˢ (Set.univ.pi fun _ : T => simplexOn G.Θ)) ∩
      ⋂ θ₀ ∈ G.Θ, (fun lp : (T → ℝ) × (T → T → ℝ) => lp.2 θ₀) ⁻¹' (G.vbarUpperLevel c)) := by
    apply IsCompact.inter_right
    · exact (isCompact_simplexOn G.Θ).prod (isCompact_univ_pi fun _ => isCompact_simplexOn G.Θ)
    · exact isClosed_biInter fun θ₀ _ =>
        (vbarUpperLevel_isClosed c).preimage ((continuous_apply θ₀).comp continuous_snd)
  have hΦc : Continuous (fun lp : (T → ℝ) × (T → T → ℝ) => fun θ => ∑ θ₀ ∈ G.Θ, lp.1 θ₀ * lp.2 θ₀ θ) := by
    apply continuous_pi; intro θ
    exact continuous_finset_sum _ fun θ₀ _ =>
      ((continuous_apply θ₀).comp continuous_fst).mul
        ((continuous_apply θ).comp ((continuous_apply θ₀).comp continuous_snd))
  have hset : {μ | μ ∈ simplexOn G.Θ ∧ c ≤ G.qcClosure μ} =
      (fun lp : (T → ℝ) × (T → T → ℝ) => fun θ => ∑ θ₀ ∈ G.Θ, lp.1 θ₀ * lp.2 θ₀ θ) ''
        (((simplexOn G.Θ) ×ˢ (Set.univ.pi fun _ : T => simplexOn G.Θ)) ∩
          ⋂ θ₀ ∈ G.Θ, (fun lp : (T → ℝ) × (T → T → ℝ) => lp.2 θ₀) ⁻¹' (G.vbarUpperLevel c)) := by
    apply Set.Subset.antisymm
    · rintro μ ⟨hμs, hμc⟩
      obtain ⟨lp, hlp, hobj⟩ := exists_qcObjective_eq_qcClosure hμs
      refine ⟨lp, ⟨⟨hlp.1, fun θ₀ _ => hlp.2.1 θ₀⟩, ?_⟩, ?_⟩
      · refine Set.mem_iInter₂.2 fun θ₀ hθ₀ => ⟨hlp.2.1 θ₀, ?_⟩
        have hc : c ≤ G.qcObjective lp := by rw [hobj]; exact hμc
        exact le_trans hc (Finset.inf'_le _ hθ₀)
      · funext θ; exact (hlp.2.2 θ).symm
    · rintro _ ⟨lp, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      have h2' : ∀ θ₀, lp.2 θ₀ ∈ simplexOn G.Θ := fun θ₀ => h2 θ₀ (Set.mem_univ θ₀)
      have hmem : ∀ θ₀ ∈ G.Θ, lp.2 θ₀ ∈ G.vbarUpperLevel c :=
        fun θ₀ hθ₀ => Set.mem_iInter₂.1 h3 θ₀ hθ₀
      have hsum : ∑ θ₀ ∈ G.Θ, lp.1 θ₀ = 1 := by
        rw [← h1.2.1, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => h1.2.2 x hx)]
      have hcon : lp ∈ G.qcConstraint (fun θ => ∑ θ₀ ∈ G.Θ, lp.1 θ₀ * lp.2 θ₀ θ) :=
        ⟨h1, h2', fun θ => rfl⟩
      refine ⟨⟨fun θ => Finset.sum_nonneg fun θ₀ _ => mul_nonneg (h1.1 θ₀) ((h2' θ₀).1 θ), ?_, ?_⟩, ?_⟩
      · rw [Finset.sum_comm]
        calc ∑ θ₀ ∈ G.Θ, ∑ θ, lp.1 θ₀ * lp.2 θ₀ θ
            = ∑ θ₀ ∈ G.Θ, lp.1 θ₀ * (∑ θ, lp.2 θ₀ θ) :=
              Finset.sum_congr rfl fun θ₀ _ => (Finset.mul_sum _ _ _).symm
          _ = ∑ θ₀ ∈ G.Θ, lp.1 θ₀ := by
              refine Finset.sum_congr rfl fun θ₀ _ => ?_
              rw [(h2' θ₀).2.1, mul_one]
          _ = 1 := hsum
      · intro θ hθ
        exact Finset.sum_eq_zero fun θ₀ _ => by rw [(h2' θ₀).2.2 θ hθ, mul_zero]
      · refine le_trans ?_ (qcObjective_le_qcClosure hcon)
        exact Finset.le_inf' _ _ fun θ₀ hθ₀ => (hmem θ₀ hθ₀).2
  rw [hset]
  exact (hPc.image hΦc).isClosed

/-
`v̄^qc` is upper semicontinuous on `ΔΘ` (auxiliary form).
-/
private lemma qcClosure_usc_aux :
    UpperSemicontinuousOn G.qcClosure (simplexOn G.Θ) := by
  intro μ hμ b hb;
  have h_closed : IsClosed {μ | μ ∈ simplexOn G.Θ ∧ b ≤ G.qcClosure μ} :=
    qcClosure_superlevel_isClosed b
  rw [ eventually_nhdsWithin_iff ];
  filter_upwards [ h_closed.isOpen_compl.mem_nhds ( show μ ∉ { μ | μ ∈ simplexOn G.Θ ∧ b ≤ G.qcClosure μ } from fun h => hb.not_ge h.2 ) ] with x hx using by aesop;

/-
Along the segment from `a` to `μ`, with `v̄(a) ≥ w` and `v̲(μ) ≤ w`, some
belief realizes `w ∈ V`.
-/
private lemma exists_mem_V_on_segment {a μ : T → ℝ} (ha : a ∈ simplexOn G.Θ)
    (hμ : μ ∈ simplexOn G.Θ) {w : ℝ} (hwa : w ≤ G.vbar a) (hwμ : G.vlow μ ≤ w) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, w ∈ G.V (fun θ => (1 - t) * a θ + t * μ θ) := by
  -- Define the segment and the sets u and v.
  set seg : ℝ → T → ℝ := fun t θ => (1 - t) * a θ + t * μ θ
  set u := {t | t ∈ Set.Icc 0 1 ∧ w ≤ G.vbar (seg t)}
  set v := {t | t ∈ Set.Icc 0 1 ∧ G.vlow (seg t) ≤ w};
  -- By preconnectedness of [0,1], u and v (closed, covering, each containing an endpoint) intersect.
  have h_inter : u ∩ v ≠ ∅ := by
    have h_closed : IsClosed u ∧ IsClosed v := by
      have h_closed : UpperSemicontinuousOn (fun t => G.vbar (seg t)) (Set.Icc 0 1) ∧ LowerSemicontinuousOn (fun t => G.vlow (seg t)) (Set.Icc 0 1) := by
        have h_cont : UpperSemicontinuousOn G.vbar (simplexOn G.Θ) ∧ LowerSemicontinuousOn G.vlow (simplexOn G.Θ) := by
          exact ⟨ G.vbar_upperSemicontinuousOn, G.vlow_lowerSemicontinuousOn ⟩;
        refine' ⟨ h_cont.1.comp _ _, h_cont.2.comp _ _ ⟩;
        · fun_prop;
        · intro t ht; simp_all +decide [ MapsTo ] ;
          simp +zetaDelta at *;
          exact ⟨ fun θ => by nlinarith [ ha.1 θ, hμ.1 θ ], by simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ha.2.1, hμ.2.1 ], fun θ hθ => by simp +decide [ ha.2.2 θ hθ, hμ.2.2 θ hθ ] ⟩;
        · fun_prop;
        · intro t ht;
          refine' ⟨ _, _, _ ⟩;
          · exact fun θ => add_nonneg ( mul_nonneg ( sub_nonneg.2 ht.2 ) ( ha.1 θ ) ) ( mul_nonneg ht.1 ( hμ.1 θ ) );
          · simp +zetaDelta at *;
            simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ha.2.1, hμ.2.1 ];
          · intro θ hθ; simp +decide [ seg, ha.2.2 θ hθ, hμ.2.2 θ hθ ] ;
      constructor;
      · refine' isClosed_of_closure_subset fun t ht => _;
        rw [ mem_closure_iff_seq_limit ] at ht;
        obtain ⟨ x, hx, hx' ⟩ := ht;
        have := h_closed.1 t ( show t ∈ Set.Icc 0 1 from ?_ );
        · refine' ⟨ _, _ ⟩;
          · exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds hx' fun n => hx n |>.1.1, le_of_tendsto_of_tendsto' hx' tendsto_const_nhds fun n => hx n |>.1.2 ⟩;
          · contrapose! this;
            simp +decide [ SemicontinuousWithinAt ];
            refine' ⟨ w, this, _ ⟩;
            rw [ Filter.frequently_iff_seq_frequently ];
            exact ⟨ x, tendsto_nhdsWithin_iff.mpr ⟨ hx', Filter.Eventually.of_forall fun n => hx n |>.1 ⟩, Filter.Eventually.frequently <| Filter.Eventually.of_forall fun n => hx n |>.2 ⟩;
        · exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds hx' fun n => hx n |>.1.1, le_of_tendsto_of_tendsto' hx' tendsto_const_nhds fun n => hx n |>.1.2 ⟩;
      · have h_closed_v : IsClosed {t ∈ Set.Icc 0 1 | G.vlow (seg t) ≤ w} := by
          have h_closed_v : ∀ c : ℝ, IsClosed {t ∈ Set.Icc 0 1 | G.vlow (seg t) ≤ c} := by
            intro c
            have h_closed_v : ∀ t ∈ Set.Icc 0 1, ∀ ε > 0, ∃ δ > 0, ∀ t' ∈ Set.Icc 0 1, |t' - t| < δ → G.vlow (seg t') > G.vlow (seg t) - ε := by
              intro t ht ε hε;
              have := h_closed.2 t ht ( G.vlow ( seg t ) - ε ) ( by linarith );
              rcases Metric.mem_nhdsWithin_iff.mp this with ⟨ δ, δpos, hδ ⟩;
              exact ⟨ δ, δpos, fun t' ht' ht'' => hδ ⟨ ht'', ht' ⟩ ⟩;
            refine' isClosed_of_closure_subset fun t ht => _;
            rw [ mem_closure_iff_seq_limit ] at ht;
            obtain ⟨ x, hx, hx' ⟩ := ht;
            have h_lim : t ∈ Set.Icc 0 1 := by
              exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds hx' fun n => hx n |>.1.1, le_of_tendsto_of_tendsto' hx' tendsto_const_nhds fun n => hx n |>.1.2 ⟩;
            exact ⟨ h_lim, le_of_forall_pos_le_add fun ε εpos => by obtain ⟨ δ, δpos, H ⟩ := h_closed_v t h_lim ε εpos; rcases Metric.tendsto_atTop.mp hx' δ δpos with ⟨ N, hN ⟩ ; linarith [ H ( x N ) ( hx N |>.1 ) ( hN N le_rfl ), hx N |>.2 ] ⟩
          exact h_closed_v w;
        exact h_closed_v;
    have h_cover : Set.Icc 0 1 ⊆ u ∪ v := by
      intro t ht
      have hseg : seg t ∈ simplexOn G.Θ := by
        refine' ⟨ fun θ => _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_mul, mul_sub ];
        · exact add_nonneg ( mul_nonneg ( sub_nonneg.2 ht.2 ) ( ha.1 θ ) ) ( mul_nonneg ht.1 ( hμ.1 θ ) );
        · simp +zetaDelta at *;
          simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ha.2.1, hμ.2.1 ];
        · grind
      have hV : G.vlow (seg t) ≤ G.vbar (seg t) := by
        grind +suggestions
      by_cases h : w ≤ G.vbar (seg t) <;> simp_all +decide [ Set.subset_def ];
      · exact Or.inl ⟨ ht, h ⟩;
      · exact Or.inr ⟨ ht, by linarith ⟩;
    have h_inter : IsPreconnected (Set.Icc (0 : ℝ) 1) := by
      exact isPreconnected_Icc;
    contrapose! h_inter;
    simp_all +decide [ IsPreconnected ];
    refine' ⟨ uᶜ, h_closed.1.isOpen_compl, vᶜ, h_closed.2.isOpen_compl, _, _, _, _ ⟩ <;> simp_all +decide [ Set.ext_iff ];
    · grind;
    · exact ⟨ 1, by norm_num, fun h => h_inter 1 h <| by aesop ⟩;
    · exact ⟨ 0, by norm_num, fun h => h_inter 0 ⟨ by norm_num, by simpa [ seg ] using hwa ⟩ h ⟩;
    · exact fun ⟨ x, hx₁, hx₂ ⟩ => hx₂.1 ( h_cover hx₁ |> Or.resolve_right <| by aesop );
  obtain ⟨ t, ht ⟩ := Set.nonempty_iff_ne_empty.2 h_inter;
  exact ⟨ t, ht.1.1, G.V_eq_Icc ( show seg t ∈ simplexOn G.Θ from by
                                    simp +zetaDelta at *;
                                    exact ⟨ fun θ => add_nonneg ( mul_nonneg ( sub_nonneg.2 ht.1.1.2 ) ( ha.1 θ ) ) ( mul_nonneg ht.1.1.1 ( hμ.1 θ ) ), by simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ha.2.1, hμ.2.1 ], fun θ hθ => by simp +decide [ ha.2.2 θ hθ, hμ.2.2 θ hθ ] ⟩ ) ▸ Set.mem_Icc.mpr ⟨ ht.2.2, ht.1.2 ⟩ ⟩

/-- **Bayes plausibility.** The prior is the average of induced beliefs over the
evidence, with weights summing to one. -/
private lemma bayes_avg_sum (H : DisclosureGame T Msg) (s : Strategy H) :
    (∀ θ, H.μ0 θ
        = ∑ m ∈ Finset.univ.filter (fun m => m ∈ s.evidence),
            s.onPathProb m * s.belief m θ) ∧
      (∑ m ∈ Finset.univ.filter (fun m => m ∈ s.evidence), s.onPathProb m = 1) := by
  refine' ⟨ fun θ => _, _ ⟩;
  · by_cases hθ : θ ∈ H.Θ <;> simp_all +decide [ Strategy.belief ];
    · rw [ Finset.sum_congr rfl fun x hx => by rw [ mul_div_cancel₀ _ ( ne_of_gt ( s.onPathProb_pos_iff_mem_evidence x |>.2 ( by simpa using hx ) ) ) ] ];
      have h_sum : ∑ m ∈ Finset.univ.filter (fun m => m ∈ s.evidence), s.σ θ m = 1 := by
        have h_key : ∑ m ∈ Finset.univ, s.σ θ m = 1 := by
          exact s.mem θ hθ |>.2.1;
        rw [ ← h_key, ← Finset.sum_subset ( Finset.subset_univ _ ) ];
        simp +contextual [ Strategy.evidence, Strategy.msgSupport ];
        exact fun m hm => le_antisymm ( hm θ hθ ) ( s.mem θ hθ |>.1 m );
      rw [ ← Finset.mul_sum _ _ _, h_sum, mul_one ];
    · have := H.μ0_mem.2.2 θ hθ; aesop;
  · unfold Strategy.onPathProb;
    rw [ Finset.sum_comm ];
    have h_sum : ∀ θ ∈ H.Θ, ∑ m ∈ Finset.univ.filter (fun m => m ∈ s.evidence), s.σ θ m = 1 := by
      intro θ hθ;
      have h_key : ∑ m ∈ Finset.univ, s.σ θ m = 1 := by
        exact s.mem θ hθ |>.2.1;
      rw [ ← h_key, ← Finset.sum_subset ( Finset.subset_univ _ ) ];
      simp +contextual [ Strategy.evidence, Strategy.msgSupport ];
      exact fun m hm => le_antisymm ( hm θ hθ ) ( s.mem θ hθ |>.1 m );
    convert H.priorMeasure_self using 1;
    exact Finset.sum_congr rfl fun x hx => by rw [ ← Finset.mul_sum _ _ _, h_sum x hx, mul_one ] ;

/-
**Realizability core (homothety).** `μ⁰_C` is a convex combination of beliefs
supported on `C`, each paying `w = v̄^qc(μ⁰_C)`.
-/
private lemma condPrior_mem_convexHull_balanced {C : Finset T} (hC : C.Nonempty)
    (hCΘ : C ⊆ G.Θ) :
    G.condPrior C ∈ convexHull ℝ
      {ν | ν ∈ simplexOn G.Θ ∧ G.qcClosure (G.condPrior C) ∈ G.V ν ∧
        simplexSupport ν ⊆ (C : Set T)} := by
  by_cases hμV : G.qcClosure ( G.condPrior C ) ∈ G.V ( G.condPrior C );
  · refine' subset_convexHull ℝ _ _;
    refine' ⟨ _, hμV, _ ⟩;
    · exact G.condPrior_mem_simplex hC hCΘ |> simplexOn_mono hCΘ;
    · exact CPD.simplexSupport_subset ( CPD.DisclosureGame.condPrior_mem_simplex hC hCΘ );
  · obtain ⟨lp, hlp_constraint, hlp_qcObjective⟩ : ∃ lp ∈ G.qcConstraint (G.condPrior C), G.qcObjective lp = G.qcClosure (G.condPrior C) := by
      apply exists_qcObjective_eq_qcClosure;
      exact CPD.DisclosureGame.condPrior_mem_simplex hC hCΘ |> CPD.simplexOn_mono hCΘ;
    obtain ⟨t, ht_mem, ht_V⟩ : ∃ t : T → ℝ, (∀ θ₀ ∈ G.Θ, t θ₀ ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ θ₀ ∈ G.Θ, G.qcClosure (G.condPrior C) ∈ G.V (fun θ => (1 - t θ₀) * lp.2 θ₀ θ + t θ₀ * G.condPrior C θ)) ∧ (∀ θ₀ ∈ G.Θ, t θ₀ ≠ 1) := by
      have ht_exists : ∀ θ₀ ∈ G.Θ, ∃ t ∈ Set.Icc (0 : ℝ) 1, G.qcClosure (G.condPrior C) ∈ G.V (fun θ => (1 - t) * lp.2 θ₀ θ + t * G.condPrior C θ) ∧ t ≠ 1 := by
        intro θ₀ hθ₀
        have hwa : G.qcClosure (G.condPrior C) ≤ G.vbar (lp.2 θ₀) := by
          exact hlp_qcObjective ▸ Finset.inf'_le _ ( Finset.mem_coe.mpr hθ₀ )
        have hwμ : G.vlow (G.condPrior C) ≤ G.qcClosure (G.condPrior C) := by
          have hwμ : G.vbar (G.condPrior C) ≤ G.qcClosure (G.condPrior C) := by
            convert qcObjective_le_qcClosure _;
            rotate_left;
            exact ⟨ G.condPrior C, fun _ => G.condPrior C ⟩;
            · exact qcConstraint_trivial_mem ( DisclosureGame.condPrior_mem_simplex hC hCΘ |> fun h => simplexOn_mono hCΘ h );
            · simp +decide [ DisclosureGame.qcObjective ];
          refine' le_trans _ hwμ;
          apply_rules [ CPD.DisclosureGame.vlow_le, CPD.DisclosureGame.vbar_mem ]; all_goals exact CPD.DisclosureGame.condPrior_mem_simplex hC hCΘ |> CPD.simplexOn_mono hCΘ;
        obtain ⟨ t, ht₁, ht₂ ⟩ := exists_mem_V_on_segment ( show lp.2 θ₀ ∈ simplexOn G.Θ from hlp_constraint.2.1 θ₀ ) ( show G.condPrior C ∈ simplexOn G.Θ from condPrior_mem_simplex hC hCΘ |> simplexOn_mono hCΘ ) hwa hwμ;
        refine' ⟨ t, ht₁, ht₂, _ ⟩;
        rintro rfl; simp_all +decide [ G.V_nonempty ] ;
      choose! t ht₁ ht₂ ht₃ using ht_exists;
      exact ⟨ t, ht₁, ht₂, ht₃ ⟩;
    -- Show that `seg θ₀ ∈ B` for `θ₀ ∈ A`.
    have hseg_mem_B : ∀ θ₀ ∈ G.Θ, 0 < lp.1 θ₀ → (fun θ => (1 - t θ₀) * lp.2 θ₀ θ + t θ₀ * G.condPrior C θ) ∈ {ν | ν ∈ simplexOn G.Θ ∧ G.qcClosure (G.condPrior C) ∈ G.V ν ∧ simplexSupport ν ⊆ (C : Set T)} := by
      intro θ₀ hθ₀ hθ₀_pos
      have h_support : ∀ θ ∉ C, lp.2 θ₀ θ = 0 := by
        intro θ hθ_not_in_C
        have h_sum_zero : ∑ θ₀' ∈ G.Θ, lp.1 θ₀' * lp.2 θ₀' θ = 0 := by
          have h_sum_zero : G.condPrior C θ = 0 := by
            exact G.condPrior_mem_simplex hC hCΘ |>.2.2 θ hθ_not_in_C;
          exact hlp_constraint.2.2 θ ▸ h_sum_zero;
        rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_sum_zero;
        · simpa [ hθ₀_pos.ne' ] using h_sum_zero θ₀ hθ₀;
        · intro i hi;
          have := hlp_constraint.1;
          exact mul_nonneg ( this.1 i ) ( hlp_constraint.2.1 i |>.1 θ );
      refine' ⟨ _, ht_V.1 θ₀ hθ₀, _ ⟩;
      · refine' ⟨ _, _, _ ⟩;
        · intro θ
          have h_nonneg : 0 ≤ lp.2 θ₀ θ ∧ 0 ≤ G.condPrior C θ := by
            have := hlp_constraint.2.1 θ₀; have := G.condPrior_mem_simplex hC hCΘ; simp_all +decide [ simplexOn ] ;
          exact add_nonneg ( mul_nonneg ( sub_nonneg.2 ( ht_mem θ₀ hθ₀ |>.2 ) ) h_nonneg.1 ) ( mul_nonneg ( ht_mem θ₀ hθ₀ |>.1 ) h_nonneg.2 );
        · have := hlp_constraint.2.1 θ₀; simp_all +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ;
          have := G.condPrior_mem_simplex hC hCΘ; simp_all +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_not ] ;
        · grind +suggestions;
      · intro θ hθ; contrapose! hθ; simp_all +decide [ simplexSupport ] ;
        rw [ DisclosureGame.condPrior, if_neg ] <;> simp_all +decide [ Finset.sum_ite ];
    -- Show that `μ = A.centerMass cc seg`.
    have hμ_centerMass : G.condPrior C = Finset.centerMass (G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀)) (fun θ₀ => lp.1 θ₀ / (1 - t θ₀)) (fun θ₀ => fun θ => (1 - t θ₀) * lp.2 θ₀ θ + t θ₀ * G.condPrior C θ) := by
      have hμ_centerMass : ∀ θ, G.condPrior C θ = (∑ θ₀ ∈ G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀), (lp.1 θ₀ / (1 - t θ₀)) * ((1 - t θ₀) * lp.2 θ₀ θ + t θ₀ * G.condPrior C θ)) / (∑ θ₀ ∈ G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀), (lp.1 θ₀ / (1 - t θ₀))) := by
        intro θ
        have h_sum : ∑ θ₀ ∈ G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀), (lp.1 θ₀ / (1 - t θ₀)) * ((1 - t θ₀) * lp.2 θ₀ θ + t θ₀ * G.condPrior C θ) = (∑ θ₀ ∈ G.Θ, lp.1 θ₀ * lp.2 θ₀ θ) + (∑ θ₀ ∈ G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀), (lp.1 θ₀ * t θ₀ / (1 - t θ₀))) * G.condPrior C θ := by
          rw [ Finset.sum_mul _ _ _ ];
          rw [ ← Finset.sum_subset ( Finset.filter_subset ( fun θ₀ => 0 < lp.1 θ₀ ) G.Θ ) ];
          · rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; ring;
            grind;
          · simp +contextual [ hlp_constraint.1.2 ];
            exact fun θ₀ hθ₀ hθ₀' => Or.inl ( le_antisymm hθ₀' ( hlp_constraint.1.1 θ₀ ) );
        have h_sum : ∑ θ₀ ∈ G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀), (lp.1 θ₀ / (1 - t θ₀)) = 1 + ∑ θ₀ ∈ G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀), (lp.1 θ₀ * t θ₀ / (1 - t θ₀)) := by
          have h_sum : ∑ θ₀ ∈ G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀), (lp.1 θ₀ / (1 - t θ₀)) = ∑ θ₀ ∈ G.Θ.filter (fun θ₀ => 0 < lp.1 θ₀), (lp.1 θ₀ + lp.1 θ₀ * t θ₀ / (1 - t θ₀)) := by
            refine' Finset.sum_congr rfl fun θ₀ hθ₀ => _;
            rw [ add_div' ] <;> ring ; exact sub_ne_zero_of_ne <| Ne.symm <| ht_V.2 θ₀ <| Finset.mem_filter.mp hθ₀ |>.1;
          rw [ h_sum, Finset.sum_add_distrib ];
          rw [ Finset.sum_filter_of_ne ];
          · have := hlp_constraint.1; simp_all +decide [ simplexOn ] ;
            rw [ ← this.2.1, Finset.sum_subset ( Finset.subset_univ G.Θ ) ] ; aesop;
          · exact fun x hx hx' => lt_of_le_of_ne ( hlp_constraint.1.1 x ) ( Ne.symm hx' );
        have := hlp_constraint.2.2 θ; simp_all +decide [ Finset.sum_filter ] ;
        rw [ eq_div_iff ] <;> nlinarith [ show 0 ≤ ∑ a ∈ G.Θ, if 0 < lp.1 a then lp.1 a * t a / ( 1 - t a ) else 0 from Finset.sum_nonneg fun _ _ => by split_ifs <;> first | positivity | exact div_nonneg ( mul_nonneg ( le_of_lt ‹_› ) ( ht_mem _ ( by aesop ) |>.1 ) ) ( sub_nonneg.2 ( ht_mem _ ( by aesop ) |>.2 ) ) ];
      ext θ;
      rw [ Finset.centerMass, hμ_centerMass ];
      simp +decide [ div_eq_inv_mul, Finset.mul_sum _ _ _, Finset.sum_mul ];
    rw [hμ_centerMass];
    convert Finset.centerMass_mem_convexHull _ _ _ _ using 1;
    · infer_instance;
    · exact fun θ₀ hθ₀ => div_nonneg ( le_of_lt ( Finset.mem_filter.mp hθ₀ |>.2 ) ) ( sub_nonneg.mpr ( ht_mem θ₀ ( Finset.mem_filter.mp hθ₀ |>.1 ) |>.2 ) );
    · refine' Finset.sum_pos _ _;
      · exact fun θ₀ hθ₀ => div_pos ( Finset.mem_filter.mp hθ₀ |>.2 ) ( sub_pos.mpr ( lt_of_le_of_ne ( ht_mem θ₀ ( Finset.mem_filter.mp hθ₀ |>.1 ) |>.2 ) ( ht_V.2 θ₀ ( Finset.mem_filter.mp hθ₀ |>.1 ) ) ) );
      · have := hlp_constraint.1;
        exact Exists.elim ( show ∃ θ₀, θ₀ ∈ G.Θ ∧ 0 < lp.1 θ₀ from by
                              contrapose! hμV;
                              have := this.2;
                              exact absurd ( this.1 ▸ Finset.sum_nonpos fun x hx => if hx' : x ∈ G.Θ then hμV x hx' else by simp +decide [ this.2 x hx' ] ) ( by norm_num ) ) fun θ₀ hθ₀ => ⟨ θ₀, Finset.mem_filter.mpr ⟨ hθ₀.1, hθ₀.2 ⟩ ⟩;
    · grind

/-- **Realizability.** With `w = v̄^qc(μ⁰_C)`, the conditional prior `μ⁰_C` is a
convex combination of at most `|Θ|` beliefs supported on `C`, each paying `w`. -/
private lemma exists_balanced_splitting {C : Finset T} (hC : C.Nonempty)
    (hCΘ : C ⊆ G.Θ) :
    ∃ (lp : (T → ℝ) × (T → T → ℝ)), lp ∈ G.qcConstraint (G.condPrior C) ∧
      (∀ θ₀ ∈ G.Θ, simplexSupport (lp.2 θ₀) ⊆ (C : Set T)) ∧
      (∀ θ₀ ∈ G.Θ, G.qcClosure (G.condPrior C) ∈ G.V (lp.2 θ₀)) := by
  have hBsub : {ν | ν ∈ simplexOn G.Θ ∧ G.qcClosure (G.condPrior C) ∈ G.V ν ∧
        simplexSupport ν ⊆ (C : Set T)} ⊆ simplexOn G.Θ := fun ν hν => hν.1
  obtain ⟨lp, hlp, hlpB⟩ :=
    exists_qcConstraint_subset hBsub (condPrior_mem_convexHull_balanced hC hCΘ)
  exact ⟨lp, hlp, fun θ₀ hθ₀ => (hlpB θ₀ hθ₀).2.2, fun θ₀ hθ₀ => (hlpB θ₀ hθ₀).2.1⟩

/-
The conditional prior of a coalition's cell is a convex combination of
beliefs each with `v̄ ≥ w`.
-/
private lemma condPrior_coalition_mem_convexHull {R : Finset T} (hne : R.Nonempty)
    (hsub : R ⊆ G.Θ) (K : Coalition (G.restrict R hne hsub)) :
    G.condPrior K.C ∈ convexHull ℝ (G.vbarUpperLevel K.w) := by
  -- Let `g := (G.restrict R hne hsub).restrict K.C K.C_nonempty K.C_subset` and `s := K.σ : Strategy g`, `E := Finset.univ.filter (fun m => m ∈ s.evidence)`.
  set g : DisclosureGame T Msg := (G.restrict R hne hsub).restrict K.C K.C_nonempty K.C_subset
  set s : Strategy g := K.σ
  set E : Finset Msg := Finset.univ.filter (fun m => m ∈ s.evidence);
  obtain ⟨hbayes, hsum1⟩ := bayes_avg_sum g s;
  -- Key rewrite: `g.μ0 = G.condPrior K.C`.
  have hgμ0 : g.μ0 = G.condPrior K.C := by
    grind +suggestions;
  -- Belief membership `hbel : ∀ m ∈ E, s.belief m ∈ G.vbarUpperLevel K.w`.
  have hbel : ∀ m ∈ E, s.belief m ∈ G.vbarUpperLevel K.w := by
    intro m hm
    have hbel_mem : s.belief m ∈ simplexOn g.Θ := by
      grind +suggestions
    have hbel_subset : g.Θ = K.C := by
      rfl
    have hbel_mem_G : s.belief m ∈ simplexOn G.Θ := by
      exact simplexOn_mono ( hbel_subset.symm ▸ K.C_subset.trans hsub ) hbel_mem
    have hbel_vbar : K.w ≤ G.vbar (s.belief m) := by
      have hbel_vbar : K.w ∈ G.V (s.coalitionBelief m) := by
        convert K.payoff m ( Finset.mem_filter.mp hm |>.2 ) using 1;
      have hbel_vbar : s.coalitionBelief m = s.belief m := by
        apply zeroExt_eq_self; assumption;
      have hbel_vbar : ∀ μ ∈ G.V (s.belief m), μ ≤ G.vbar (s.belief m) := by
        exact fun μ hμ => le_csSup ( G.V_isCompact ( s.belief m ) hbel_mem_G |> IsCompact.bddAbove ) hμ;
      grind
    exact ⟨hbel_mem_G, hbel_vbar⟩;
  -- Nonnegativity `hnn : ∀ m ∈ E, 0 ≤ s.onPathProb m`.
  have hnn : ∀ m ∈ E, 0 ≤ s.onPathProb m := by
    intro m hm; exact (by
    exact Finset.sum_nonneg fun _ _ => mul_nonneg ( g.μ0_mem.1 _ ) ( s.mem _ ( by aesop ) |>.1 _ ));
  convert Finset.centerMass_mem_convexHull E hnn ( by rw [ hsum1 ] ; norm_num ) hbel using 1;
  rw [ Finset.centerMass_eq_of_sum_1 ] <;> aesop

/-! ## Closure-game facts -/

/-- `v_min ≤ v̄^qc(μ)` (used to build the closure game). -/
lemma vMin_le_qcClosure {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.vMin ≤ G.qcClosure μ := by
  have htriv := qcConstraint_trivial_mem hμ
  have hobj : G.qcObjective ((μ, fun _ => μ) : (T → ℝ) × (T → T → ℝ)) = G.vbar μ := by
    simp [qcObjective, Finset.inf'_const]
  calc G.vMin ≤ G.vlow μ := vMin_le_vlow hμ
    _ ≤ G.vbar μ := G.vlow_le hμ (vbar_mem hμ)
    _ = G.qcObjective ((μ, fun _ => μ) : (T → ℝ) × (T → T → ℝ)) := hobj.symm
    _ ≤ G.qcClosure μ := qcObjective_le_qcClosure htriv

/-
The closure-game payoff `V^qc(μ) = [v_min, v̄^qc(μ)]` is upper hemicontinuous.
-/
lemma closureGame_V_uhc :
    UpperHemicontinuousOn (fun μ => Set.Icc G.vMin (G.qcClosure μ)) (simplexOn G.Θ) := by
  intro μ hμ U hU hU';
  -- By upper semicontinuity of `G.qcClosure` at `μ`, there exists `W ∈ 𝓝[simplexOn G.Θ] μ` such that `∀ μ' ∈ W, G.qcClosure μ' < G.qcClosure μ + δ`.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, Metric.thickening δ (Set.Icc G.vMin (G.qcClosure μ)) ⊆ U := by
    apply_rules [ IsCompact.exists_thickening_subset_open ];
    exact CompactIccSpace.isCompact_Icc;
  have := G.qcClosure_usc_aux μ hμ;
  rcases Filter.eventually_iff_exists_mem.mp ( this ( G.qcClosure μ + δ ) ( by linarith ) ) with ⟨ W, hW₁, hW₂ ⟩;
  refine' ⟨ W, hW₁, fun μ' hμ' => _ ⟩;
  intro y hy;
  by_cases hy' : y ≤ G.qcClosure μ;
  · exact hU' ⟨ hy.1, hy' ⟩;
  · refine' hδ _;
    rw [ Metric.mem_thickening_iff ];
    exact ⟨ G.qcClosure μ, ⟨ by linarith [ hy.1, G.vMin_le_qcClosure hμ ], by linarith [ hy.1, G.vMin_le_qcClosure hμ ] ⟩, abs_lt.mpr ⟨ by linarith [ hy.2, hW₂ μ' hμ' ], by linarith [ hy.2, hW₂ μ' hμ' ] ⟩ ⟩

/-! ## The closure game (Lemma F.1) -/

variable (G) in
/-- **Lemma F.1** (closure game): `G^qc := (Θ, 𝓜, M, μ⁰, V^qc)` with
`V^qc(μ) := [v_min, v̄^qc(μ)]` is a disclosure game. -/
noncomputable def closureGame : DisclosureGame T Msg where
  Θ := G.Θ
  𝓜 := G.𝓜
  Θ_nonempty := G.Θ_nonempty
  𝓜_nonempty := G.𝓜_nonempty
  M := G.M
  M_subset := G.M_subset
  M_nonempty := G.M_nonempty
  cover := G.cover
  μ0 := G.μ0
  μ0_mem := G.μ0_mem
  μ0_fullSupport := G.μ0_fullSupport
  V := fun μ => Set.Icc G.vMin (G.qcClosure μ)
  V_nonempty := fun μ hμ => Set.nonempty_Icc.2 (vMin_le_qcClosure hμ)
  V_isCompact := fun μ _ => isCompact_Icc
  V_ordConnected := fun μ _ => ordConnected_Icc
  V_uhc := closureGame_V_uhc

@[simp] lemma closureGame_Θ : (G.closureGame).Θ = G.Θ := rfl
@[simp] lemma closureGame_𝓜 : (G.closureGame).𝓜 = G.𝓜 := rfl
@[simp] lemma closureGame_M : (G.closureGame).M = G.M := rfl
@[simp] lemma closureGame_μ0 : (G.closureGame).μ0 = G.μ0 := rfl
@[simp] lemma closureGame_V (μ : T → ℝ) :
    (G.closureGame).V μ = Set.Icc G.vMin (G.qcClosure μ) := rfl
@[simp] lemma closureGame_canSend (m : Msg) :
    (G.closureGame).canSend m = G.canSend m := rfl

/-! ## Closure properties of `v̄^qc` (Lemma F.1) -/

/-- **Lemma F.1** (closure properties): `v̄^qc` is upper semicontinuous on
`ΔΘ`. -/
lemma qcClosure_upperSemicontinuousOn :
    UpperSemicontinuousOn G.qcClosure (simplexOn G.Θ) :=
  qcClosure_usc_aux

/-
**Lemma F.1** (closure properties): `v̄^qc` is quasiconcave.
-/
lemma qcClosure_quasiconcave {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ)
    {μ' : T → ℝ} (hμ' : μ' ∈ simplexOn G.Θ) {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    min (G.qcClosure μ) (G.qcClosure μ')
      ≤ G.qcClosure (fun θ => l * μ θ + (1 - l) * μ' θ) := by
  set c := min (G.qcClosure μ) (G.qcClosure μ');
  -- By definition of $c$, we know that $μ$ and $μ'$ are in the set ${ν | ν ∈ simplexOn G.Θ ∧ c ≤ G.qcClosure ν}$.
  have hμc : μ ∈ {ν | ν ∈ simplexOn G.Θ ∧ c ≤ G.qcClosure ν} := by
    exact ⟨ hμ, min_le_left _ _ ⟩
  have hμ'c : μ' ∈ {ν | ν ∈ simplexOn G.Θ ∧ c ≤ G.qcClosure ν} := by
    exact ⟨ hμ', min_le_right _ _ ⟩;
  -- By definition of $c$, we know that the set ${ν | ν ∈ simplexOn G.Θ ∧ c ≤ G.qcClosure ν}$ is convex.
  have h_convex : Convex ℝ {ν | ν ∈ simplexOn G.Θ ∧ c ≤ G.qcClosure ν} := by
    rw [ qcClosure_superlevel_eq_convexHull ];
    exact convex_convexHull ℝ _;
  have := h_convex hμc hμ'c hl.1.le ( sub_nonneg.2 hl.2.le ) ( by linarith [ hl.1, hl.2 ] ) ; aesop;

/-- **Lemma F.1** (closure properties): superlevel identity,
`{v̄^qc ≥ y} = conv{v̄ ≥ y}`. -/
lemma qcClosure_upperLevel (y : ℝ) :
    {μ | μ ∈ simplexOn G.Θ ∧ y ≤ G.qcClosure μ}
      = convexHull ℝ (G.vbarUpperLevel y) :=
  qcClosure_superlevel_eq_convexHull y

/-
**Lemma F.1** (closure game): the upper envelope of `G^qc` is `v̄^qc`.
-/
lemma closureGame_vbar {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    (G.closureGame).vbar μ = G.qcClosure μ := by
  simp +decide only [vbar, closureGame_V, csSup_Icc (vMin_le_qcClosure hμ)]

/-
**Lemma F.1** (closure game): `G^qc` is quasiconcave.
-/
lemma closureGame_QC : (G.closureGame).QC := by
  intro μ hμ μ' hμ' l hl;
  rw [ DisclosureGame.closureGame_vbar, DisclosureGame.closureGame_vbar, DisclosureGame.closureGame_vbar ];
  · apply qcClosure_quasiconcave;
    · exact hμ;
    · exact hμ';
    · exact hl;
  · convert simplexOn_convex G.Θ hμ hμ' hl.1.le ( sub_nonneg.2 hl.2.le ) ( by linarith [ hl.1, hl.2 ] ) using 1;
  · exact hμ';
  · exact hμ

/-
**Lemma F.1** (closure game): M-C of `G` gives M-C of `G^qc`.
-/
lemma closureGame_MC (hMC : G.MC) : (G.closureGame).MC := by
  intro m hm m' hm';
  obtain ⟨ m'', hm'', hm''_eq ⟩ := hMC m hm m' hm';
  exact ⟨ m'', hm'', hm''_eq ⟩

/-! ## The qc-bound and ct-realization (Lemmas F.2, F.3) -/

/-- **Lemma F.2** (qc-bound): for every non-empty `R ⊆ Θ` and every coalition
`(C,σ,w)` of `G|_R`, `w ≤ v̄^qc(μ⁰_C)` (the closure of `G`'s upper envelope,
`μ⁰_C` the conditional prior of `μ⁰`). -/
lemma coalition_w_le_qcClosure {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (K : Coalition (G.restrict R hne hsub)) :
    K.w ≤ G.qcClosure (G.condPrior K.C) := by
  have hmem : G.condPrior K.C ∈ {μ | μ ∈ simplexOn G.Θ ∧ K.w ≤ G.qcClosure μ} := by
    rw [qcClosure_upperLevel]
    exact condPrior_coalition_mem_convexHull hne hsub K
  exact hmem.2

/-
**(M-CT) message assignment.** Under M-CT, the `n := |Θ|` types can be
injectively assigned cheap-talk copies of `m̄` (same preimage as `m̄`).
-/
private lemma exists_ct_msg (hMCT : G.MCT) {mbar : Msg} (hmbar : mbar ∈ G.𝓜) :
    ∃ msg : T → Msg, Set.InjOn msg (G.Θ : Set T) ∧ (∀ θ₀ ∈ G.Θ, msg θ₀ ∈ G.𝓜) ∧
      (∀ θ₀ ∈ G.Θ, G.canSend (msg θ₀) = G.canSend mbar) := by
  obtain ⟨e, he⟩ : ∃ e : G.Θ ↪ {m' : Msg | m' ∈ G.𝓜 ∧ G.canSend m' = G.canSend mbar}, True := by
    refine' ⟨ _, trivial ⟩;
    refine' Function.Embedding.nonempty_of_card_le _ |> Classical.choice;
    have := hMCT mbar hmbar; simp_all +decide [ Fintype.card_subtype ] ;
    convert this using 2 ; aesop;
  refine' ⟨ fun θ₀ => if h : θ₀ ∈ G.Θ then ( e ⟨ θ₀, h ⟩ : Msg ) else mbar, _, _, _ ⟩ <;> simp_all +decide [ InjOn ];
  · exact fun x₁ hx₁ x₂ hx₂ h => by simpa [ Subtype.ext_iff ] using e.injective ( Subtype.ext h ) ;
  · exact fun θ₀ hθ₀ => e ⟨ θ₀, hθ₀ ⟩ |>.2.1;
  · exact fun θ₀ hθ₀ => e ⟨ θ₀, hθ₀ ⟩ |>.2.2

/-
The cheap-talk splitting strategy on `G|_R|_{P(m̄)∩R}`.
-/
private lemma ct_sigma_strategy {Θt : Finset T} (hne : Θt.Nonempty) (hsub : Θt ⊆ G.Θ)
    {mbar : Msg} (hCne : (G.canSend mbar ∩ Θt).Nonempty)
    {lp : (T → ℝ) × (T → T → ℝ)}
    (hlpC : lp ∈ G.qcConstraint (G.condPrior (G.canSend mbar ∩ Θt)))
    (hlpsupp : ∀ θ₀ ∈ G.Θ, simplexSupport (lp.2 θ₀) ⊆ (↑(G.canSend mbar ∩ Θt) : Set T))
    {msg : T → Msg}
    (hmsgP : ∀ θ₀ ∈ G.Θ, G.canSend (msg θ₀) = G.canSend mbar) :
    ∃ σ : Strategy ((G.restrict Θt hne hsub).restrict (G.canSend mbar ∩ Θt) hCne
        Finset.inter_subset_right),
      ∀ θ m, σ.σ θ m =
        (∑ θ₀ ∈ Finset.univ.filter (fun θ₀ => msg θ₀ = m), lp.1 θ₀ * lp.2 θ₀ θ)
          / G.condPrior (G.canSend mbar ∩ Θt) θ := by
  refine' ⟨ ⟨ fun θ m => ( ∑ θ₀ ∈ Finset.univ.filter ( fun θ₀ => msg θ₀ = m ), lp.1 θ₀ * lp.2 θ₀ θ ) / G.condPrior ( G.canSend mbar ∩ Θt ) θ, _ ⟩, fun θ m => rfl ⟩;
  intro θ hθ;
  refine' ⟨ _, _, _ ⟩;
  · intro m
    have h_pos : 0 < G.condPrior (G.canSend mbar ∩ Θt) θ := by
      apply condPrior_pos;
      · exact hCne;
      · exact Finset.inter_subset_right.trans hsub;
      · exact hθ;
    refine' div_nonneg ( Finset.sum_nonneg fun θ₀ hθ₀ => mul_nonneg _ _ ) h_pos.le;
    · exact hlpC.1.1 θ₀;
    · exact hlpC.2.1 θ₀ |>.1 θ;
  · have h_sum : ∑ m, ∑ θ₀ ∈ Finset.univ.filter (fun θ₀ => msg θ₀ = m), lp.1 θ₀ * lp.2 θ₀ θ = G.condPrior (G.canSend mbar ∩ Θt) θ := by
      have h_sum : ∑ m, ∑ θ₀ ∈ Finset.univ.filter (fun θ₀ => msg θ₀ = m), lp.1 θ₀ * lp.2 θ₀ θ = ∑ θ₀ ∈ Finset.univ, lp.1 θ₀ * lp.2 θ₀ θ :=
        Finset.sum_fiberwise Finset.univ msg (fun θ₀ => lp.1 θ₀ * lp.2 θ₀ θ)
      have := hlpC.2.2 θ;
      convert this.symm using 1;
      convert h_sum using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ G.Θ ) ];
      exact fun x _ hx => by rw [ hlpC.1.2.2 x hx, MulZeroClass.zero_mul ] ;
    have h_denom_pos : 0 < G.condPrior (G.canSend mbar ∩ Θt) θ := by
      apply condPrior_pos;
      · exact hCne;
      · exact Finset.inter_subset_right.trans hsub;
      · exact hθ;
    rw [ ← Finset.sum_div, h_sum, div_self h_denom_pos.ne' ];
  · intro m hm;
    simp_all +decide [ DisclosureGame.restrict, DisclosureGame.canSend ];
    refine' Or.inl ( Finset.sum_eq_zero fun θ₀ hθ₀ => _ );
    by_cases hθ₀G : θ₀ ∈ G.Θ <;> simp_all +decide [ Finset.ext_iff, Set.subset_def ];
    · contrapose! hm; specialize hmsgP θ₀ hθ₀G θ; simp_all +decide [ DisclosureGame.preimageFull ] ;
      simp_all +decide [ preimage ];
      grind;
    · exact Or.inl ( hlpC.1.2.2 θ₀ hθ₀G )

/-
The cheap-talk strategy induces belief `lp.2 θ₀` at the on-path copy `msg θ₀`.
-/
private lemma ct_coalitionBelief {Θt : Finset T} (hne : Θt.Nonempty) (hsub : Θt ⊆ G.Θ)
    {mbar : Msg} (hCne : (G.canSend mbar ∩ Θt).Nonempty)
    {lp : (T → ℝ) × (T → T → ℝ)}
    (hlpC : lp ∈ G.qcConstraint (G.condPrior (G.canSend mbar ∩ Θt)))
    (hlpsupp : ∀ θ₀ ∈ G.Θ, simplexSupport (lp.2 θ₀) ⊆ (↑(G.canSend mbar ∩ Θt) : Set T))
    {msg : T → Msg} (hmsginj : Set.InjOn msg (G.Θ : Set T))
    {σ : Strategy ((G.restrict Θt hne hsub).restrict (G.canSend mbar ∩ Θt) hCne
        Finset.inter_subset_right)}
    (hσeq : ∀ θ m, σ.σ θ m =
        (∑ θ₀ ∈ Finset.univ.filter (fun θ₀ => msg θ₀ = m), lp.1 θ₀ * lp.2 θ₀ θ)
          / G.condPrior (G.canSend mbar ∩ Θt) θ)
    {θ₀ : T} (hθ₀ : θ₀ ∈ G.Θ) (hpos : 0 < lp.1 θ₀) :
    σ.coalitionBelief (msg θ₀) = lp.2 θ₀ := by
  have h_sigma_eq : ∀ θ, σ.σ θ (msg θ₀) = (lp.1 θ₀ * lp.2 θ₀ θ) / G.condPrior (G.canSend mbar ∩ Θt) θ := by
    intro θ; rw [ hσeq ] ; rw [ Finset.sum_eq_single θ₀ ] <;> simp +contextual [ hmsginj.eq_iff ] ;
    intro b hb hb'; contrapose! hb'; have := hmsginj ( show b ∈ G.Θ from by
                                                        exact Classical.not_not.1 fun h => hb'.1 <| by simpa [ h ] using hlpC.1.2.2 b h; ) ( show θ₀ ∈ G.Θ from hθ₀ ) ; aesop;
  have h_onPathProb : σ.onPathProb (msg θ₀) = lp.1 θ₀ := by
    have h_onPathProb : σ.onPathProb (msg θ₀) = ∑ θ ∈ (G.canSend mbar ∩ Θt), G.condPrior (G.canSend mbar ∩ Θt) θ * σ.σ θ (msg θ₀) := by
      convert rfl;
      unfold Strategy.onPathProb;
      convert rfl;
      grind +suggestions;
    rw [ h_onPathProb, Finset.sum_congr rfl fun x hx => by rw [ h_sigma_eq x, mul_div_cancel₀ _ ( ne_of_gt ( condPrior_pos hCne ( Finset.inter_subset_left.trans ( Finset.filter_subset _ _ ) ) hx ) ) ] ];
    rw [ ← Finset.mul_sum _ _ _, show ∑ x ∈ G.canSend mbar ∩ Θt, lp.2 θ₀ x = 1 from ?_ ];
    · ring;
    · have := hlpC.2.1 θ₀;
      rw [ ← this.2.1, ← Finset.sum_subset ( Finset.subset_univ ( G.canSend mbar ∩ Θt ) ) ];
      exact fun x _ hx => le_antisymm ( le_of_not_gt fun hx' => hx <| hlpsupp θ₀ hθ₀ <| by simpa using hx' ) ( this.1 x );
  ext θ;
  by_cases hθ : θ ∈ G.canSend mbar ∩ Θt <;> simp_all +decide [ Strategy.coalitionBelief ];
  · unfold Strategy.belief zeroExt; simp +decide [ *, Finset.sum_ite ] ;
    rw [ mul_div, div_eq_iff ] <;> try linarith;
    rw [ mul_comm, mul_div_assoc ];
    rw [ mul_div, div_eq_iff ];
    · simp +decide [ mul_assoc, mul_comm, mul_left_comm,DisclosureGame.condPrior];
      simp +decide [ hθ, DisclosureGame.priorMeasure ];
      simp +decide [ div_div, Finset.sum_div _ _ _, DisclosureGame.condPrior ];
      simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_not, Finset.sum_div _ _ _, DisclosureGame.priorMeasure ];
      rw [ ← Finset.sum_div _ _ _, mul_div_cancel₀ _ ( ne_of_gt ( Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( hsub hx ) ) hne ) ) ] ; simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_not, Finset.sum_div _ _ _, hθ ];
    · apply ne_of_gt; exact (by
      grind +suggestions);
  · unfold zeroExt; simp +decide [ hθ ] ;
    split_ifs <;> simp_all +decide [ simplexSupport ];
    exact Eq.symm ( le_antisymm ( le_of_not_gt fun h => hθ ( hlpsupp θ₀ hθ₀ |>.1 h ) ( hlpsupp θ₀ hθ₀ |>.2 h ) ) ( by have := hlpC.2.1 θ₀; exact this.1 θ ) )

/-
**Lemma F.3** (ct-realization): under M-CT, for non-empty `R ⊆ Θ` and
`m̄ ∈ 𝓜_R`, the game `G|_R` has a coalition with type set `P(m̄) ∩ R` and
payoff `v̄^qc(μ⁰_{P(m̄)∩R})`.
-/
theorem ct_realization (hMCT : G.MCT) {Θt : Finset T} (hne : Θt.Nonempty)
    (hsub : Θt ⊆ G.Θ) {mbar : Msg} (hmbar : mbar ∈ G.restrictMsgSpace Θt) :
    ∃ K : Coalition (G.restrict Θt hne hsub),
      K.C = G.canSend mbar ∩ Θt ∧
      K.w = G.qcClosure (G.condPrior (G.canSend mbar ∩ Θt)) := by
  obtain ⟨ lp, hlpC, hlpsupp, hlpV ⟩ := exists_balanced_splitting ( show ( G.canSend mbar ∩ Θt ).Nonempty from by
                                                                      simp_all +decide [ Finset.ext_iff, DisclosureGame.restrictMsgSpace ];
                                                                      obtain ⟨ a, ha, ham ⟩ := hmbar; use a; simp_all +decide [ DisclosureGame.canSend ] ;
                                                                      exact Finset.mem_filter.mpr ⟨ hsub ha, by aesop ⟩ ) ( Finset.inter_subset_left.trans ( Finset.filter_subset _ _ ) )
  generalize_proofs at *;
  obtain ⟨ msg, hmsginj, hmsg𝓜, hmsgP ⟩ := exists_ct_msg hMCT ( G.restrictMsgSpace_subset hsub hmbar );
  obtain ⟨σ, hσeq⟩ := ct_sigma_strategy hne hsub (by
  contrapose! hmbar; simp_all +decide [ DisclosureGame.restrictMsgSpace ] ;
  intro x hx; replace hmbar := Finset.ext_iff.mp hmbar x; simp_all +decide [ DisclosureGame.canSend ] ;
  exact fun h => hmbar <| by rw [ DisclosureGame.preimageFull ] ; exact Finset.mem_filter.mpr ⟨ hsub hx, by aesop ⟩ ;) hlpC hlpsupp hmsgP
  generalize_proofs at *;
  refine' ⟨ ⟨ _, _, _, σ, _, _, _ ⟩, rfl, rfl ⟩ <;> simp_all +decide [ DisclosureGame.preimageSetFull ];
  · intro θ hθ; simp_all +decide [ DisclosureGame.preimageSet ] ;
    obtain ⟨ m, hm ⟩ := hθ.2; simp_all +decide [ Strategy.evidence ] ;
    obtain ⟨ i, hi, hm ⟩ := hm.2; simp_all +decide [ Strategy.msgSupport ] ;
    obtain ⟨ θ₀, hθ₀, hθ₀' ⟩ := Finset.exists_ne_zero_of_sum_ne_zero ( show ( ∑ θ₀ with msg θ₀ = m, lp.1 θ₀ * lp.2 θ₀ i ) ≠ 0 from fun h => by simp +decide [ h ] at hm ) ; simp_all +decide [ DisclosureGame.canSend ] ;
    have := hmsgP θ₀ ( by
      exact Classical.not_not.1 fun h => hθ₀'.1 <| hlpC.1.2.2 _ h ) ; simp_all +decide [ DisclosureGame.preimageFull ] ;
    simp_all +decide [ preimage ];
    exact ⟨ hsub hθ.1, by rw [ Finset.ext_iff ] at this; specialize this θ; aesop ⟩;
  · intro m hm
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ G.Θ, 0 < lp.1 θ₀ ∧ msg θ₀ = m := by
      obtain ⟨θ, hθ⟩ : ∃ θ ∈ (G.restrict Θt hne hsub).restrict (G.canSend mbar ∩ Θt) ‹_› ‹_› |>.Θ, 0 < σ.σ θ m := by
        contrapose! hm; simp_all +decide [ Strategy.evidence ] ;
        intro θ hθ₁ hθ₂; specialize hm θ hθ₁ hθ₂; simp_all +decide [ Strategy.msgSupport ] ;
      generalize_proofs at *;
      contrapose! hθ; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_nonneg ] ;
      intro hθ₁ hθ₂; rw [ Finset.sum_eq_zero ] <;> simp_all +decide [ Finset.sum_ite ] ;
      intro θ₀ hθ₀; specialize hθ θ₀; by_cases h : 0 < lp.1 θ₀ <;> simp_all +decide ;
      · exact absurd ( hlpC.1.2.2 θ₀ hθ ) ( by linarith );
      · exact Or.inl ( le_antisymm h ( hlpC.1.1 θ₀ ) )
    generalize_proofs at *;
    convert hlpV θ₀ hθ₀.1 using 1;
    rw [ ← hθ₀.2.2, ct_coalitionBelief ];
    grobner;
    · grind +splitImp;
    · exact hmsginj;
    · exact hσeq;
    · exact hθ₀.1;
    · exact hθ₀.2.1

end DisclosureGame

end CPD
