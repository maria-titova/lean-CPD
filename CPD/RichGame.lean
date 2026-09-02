import CPD.Simplex

/-!
# Rich disclosure games and the tent (§7)

A lightweight framework: rich disclosure games do **not** use the
`DisclosureGame` message machinery of the rest of the library. A rich
disclosure game fixes `(Θ, μ⁰, v̄)` — **Definition 23** — with coalitions
given by nonzero sub-measures of the current residual, an induced belief, and
a payoff `v̄` of that belief; a coalition-optimal partition (**Definition
24**) greedily exhausts the prior. Under unique face maximizers and the tent
assumption, the induced tent function (**Definition 26**) is characterized on
`ΔΘ`.

Results formalized: **Lemma I.1** (attainability: any belief on the current face
is induced by a sub-measure that retires a type) → `attainability`;
**Proposition 7** (existence of a coalition-optimal partition, reached
greedily in at most `|Θ|` steps, and uniqueness under unique face maximizers)
→ `cutecase_existence`, `cutecase_unique`; **Definition 25** (nested chain,
simplex decomposition) → `NestedChain`, `SimplexDecomp`,
`simplexDecomp_exists`; **Definition 26** and **Proposition 9** (the tent
`v^tent`: value formula at face maximizers, affine on chains, uniqueness) →
`tent`, `tent_eq_at_faceMax`, `tent_affine_on_chain`, `tent_unique`.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T : Type*} [Fintype T]

/-- **Definition 23** (rich disclosure game). A *rich disclosure game*: a
finite type space `Θ`, a full-support prior `μ⁰ ∈ ΔΘ`, and an
upper-semicontinuous value `v̄`. -/
structure RichGame (T : Type*) [Fintype T] where
  /-- The finite type space. -/
  Θ : Finset T
  /-- `Θ` is non-empty. -/
  Θ_nonempty : Θ.Nonempty
  /-- The prior. -/
  μ0 : T → ℝ
  /-- `μ⁰ ∈ ΔΘ`. -/
  μ0_mem : μ0 ∈ simplexOn Θ
  /-- `μ⁰` has full support on `Θ`. -/
  μ0_fullSupport : ∀ θ ∈ Θ, 0 < μ0 θ
  /-- The value function `v̄ : ΔΘ → ℝ`. -/
  vbar : (T → ℝ) → ℝ
  /-- `v̄` is upper semicontinuous on `ΔΘ`. -/
  vbar_usc : UpperSemicontinuousOn vbar (simplexOn Θ)

namespace RichGame

variable {Γ : RichGame T}

/-! ## Sub-measures, coalitions, `Δ_ν` -/

/-- **Definition 23** (sub-measure). `η` is a *sub-measure* of `ν`:
`0 ≤ η ≤ ν` pointwise. -/
def SubMeasure (η ν : T → ℝ) : Prop := (∀ θ, 0 ≤ η θ) ∧ ∀ θ, η θ ≤ ν θ

/-- The mass `η(Θ) = ∑_θ η(θ)`. -/
noncomputable def mass (η : T → ℝ) : ℝ := ∑ θ, η θ

/-- The induced belief `η̂ := η / η(Θ)`. -/
noncomputable def normalize (η : T → ℝ) : T → ℝ := fun θ => η θ / mass η

/-- **Definition 23** (coalition). A *coalition* of the restricted rich game
`Γ_ν`: a nonzero sub-measure `η ≤ ν`; it induces the belief `η̂` and the
payoff `v̄(η̂)`. -/
def IsCoalition (ν η : T → ℝ) : Prop := SubMeasure η ν ∧ η ≠ 0

variable (Γ) in
/-- `Δ_ν`: the beliefs in `ΔΘ` supported inside `supp ν`. -/
def deltaOn (ν : T → ℝ) : Set (T → ℝ) :=
  {μ ∈ simplexOn Γ.Θ | simplexSupport μ ⊆ simplexSupport ν}

/-! ## Attainability (Lemma I.1) -/

/-- **Lemma I.1** (attainability). For nonzero `ν ≥ 0` and `μ ∈ Δ_ν` there is a
coalition `η ≤ ν` with `η̂ = μ` retiring at least one type of `supp ν`. -/
lemma attainability {ν : T → ℝ} (hν0 : ∀ θ, 0 ≤ ν θ) (hνne : ν ≠ 0)
    {μ : T → ℝ} (hμ : μ ∈ Γ.deltaOn ν) :
    ∃ η : T → ℝ, IsCoalition ν η ∧ normalize η = μ ∧
      simplexSupport (fun θ => ν θ - η θ) ⊂ simplexSupport ν := by
  -- Set S := Finset.univ.filter (fun θ => 0 < μ θ), the support of μ as a finset.
  set S := Finset.univ.filter (fun θ => 0 < μ θ) with hS_def
  have hS_nonempty : S.Nonempty := by
    by_contra hS_empty;
    have := hμ.1.2.1; simp_all +decide [ Finset.ext_iff ] ;
    exact absurd ( this ▸ Finset.sum_nonpos fun _ _ => hS_empty _ ) ( by norm_num );
  -- Set lam := ν θ0 / μ θ0.
  obtain ⟨θ0, hθ0⟩ : ∃ θ0 ∈ S, ∀ θ ∈ S, ν θ0 / μ θ0 ≤ ν θ / μ θ := by
    exact Finset.exists_min_image _ _ hS_nonempty
  set lam := ν θ0 / μ θ0 with hlam_def
  have hlam_pos : 0 < lam := by
    exact hμ.2 ( Finset.mem_filter.mp hθ0.1 |>.2 ) |> fun h => by aesop;
  refine' ⟨ fun θ => lam * μ θ, _, _, _ ⟩ <;> simp_all +decide [ IsCoalition, SubMeasure ];
  · refine' ⟨ ⟨ fun θ => _, fun θ => _ ⟩, _ ⟩;
    · exact hμ.1.1 θ;
    · by_cases hθ : 0 < μ θ;
      · exact le_div_iff₀ hθ |>.1 ( hθ0.2 θ hθ );
      · nlinarith [ hν0 θ, div_nonneg hlam_pos.le hθ0.1.le ];
    · exact fun h => by have := congr_fun h θ0; simp_all +decide [ ne_of_gt ] ;
  · ext θ; simp +decide [ normalize, hlam_pos.ne', hθ0.1.ne' ] ;
    rw [ show mass ( fun θ => ν θ0 / μ θ0 * μ θ ) = ν θ0 / μ θ0 * ∑ θ, μ θ by rw [ mass, Finset.mul_sum _ _ _ ] ] ; simp +decide [ hlam_pos.ne', hθ0.1.ne', hμ.1.2.1 ];
  · refine' ⟨ _, _ ⟩;
    · intro θ hθ; simp_all +decide [ simplexSupport ] ;
      exact lt_of_le_of_lt ( mul_nonneg ( div_nonneg hlam_pos.le hθ0.1.le ) ( show 0 ≤ μ θ from by have := hμ.1; exact this.1 θ ) ) hθ;
    · simp_all +decide [ Set.not_subset, simplexSupport ];
      exact ⟨ θ0, hlam_pos, by rw [ div_mul_cancel₀ _ hθ0.1.ne' ] ⟩

/-! ## Greedy machinery (private helpers for Proposition 7) -/

/-
`Δ_ν` equals the simplex on the support finset of `ν` (when `ν ≥ 0` has
support inside `Θ`).
-/
private lemma deltaOn_eq_simplexOn_supp {ν : T → ℝ} (hν0 : ∀ θ, 0 ≤ ν θ)
    (hsub : simplexSupport ν ⊆ (Γ.Θ : Set T)) :
    Γ.deltaOn ν = simplexOn (Finset.univ.filter (fun θ => 0 < ν θ)) := by
  refine' Set.ext fun x => ⟨ _, _ ⟩ <;> intro hx;
  · obtain ⟨ hx₁, hx₂ ⟩ := hx;
    refine' ⟨ hx₁.1, hx₁.2.1, _ ⟩;
    intro θ hθ; contrapose! hθ; simp_all +decide [ simplexSupport ] ;
    exact hx₂ θ ( lt_of_le_of_ne ( hx₁.1 θ ) ( Ne.symm hθ ) );
  · refine' ⟨ _, _ ⟩;
    · exact simplexOn_mono ( fun θ hθ => hsub <| by aesop ) hx;
    · intro θ hθ; contrapose! hθ; simp_all +decide [ simplexSupport ] ;

private lemma deltaOn_subset_simplex {ν : T → ℝ} :
    Γ.deltaOn ν ⊆ simplexOn Γ.Θ := fun _ hμ => hμ.1

private lemma isCompact_deltaOn {ν : T → ℝ} (hν0 : ∀ θ, 0 ≤ ν θ)
    (hsub : simplexSupport ν ⊆ (Γ.Θ : Set T)) :
    IsCompact (Γ.deltaOn ν) := by
  rw [deltaOn_eq_simplexOn_supp hν0 hsub]; exact isCompact_simplexOn _

/-
The mass of a nonzero nonnegative measure is positive.
-/
private lemma mass_pos {ν : T → ℝ} (hν0 : ∀ θ, 0 ≤ ν θ) (hνne : ν ≠ 0) :
    0 < mass ν := by
  by_contra h_neg;
  exact hνne ( funext fun θ => le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => hν0 a ) ( Finset.mem_univ θ ) ) ( le_of_not_gt h_neg ) ) ( hν0 θ ) )

private lemma normalize_mem_deltaOn {ν : T → ℝ} (hν0 : ∀ θ, 0 ≤ ν θ)
    (hνne : ν ≠ 0) (hsub : simplexSupport ν ⊆ (Γ.Θ : Set T)) :
    normalize ν ∈ Γ.deltaOn ν := by
  refine' ⟨ _, _ ⟩ <;> simp_all +decide [ normalize, Finset.sum_div _ _ _ ];
  · refine' ⟨ fun θ => div_nonneg ( hν0 θ ) ( Finset.sum_nonneg fun _ _ => hν0 _ ), _, _ ⟩;
    · rw [ ← Finset.sum_div _ _ _, div_eq_iff ] <;> norm_num [ mass_pos hν0 hνne ];
      · rfl;
      · exact ne_of_gt ( mass_pos hν0 hνne );
    · exact fun θ hθ => Or.inl <| le_antisymm ( le_of_not_gt fun h => hθ <| hsub h ) ( hν0 θ );
  · intro θ; simp +decide [ normalize, Finset.sum_div _ _ _, *, simplexSupport ] ;
    exact fun h => lt_of_le_of_ne ( hν0 θ ) ( Ne.symm <| by rintro h'; simp +decide [ h' ] at h )

private lemma deltaOn_nonempty {ν : T → ℝ} (hν0 : ∀ θ, 0 ≤ ν θ)
    (hνne : ν ≠ 0) (hsub : simplexSupport ν ⊆ (Γ.Θ : Set T)) :
    (Γ.deltaOn ν).Nonempty :=
  ⟨normalize ν, normalize_mem_deltaOn hν0 hνne hsub⟩

private lemma vbar_usc_deltaOn {ν : T → ℝ} :
    UpperSemicontinuousOn Γ.vbar (Γ.deltaOn ν) :=
  Γ.vbar_usc.mono deltaOn_subset_simplex

/-- A single greedy step: from a nonzero residual `ν` extract a coalition
attaining the largest payoff over `Δ_ν` and retiring a type. -/
private lemma greedy_step {ν : T → ℝ} (hν0 : ∀ θ, 0 ≤ ν θ) (hνne : ν ≠ 0)
    (hsub : simplexSupport ν ⊆ (Γ.Θ : Set T)) :
    ∃ η : T → ℝ, IsCoalition ν η ∧
      IsGreatest (Γ.vbar '' Γ.deltaOn ν) (Γ.vbar (normalize η)) ∧
      simplexSupport (fun θ => ν θ - η θ) ⊂ simplexSupport ν := by
  obtain ⟨μs, hμs_mem, hμs_max⟩ :=
    UpperSemicontinuousOn.exists_isMaxOn (deltaOn_nonempty hν0 hνne hsub)
      (isCompact_deltaOn hν0 hsub) vbar_usc_deltaOn
  obtain ⟨η, hcoal, hnorm, hretire⟩ := attainability hν0 hνne hμs_mem
  refine ⟨η, hcoal, ?_, hretire⟩
  rw [hnorm]
  exact ⟨⟨μs, hμs_mem, rfl⟩, by rintro y ⟨x, hx, rfl⟩; exact hμs_max hx⟩

/-
Greedy recursion, `ℕ`-indexed: exhausts any nonzero residual in at most
`|supp ν|` steps.
-/
set_option maxHeartbeats 1000000 in
private lemma greedy_chain_aux (m : ℕ) : ∀ (ν : T → ℝ), (∀ θ, 0 ≤ ν θ) →
    simplexSupport ν ⊆ (Γ.Θ : Set T) →
    (Finset.univ.filter (fun θ => 0 < ν θ)).card ≤ m →
    ∃ (n : ℕ) (νs : ℕ → (T → ℝ)) (ηs : ℕ → (T → ℝ)),
      νs 0 = ν ∧
      (∀ t, t < n → νs (t + 1) = fun θ => νs t θ - ηs t θ) ∧
      (∀ t, t < n → IsCoalition (νs t) (ηs t)) ∧
      νs n = 0 ∧
      (∀ t, t < n → simplexSupport (νs (t + 1)) ⊂ simplexSupport (νs t)) ∧
      (∀ t, t < n →
        IsGreatest (Γ.vbar '' Γ.deltaOn (νs t)) (Γ.vbar (normalize (ηs t)))) ∧
      n ≤ (Finset.univ.filter (fun θ => 0 < ν θ)).card := by
  intro ν hν0 hsub hcard
  induction' m with m ih generalizing ν;
  · use 0, fun _ => ν, fun _ => 0; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
    exact funext fun x => le_antisymm ( hcard x ) ( hν0 x );
  · by_cases hνne : ν = 0;
    · refine' ⟨ 0, fun _ => 0, fun _ => 0, _, _, _, _ ⟩ <;> simp +decide [ hνne ];
    · obtain ⟨ η, hη₁, hη₂, hη₃ ⟩ := greedy_step ( by assumption ) hνne hsub;
      obtain ⟨ n, νs, ηs, hνs₀, hνs₁, hνs₂, hνs₃, hνs₄, hνs₅, hνs₆ ⟩ := ih ( fun θ => ν θ - η θ ) ( fun θ => sub_nonneg.2 ( hη₁.1.2 θ ) ) ( hη₃.1.trans hsub ) ( by
        have h_card : (Finset.univ.filter (fun θ => 0 < ν θ - η θ)).card < (Finset.univ.filter (fun θ => 0 < ν θ)).card := by
          convert Finset.card_lt_card ( show Finset.filter ( fun θ => 0 < ν θ - η θ ) Finset.univ ⊂ Finset.filter ( fun θ => 0 < ν θ ) Finset.univ from ?_ ) using 1;
          simp_all +decide [ Finset.ssubset_def, Finset.subset_iff, Set.ssubset_def, Set.subset_def ];
        linarith );
      refine' ⟨ n + 1, fun t => if t = 0 then ν else νs ( t - 1 ), fun t => if t = 0 then η else ηs ( t - 1 ), _, _, _, _, _ ⟩ <;> simp +decide [ * ];
      · grind;
      · grind;
      · refine' ⟨ _, _, _ ⟩;
        · grind +locals;
        · grind +revert;
        · refine' lt_of_le_of_lt hνs₆ _;
          convert Finset.card_lt_card _;
          simp_all +decide [ Finset.ssubset_def, Finset.subset_iff, Set.ssubset_def, Set.subset_def ]

/-! ## Coalition-optimal partitions (Definition 24, Proposition 7) -/

variable (Γ) in
/-- **Definition 24** (coalition-optimal partition). A *coalition-optimal
partition* of `Γ_{μ⁰}`: coalitions `η_1, …, η_T` of the successive residuals
`ν_0 = μ⁰`, `ν_t = ν_{t-1} − η_t`, exhausting the prior, each retiring at
least one remaining type and attaining the largest remaining coalition
payoff. -/
structure CoalitionOptimalPartition where
  /-- The number of steps. -/
  card : ℕ
  /-- The residual sub-measures `ν_0, …, ν_card`. -/
  ν : Fin (card + 1) → (T → ℝ)
  /-- The coalitions `η_1, …, η_card` (index `t` retires from `ν t.castSucc`). -/
  η : Fin card → (T → ℝ)
  /-- `ν_0 = μ⁰`. -/
  ν_zero : ν 0 = Γ.μ0
  /-- `ν_t = ν_{t-1} − η_t`. -/
  ν_succ : ∀ t : Fin card, ν t.succ = fun θ => ν t.castSucc θ - η t θ
  /-- Each `η_t` is a coalition of `Γ_{ν_{t-1}}`. -/
  coalition : ∀ t : Fin card, IsCoalition (ν t.castSucc) (η t)
  /-- The prior is exhausted: `ν_T = 0`. -/
  exhaust : ν (Fin.last card) = 0
  /-- Each step retires at least one remaining type. -/
  retire : ∀ t : Fin card,
    simplexSupport (ν t.succ) ⊂ simplexSupport (ν t.castSucc)
  /-- Each step attains the largest remaining coalition payoff
  `max_{μ ∈ Δ_{ν_{t-1}}} v̄(μ)`. -/
  optimal : ∀ t : Fin card,
    IsGreatest (Γ.vbar '' Γ.deltaOn (ν t.castSucc)) (Γ.vbar (normalize (η t)))

variable (Γ) in
/-- **Proposition 7 (i)–(ii)**. Every rich disclosure game admits a
coalition-optimal partition, reached (greedily) in at most `|Θ|` steps. -/
theorem cutecase_existence :
    ∃ P : Γ.CoalitionOptimalPartition, P.card ≤ Γ.Θ.card := by
  have hfilter : (Finset.univ.filter (fun θ => 0 < Γ.μ0 θ)) = Γ.Θ := by
    ext θ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hθ; by_contra hcon; exact absurd (Γ.μ0_mem.2.2 θ hcon) hθ.ne'
    · intro hθ; exact Γ.μ0_fullSupport θ hθ
  obtain ⟨n, νs, ηs, h0, hsucc, hcoal, hexh, hretire, hopt, hle⟩ :=
    greedy_chain_aux (Γ := Γ) (Finset.univ.filter (fun θ => 0 < Γ.μ0 θ)).card
      Γ.μ0 (fun θ => Γ.μ0_mem.1 θ) (simplexSupport_subset Γ.μ0_mem) le_rfl
  refine ⟨{ card := n
            ν := fun i => νs i.val
            η := fun i => ηs i.val
            ν_zero := h0
            ν_succ := fun t => hsucc t.val t.isLt
            coalition := fun t => hcoal t.val t.isLt
            exhaust := hexh
            retire := fun t => hretire t.val t.isLt
            optimal := fun t => hopt t.val t.isLt }, ?_⟩
  rw [hfilter] at hle; exact hle

variable (Γ) in
/-- `v̄` has a **unique maximizer** over `Δ_ν` for every nonzero sub-measure
`ν` (the standing hypothesis of the tent development). -/
def UniqueMaximizers : Prop :=
  ∀ ν : T → ℝ, (∀ θ, 0 ≤ ν θ) → ν ≠ 0 → simplexSupport ν ⊆ Γ.Θ →
    ∃! μ, μ ∈ Γ.deltaOn ν ∧ IsMaxOn Γ.vbar (Γ.deltaOn ν) μ

/-
The normalized belief of any coalition of `ν` lies in `Δ_ν`.
-/
private lemma normalize_coalition_mem {ν η : T → ℝ} (hν0 : ∀ θ, 0 ≤ ν θ)
    (hsub : simplexSupport ν ⊆ (Γ.Θ : Set T)) (hc : IsCoalition ν η) :
    normalize η ∈ Γ.deltaOn ν := by
  constructor;
  · constructor;
    · exact fun θ => div_nonneg ( hc.1.1 θ ) ( Finset.sum_nonneg fun _ _ => hc.1.1 _ );
    · constructor;
      · unfold normalize;
        rw [ ← Finset.sum_div, div_eq_iff ] <;> norm_num [ mass ];
        exact ne_of_gt ( mass_pos ( fun θ => hc.1.1 θ ) hc.2 );
      · intro θ hθ
        have hηθ : η θ = 0 := by
          exact le_antisymm ( le_trans ( hc.1.2 θ ) ( le_of_not_gt fun h => hθ <| hsub h ) ) ( hc.1.1 θ )
        simp [hηθ, normalize];
  · intro θ hθ;
    contrapose! hθ; simp_all +decide [ normalize ] ;
    exact div_nonpos_of_nonpos_of_nonneg ( le_trans ( hc.1.2 θ ) hθ ) ( Finset.sum_nonneg fun _ _ => hc.1.1 _ )

/-
Every residual of a coalition-optimal partition is a sub-measure with
support inside `Θ`.
-/
private lemma residual_props (P : Γ.CoalitionOptimalPartition) :
    ∀ i : Fin (P.card + 1),
      (∀ θ, 0 ≤ P.ν i θ) ∧ simplexSupport (P.ν i) ⊆ (Γ.Θ : Set T) := by
  -- We proceed by induction on $i$.
  intro i
  induction' i using Fin.induction with i ih;
  · exact ⟨ fun θ => P.ν_zero.symm ▸ Γ.μ0_mem.1 θ, P.ν_zero.symm ▸ simplexSupport_subset Γ.μ0_mem ⟩;
  · simp_all +decide [ Finset.subset_iff, Set.subset_def ];
    simp_all +decide [ P.ν_succ ];
    exact ⟨ fun θ => P.coalition i |>.1.2 θ, fun θ hθ => ih.2 θ ( by linarith [ P.coalition i |>.1.1 θ ] ) ⟩

/-
Under unique maximizers, the coalition extracted from a residual `ν` is
forced: two coalitions that both attain the maximal payoff and retire a type
coincide.
-/
private lemma coalition_forced (huniq : Γ.UniqueMaximizers) {ν η η' : T → ℝ}
    (hν0 : ∀ θ, 0 ≤ ν θ) (hsub : simplexSupport ν ⊆ (Γ.Θ : Set T))
    (hc : IsCoalition ν η)
    (hopt : IsGreatest (Γ.vbar '' Γ.deltaOn ν) (Γ.vbar (normalize η)))
    (hret : simplexSupport (fun θ => ν θ - η θ) ⊂ simplexSupport ν)
    (hc' : IsCoalition ν η')
    (hopt' : IsGreatest (Γ.vbar '' Γ.deltaOn ν) (Γ.vbar (normalize η')))
    (hret' : simplexSupport (fun θ => ν θ - η' θ) ⊂ simplexSupport ν) :
    η = η' := by
  -- From hopt and hopt', we know that normalize η = normalize η'.
  have hnorm : normalize η = normalize η' := by
    apply (huniq ν hν0 (by
    intro h; simp_all +decide [ IsCoalition ] ;
    exact hc.2 ( funext fun x => le_antisymm ( hc.1.2 x ) ( hc.1.1 x ) )) hsub).unique;
    · exact ⟨ normalize_coalition_mem hν0 hsub hc, fun x hx => hopt.2 ⟨ x, hx, rfl ⟩ ⟩;
    · exact ⟨ normalize_coalition_mem hν0 hsub hc', fun x hx => hopt'.2 ⟨ x, hx, rfl ⟩ ⟩;
  obtain ⟨θ0, hθ0⟩ : ∃ θ0, 0 < ν θ0 ∧ ν θ0 - η θ0 = 0 := by
    simp_all +decide [ Set.ssubset_def, Set.subset_def ];
    exact hret.2.imp fun x hx => ⟨ hx.1, by linarith [ hc.1.2 x ] ⟩
  obtain ⟨θ1, hθ1⟩ : ∃ θ1, 0 < ν θ1 ∧ ν θ1 - η' θ1 = 0 := by
    exact Exists.elim ( Set.exists_of_ssubset hret' ) fun x hx => ⟨ x, hx.1, le_antisymm ( le_of_not_gt fun hx' => hx.2 hx' ) ( sub_nonneg.2 <| hc'.1.2 x ) ⟩;
  -- Since $\eta \neq 0$ and $\eta' \neq 0$, we have $mass \eta > 0$ and $mass \eta' > 0$.
  have hmass_pos : 0 < mass η ∧ 0 < mass η' := by
    exact ⟨ mass_pos ( fun θ => hc.1.1 θ ) hc.2, mass_pos ( fun θ => hc'.1.1 θ ) hc'.2 ⟩;
  -- Since $\eta \neq 0$ and $\eta' \neq 0$, we have $mass \eta = mass \eta'$.
  have hmass_eq : mass η = mass η' := by
    have := congr_fun hnorm θ0; have := congr_fun hnorm θ1; simp_all +decide [ normalize ] ;
    rw [ div_eq_div_iff ] at * <;> try linarith;
    nlinarith [ hc.1.2 θ0, hc'.1.2 θ0, hc.1.2 θ1, hc'.1.2 θ1 ];
  ext θ; have := congr_fun hnorm θ; simp_all +decide [ div_eq_iff, ne_of_gt ] ;
  replace hnorm := congr_fun hnorm θ; simp_all +decide [ normalize, div_eq_iff, ne_of_gt ] ;

/-- **Proposition 7 (iii)**. Under unique maximizers the coalition-optimal
partition is unique (same length, same coalitions stepwise). -/
theorem cutecase_unique (huniq : Γ.UniqueMaximizers)
    (P P' : Γ.CoalitionOptimalPartition) :
    P.card = P'.card ∧
      ∀ (s : Fin P.card) (t : Fin P'.card), (s : ℕ) = (t : ℕ) →
        P.η s = P'.η t := by
  -- First prove the generalized residual-matching claim applicable to any ordered pair:
  have key : ∀ (Q Q' : Γ.CoalitionOptimalPartition) (i : ℕ) (hi : i ≤ Q.card) (hi' : i ≤ Q'.card),
      Q.ν ⟨i, by omega⟩ = Q'.ν ⟨i, by omega⟩ := by
        intro Q Q' i hi hi'
        induction' i with i ih;
        · exact Q.ν_zero.trans Q'.ν_zero.symm;
        · -- Let ν := Q.ν ⟨i, by omega⟩.
          set ν := Q.ν ⟨i, by omega⟩;
          -- By coalition_forced, we have Q.η ⟨i, by omega⟩ = Q'.η ⟨i, by omega⟩.
          have h_eta_eq : Q.η ⟨i, by omega⟩ = Q'.η ⟨i, by omega⟩ := by
            apply coalition_forced;
            exact huniq;
            exact residual_props Q ⟨ i, by linarith ⟩ |>.1;
            exact residual_props Q ⟨ i, by linarith ⟩ |>.2;
            exact Q.coalition ⟨ i, by linarith ⟩;
            · exact Q.optimal ⟨ i, by linarith ⟩;
            · convert Q.retire ⟨ i, by linarith ⟩ using 1;
              exact Q.ν_succ ⟨ i, by linarith ⟩ ▸ rfl;
            · convert Q'.coalition ⟨ i, by linarith ⟩ using 1;
              exact ih ( Nat.le_of_succ_le hi ) ( Nat.le_of_succ_le hi' );
            · convert Q'.optimal ⟨ i, by linarith ⟩ using 1;
              exact ih ( Nat.le_of_succ_le hi ) ( Nat.le_of_succ_le hi' ) ▸ rfl;
            · convert Q'.retire ⟨ i, by linarith ⟩ using 1;
              · rw [ Q'.ν_succ ];
                exact ih ( Nat.le_of_succ_le hi ) ( Nat.le_of_succ_le hi' ) ▸ rfl;
              · exact ih ( Nat.le_of_succ_le hi ) ( Nat.le_of_succ_le hi' ) ▸ rfl;
          convert congr_arg₂ ( fun x y => x - y ) ( ih ( Nat.le_of_succ_le hi ) ( Nat.le_of_succ_le hi' ) ) h_eta_eq using 1;
          · convert Q.ν_succ ⟨ i, by linarith ⟩ using 1;
          · exact Q'.ν_succ ⟨ i, by linarith ⟩;
  -- By lt_trichotomy on P.card, P'.card, we can conclude that P.card = P'.card.
  have h_card_eq : P.card = P'.card := by
    by_contra h_card_neq
    have h_card_lt : P.card < P'.card ∨ P'.card < P.card := by
      exact lt_or_gt_of_ne h_card_neq
    cases' h_card_lt with h_lt h_lt';
    · have h_contra : P'.ν ⟨P.card, by linarith⟩ = 0 := by
        convert key P P' P.card le_rfl ( by linarith ) |> Eq.symm |> Eq.trans <| P.exhaust using 1;
      have := P'.coalition ⟨ P.card, h_lt ⟩;
      simp_all +decide [ IsCoalition ];
      exact this.2 ( funext fun x => le_antisymm ( this.1.2 x ) ( this.1.1 x ) );
    · have := key P P' P'.card ( by linarith ) ( by linarith );
      have := P'.exhaust; simp_all +decide [ Fin.add_def, Fin.last ] ;
      have := P.coalition ⟨ P'.card, h_lt' ⟩ ; simp_all +decide [ IsCoalition ] ;
      exact this.2 ( funext fun x => le_antisymm ( this.1.2 x ) ( this.1.1 x ) );
  refine' ⟨ h_card_eq, _ ⟩;
  intro s t h_eq
  have h_res : P.ν s.castSucc = P'.ν t.castSucc := by
    convert key P P' s.val ( Nat.le_of_lt s.2 ) ( Nat.le_of_lt ( h_eq.symm ▸ t.2 ) ) using 1;
    exact congr_arg _ ( Fin.ext h_eq.symm );
  apply coalition_forced;
  exact huniq;
  exact P'.ν t.castSucc |> fun ν => residual_props P' t.castSucc |>.1;
  exact residual_props P' t.castSucc |>.2;
  exact h_res ▸ P.coalition s;
  · convert P.optimal s using 1;
    rw [ h_res ];
  · convert P.retire s using 1;
    · rw [ P.ν_succ s ];
      rw [ h_res ];
    · rw [ h_res ];
  · exact P'.coalition t;
  · exact P'.optimal t;
  · simpa only [ ← P'.ν_succ t ] using P'.retire t

/-! ## Nested chains and simplex decompositions (Definition 25) -/

variable (Γ) in
/-- A **face-maximizer selection**: for every non-empty `C ⊆ Θ` a maximizer
`μ*_C` of `v̄` over `Δ_C` (unique under `UniqueMaximizers`). `Δ_C` is
`deltaOn` of the indicator of `C`, i.e. beliefs supported inside `C`. -/
structure FaceMax where
  /-- The selected maximizer `μ*_C`. -/
  μstar : ∀ C : Finset T, C.Nonempty → C ⊆ Γ.Θ → (T → ℝ)
  /-- `μ*_C ∈ Δ_C`. -/
  mem : ∀ C hne hsub, μstar C hne hsub ∈ simplexOn Γ.Θ ∧
    simplexSupport (μstar C hne hsub) ⊆ C
  /-- `μ*_C` maximizes `v̄` over `Δ_C`. -/
  isMax : ∀ (C : Finset T) (hne : C.Nonempty) (hsub : C ⊆ Γ.Θ),
    ∀ μ ∈ simplexOn Γ.Θ, simplexSupport μ ⊆ (C : Set T) →
      Γ.vbar μ ≤ Γ.vbar (μstar C hne hsub)

variable (Γ) in
/-- **Definition 25 (i)** (nested chain). Subsets
`C_0 ⊇ C_1 ⊇ ⋯ ⊇ C_{n-1}` of `Θ` with `|C_j| = n − j` (so `C_0 = Θ` and
`C_{n-1}` is a singleton), `n := |Θ|`. -/
structure NestedChain where
  /-- The chain sets. -/
  C : Fin Γ.Θ.card → Finset T
  /-- Each `C_j ⊆ Θ`. -/
  C_subset : ∀ j, C j ⊆ Γ.Θ
  /-- `|C_j| = n − j`. -/
  C_card : ∀ j : Fin Γ.Θ.card, (C j).card = Γ.Θ.card - (j : ℕ)
  /-- The chain is nested. -/
  C_mono : ∀ i j : Fin Γ.Θ.card, i ≤ j → C j ⊆ C i
  /-- Each `C_j` is non-empty. -/
  C_nonempty : ∀ j, (C j).Nonempty

variable (Γ) in
/-- The belief `∑_j ω_j μ*_{C_j}` induced by a chain and a weight vector. -/
noncomputable def chainCombo (F : Γ.FaceMax) (ch : Γ.NestedChain)
    (ω : Fin Γ.Θ.card → ℝ) : T → ℝ :=
  fun θ => ∑ j, ω j * F.μstar (ch.C j) (ch.C_nonempty j) (ch.C_subset j) θ

variable (Γ) in
/-- **Definition 25 (ii)** (simplex decomposition). A *simplex decomposition*
of `μ`: a nested chain and a weight vector `ω ∈ Δ` with `μ = ∑_j ω_j μ*_{C_j}`. -/
structure SimplexDecomp (F : Γ.FaceMax) (μ : T → ℝ) where
  /-- The nested chain. -/
  chain : Γ.NestedChain
  /-- The weights. -/
  ω : Fin Γ.Θ.card → ℝ
  /-- The weights are non-negative. -/
  ω_nonneg : ∀ j, 0 ≤ ω j
  /-- The weights sum to one. -/
  ω_sum : ∑ j, ω j = 1
  /-- The decomposition identity. -/
  eq : μ = Γ.chainCombo F chain ω

/-- The value `∑_j ω_j v̄(μ*_{C_j})` of a simplex decomposition. -/
noncomputable def SimplexDecomp.value {F : Γ.FaceMax} {μ : T → ℝ}
    (d : Γ.SimplexDecomp F μ) : ℝ :=
  ∑ j, d.ω j * Γ.vbar (F.μstar (d.chain.C j) (d.chain.C_nonempty j)
    (d.chain.C_subset j))

/-
A strictly-decreasing-by-one chain of sets is strictly antitone.
-/
private lemma strictAnti_of_adjacent {N : ℕ} (g : ℕ → Finset T)
    (hadj : ∀ t, t + 1 < N → g (t + 1) ⊂ g t) :
    ∀ t t', t < t' → t' < N → g t' ⊂ g t := by
  intro t t' ht ht';
  induction' ht with t' ht' ih;
  · exact hadj t ht';
  · grind +qlia

/-
The face maximizer of `supp ν` is a belief in `Δ_ν`.
-/
private lemma faceMax_belief_mem (F : Γ.FaceMax) {ν : T → ℝ}
    (hsub : simplexSupport ν ⊆ (Γ.Θ : Set T))
    (hCne : (Finset.univ.filter (fun θ => 0 < ν θ)).Nonempty)
    (hCsub : (Finset.univ.filter (fun θ => 0 < ν θ)) ⊆ Γ.Θ) :
    F.μstar (Finset.univ.filter (fun θ => 0 < ν θ)) hCne hCsub ∈ Γ.deltaOn ν := by
  exact ⟨ F.mem _ hCne hCsub |>.1, fun x hx => by have := F.mem _ hCne hCsub |>.2 hx; aesop ⟩

/-
Face-maximizer greedy: run the greedy construction on `ν`, but always split
off the coalition whose belief is the face maximizer `μ*_{supp ν}`. Returns the
telescoping data `ν = ∑_{t<n} w_t • b_t` with `b_t = μ*_{C_t}`, `C_t = supp ν_t`
strictly decreasing.
-/
set_option maxHeartbeats 1000000 in
private lemma faceMax_greedy (F : Γ.FaceMax) (m : ℕ) :
    ∀ (ν : T → ℝ), (∀ θ, 0 ≤ ν θ) → simplexSupport ν ⊆ (Γ.Θ : Set T) →
    (Finset.univ.filter (fun θ => 0 < ν θ)).card ≤ m →
    ∃ (n : ℕ) (νs : ℕ → (T → ℝ)) (ws : ℕ → ℝ) (bs : ℕ → (T → ℝ))
      (Cs : ℕ → Finset T),
      νs 0 = ν ∧ νs n = 0 ∧
      (∀ t, t < n → Cs t = Finset.univ.filter (fun θ => 0 < νs t θ)) ∧
      (∀ t, t < n → (Cs t).Nonempty) ∧
      (∀ t, t < n → Cs t ⊆ Γ.Θ) ∧
      (∀ t, t < n → 0 ≤ ws t) ∧
      (∀ t, t < n → ∀ (h1 : (Cs t).Nonempty) (h2 : Cs t ⊆ Γ.Θ),
        bs t = F.μstar (Cs t) h1 h2) ∧
      (∀ t, t < n → (fun θ => νs t θ - νs (t + 1) θ) = fun θ => ws t * bs t θ) ∧
      (∀ t, t + 1 < n → Cs (t + 1) ⊂ Cs t) ∧
      n ≤ (Finset.univ.filter (fun θ => 0 < ν θ)).card := by
  induction' m with m ih;
  · intro ν hν0 hsub hcard;
    use 0; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
    exact ⟨ fun _ => ν, rfl, funext fun _ => le_antisymm ( hcard _ ) ( hν0 _ ) ⟩;
  · intro ν hν0 hsub hcard
    by_cases hνne : ν = 0
    generalize_proofs at *;
    · use 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => ∅; simp +decide [ hνne ] ;
    · -- Set C := Finset.univ.filter (fun θ => 0 < ν θ) with hC.
      set C := Finset.univ.filter (fun θ => 0 < ν θ) with hC
      have hCne : C.Nonempty := by
        contrapose! hνne; ext θ; simp_all +decide [ funext_iff ] ;
        exact le_antisymm ( le_of_not_gt fun h => Finset.notMem_empty θ <| hC.symm ▸ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h ⟩ ) ( hν0 θ )
      have hCsub : C ⊆ Γ.Θ := by
        exact fun x hx => hsub <| by aesop;
      generalize_proofs at *;
      -- Obtain the coalition η from the attainability lemma.
      obtain ⟨η, hηcoal, hηnorm, hηret⟩ := attainability hν0 hνne (faceMax_belief_mem F hsub hCne hCsub);
      -- Apply the induction hypothesis to the residual ν - η.
      obtain ⟨n', νs', ws', bs', Cs', hνs', hνs'_zero, hCs', hCs'_nonempty, hCs'_subset, hws'_nonneg, hbs'_eq, htel', hadj', hle'⟩ := ih (fun θ => ν θ - η θ) (fun θ => sub_nonneg.2 (hηcoal.1.2 θ)) (hηret.1.trans hsub) (by
      have h_card_lt : (Finset.univ.filter (fun θ => 0 < ν θ - η θ)).card < (Finset.univ.filter (fun θ => 0 < ν θ)).card := by
        convert Finset.card_lt_card _ using 1
        generalize_proofs at *;
        convert hηret using 1;
        simp +decide [ Finset.ssubset_def, Finset.subset_iff, Set.ssubset_def, Set.subset_def, simplexSupport ]
      generalize_proofs at *;
      grind)
      generalize_proofs at *;
      refine' ⟨ n' + 1, fun t => if t = 0 then ν else νs' ( t - 1 ), fun t => if t = 0 then mass η else ws' ( t - 1 ), fun t => if t = 0 then F.μstar C hCne hCsub else bs' ( t - 1 ), fun t => if t = 0 then C else Cs' ( t - 1 ), _, _, _, _, _ ⟩ <;> simp +decide [ * ];
      · grind;
      · grind;
      · refine' ⟨ _, _, _, _, _ ⟩
        all_goals generalize_proofs at *;
        · grind +qlia;
        · intro t ht; split_ifs <;> [ exact Finset.sum_nonneg fun _ _ => hηcoal.1.1 _; exact hws'_nonneg _ ( Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Nat.pos_of_ne_zero ( by aesop ) ) ) ) ht ) ] ;
        · grind;
        · intro t ht; rcases t with ( _ | t ) <;> simp +decide [ * ] ;
          · ext θ; rw [ ← hηnorm ] ; simp +decide [ normalize ] ;
            rw [ mul_div_cancel₀ _ ( ne_of_gt ( mass_pos ( fun θ => hηcoal.1.1 θ ) hηcoal.2 ) ) ];
          · exact htel' t ( Nat.lt_of_succ_le ht );
        · refine' ⟨ _, _ ⟩
          all_goals generalize_proofs at *;
          · intro t ht; rcases t with ( _ | t ) <;> simp +decide [ * ] ;
            · convert hηret using 1;
              simp +decide [ Finset.ssubset_def, Finset.subset_iff, Set.ssubset_def, Set.subset_def ];
            · grind +suggestions;
          · refine' lt_of_le_of_lt hle' _;
            convert Finset.card_lt_card _;
            simp +decide [ Finset.ssubset_def, Finset.subset_iff, Set.ssubset_def, Set.subset_def ] at hηret ⊢;
            exact hηret

/-
Extend a strictly decreasing family of non-empty subsets of `Θ` to a
maximal nested chain that passes through every member of the family.
-/
private lemma exists_chain_extending {N : ℕ} (Cs : ℕ → Finset T)
    (hsub : ∀ t, t < N → Cs t ⊆ Γ.Θ) (hne : ∀ t, t < N → (Cs t).Nonempty)
    (hanti : ∀ t t', t < t' → t' < N → Cs t' ⊂ Cs t) :
    ∃ (ch : Γ.NestedChain) (idx : ℕ → Fin Γ.Θ.card),
      ∀ t, t < N → ch.C (idx t) = Cs t := by
  by_cases hN : N = 0;
  · obtain ⟨ch, hch⟩ : ∃ ch : Γ.NestedChain, True := by
      -- Let's choose any permutation of the elements of `Θ`.
      obtain ⟨perm, hperm⟩ : ∃ perm : Fin Γ.Θ.card → T, Function.Injective perm ∧ ∀ i, perm i ∈ Γ.Θ := by
        have h_perm : Nonempty (Fin Γ.Θ.card ≃ {x : T | x ∈ Γ.Θ}) := by
          exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ Fintype.card_subtype ] ⟩;
        exact ⟨ _, Subtype.val_injective.comp h_perm.some.injective, fun i => h_perm.some i |>.2 ⟩;
      refine' ⟨ ⟨ fun j => Finset.image perm ( Finset.Ici j ), _, _, _, _ ⟩, trivial ⟩ <;> simp +decide [ Finset.card_image_of_injective _ hperm.1 ];
      · exact fun j => Finset.image_subset_iff.mpr fun i _ => hperm.2 i;
      · exact fun i j hij => Finset.image_subset_image <| Finset.Ici_subset_Ici.mpr hij;
    exact ⟨ ch, fun _ => ⟨ 0, Nat.pos_of_ne_zero Γ.Θ_nonempty.card_pos.ne' ⟩, by aesop ⟩;
  · -- Define depth : T → ℕ, depth x := ((Finset.range N).filter (fun t => x ∈ Cs t)).card.
    set depth := fun x => ((Finset.range N).filter (fun t => x ∈ Cs t)).card with hdepth_def;
    --.Ordering list: L := (List.range (N+1)).flatMap (fun d => (Γ.Θ.filter (fun x => depth x = d)).toList).
    set L := (List.range (N + 1)).flatMap (fun d => (Γ.Θ.filter (fun x => depth x = d)).toList) with hL_def;
    -- Show that L is a list of unique elements from Γ.Θ.
    have hL_nodup : L.Nodup := by
      rw [ List.nodup_flatMap ];
      simp +decide [ List.pairwise_iff_get ];
      simp +decide [ Function.onFun, List.disjoint_left ];
      exact ⟨ fun x hx => Finset.nodup_toList _, fun i j hij a ha₁ ha₂ ha₃ => by linarith [ show ( i : ℕ ) < j from hij ] ⟩
    have hL_toFinset : L.toFinset = Γ.Θ := by
      ext x; simp [L];
      exact fun hx => le_trans ( Finset.card_filter_le _ _ ) ( by simp +decide )
    have hL_length : L.length = Γ.Θ.card := by
      rw [ ← hL_toFinset, List.toFinset_card_of_nodup hL_nodup ];
    -- Define the chain `ch` using the list `L`.
    obtain ⟨ch, hch⟩ : ∃ ch : Γ.NestedChain, ∀ j : Fin Γ.Θ.card, ch.C j = (L.drop j).toFinset := by
      refine' ⟨ ⟨ fun j => ( L.drop j ).toFinset, _, _, _, _ ⟩, _ ⟩ <;> simp +decide [ hL_length ];
      · exact fun j => Finset.subset_iff.mpr fun x hx => hL_toFinset ▸ List.mem_toFinset.mpr ( List.mem_of_mem_drop ( List.mem_toFinset.mp hx ) );
      · intro j; rw [ List.toFinset_card_of_nodup ] ; simp +decide [ hL_nodup, hL_length ] ;
        exact hL_nodup.sublist ( List.drop_sublist _ _ );
      · intro i j hij; intro x hx; simp_all +decide [ List.mem_toFinset ] ;
        rw [ List.mem_iff_get ] at hx ⊢; obtain ⟨ k, hk ⟩ := hx; use ⟨ k + ( j - i ), by
          grind ⟩ ; simp_all +decide [ List.getElem_drop ] ;
        convert hk using 2 ; omega;
    -- Show that for each t < N, there exists an index j such that ch.C j = Cs t.
    have h_exists_idx : ∀ t < N, ∃ j : Fin Γ.Θ.card, ch.C j = Cs t := by
      intro t ht
      have hLhigh : (L.drop (Γ.Θ.card - (Cs t).card)).toFinset = Cs t := by
        have hLhigh : (L.drop (Γ.Θ.card - (Cs t).card)).toFinset = {x ∈ Γ.Θ | depth x ≥ t + 1} := by
          have hLlow_length : (List.flatMap (fun d => (Γ.Θ.filter (fun x => depth x = d)).toList) (List.range (t + 1))).length = Γ.Θ.card - (Cs t).card := by
            have hLlow_length : (List.flatMap (fun d => (Γ.Θ.filter (fun x => depth x = d)).toList) (List.range (t + 1))).toFinset = Γ.Θ \ Cs t := by
              ext x; simp [hdepth_def];
              constructor <;> intro hx;
              · contrapose! hx;
                intro hx' hx''; have := Finset.card_le_card ( show Finset.filter ( fun t => x ∈ Cs t ) ( Finset.range N ) ⊇ Finset.Icc 0 t from fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hi ] ), by
                                                                by_cases hi' : i < t;
                                                                · exact Finset.mem_of_subset ( hanti _ _ hi' ht |>.1 ) ( hx hx'' );
                                                                · grind ⟩ ) ; simp_all +decide ;
                linarith;
              · refine' ⟨ _, hx.1 ⟩;
                refine' le_trans ( Finset.card_le_card _ ) _;
                exact Finset.range t;
                · intro u hu; contrapose! hx; simp_all +decide [ Finset.subset_iff ] ;
                  exact fun _ => if h : t = u then h.symm ▸ hu.2 else hanti _ _ ( lt_of_le_of_ne hx h ) hu.1 |>.1 hu.2;
                · simp +decide;
            rw [ ← List.toFinset_card_of_nodup ];
            · grind;
            · refine' List.Nodup.sublist _ hL_nodup;
              simp +zetaDelta at *;
              rw [ ← List.take_append_drop ( t + 1 ) ( List.range ( N + 1 ) ), List.flatMap_append ] ; simp +decide [ List.take_range, ht.le ];
          have hLhigh : L.drop (Γ.Θ.card - (Cs t).card) = List.flatMap (fun d => (Γ.Θ.filter (fun x => depth x = d)).toList) (List.range (N + 1) |>.drop (t + 1)) := by
            rw [ ← hLlow_length, hL_def ];
            rw [ ← List.take_append_drop ( t + 1 ) ( List.range ( N + 1 ) ), List.flatMap_append ];
            simp +decide [ List.take_range, ht.le ];
          ext x; simp [hLhigh];
          grind +suggestions;
        ext x; simp [hLhigh];
        constructor <;> intro hx;
        · contrapose! hx;
          intro hxΘ
          have h_depth_le_t : ∀ t' < N, t' ≥ t → x ∉ Cs t' := by
            intro t' ht' ht'_ge_t
            induction' ht'_ge_t with t' ht' ht'_ge_t ih;
            · exact hx;
            · exact fun hx' => ht'_ge_t ( Nat.lt_of_succ_lt ht' ) ( hanti _ _ ( Nat.lt_succ_self _ ) ht' |>.1 hx' );
          exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun t => x ∈ Cs t ) ( Finset.range N ) ⊆ Finset.range t from fun i hi => Finset.mem_range.mpr ( Nat.lt_of_not_ge fun hi' => h_depth_le_t i ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) hi' ( Finset.mem_filter.mp hi |>.2 ) ) ) ) ( by simp +decide );
        · refine' ⟨ hsub t ht hx, _ ⟩;
          refine' lt_of_lt_of_le _ ( Finset.card_mono <| show Finset.filter ( fun s => x ∈ Cs s ) ( Finset.range N ) ≥ Finset.Icc 0 t from _ ) <;> simp +decide [ Finset.subset_iff ];
          intro s hs; exact ⟨ by linarith, by exact (by
          induction' hs.eq_or_lt with hs hs <;> [ aesop; exact Finset.mem_of_subset ( Finset.ssubset_iff_subset_ne.mp ( hanti _ _ hs ( by linarith ) ) |>.1 ) hx ]) ⟩ ;
      use ⟨Γ.Θ.card - (Cs t).card, by
        exact Nat.sub_lt ( Finset.card_pos.mpr Γ.Θ_nonempty ) ( Finset.card_pos.mpr ( hne t ht ) )⟩
      generalize_proofs at *;
      exact hch _ ▸ hLhigh;
    exact ⟨ ch, fun t => if ht : t < N then Classical.choose ( h_exists_idx t ht ) else ⟨ 0, Nat.pos_of_ne_zero ( by linarith [ Nat.pos_of_ne_zero hN, show Γ.Θ.card > 0 from Finset.card_pos.mpr Γ.Θ_nonempty ] ) ⟩, fun t ht => by simpa [ ht ] using Classical.choose_spec ( h_exists_idx t ht ) ⟩

/-- **Definition 25** (existence). Every belief in `ΔΘ` admits a simplex
decomposition (greedy construction underlying Proposition 7, padding the
chain with weight-zero sets). -/
lemma simplexDecomp_exists (F : Γ.FaceMax) {μ : T → ℝ}
    (hμ : μ ∈ simplexOn Γ.Θ) :
    Nonempty (Γ.SimplexDecomp F μ) := by
  obtain ⟨n, νs, ws, bs, Cs, h0, hn0, hCeq, hCne, hCsub, hwnn, hbs, htel, hadj, hle⟩ := faceMax_greedy F (Finset.univ.filter (fun θ => 0 < μ θ)).card μ (fun θ => hμ.1 θ) (simplexSupport_subset hμ) (Nat.le_refl _);
  -- By `exists_chain_extending`, there exists a maximal nested chain `ch` that contains `Cs`.
  obtain ⟨ch, idx, hidx⟩ := exists_chain_extending (Γ := Γ) (Cs := Cs) (hsub := hCsub) (hne := hCne) (hanti := fun t t' ht ht' => strictAnti_of_adjacent Cs hadj t t' ht ht');
  refine' ⟨ ⟨ ch, fun j => ∑ t ∈ Finset.range n, if idx t = j then ws t else 0, _, _, _ ⟩ ⟩;
  · exact fun j => Finset.sum_nonneg fun t ht => by split_ifs <;> linarith [ hwnn t ( Finset.mem_range.mp ht ) ] ;
  · -- By definition of `ws`, we know that $\sum_{t=0}^{n-1} ws t = 1$.
    have h_sum_ws : ∑ t ∈ Finset.range n, ws t = 1 := by
      have h_sum_ws : ∑ t ∈ Finset.range n, ws t * (∑ θ, bs t θ) = ∑ θ, μ θ := by
        have h_sum_ws : ∑ t ∈ Finset.range n, ∑ θ, (νs t θ - νs (t + 1) θ) = ∑ θ, μ θ := by
          have h_sum_ws : ∑ t ∈ Finset.range n, ∑ θ, (νs t θ - νs (t + 1) θ) = ∑ θ, (νs 0 θ - νs n θ) := by
            rw [ Finset.sum_comm ];
            exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.sum_range_sub' ] ;
          aesop;
        exact Eq.trans ( Finset.sum_congr rfl fun t ht => by rw [ Finset.mul_sum _ _ _, ← Finset.sum_congr rfl fun θ _ => congr_fun ( htel t ( Finset.mem_range.mp ht ) ) θ ] ) h_sum_ws;
      have h_sum_bs : ∀ t < n, ∑ θ, bs t θ = 1 := by
        intro t ht; specialize hbs t ht ( hCne t ht ) ( hCsub t ht ) ; simp_all +decide [ Finset.sum_ite ] ;
        have := F.mem ( Cs t ) ( hCne t ht ) ( hCsub t ht ) ; simp_all +decide [ Finset.sum_ite ] ;
      rw [ Finset.sum_congr rfl fun t ht => by rw [ h_sum_bs t ( Finset.mem_range.mp ht ) ] ] at h_sum_ws ; aesop;
    rw [ ← h_sum_ws, Finset.sum_comm ];
    simp +decide [ Finset.sum_ite_eq ];
  · ext θ; simp +decide [ chainCombo ] ;
    -- By definition of `chainCombo`, we can rewrite the right-hand side of the equation.
    have h_chainCombo : ∑ j, (∑ t ∈ Finset.range n, if idx t = j then ws t else 0) * F.μstar (ch.C j) (ch.C_nonempty j) (ch.C_subset j) θ = ∑ t ∈ Finset.range n, ws t * bs t θ := by
      simp +decide [ Finset.sum_mul _ _ _, Finset.sum_comm ];
      refine' Finset.sum_congr rfl fun t ht => _;
      grind;
    rw [ h_chainCombo, ← Finset.sum_congr rfl fun t ht => congr_fun ( htel t ( Finset.mem_range.mp ht ) ) θ ];
    rw [ Finset.sum_range_sub' ] ; aesop

/-! ## The tent (Definition 26, Proposition 9) -/

variable (Γ) in
/-- A hypothesis of the tent development (never an axiom): any two simplex
decompositions of the same belief have the same value — the well-definedness
condition needed for **Definition 26** (the tent) to be well defined. -/
def TentAssumption (F : Γ.FaceMax) : Prop :=
  ∀ (μ : T → ℝ) (d d' : Γ.SimplexDecomp F μ), d.value = d'.value

variable (Γ) in
/-- **Definition 26** (the tent). The *tent* of `v̄`: the common value of any
simplex decomposition (junk value `0` where no decomposition exists). -/
noncomputable def tent (F : Γ.FaceMax) (μ : T → ℝ) : ℝ :=
  if h : Nonempty (Γ.SimplexDecomp F μ) then (Classical.choice h).value else 0

/-- The canonical simplex decomposition of `chainCombo F ch ω` given by the chain
itself. -/
private def chainDecomp (F : Γ.FaceMax) (ch : Γ.NestedChain)
    (ω : Fin Γ.Θ.card → ℝ) (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1) :
    Γ.SimplexDecomp F (Γ.chainCombo F ch ω) :=
  { chain := ch, ω := ω, ω_nonneg := hω, ω_sum := hsum, eq := rfl }

/-- The tent value of a chain combination equals the corresponding weighted sum
of face-maximizer payoffs. -/
private lemma tent_chainCombo (F : Γ.FaceMax) (hT : Γ.TentAssumption F)
    (ch : Γ.NestedChain) (ω : Fin Γ.Θ.card → ℝ) (hω : ∀ j, 0 ≤ ω j)
    (hsum : ∑ j, ω j = 1) :
    Γ.tent F (Γ.chainCombo F ch ω) =
      ∑ j, ω j * Γ.vbar (F.μstar (ch.C j) (ch.C_nonempty j) (ch.C_subset j)) := by
  have hne : Nonempty (Γ.SimplexDecomp F (Γ.chainCombo F ch ω)) :=
    ⟨chainDecomp F ch ω hω hsum⟩
  rw [tent, dif_pos hne,
    hT _ (Classical.choice hne) (chainDecomp F ch ω hω hsum)]
  rfl

/-
Extend any non-empty `C ⊆ Θ` to a maximal nested chain passing through it.
-/
private lemma exists_chain_through {C : Finset T} (hne : C.Nonempty)
    (hsub : C ⊆ Γ.Θ) :
    ∃ (ch : Γ.NestedChain) (j : Fin Γ.Θ.card), ch.C j = C := by
  obtain ⟨l₁, l₂, hl₁, hl₂, hl⟩ : ∃ l₁ l₂ : List T, l₁.Nodup ∧ l₂.Nodup ∧ l₁.toFinset = Γ.Θ \ C ∧ l₂.toFinset = C ∧ List.Disjoint l₁ l₂ := by
    refine' ⟨ Finset.toList ( Γ.Θ \ C ), Finset.toList C, _, _, _, _, _ ⟩ <;> simp +decide [ Finset.nodup_toList, List.disjoint_left ];
  refine' ⟨ ⟨ fun j => ( l₁ ++ l₂ ).drop j |>.toFinset, _, _, _, _ ⟩, ⟨ l₁.length, _ ⟩, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · intro j x hx; have := List.mem_of_mem_drop hx; simp_all +decide [ Finset.ext_iff ] ;
    grind +ring;
  · intro j
    have h_card : (l₁ ++ l₂).length = Γ.Θ.card := by
      have h_card : (l₁ ++ l₂).toFinset = Γ.Θ := by
        simp_all +decide [ Finset.ext_iff ];
        grind;
      rw [ ← h_card, List.toFinset_card_of_nodup ];
      exact List.Nodup.append hl₁ hl₂ hl.2.2;
    rw [ List.toFinset_card_of_nodup ] <;> simp_all +decide [ List.nodup_append ];
    grind +suggestions;
  · intro i j hij x hx; rw [ List.mem_iff_get ] at hx ⊢; obtain ⟨ k, hk ⟩ := hx; use ⟨ k + j - i, by
      grind ⟩ ; simp_all +decide [ add_assoc, Nat.add_sub_assoc ] ;
    convert hk using 2 ; omega;
  · intro j;
    convert j.2 using 1;
    rw [ ← List.toFinset_card_of_nodup hl₁, ← List.toFinset_card_of_nodup hl₂, hl.1, hl.2.1, Finset.card_sdiff ];
    rw [ Finset.inter_eq_left.mpr hsub, tsub_add_cancel_of_le ( Finset.card_le_card hsub ) ];
  · have := List.toFinset_card_of_nodup hl₁; simp_all +decide [ Finset.card_sdiff ] ;
    rw [ ← this, Finset.inter_eq_left.mpr hsub ] ; exact Nat.sub_lt ( Finset.card_pos.mpr ⟨ _, hsub hne.choose_spec ⟩ ) ( Finset.card_pos.mpr hne )

/-- **Proposition 9 (i)**. `v̂(μ*_C) = v̄(μ*_C)` for every non-empty
`C ⊆ Θ`: the tent agrees with `v̄` at face maximizers. -/
theorem tent_eq_at_faceMax (F : Γ.FaceMax) (hT : Γ.TentAssumption F)
    {C : Finset T} (hne : C.Nonempty) (hsub : C ⊆ Γ.Θ) :
    Γ.tent F (F.μstar C hne hsub) = Γ.vbar (F.μstar C hne hsub) := by
  obtain ⟨ch, j0, hj0⟩ : ∃ (ch : Γ.NestedChain) (j0 : Fin Γ.Θ.card), ch.C j0 = C :=
    exists_chain_through hne hsub
  have hcombo : Γ.chainCombo F ch (fun j => if j = j0 then 1 else 0) = F.μstar C hne hsub := by
    unfold CPD.RichGame.chainCombo; simp +decide [ hj0 ] ;
  have := tent_chainCombo F hT ch ( fun j => if j = j0 then 1 else 0 ) ( fun j => by positivity ) ( by simp +decide ) ; aesop;

/-- **Proposition 9 (ii)**. Along any nested chain the tent is affine in the
weight vector. -/
theorem tent_affine_on_chain (F : Γ.FaceMax) (hT : Γ.TentAssumption F)
    (ch : Γ.NestedChain) (ω ω' : Fin Γ.Θ.card → ℝ)
    (hω : (∀ j, 0 ≤ ω j) ∧ ∑ j, ω j = 1)
    (hω' : (∀ j, 0 ≤ ω' j) ∧ ∑ j, ω' j = 1)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Γ.tent F (Γ.chainCombo F ch (fun j => s * ω j + (1 - s) * ω' j)) =
      s * Γ.tent F (Γ.chainCombo F ch ω) +
        (1 - s) * Γ.tent F (Γ.chainCombo F ch ω') := by
  rw [ tent_chainCombo, tent_chainCombo, tent_chainCombo ];
  any_goals tauto;
  · simp +decide only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum _ _ _];
  · exact fun j => add_nonneg ( mul_nonneg hs.1 ( hω.1 j ) ) ( mul_nonneg ( sub_nonneg.2 hs.2 ) ( hω'.1 j ) );
  · simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, hω.2, hω'.2 ]

/-
Any `f` satisfying the two tent axioms equals the weighted sum of
face-maximizer payoffs on every chain combination. Proved by induction on the
number of positive weights, peeling one weight at a time.
-/
set_option maxHeartbeats 1000000 in
private lemma f_chainCombo_eq (F : Γ.FaceMax) (f : (T → ℝ) → ℝ)
    (hi : ∀ (C : Finset T) (hne : C.Nonempty) (hsub : C ⊆ Γ.Θ),
      f (F.μstar C hne hsub) = Γ.vbar (F.μstar C hne hsub))
    (hii : ∀ (ch : Γ.NestedChain) (ω ω' : Fin Γ.Θ.card → ℝ),
      (∀ j, 0 ≤ ω j) → ∑ j, ω j = 1 → (∀ j, 0 ≤ ω' j) → ∑ j, ω' j = 1 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        f (Γ.chainCombo F ch (fun j => s * ω j + (1 - s) * ω' j)) =
          s * f (Γ.chainCombo F ch ω) + (1 - s) * f (Γ.chainCombo F ch ω'))
    (ch : Γ.NestedChain) (k : ℕ) :
    ∀ ω : Fin Γ.Θ.card → ℝ, (Finset.univ.filter (fun j => 0 < ω j)).card ≤ k →
      (∀ j, 0 ≤ ω j) → ∑ j, ω j = 1 →
      f (Γ.chainCombo F ch ω) =
        ∑ j, ω j * Γ.vbar (F.μstar (ch.C j) (ch.C_nonempty j) (ch.C_subset j)) := by
  intro ω hω_card hω_nonneg hω_sum
  induction' k with k ih generalizing ω
  generalize_proofs at *;
  · simp_all +decide [ Finset.ext_iff ];
    exact absurd ( hω_sum ▸ Finset.sum_nonpos fun j _ => hω_card j ) ( by norm_num );
  · by_cases hω_pos : ∃ j, 0 < ω j ∧ ω j < 1;
    · obtain ⟨ j0, hj0_pos, hj0_lt ⟩ := hω_pos
      set ζ := ω j0
      set ω' : Fin Γ.Θ.card → ℝ := fun j => if j = j0 then 0 else ω j / (1 - ζ);
      have hω'_card : (Finset.univ.filter (fun j => 0 < ω' j)).card ≤ k := by
        have hω'_card : (Finset.univ.filter (fun j => 0 < ω' j)) ⊆ (Finset.univ.filter (fun j => 0 < ω j)) \ {j0} := by
          grind;
        exact le_trans ( Finset.card_le_card hω'_card ) ( by rw [ Finset.card_sdiff ] ; aesop );
      have hω'_nonneg : ∀ j, 0 ≤ ω' j := by
        simp +zetaDelta at *;
        exact fun j => by split_ifs <;> [ exact le_rfl; exact div_nonneg ( hω_nonneg j ) ( sub_nonneg.2 hj0_lt.le ) ] ;
      have hω'_sum : ∑ j, ω' j = 1 := by
        simp +zetaDelta at *;
        simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ];
        rw [ ← Finset.sum_div, hω_sum, div_sub_div_same, div_eq_iff ] <;> linarith
      have hω'_mix : ω = fun j => ζ * (if j = j0 then 1 else 0) + (1 - ζ) * ω' j := by
        grind;
      have hω'_mix : f (Γ.chainCombo F ch ω) = ζ * f (Γ.chainCombo F ch (fun j => if j = j0 then 1 else 0)) + (1 - ζ) * f (Γ.chainCombo F ch ω') := by
        convert hii ch ( fun j => if j = j0 then 1 else 0 ) ω' _ _ _ _ ζ ⟨ hj0_pos.le, hj0_lt.le ⟩ using 1;
        · rw [ ← hω'_mix ];
        · exact fun j => by positivity;
        · simp +decide [ Finset.sum_ite_eq', Finset.filter_eq', Finset.filter_ne' ];
        · exact hω'_nonneg;
        · exact hω'_sum;
      have hω'_mix : f (Γ.chainCombo F ch (fun j => if j = j0 then 1 else 0)) = Γ.vbar (F.μstar (ch.C j0) (ch.C_nonempty j0) (ch.C_subset j0)) := by
        convert hi ( ch.C j0 ) ( ch.C_nonempty j0 ) ( ch.C_subset j0 ) using 1;
        congr! 1;
        ext θ; simp +decide [ chainCombo ] ;
      rw [ ‹f ( Γ.chainCombo F ch ω ) = ζ * f ( Γ.chainCombo F ch fun j => if j = j0 then 1 else 0 ) + ( 1 - ζ ) * f ( Γ.chainCombo F ch ω' ) ›, hω'_mix, ih ω' hω'_card hω'_nonneg hω'_sum ];
      rw [ show ω = fun j => ( ζ * if j = j0 then 1 else 0 ) + ( 1 - ζ ) * ω' j from ‹ω = fun j => ( ζ * if j = j0 then 1 else 0 ) + ( 1 - ζ ) * ω' j› ] ; simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_left_comm, mul_comm ] ; ring;
      simp +decide [ Finset.sum_add_distrib, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] ; ring;
    · -- Since there's no j with 0 < ω j < 1, all positive weights must be 1.
      have hω_one : ∀ j, ω j = 0 ∨ ω j = 1 := by
        exact fun j => Classical.or_iff_not_imp_left.2 fun hj => le_antisymm ( hω_sum ▸ Finset.single_le_sum ( fun a _ => hω_nonneg a ) ( Finset.mem_univ j ) ) ( le_of_not_gt fun hj' => hω_pos ⟨ j, lt_of_le_of_ne ( hω_nonneg j ) ( Ne.symm hj ), hj' ⟩ );
      -- Since there's no j with 0 < ω j < 1, all positive weights must be 1. Hence, there exists a unique j such that ω j = 1.
      obtain ⟨j, hj⟩ : ∃ j, ω j = 1 ∧ ∀ i ≠ j, ω i = 0 := by
        obtain ⟨j, hj⟩ : ∃ j, ω j = 1 := by
          contrapose! hω_sum; aesop;
        refine' ⟨ j, hj, fun i hi => _ ⟩;
        rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ) ] at hω_sum;
        exact Or.resolve_right ( hω_one i ) fun hi' => by linarith [ hω_nonneg i, Finset.single_le_sum ( fun a _ => hω_nonneg a ) ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ i, by simpa [ hi ] ⟩ : i ∈ Finset.univ \ { j } ) ] ;
      convert hi ( ch.C j ) ( ch.C_nonempty j ) ( ch.C_subset j ) using 1;
      · congr! 1;
        ext θ; simp +decide [ hj, chainCombo ] ;
        rw [ Finset.sum_eq_single j ] <;> simp +contextual [ hj ];
      · rw [ Finset.sum_eq_single j ] <;> simp +contextual [ hj ]

/-- **Proposition 9 (iii)**. Any `f` satisfying (i) and (ii) equals the tent
on `ΔΘ`. -/
theorem tent_unique (F : Γ.FaceMax) (hT : Γ.TentAssumption F)
    (f : (T → ℝ) → ℝ)
    (hi : ∀ (C : Finset T) (hne : C.Nonempty) (hsub : C ⊆ Γ.Θ),
      f (F.μstar C hne hsub) = Γ.vbar (F.μstar C hne hsub))
    (hii : ∀ (ch : Γ.NestedChain) (ω ω' : Fin Γ.Θ.card → ℝ),
      (∀ j, 0 ≤ ω j) → ∑ j, ω j = 1 → (∀ j, 0 ≤ ω' j) → ∑ j, ω' j = 1 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        f (Γ.chainCombo F ch (fun j => s * ω j + (1 - s) * ω' j)) =
          s * f (Γ.chainCombo F ch ω) + (1 - s) * f (Γ.chainCombo F ch ω')) :
    ∀ μ ∈ simplexOn Γ.Θ, f μ = Γ.tent F μ := by
  intro μ hμ
  obtain ⟨d⟩ := simplexDecomp_exists F hμ
  rw [d.eq, f_chainCombo_eq F f hi hii d.chain
      (Finset.univ.filter (fun j => 0 < d.ω j)).card d.ω le_rfl d.ω_nonneg d.ω_sum,
    tent_chainCombo F hT d.chain d.ω d.ω_nonneg d.ω_sum]

end RichGame

end CPD
