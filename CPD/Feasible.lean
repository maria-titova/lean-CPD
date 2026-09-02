import CPD.Partition

/-!
# Feasible beliefs and skeptical payoffs  (§4: Perfect Bayesian Equilibrium)

The **set of feasible beliefs** `𝓕(m) := {μ_σ(·|m) | σ a sender strategy,
m ∈ X(σ)}` (**Definition 5**).  **Lemma K.3** (feasible polytope): `𝓕(m)`
equals the polytope cut out by conditions (i)–(iii), and is a non-empty
compact convex polytope.  The **skeptical payoff**
`u̲(θ) := max_{m∈M(θ)} min_{μ∈𝓕(m)} v̲(μ)` (**Definition 6**), shown to be
well defined.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-- **Definition 5** (set of feasible beliefs):
`𝓕(m) := {μ_σ(·|m) | σ a sender strategy, m ∈ X(σ)}`. -/
def feasibleBeliefs (m : Msg) : Set (T → ℝ) :=
  {μ | ∃ s : Strategy G, m ∈ s.evidence ∧ s.belief m = μ}

/-- **Lemma K.3** (feasible polytope): the polytope cut out by conditions
(i)–(iii) that characterizes `𝓕(m)`. -/
def feasiblePolytope (m : Msg) : Set (T → ℝ) :=
  {μ | μ ∈ simplexOn G.Θ ∧
    (∀ θ ∉ G.canSend m, μ θ = 0) ∧
    (∀ θ ∈ G.forced m, ∀ θ' ∈ G.forced m,
        μ θ * G.μ0 θ' = μ θ' * G.μ0 θ) ∧
    (∀ θ ∈ G.canSend m \ G.forced m, ∀ θF ∈ G.forced m,
        μ θ * G.μ0 θF ≤ G.μ0 θ * μ θF)}

@[simp] lemma mem_feasiblePolytope {m : Msg} {μ : T → ℝ} :
    μ ∈ G.feasiblePolytope m ↔
      μ ∈ simplexOn G.Θ ∧
      (∀ θ ∉ G.canSend m, μ θ = 0) ∧
      (∀ θ ∈ G.forced m, ∀ θ' ∈ G.forced m,
          μ θ * G.μ0 θ' = μ θ' * G.μ0 θ) ∧
      (∀ θ ∈ G.canSend m \ G.forced m, ∀ θF ∈ G.forced m,
          μ θ * G.μ0 θF ≤ G.μ0 θ * μ θF) :=
  Iff.rfl

/-- `𝓕(m) ⊆ Δ Θ`. -/
lemma feasibleBeliefs_subset_simplex (m : Msg) :
    G.feasibleBeliefs m ⊆ simplexOn G.Θ := by
  rintro μ ⟨s, hm, rfl⟩
  exact s.belief_mem_simplex hm

/-
(⊆) of the polytope characterization.
-/
lemma feasibleBeliefs_subset_polytope {m : Msg} (hm : m ∈ G.𝓜) :
    G.feasibleBeliefs m ⊆ G.feasiblePolytope m := by
  intro μ hμ
  obtain ⟨s, hs⟩ := hμ;
  refine' ⟨ _, _, _, _ ⟩;
  · exact hs.2 ▸ s.belief_mem_simplex hs.1;
  · intro θ hθ;
    by_cases hθ' : θ ∈ G.Θ <;> simp_all +decide [ DisclosureGame.canSend ];
    · simp_all +decide [ DisclosureGame.preimageFull, preimage ];
      simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
      rw [ ← hs.2, Strategy.belief ];
      rw [ show s.σ θ m = 0 from _ ] ; ring;
      exact s.mem θ hθ' |>.2.2 m hθ;
    · rw [ ← hs.2, Strategy.belief ];
      rw [ G.μ0_mem.2.2 θ hθ', MulZeroClass.zero_mul, zero_div ];
  · intro θ hθ θ' hθ'
    have hσ : s.σ θ m = 1 ∧ s.σ θ' m = 1 := by
      have hσ : ∀ θ ∈ G.forced m, s.σ θ m = 1 := by
        intro θ hθ
        have hσ : s.σ θ ∈ simplexOn (G.M θ) := by
          exact s.mem θ ( Finset.mem_filter.mp hθ |>.1 )
        have hM : G.M θ = {m} := by
          exact Finset.mem_filter.mp hθ |>.2
        rw [hM] at hσ
        simp at hσ;
        rw [ ← hσ.2.1, Finset.sum_eq_single m ] <;> aesop
      exact ⟨hσ θ hθ, hσ θ' hθ'⟩;
    rw [ ← hs.2, Strategy.belief, Strategy.belief ];
    rw [ hσ.1, hσ.2 ] ; ring;
  · intro θ hθ θF hθF
    have hσθ : s.σ θ m ≤ 1 := by
      have := s.mem θ (by
      exact Finset.mem_filter.mp ( Finset.mem_sdiff.mp hθ |>.1 ) |>.1);
      exact this.2.1 ▸ Finset.single_le_sum ( fun a _ => this.1 a ) ( Finset.mem_univ m )
    have hσθF : s.σ θF m = 1 := by
      have := s.mem θF (by
      exact Finset.mem_filter.mp hθF |>.1);
      simp_all +decide [ DisclosureGame.forced ];
      rw [ ← this.2.1, Finset.sum_eq_single m ] <;> aesop
    have hμθ : μ θ = G.μ0 θ * s.σ θ m / s.onPathProb m := by
      exact hs.2 ▸ rfl
    have hμθF : μ θF = G.μ0 θF / s.onPathProb m := by
      rw [ ← hs.2, Strategy.belief ];
      rw [ hσθF, mul_one ];
    rw [ hμθ, hμθF, div_mul_eq_mul_div, mul_div_assoc ];
    exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right ( G.μ0_mem.1 θ ) hσθ ) ( div_nonneg ( G.μ0_mem.1 θF ) ( show 0 ≤ s.onPathProb m from Finset.sum_nonneg fun _ _ => mul_nonneg ( G.μ0_mem.1 _ ) ( s.mem _ ( by aesop ) |>.1 _ ) ) )

/-
A forced type carries positive mass in any feasible belief.
-/
lemma feasiblePolytope_forced_pos {m : Msg} {μ : T → ℝ}
    (hμ : μ ∈ G.feasiblePolytope m) {θF : T} (hθF : θF ∈ G.forced m) :
    0 < μ θF := by
  obtain ⟨hμ_simp, hμ_zero, hμ_forced, hμ_ineq⟩ := hμ;
  by_contra h_neg;
  -- Since μ θF ≤ 0 and G.μ0 θF > 0, we have μ θ = 0 for all θ ∈ G.forced m.
  have h_forced_zero : ∀ θ ∈ G.forced m, μ θ = 0 := by
    intro θ hθ
    have := hμ_forced θ hθ θF hθF
    simp [h_neg] at this;
    nlinarith [ G.μ0_fullSupport θF ( Finset.mem_filter.mp hθF |>.1 ), G.μ0_fullSupport θ ( Finset.mem_filter.mp hθ |>.1 ), hμ_simp.1 θF, hμ_simp.1 θ ];
  -- Since μ θ = 0 for all θ ∈ G.forced m, we have μ θ = 0 for all θ ∈ G.canSend m.
  have h_canSend_zero : ∀ θ ∈ G.canSend m, μ θ = 0 := by
    intro θ hθ
    by_cases hθ_forced : θ ∈ G.forced m;
    · exact h_forced_zero θ hθ_forced;
    · exact le_antisymm ( le_of_not_gt fun h => by have := hμ_ineq θ ( by aesop ) θF hθF; nlinarith [ G.μ0_fullSupport θ ( by
        exact Finset.mem_filter.mp hθ |>.1 ), G.μ0_fullSupport θF ( by
        exact Finset.mem_filter.mp hθF |>.1 ), h_forced_zero θF hθF ] ) ( hμ_simp.1 θ );
  exact absurd ( hμ_simp.2.1 ) ( by rw [ Finset.sum_eq_zero fun x hx => if hx' : x ∈ G.canSend m then h_canSend_zero x hx' else hμ_zero x hx' ] ; norm_num )

/-
The scaling constant for the constructive direction: a `p > 0` with
`μ θ * p ≤ μ⁰ θ` on `P(m)` and equality on the forced types.
-/
lemma feasiblePolytope_exists_scale {m : Msg} {μ : T → ℝ} (hm : m ∈ G.𝓜)
    (hμ : μ ∈ G.feasiblePolytope m) :
    ∃ p : ℝ, 0 < p ∧ (∀ θ ∈ G.canSend m, μ θ * p ≤ G.μ0 θ) ∧
      (∀ θ ∈ G.forced m, μ θ * p = G.μ0 θ) := by
  by_cases h_forced : (G.forced m).Nonempty;
  · refine' ⟨ G.μ0 ( Classical.choose h_forced ) / μ ( Classical.choose h_forced ), _, _, _ ⟩;
    · refine' div_pos _ _;
      · exact G.μ0_fullSupport _ ( Classical.choose_spec h_forced |> fun h => by simpa using Finset.mem_filter.mp h |>.1 );
      · exact feasiblePolytope_forced_pos hμ ( Classical.choose_spec h_forced );
    · intro θ hθ
      by_cases hθ_forced : θ ∈ G.forced m;
      · have := hμ.2.2.1 θ hθ_forced ( Classical.choose h_forced ) ( Classical.choose_spec h_forced );
        rw [ mul_div, div_le_iff₀ ] <;> nlinarith [ feasiblePolytope_forced_pos hμ ( Classical.choose_spec h_forced ) ];
      · have := hμ.2.2.2 θ ( Finset.mem_sdiff.mpr ⟨ hθ, hθ_forced ⟩ ) ( Classical.choose h_forced ) ( Classical.choose_spec h_forced );
        rw [ mul_div, div_le_iff₀ ] <;> nlinarith [ feasiblePolytope_forced_pos hμ ( Classical.choose_spec h_forced ) ];
    · intro θ hθ
      have h_eq : μ θ * G.μ0 (Classical.choose h_forced) = μ (Classical.choose h_forced) * G.μ0 θ := by
        exact hμ.2.2.1 _ hθ _ ( Classical.choose_spec h_forced );
      rw [ mul_div, div_eq_iff ] <;> nlinarith [ feasiblePolytope_forced_pos hμ ( Classical.choose_spec h_forced ) ];
  · -- Since there are no forced types, we can choose $p$ to be the minimum value of $G.μ0 θ / μ θ$ over all $\theta \in G.canSend m$.
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ G.canSend m, 0 < μ θ₀ := by
      by_contra h_contra;
      have h_sum_zero : ∑ θ, μ θ = 0 := by
        exact Finset.sum_eq_zero fun θ _ => if hθ : θ ∈ G.canSend m then le_antisymm ( le_of_not_gt fun h => h_contra ⟨ θ, hθ, h ⟩ ) ( hμ.1.1 θ ) else hμ.2.1 θ hθ;
      exact absurd h_sum_zero ( by rw [ hμ.1.2.1 ] ; norm_num );
    obtain ⟨p, hp⟩ : ∃ p ∈ Finset.image (fun θ => G.μ0 θ / μ θ) (Finset.filter (fun θ => 0 < μ θ) (G.canSend m)), ∀ q ∈ Finset.image (fun θ => G.μ0 θ / μ θ) (Finset.filter (fun θ => 0 < μ θ) (G.canSend m)), p ≤ q := by
      exact ⟨ Finset.min' _ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hθ₀.1, hθ₀.2 ⟩ ) ⟩, Finset.min'_mem _ _, fun q hq => Finset.min'_le _ _ hq ⟩;
    refine' ⟨ p, _, _, _ ⟩ <;> simp_all +decide [ Finset.mem_image ];
    · obtain ⟨ ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩, hp ⟩ := hp;
      exact div_pos ( G.μ0_fullSupport a ( Finset.mem_filter.mp ha₁ |>.1 ) ) ha₂;
    · intro θ hθ; by_cases hμθ : 0 < μ θ <;> simp_all +decide [ div_eq_iff, mul_comm ] ;
      · have := hp.2 _ _ hθ hμθ rfl; rw [ le_div_iff₀ hμθ ] at this; linarith;
      · exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( show 0 ≤ p by obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := hp.1; exact div_nonneg ( show 0 ≤ G.μ0 a by exact G.μ0_mem.1 a ) ha₂.le ) hμθ ) ( show 0 ≤ G.μ0 θ by exact G.μ0_mem.1 θ )

/-
(⊇) of the polytope characterization: the constructive direction.
-/
lemma polytope_subset_feasibleBeliefs {m : Msg} (hm : m ∈ G.𝓜) :
    G.feasiblePolytope m ⊆ G.feasibleBeliefs m := by
  intro μ hμ;
  -- By definition of feasibleBeliefs, we need to show that there exists a strategy s such that m is in s.evidence and s.belief m = μ.
  obtain ⟨p, hp_pos, hp_le, hp_eq⟩ := feasiblePolytope_exists_scale hm hμ;
  obtain ⟨hsimp, hzero, hforced, hineq⟩ := hμ;
  -- Define the building blocks:
  set q : T → ℝ := fun θ => μ θ * p / G.μ0 θ
  set alt : T → Msg := fun θ => if h : (G.M θ \ {m}).Nonempty then h.choose else m
  set σ : T → Msg → ℝ := fun θ msg => if msg = m then q θ else if msg = alt θ then 1 - q θ else 0;
  -- Show that `σ` is a valid strategy.
  have hσ_valid : ∀ θ ∈ G.Θ, σ θ ∈ simplexOn (G.M θ) := by
    intro θ hθ
    have hq_nonneg : 0 ≤ q θ := by
      exact div_nonneg ( mul_nonneg ( hsimp.1 θ ) hp_pos.le ) ( G.μ0_fullSupport θ hθ |> le_of_lt )
    have hq_le_one : q θ ≤ 1 := by
      by_cases hθm : θ ∈ G.canSend m;
      · exact div_le_one_of_le₀ ( hp_le θ hθm ) ( le_of_lt ( G.μ0_fullSupport θ hθ ) );
      · aesop
    have hq_eq_one : ∀ θ ∈ G.forced m, q θ = 1 := by
      intro θ hθ
      simp [q, hp_eq θ hθ];
      exact ne_of_gt ( G.μ0_fullSupport θ ( by
        exact Finset.mem_filter.mp hθ |>.1 ) )
    have halt_mem : ∀ θ ∈ G.Θ, alt θ ∈ G.M θ := by
      intro θ hθ
      simp [alt];
      split_ifs with h;
      · exact Finset.mem_sdiff.mp ( h.choose_spec ) |>.1;
      · simp_all +decide [ Finset.Nonempty ];
        exact G.M_nonempty θ hθ |> fun ⟨ x, hx ⟩ => h x hx ▸ hx;
    refine' ⟨ _, _, _ ⟩;
    · grind;
    · by_cases h : alt θ = m <;> simp +decide [ h, σ ];
      · have h_forced : G.M θ = {m} := by
          grind;
        simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', hq_eq_one θ ( by unfold DisclosureGame.forced; aesop ) ];
      · simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', h ];
        simp +decide [ Finset.card_filter ];
    · simp_all +decide [ DisclosureGame.canSend ];
      simp_all +decide [ DisclosureGame.preimageFull ];
      grind +suggestions;
  refine' ⟨ ⟨ σ, hσ_valid ⟩, _, _ ⟩;
  · -- Show that `m` is in the evidence of `σ`.
    have h_evidence : 0 < ∑ θ ∈ G.Θ, G.μ0 θ * σ θ m := by
      have h_onPathProb_pos : ∑ θ ∈ G.Θ, G.μ0 θ * q θ = p * ∑ θ ∈ G.Θ, μ θ := by
        rw [ Finset.mul_sum _ _ _ ];
        refine' Finset.sum_congr rfl fun θ hθ => _;
        rw [ mul_div, div_eq_iff ] <;> ring ; exact ne_of_gt ( G.μ0_fullSupport θ hθ );
      simp +zetaDelta at *;
      rw [ h_onPathProb_pos, show ∑ θ ∈ G.Θ, μ θ = 1 from by rw [ ← hsimp.2.1, Finset.sum_subset ( Finset.subset_univ G.Θ ) fun x hx₁ hx₂ => hsimp.2.2 x hx₂ ] ] ; positivity;
    exact ( Strategy.onPathProb_pos_iff_mem_evidence _ _ ).mp h_evidence;
  · ext θ; by_cases hθ : θ ∈ G.Θ <;> simp_all +decide [ Strategy.onPathProb, Strategy.belief ] ;
    · -- By definition of `σ`, we know that `σ θ m = q θ`.
      have hσ_m : ∀ θ ∈ G.Θ, σ θ m = q θ := by
        grind;
      -- By definition of `σ`, we know that `∑ x ∈ G.Θ, G.μ0 x * σ x m = p`.
      have hsum : ∑ x ∈ G.Θ, G.μ0 x * σ x m = p := by
        rw [ Finset.sum_congr rfl fun x hx => by rw [ hσ_m x hx, mul_div_cancel₀ _ ( ne_of_gt ( G.μ0_fullSupport x hx ) ) ] ];
        rw [ ← Finset.sum_mul _ _ _, Finset.sum_subset ( Finset.subset_univ G.Θ ) fun x hx₁ hx₂ => by aesop, hsimp.2.1, one_mul ];
      rw [ hsum, hσ_m θ hθ, mul_div_cancel₀ _ ( ne_of_gt ( G.μ0_fullSupport θ hθ ) ), mul_div_cancel_right₀ _ hp_pos.ne' ];
    · exact Or.inl <| Or.inl <| G.μ0_mem.2.2 θ hθ

/-- **Lemma K.3** (feasible polytope): `𝓕(m)` equals the polytope
characterized by conditions (i)–(iii). -/
theorem feasibleBeliefs_eq_polytope {m : Msg} (hm : m ∈ G.𝓜) :
    G.feasibleBeliefs m = G.feasiblePolytope m :=
  Set.Subset.antisymm (feasibleBeliefs_subset_polytope hm)
    (polytope_subset_feasibleBeliefs hm)

/-
`P(m)` is non-empty for `m ∈ 𝓜`.
-/
lemma canSend_nonempty {m : Msg} (hm : m ∈ G.𝓜) : (G.canSend m).Nonempty := by
  obtain ⟨θ, hθ⟩ : ∃ θ ∈ G.Θ, m ∈ G.M θ := by
    have := G.cover;
    replace this := Set.ext_iff.mp this m; aesop;
  refine' ⟨ θ, _ ⟩;
  exact Finset.mem_filter.mpr ⟨ hθ.1, by aesop ⟩

/-
`μ⁰_{P(m)}` belongs to the feasible polytope.
-/
lemma condPrior_canSend_mem_polytope {m : Msg} (hm : m ∈ G.𝓜) :
    G.condPrior (G.canSend m) ∈ G.feasiblePolytope m := by
  refine' ⟨ _, _, _, _ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · intro θ; by_cases hθ : θ ∈ G.canSend m <;> simp +decide [ *, DisclosureGame.condPrior ] ;
      exact div_nonneg ( G.μ0_mem.1 θ ) ( Finset.sum_nonneg fun _ _ => G.μ0_mem.1 _ );
    · convert G.condPrior_mem_simplex ( G.canSend_nonempty hm ) ( Finset.filter_subset _ _ ) |> fun h => h.2.1;
    · intro θ hθ; simp +decide [ DisclosureGame.condPrior, hθ ] ;
      exact Or.inl fun h => False.elim <| hθ <| Finset.mem_filter.mp h |>.1;
  · exact fun θ hθ => condPrior_of_not_mem hθ
  · intro θ hθ θ' hθ';
    simp +decide only [condPrior, canSend, priorMeasure] at hθ hθ' ⊢;
    simp_all +decide [ DisclosureGame.forced, DisclosureGame.preimageFull ];
    simp +decide [ preimage, hθ, hθ' ] ; ring;
  · simp +decide [ condPrior, mul_comm ];
    intro θ hθ hθ' θF hθF; rw [ if_pos hθ, if_pos ( by
      exact mem_preimage.mpr ⟨ hθF |> Finset.mem_filter.mp |>.1, by simp +decide [ Finset.mem_filter.mp hθF |>.2 ] ⟩ ) ] ; ring_nf; norm_num;

/-- **`𝓕(m)` is non-empty.** -/
lemma feasibleBeliefs_nonempty {m : Msg} (hm : m ∈ G.𝓜) :
    (G.feasibleBeliefs m).Nonempty := by
  rw [feasibleBeliefs_eq_polytope hm]
  exact ⟨G.condPrior (G.canSend m), condPrior_canSend_mem_polytope hm⟩

/-
The feasible polytope is convex.
-/
lemma convex_feasiblePolytope (m : Msg) :
    Convex ℝ (G.feasiblePolytope m) := by
  refine' fun x hx y hy a b ha hb hab => _;
  refine' ⟨ _, _, _, _ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · exact fun θ => add_nonneg ( mul_nonneg ha ( hx.1.1 θ ) ) ( mul_nonneg hb ( hy.1.1 θ ) );
    · simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hx.1.2.1, hy.1.2.1, hab ];
    · intro θ hθ; have := hx.1; have := hy.1; simp_all +decide [ simplexOn ] ;
  · simp_all +decide [ feasiblePolytope ];
  · simp_all +decide [ mul_comm, mul_assoc, mul_left_comm, add_mul, mul_add ];
  · intro θ hθ θF hθF
    have h1 := hx.2.2.2 θ hθ θF hθF
    have h2 := hy.2.2.2 θ hθ θF hθF;
    simpa using by nlinarith

/-- **`𝓕(m)` is convex.** -/
theorem convex_feasibleBeliefs {m : Msg} (hm : m ∈ G.𝓜) :
    Convex ℝ (G.feasibleBeliefs m) := by
  rw [feasibleBeliefs_eq_polytope hm]
  exact convex_feasiblePolytope m

/-
The feasible polytope is closed.
-/
lemma isClosed_feasiblePolytope (m : Msg) :
    IsClosed (G.feasiblePolytope m) := by
  refine' IsClosed.inter _ _;
  · exact isClosed_simplexOn G.Θ
  · refine' IsClosed.inter _ _;
    · refine' isClosed_iff_clusterPt.mpr _;
      intro a ha θ hθ;
      contrapose! ha;
      simp +decide [ clusterPt_principal_iff, ha ];
      exact ⟨ { μ : T → ℝ | μ θ ≠ 0 }, IsOpen.mem_nhds ( isOpen_compl_singleton.preimage ( continuous_apply θ ) ) ha, by rintro ⟨ μ, hμ₁, hμ₂ ⟩ ; exact hμ₁ ( hμ₂ θ hθ ) ⟩;
    · refine' IsClosed.inter _ _;
      · refine' isClosed_of_closure_subset _;
        intro μ hμ θ hθ θ' hθ';
        rw [ mem_closure_iff_seq_limit ] at hμ;
        obtain ⟨ x, hx, hx' ⟩ := hμ;
        exact tendsto_nhds_unique ( Filter.Tendsto.mul ( tendsto_pi_nhds.mp hx' θ ) tendsto_const_nhds ) ( Filter.Tendsto.mul ( tendsto_pi_nhds.mp hx' θ' ) tendsto_const_nhds |> Filter.Tendsto.congr ( by aesop ) );
      · refine' isClosed_of_closure_subset _;
        intro μ hμ;
        rw [ mem_closure_iff_seq_limit ] at hμ;
        rcases hμ with ⟨ x, hx, hx' ⟩;
        intro θ hθ θF hθF;
        exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.mul ( tendsto_pi_nhds.mp hx' θ ) tendsto_const_nhds ) ( Filter.Tendsto.mul tendsto_const_nhds ( tendsto_pi_nhds.mp hx' θF ) ) fun n => hx n θ hθ θF hθF

/-
The feasible polytope is compact.
-/
lemma isCompact_feasiblePolytope (m : Msg) :
    IsCompact (G.feasiblePolytope m) := by
  refine' IsCompact.of_isClosed_subset ( isCompact_simplexOn G.Θ ) ( isClosed_feasiblePolytope m ) fun x hx => hx.1

/-- **`𝓕(m)` is a compact convex set** (non-empty compact convex polytope). -/
theorem isCompact_convex_feasibleBeliefs {m : Msg} (hm : m ∈ G.𝓜) :
    IsCompact (G.feasibleBeliefs m) ∧ Convex ℝ (G.feasibleBeliefs m) := by
  rw [feasibleBeliefs_eq_polytope hm]
  exact ⟨isCompact_feasiblePolytope m, convex_feasiblePolytope m⟩

/-- The inner minimum `min_{μ ∈ 𝓕(m)} v̲(μ)`. -/
noncomputable def skepticalInner (m : Msg) : ℝ :=
  sInf (G.vlow '' G.feasibleBeliefs m)

variable (G) in
/-- **Definition 6** (skeptical payoff):
`u̲(θ) := max_{m ∈ M(θ)} min_{μ ∈ 𝓕(m)} v̲(μ)`. -/
noncomputable def skeptical (θ : T) : ℝ :=
  sSup (G.skepticalInner '' (G.M θ : Set Msg))

/-
The inner minimum is attained for `m ∈ 𝓜`.
-/
lemma exists_isMinOn_vlow_feasibleBeliefs {m : Msg} (hm : m ∈ G.𝓜) :
    ∃ μ ∈ G.feasibleBeliefs m, IsMinOn G.vlow (G.feasibleBeliefs m) μ ∧
      G.skepticalInner m = G.vlow μ := by
  have h_lower_semicontinuous : LowerSemicontinuousOn G.vlow (G.feasibleBeliefs m) := by
    exact G.vlow_lowerSemicontinuousOn.mono ( feasibleBeliefs_subset_simplex m );
  have := h_lower_semicontinuous.exists_isMinOn ( feasibleBeliefs_nonempty hm ) ( isCompact_convex_feasibleBeliefs hm |>.1 );
  obtain ⟨ μ, hμ₁, hμ₂ ⟩ := this; use μ; simp_all +decide [ IsMinOn, IsMinFilter ] ;
  exact IsLeast.csInf_eq ( ⟨ Set.mem_image_of_mem _ hμ₁, Set.forall_mem_image.2 hμ₂ ⟩ )

/-- **Definition 6** (skeptical payoff, well-definedness): the outer max
and inner min are attained, with `u̲(θ) = v̲(μ)` for some `m ∈ M(θ)`,
`μ ∈ 𝓕(m)`. -/
theorem skeptical_isWellDefined {θ : T} (hθ : θ ∈ G.Θ) :
    ∃ m ∈ G.M θ, ∃ μ ∈ G.feasibleBeliefs m,
      IsMinOn G.vlow (G.feasibleBeliefs m) μ ∧
      IsMaxOn G.skepticalInner (G.M θ : Set Msg) m ∧
      G.skeptical θ = G.vlow μ := by
  obtain ⟨m, hm⟩ : ∃ m ∈ G.M θ, ∀ m' ∈ G.M θ, G.skepticalInner m' ≤ G.skepticalInner m := by
    exact Finset.exists_max_image _ _ ( G.M_nonempty θ hθ );
  obtain ⟨μ, hμ, hμ_min, hμ_eq⟩ : ∃ μ ∈ G.feasibleBeliefs m, IsMinOn G.vlow (G.feasibleBeliefs m) μ ∧ G.skepticalInner m = G.vlow μ := by
    apply exists_isMinOn_vlow_feasibleBeliefs;
    exact G.M_subset θ hθ hm.1;
  refine' ⟨ m, hm.1, μ, hμ, hμ_min, fun m' hm' => _, _ ⟩;
  · exact hm.2 m' hm';
  · refine' le_antisymm _ _;
    · exact csSup_le ( Set.Nonempty.image _ ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) ( Set.forall_mem_image.2 fun m' hm' => hm.2 m' ( by aesop_cat ) |> le_trans <| hμ_eq ▸ le_rfl );
    · exact hμ_eq ▸ le_csSup ( Set.Finite.bddAbove ( Set.toFinite _ ) ) ( Set.mem_image_of_mem _ hm.1 )

end DisclosureGame

end CPD
