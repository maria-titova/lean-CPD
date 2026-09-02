import CPD.Coalition

/-!
# The coalition payoff set (§5)

Fix a disclosure game `G = (Θ, 𝓜, M, μ⁰, V)` and a set of sender types `R ⊆ Θ`.
A **coalition** `(C,σ,w)` of the restricted game `G|_R` is a subset `C ⊆ R`
together with a strategy `σ` on `G|_R` and a common payoff `w`, satisfying the
conditions (C1)-(C4) of Definition 2 (in particular `C` is exclusive: only
types in `C` can produce the evidence `X(σ)`, and every on-path message pays
exactly `w`). The **coalition payoff set**

`𝒲_R := {w | (C,σ,w) is a coalition of G|_R for some C ⊆ R}`

is recorded here as `coalitionPayoffs` (a set attached to a `DisclosureGame`;
apply it to `G.restrict R hR ...` for the subscript-`R` version). **Lemma 2**
(coalition-compact) states that `𝒲_R` is non-empty and compact; this is
`isCompact_coalitionPayoffs` below, built from non-emptiness
(`coalitionPayoffs_nonempty`), boundedness (via the uniform bound on `V`
coming from upper hemicontinuity and compactness of the simplex), and
closedness (via sequential compactness of the strategy space, cell by cell).
-/

open Set Topology

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable (G : DisclosureGame T Msg)

/-- **§5** (the coalition payoff set): the **set of attainable coalition
payoffs** of `G`, `𝒲 := {w | (C,σ,w) is a coalition of G}`. -/
def coalitionPayoffs : Set ℝ := {w | ∃ K : Coalition G, K.w = w}

variable {G}

/-- **`𝒲_R` is non-empty** (a coalition exists). -/
lemma coalitionPayoffs_nonempty (G : DisclosureGame T Msg) :
    G.coalitionPayoffs.Nonempty := by
  obtain ⟨K⟩ := exists_coalition (G := G)
  exact ⟨K.w, K, rfl⟩

/--
The payoff correspondence is uniformly bounded on the simplex.
-/
lemma exists_bound_V (G : DisclosureGame T Msg) :
    ∃ M : ℝ, ∀ μ ∈ simplexOn G.Θ, ∀ w ∈ G.V μ, |w| ≤ M := by
  -- By assumption (A4), $V$ is upper hemicontinuous.
  have h_uhc : UpperHemicontinuousOn G.V (simplexOn G.Θ) := by
    exact G.V_uhc;
  have h_compact : IsCompact (simplexOn G.Θ) := isCompact_simplexOn _
  have h_bounded : ∀ μ ∈ simplexOn G.Θ, ∃ U : Set ℝ, IsOpen U ∧ G.V μ ⊆ U ∧ ∃ M, ∀ w ∈ U, |w| ≤ M := by
    intro μ hμ
    obtain ⟨M, hM⟩ : ∃ M, ∀ w ∈ G.V μ, |w| ≤ M := by
      exact IsCompact.bddAbove ( G.V_isCompact μ hμ |> IsCompact.image <| continuous_abs ) |> fun ⟨ M, hM ⟩ => ⟨ M, fun w hw => hM <| Set.mem_image_of_mem _ hw ⟩;
    exact ⟨ Set.Ioo ( -M - 1 ) ( M + 1 ), isOpen_Ioo, fun w hw => ⟨ by linarith [ abs_le.mp ( hM w hw ) ], by linarith [ abs_le.mp ( hM w hw ) ] ⟩, M + 1, fun w hw => abs_le.mpr ⟨ by linarith [ hw.1 ], by linarith [ hw.2 ] ⟩ ⟩;
  choose! U hU₁ hU₂ M hM using h_bounded;
  have h_subcover : ∀ μ ∈ simplexOn G.Θ, ∃ W ∈ 𝓝[simplexOn G.Θ] μ, ∀ μ' ∈ W, G.V μ' ⊆ U μ := by
    exact fun μ hμ => h_uhc μ hμ ( U μ ) ( hU₁ μ hμ ) ( hU₂ μ hμ );
  choose! W hW₁ hW₂ using h_subcover;
  have := h_compact.elim_nhdsWithin_subcover W hW₁;
  obtain ⟨ t, ht₁, ht₂ ⟩ := this;
  exact ⟨ ∑ x ∈ t, |M x|, fun μ hμ w hw => by rcases Set.mem_iUnion₂.1 ( ht₂ hμ ) with ⟨ x, hx, hx' ⟩ ; exact le_trans ( hM x ( ht₁ x hx ) w ( hW₂ x ( ht₁ x hx ) μ hx' hw ) ) ( le_trans ( le_abs_self _ ) ( Finset.single_le_sum ( fun x _ => abs_nonneg ( M x ) ) hx ) ) ⟩

/--
**`𝒲_R` is bounded.**
-/
lemma isBounded_coalitionPayoffs (G : DisclosureGame T Msg) :
    Bornology.IsBounded G.coalitionPayoffs := by
  obtain ⟨ M, hM ⟩ := exists_bound_V G;
  refine' isBounded_iff_forall_norm_le.mpr ⟨ M, _ ⟩;
  rintro w ⟨ K, rfl ⟩;
  obtain ⟨m, hm⟩ : ∃ m ∈ K.σ.evidence, True := by
    obtain ⟨θ, hθ⟩ : ∃ θ ∈ K.C, True := by
      exact ⟨ _, K.C_nonempty.choose_spec, trivial ⟩;
    obtain ⟨m, hm⟩ : ∃ m, K.σ.σ θ m > 0 := by
      have := K.σ.mem θ hθ.1;
      have := this.2.1;
      exact not_forall_not.mp fun h => by rw [ Finset.sum_eq_zero fun m hm => le_antisymm ( le_of_not_gt fun h' => h m h' ) ( by aesop ) ] at this; norm_num at this;
    exact ⟨ m, Set.mem_iUnion₂.mpr ⟨ θ, hθ.1, hm ⟩, trivial ⟩;
  convert hM _ _ _ ( K.payoff m hm.1 ) using 1;
  convert zeroExt_mem_simplex K.C_subset ( K.σ.belief_mem_simplex hm.1 ) using 1

/--
**Closed graph of `V`.** If `μ n → μ∞` inside the simplex, `w n ∈ V(μ n)`,
and `w n → w∞`, then `w∞ ∈ V(μ∞)`. (Consequence of upper hemicontinuity with
closed values.)
-/
lemma V_mem_of_tendsto (G : DisclosureGame T Msg) {μs : ℕ → (T → ℝ)} {μL : T → ℝ}
    {ws : ℕ → ℝ} {wL : ℝ}
    (hμ : ∀ n, μs n ∈ simplexOn G.Θ) (hμL : μL ∈ simplexOn G.Θ)
    (hμconv : Filter.Tendsto μs Filter.atTop (𝓝 μL))
    (hw : ∀ n, ws n ∈ G.V (μs n))
    (hwconv : Filter.Tendsto ws Filter.atTop (𝓝 wL)) :
    wL ∈ G.V μL := by
  by_contra h;
  -- Since $wL \notin G.V μL$, there exists an $\epsilon > 0$ such that $B(wL, \epsilon) \cap G.V μL = \emptyset$.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball wL ε ∩ G.V μL = ∅ := by
    exact Metric.mem_nhds_iff.1 ( IsOpen.mem_nhds ( isOpen_compl_iff.2 ( G.V_isCompact μL hμL |> IsCompact.isClosed ) ) h ) |> fun ⟨ ε, εpos, hε ⟩ => ⟨ ε, εpos, Set.eq_empty_iff_forall_notMem.2 fun x hx => hε hx.1 hx.2 ⟩;
  have := G.V_uhc μL hμL ( Metric.closedBall wL ( ε / 2 ) )ᶜ ( Metric.isClosed_closedBall.isOpen_compl ) ?_;
  · obtain ⟨ W, hW₁, hW₂ ⟩ := this;
    rw [ mem_nhdsWithin_iff_exists_mem_nhds_inter ] at hW₁;
    rcases hW₁ with ⟨ u, hu₁, hu₂ ⟩ ; rcases Filter.eventually_atTop.mp ( hμconv.eventually hu₁ ) with ⟨ N, hN ⟩ ; have := hwconv.eventually ( Metric.ball_mem_nhds _ ( half_pos hε_pos ) ) ; rcases this.and ( Filter.eventually_ge_atTop N ) with h ; obtain ⟨ n, hn₁, hn₂ ⟩ := h.exists ; exact hW₂ _ ( hu₂ ⟨ hN _ hn₂, hμ _ ⟩ ) ( hw _ ) ( Metric.mem_closedBall.mpr <| le_of_lt hn₁ ) ;
  · exact fun x hx => fun hx' => hε.subset ⟨ Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hx' ) ( half_lt_self hε_pos ) ), hx ⟩

/--
**Continuity of induced beliefs at on-path messages.** If the strategy
functions converge pointwise to that of `σL` and `m` is on path for `σL`, then the
coalition-induced beliefs converge.
-/
lemma coalitionBelief_tendsto {g : DisclosureGame T Msg} {σs : ℕ → Strategy g}
    {σL : Strategy g} {m : Msg}
    (hconv : Filter.Tendsto (fun k => (σs k).σ) Filter.atTop (𝓝 σL.σ))
    (hm : m ∈ σL.evidence) :
    Filter.Tendsto (fun k => (σs k).coalitionBelief m) Filter.atTop
      (𝓝 (σL.coalitionBelief m)) := by
  refine' ( Filter.Tendsto.comp ( continuous_zeroExt _ |> Continuous.continuousAt ) _ );
  refine' tendsto_pi_nhds.mpr fun θ => _;
  refine' Filter.Tendsto.div _ _ _;
  · exact tendsto_const_nhds.mul ( tendsto_pi_nhds.mp ( tendsto_pi_nhds.mp hconv θ ) m );
  · convert tendsto_finset_sum _ fun θ _ => Filter.Tendsto.mul tendsto_const_nhds ( tendsto_pi_nhds.mp hconv θ |> tendsto_pi_nhds.mp <| m ) using 1;
  · exact ne_of_gt ( by simpa using ( σL.onPathProb_pos_iff_mem_evidence m ).mpr hm )

/--
Evidence depends only on the strategy's values on `g.Θ`.
-/
lemma evidence_eqOn {g : DisclosureGame T Msg} {s1 s2 : Strategy g}
    (h : ∀ θ ∈ g.Θ, s1.σ θ = s2.σ θ) : s1.evidence = s2.evidence := by
  convert Set.iUnion₂_congr fun θ hθ => ?_;
  unfold Strategy.msgSupport; aesop;

/--
The coalition-induced belief depends only on the strategy's values on `g.Θ`.
-/
lemma coalitionBelief_eqOn {g : DisclosureGame T Msg} {s1 s2 : Strategy g}
    (h : ∀ θ ∈ g.Θ, s1.σ θ = s2.σ θ) (m : Msg) :
    s1.coalitionBelief m = s2.coalitionBelief m := by
  ext θ; simp [Strategy.coalitionBelief, h];
  unfold zeroExt Strategy.belief;
  split_ifs <;> simp_all +decide [ Strategy.onPathProb ]

/--
**Fixed-cell payoff set, in terms of the restricted game.** A real number is
an attainable payoff with cell `C` iff some strategy of `G|_C` has exclusive
evidence and yields it on every on-path message.
-/
lemma payoffCell_eq (G : DisclosureGame T Msg) (C : Finset T)
    (hCne : C.Nonempty) (hCsub : C ⊆ G.Θ) :
    {w : ℝ | ∃ K : Coalition G, K.C = C ∧ K.w = w} =
      {w : ℝ | ∃ σ : Strategy (G.restrict C hCne hCsub),
        G.preimageSetFull σ.evidence ⊆ C ∧
        ∀ m ∈ σ.evidence, w ∈ G.V (σ.coalitionBelief m)} := by
  ext w
  constructor
  intro hw
  obtain ⟨K, hKC, hwK⟩ := hw;
  · subst hKC;
    refine' ⟨ K.σ, _, _ ⟩;
    · exact K.exclusive;
    · exact fun m hm => hwK ▸ K.payoff m hm;
  · rintro ⟨ σ, hσ₁, hσ₂ ⟩;
    refine' ⟨ ⟨ C, hCne, hCsub, σ, hσ₁, w, hσ₂ ⟩, rfl, rfl ⟩

/-- **Sequential compactness of the (off-`C`-zeroed) strategy space.** Any
sequence of `G|_C`-strategies has strategies `τ n` agreeing with it on `C` and
vanishing off `C`, together with a subsequence whose functions converge (fully)
to those of a limit strategy. -/
lemma exists_zeroed_convergent_subseq (G : DisclosureGame T Msg) (C : Finset T)
    (hCne : C.Nonempty) (hCsub : C ⊆ G.Θ)
    (σ : ℕ → Strategy (G.restrict C hCne hCsub)) :
    ∃ (τ : ℕ → Strategy (G.restrict C hCne hCsub))
      (σL : Strategy (G.restrict C hCne hCsub)) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ n, ∀ θ ∈ C, (τ n).σ θ = (σ n).σ θ) ∧
      Filter.Tendsto (fun k => (τ (φ k)).σ) Filter.atTop (𝓝 σL.σ) := by
  classical
  set g : ℕ → (T → Msg → ℝ) := fun n θ => if θ ∈ C then (σ n).σ θ else 0 with hg
  have hτmem : ∀ n, ∀ θ ∈ (G.restrict C hCne hCsub).Θ,
      g n θ ∈ simplexOn ((G.restrict C hCne hCsub).M θ) := by
    intro n θ hθ
    simp only [restrict_Θ] at hθ
    simp only [restrict_M, hg, if_pos hθ]
    exact (σ n).mem θ (by simpa using hθ)
  set τ : ℕ → Strategy (G.restrict C hCne hCsub) := fun n => ⟨g n, hτmem n⟩ with hτ
  set 𝒦 : Set (T → Msg → ℝ) :=
    Set.univ.pi (fun θ => if θ ∈ C then simplexOn (G.M θ) else ({0} : Set (Msg → ℝ))) with h𝒦
  have hKcompact : IsCompact 𝒦 := by
    apply isCompact_univ_pi
    intro θ
    by_cases hθ : θ ∈ C
    · simp only [if_pos hθ]; exact isCompact_simplexOn _
    · simp only [if_neg hθ]; exact isCompact_singleton
  have hgK : ∀ n, g n ∈ 𝒦 := by
    intro n
    rw [h𝒦, Set.mem_univ_pi]
    intro θ
    by_cases hθ : θ ∈ C
    · simp only [if_pos hθ, hg]
      exact (σ n).mem θ (by simpa using hθ)
    · simp only [if_neg hθ, hg, Set.mem_singleton_iff]
  obtain ⟨gL, hgLK, φ, hφ, hconv⟩ := hKcompact.tendsto_subseq hgK
  have hσLmem : ∀ θ ∈ (G.restrict C hCne hCsub).Θ,
      gL θ ∈ simplexOn ((G.restrict C hCne hCsub).M θ) := by
    intro θ hθ
    simp only [restrict_Θ] at hθ
    simp only [restrict_M]
    have := hgLK θ (Set.mem_univ θ)
    simpa only [if_pos hθ] using this
  refine ⟨τ, ⟨gL, hσLmem⟩, φ, hφ, ?_, ?_⟩
  · intro n θ hθ
    simp only [hτ, hg, if_pos hθ]
  · simpa only [Function.comp] using hconv

/--
The analytic core: the fixed-cell payoff set described via `G|_C`-strategies
is closed.
-/
lemma isClosed_payoffCellAux (G : DisclosureGame T Msg) (C : Finset T)
    (hCne : C.Nonempty) (hCsub : C ⊆ G.Θ) :
    IsClosed {w : ℝ | ∃ σ : Strategy (G.restrict C hCne hCsub),
        G.preimageSetFull σ.evidence ⊆ C ∧
        ∀ m ∈ σ.evidence, w ∈ G.V (σ.coalitionBelief m)} := by
  refine' isClosed_of_closure_subset _;
  intro w hw
  obtain ⟨ws, hws⟩ : ∃ ws : ℕ → ℝ, (∀ n, ws n ∈ {w | ∃ σ : Strategy (G.restrict C hCne hCsub), G.preimageSetFull σ.evidence ⊆ C ∧ ∀ m ∈ σ.evidence, w ∈ G.V (σ.coalitionBelief m)}) ∧ Filter.Tendsto ws Filter.atTop (nhds w) := by
    exact mem_closure_iff_seq_limit.mp hw;
  choose σ hσ using hws.1
  obtain ⟨τ, σL, φ, hφ, hagree, hτconv⟩ := exists_zeroed_convergent_subseq G C hCne hCsub σ
  have hτexcl : ∀ n, G.preimageSetFull (τ n).evidence ⊆ C := by
    intro n
    have h_eq : (τ n).evidence = (σ n).evidence := by
      apply evidence_eqOn; intro θ hθ; exact hagree n θ hθ;
    rw [h_eq]
    exact (hσ n).left
  have hτpay : ∀ n, ∀ m ∈ (τ n).evidence, ws n ∈ G.V ((τ n).coalitionBelief m) := by
    intro n m hm
    have h_eq : (τ n).coalitionBelief m = (σ n).coalitionBelief m := by
      apply coalitionBelief_eqOn; exact hagree n;
    generalize_proofs at *;
    rw [h_eq];
    grind +suggestions
  have hev : ∀ m ∈ σL.evidence, ∃ N, ∀ k ≥ N, m ∈ (τ (φ k)).evidence := by
    intro m hm
    obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ ∈ C, 0 < σL.σ θ₁ m := by
      obtain ⟨ θ₁, hθ₁ ⟩ := Set.mem_iUnion₂.mp hm
      generalize_proofs at *;
      exact ⟨ θ₁, hθ₁.1, hθ₁.2 ⟩
    generalize_proofs at *;
    have := tendsto_pi_nhds.mp hτconv θ₁ |> tendsto_pi_nhds.mp |> fun h => h m;
    exact Filter.eventually_atTop.mp ( this.eventually ( lt_mem_nhds hθ₁.2 ) ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun k hk => Set.mem_iUnion₂.mpr ⟨ θ₁, hθ₁.1, by simpa using hN k hk ⟩ ⟩
  use σL
  constructor
  ·
    intro θ hθ
    obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m ∈ G.M θ ∧ m ∈ σL.evidence := by
      simp_all +decide [ mem_preimageSet, DisclosureGame.preimageSetFull ];
      exact ⟨ hθ.2.choose, hθ.2.choose_spec.1, hθ.2.choose_spec.2 ⟩
    obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, m ∈ (τ (φ k)).evidence := hev m hm₂
    have hθ_in_C : θ ∈ C := by
      exact hτexcl ( φ N ) ( mem_preimageSet.mpr ⟨ by
        exact G.mem_preimageSet.mp hθ |>.1, by
        exact ⟨ m, hm₁, hN N le_rfl ⟩ ⟩ )
    exact hθ_in_C
  ·
    intro m hm
    obtain ⟨N, hN⟩ := hev m hm
    have hμs : ∀ j, (τ (φ (N + j))).coalitionBelief m ∈ simplexOn G.Θ := by
      intro j
      have hμs : (τ (φ (N + j))).belief m ∈ simplexOn C := by
        apply Strategy.belief_mem_simplex;
        exact hN _ ( Nat.le_add_right _ _ )
      have hμs' : (τ (φ (N + j))).coalitionBelief m ∈ simplexOn G.Θ := by
        exact zeroExt_mem_simplex hCsub hμs
      exact hμs'
    have hμL : σL.coalitionBelief m ∈ simplexOn G.Θ := by
      convert zeroExt_mem_simplex hCsub ( σL.belief_mem_simplex hm ) using 1
    have hμconv : Filter.Tendsto (fun j => (τ (φ (N + j))).coalitionBelief m) Filter.atTop (𝓝 (σL.coalitionBelief m)) := by
      apply coalitionBelief_tendsto;
      · exact hτconv.comp ( Filter.tendsto_atTop_mono ( fun k => Nat.le_add_left _ _ ) Filter.tendsto_id );
      · exact hm
    have hwsconv : Filter.Tendsto (fun j => ws (φ (N + j))) Filter.atTop (𝓝 w) := by
      exact hws.2.comp ( hφ.tendsto_atTop.comp ( Filter.tendsto_atTop_mono ( fun j => Nat.le_add_left _ _ ) Filter.tendsto_id ) )
    exact V_mem_of_tendsto G hμs hμL hμconv (fun j => hτpay (φ (N + j)) m (hN (N + j) (Nat.le_add_right N j))) hwsconv

/-- The set of coalition payoffs attainable with a **fixed cell `C`** is closed. -/
lemma isClosed_payoffCell (G : DisclosureGame T Msg) (C : Finset T)
    (hCne : C.Nonempty) (hCsub : C ⊆ G.Θ) :
    IsClosed {w : ℝ | ∃ K : Coalition G, K.C = C ∧ K.w = w} := by
  rw [payoffCell_eq G C hCne hCsub]
  exact isClosed_payoffCellAux G C hCne hCsub

/-- **`𝒲_R` is closed.** -/
lemma isClosed_coalitionPayoffs (G : DisclosureGame T Msg) :
    IsClosed G.coalitionPayoffs := by
  have hUnion : G.coalitionPayoffs =
      ⋃ C ∈ G.Θ.powerset, {w : ℝ | ∃ K : Coalition G, K.C = C ∧ K.w = w} := by
    ext w
    simp only [coalitionPayoffs, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe,
      Finset.mem_powerset, exists_prop]
    constructor
    · rintro ⟨K, rfl⟩; exact ⟨K.C, K.C_subset, K, rfl, rfl⟩
    · rintro ⟨C, _, K, _, rfl⟩; exact ⟨K, rfl⟩
  rw [hUnion]
  refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) ?_
  intro C hC
  by_cases hCne : C.Nonempty
  · exact isClosed_payoffCell G C hCne (Finset.mem_powerset.mp (Finset.mem_coe.mp hC))
  · have : {w : ℝ | ∃ K : Coalition G, K.C = C ∧ K.w = w} = ∅ := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨K, hKC, _⟩; exact hCne (hKC ▸ K.C_nonempty)
    rw [this]; exact isClosed_empty

/-- **Lemma 2** (coalition-compact): `𝒲_R` is compact. -/
lemma isCompact_coalitionPayoffs (G : DisclosureGame T Msg) :
    IsCompact G.coalitionPayoffs :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_coalitionPayoffs G, isBounded_coalitionPayoffs G⟩

end DisclosureGame

end CPD
