import CPD.CoalitionProof
import CPD.GreedyPrefix

/-!
# Auxiliary results for lexicographically maximal PBE partitions

Lexicographically maximal PBE partitions (Definition 11 and Proposition 3)
provide, when no coalition-proof PBE exists, the natural
fallback notion of "as good a PBE partition as possible," comparing PBE
partitions cell by cell, step by step, in the order of the partition. This
file collects the *axiom-free* machinery used by `CPD.LexMax` to build one:
agreement of residual sets `R_t` for two partitions that share a cell-prefix,
the padded payoff vector `padW` of a partition and its set `padWSet` (over
all PBE partitions, padded to a common length so they live in a single
finite-dimensional space), the general fact that a non-empty compact subset
of `Fin n → ℝ` has a lexicographically greatest element, invariance of
`IsPBE` under changing a sender strategy off the type space `Θ`, and
compactness of `padWSet`.

Keeping this separate from `LexMax` (which invokes PBE existence, hence the
`kakutani` axiom) lets these results stay axiom-free.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ### Agreement of residuals for partitions sharing a cell-prefix -/

/-- If two partitions share cells on every step before `t` (with `t` and `t'`
at the same numeric index), then their step-`t` prefix unions coincide. -/
lemma prefixCells_agree {P P' : Partition G}
    {t : Fin P.card} {t' : Fin P'.card} (htt' : (t : ℕ) = (t' : ℕ))
    (hagree : ∀ (s : Fin P.card) (s' : Fin P'.card),
      (s : ℕ) = (s' : ℕ) → (s : ℕ) < (t : ℕ) → P'.C s' = P.C s) :
    (Finset.univ.filter (fun s : Fin P.card => s < t)).biUnion P.C
      = (Finset.univ.filter (fun s' : Fin P'.card => s' < t')).biUnion P'.C := by
  ext x
  constructor <;> intro hx <;> obtain ⟨s, hs, hs'⟩ := Finset.mem_biUnion.mp hx <;>
    simp_all +decide [Finset.mem_filter]
  · refine ⟨⟨s.val, ?_⟩, ?_⟩
    · exact lt_of_lt_of_le hs (Nat.le_of_lt_succ (by linarith [Fin.is_lt t, Fin.is_lt t']))
    · generalize_proofs at *
      grind
  · refine ⟨⟨s, ?_⟩, ?_⟩
    · exact lt_of_lt_of_le hs (Nat.le_of_lt_succ (by linarith [Fin.is_lt t, Fin.is_lt t']))
    · generalize_proofs at *
      grind

/-- If two partitions share cells on every step before `t`, their step-`t`
residuals coincide. -/
lemma thetaStep_agree_of_prefix {P P' : Partition G}
    {t : Fin P.card} {t' : Fin P'.card} (htt' : (t : ℕ) = (t' : ℕ))
    (hagree : ∀ (s : Fin P.card) (s' : Fin P'.card),
      (s : ℕ) = (s' : ℕ) → (s : ℕ) < (t : ℕ) → P'.C s' = P.C s) :
    thetaStep P.C t = thetaStep P'.C t' := by
  rw [thetaStep_eq_prefixResidual P.C P.cover_eq P.C_subset P.C_disjoint t,
      thetaStep_eq_prefixResidual P'.C P'.cover_eq P'.C_subset P'.C_disjoint t']
  unfold prefixResidual
  rw [prefixCells_agree htt' hagree]

/-- The step-payoff sets agree when the residuals agree. -/
lemma stepPayoffs_agree_of_prefix {P P' : Partition G}
    {t : Fin P.card} {t' : Fin P'.card}
    (hR : thetaStep P.C t = thetaStep P'.C t') :
    P.stepPayoffs t = P'.stepPayoffs t' := by
  rw [Partition.stepPayoffs, Partition.stepPayoffs]
  grind

/-- The greedy lower bounds agree when the residuals agree. -/
lemma greedyLower_agree_of_prefix {P P' : Partition G}
    {t : Fin P.card} {t' : Fin P'.card}
    (hR : thetaStep P.C t = thetaStep P'.C t') :
    P.greedyLower t = P'.greedyLower t' := by
  unfold Partition.greedyLower
  grind +qlia

/-! ### Padded payoff vectors -/

open scoped Classical in
/-- The padded payoff vector of a partition, valued in `Fin (G.Θ.card) → ℝ`
(the number of steps never exceeds `|Θ|`).  Coordinates beyond `P.card` are
padded with `0`. -/
noncomputable def padW (P : Partition G) (i : Fin G.Θ.card) : ℝ :=
  if h : (i : ℕ) < P.card then P.w ⟨i, h⟩ else 0

variable (G) in
/-- The set of padded payoff vectors of PBE partitions. -/
def padWSet : Set (Fin G.Θ.card → ℝ) :=
  {v | ∃ P : Partition G, P.IsPBEPartition ∧ padW P = v}

/-- Value of `padW` at an in-range coordinate. -/
lemma padW_apply {P : Partition G} {i : Fin G.Θ.card} (h : (i : ℕ) < P.card) :
    padW P i = P.w ⟨(i : ℕ), h⟩ := dif_pos h

/-! ### A lexicographically greatest element of a compact set -/

/-- **General fact.** A nonempty compact subset of `Fin n → ℝ` (product
topology) has a lexicographically greatest element. -/
lemma exists_lex_isGreatest {n : ℕ} (V : Set (Fin n → ℝ))
    (hne : V.Nonempty) (hc : IsCompact V) :
    ∃ v ∈ V, ∀ w ∈ V, toLex w ≤ toLex v := by
  induction' n with n ih
  · obtain ⟨v, hv⟩ := hne; use v; aesop
  · obtain ⟨m, hm⟩ : ∃ m, IsGreatest (Set.image (fun v : Fin (n + 1) → ℝ => v 0) V) m := by
      apply_rules [IsCompact.exists_isGreatest, hc.image]
      · exact continuous_apply 0
      · exact hne.image _
    obtain ⟨v0, hv0⟩ : ∃ v0 ∈ V, v0 0 = m ∧ ∀ v ∈ V, v 0 = m →
        toLex (fun i => v (Fin.succ i)) ≤ toLex (fun i => v0 (Fin.succ i)) := by
      have hV0_compact : IsCompact (Set.image (fun v : Fin (n + 1) → ℝ => fun i => v (Fin.succ i))
          {v ∈ V | v 0 = m}) := by
        refine IsCompact.image ?_ ?_
        · exact hc.inter_right (isClosed_eq (continuous_apply 0) continuous_const)
        · fun_prop
      obtain ⟨v0, hv0⟩ := ih _ (Set.Nonempty.image _ <|
        show {v ∈ V | v 0 = m}.Nonempty from by rcases hm.1 with ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩)
        hV0_compact
      rcases hv0 with ⟨⟨v0, hv0, rfl⟩, hv0'⟩
      exact ⟨v0, hv0.1, hv0.2, fun v hv hv' => hv0' _ <| Set.mem_image_of_mem _ ⟨hv, hv'⟩⟩
    refine ⟨v0, hv0.1, fun w hw => ?_⟩
    by_cases hw0 : w 0 = m
    · by_cases h : toLex (fun i => w (Fin.succ i)) = toLex (fun i => v0 (Fin.succ i))
      · simp_all +decide [funext_iff, Fin.forall_fin_succ]
        exact le_of_eq (by congr; ext i; induction i using Fin.inductionOn <;> aesop)
      · obtain ⟨i, hi⟩ := lt_of_le_of_ne (hv0.2.2 w hw hw0) h
        refine le_of_lt ?_
        refine ⟨Fin.succ i, ?_, ?_⟩ <;> simp_all +decide [Fin.forall_fin_succ]
    · have h_lt : w 0 < m := lt_of_le_of_ne (hm.2 ⟨w, hw, rfl⟩) hw0
      exact le_of_lt (by exact ⟨0, by aesop⟩)

/-! ### Invariance of `IsPBE` under changing a strategy off `Θ` -/

/-
Induced beliefs depend only on the strategy's values on `G.Θ`.
-/
lemma belief_eqOn {s1 s2 : Strategy G} (h : ∀ θ ∈ G.Θ, s1.σ θ = s2.σ θ)
    (m : Msg) : s1.belief m = s2.belief m := by
  ext θ; by_cases hθ : θ ∈ G.Θ <;> simp_all +decide [ Strategy.onPathProb, Strategy.belief ] ;
  have := G.μ0_mem.2.2 θ hθ; aesop;

/-- Being a PBE strategy depends only on the values on `G.Θ`. -/
lemma isPBE_of_eqOn {s1 s2 : Strategy G} (h : ∀ θ ∈ G.Θ, s1.σ θ = s2.σ θ)
    (hs : G.IsPBE s1) : G.IsPBE s2 := by
  obtain ⟨μ, r, hsup⟩ := hs
  have hev : s2.evidence = s1.evidence := evidence_eqOn (fun θ hθ => (h θ hθ).symm)
  refine ⟨μ, r, ?_⟩
  refine { belief_system := hsup.belief_system, feasible := hsup.feasible,
           payoff_compat := hsup.payoff_compat, bayesian := ?_, seq_optimal := ?_ }
  · intro m hm
    rw [hsup.bayesian m (by rwa [hev] at hm), belief_eqOn h m]
  · intro θ hθ
    have : s2.msgSupport θ = s1.msgSupport θ := by
      unfold Strategy.msgSupport; rw [h θ hθ]
    rw [this]; exact hsup.seq_optimal θ hθ

/-! ### Fixed-cell residual payoffs, cell signatures and assembly -/

/-- The set of payoffs attainable by a coalition of the step-`t` residual game
of `Q` whose cell is exactly `Q.C t`. -/
noncomputable def stepPayoffCell (Q : Partition G) (t : Fin Q.card) : Set ℝ :=
  {x | ∃ K : Coalition (G.restrict (thetaStep Q.C t)
      (thetaStep_nonempty t (Q.C_nonempty t)) (Q.thetaStep_subset t)),
    K.C = Q.C t ∧ K.w = x}

/-
`stepPayoffCell` is closed.
-/
lemma isClosed_stepPayoffCell (Q : Partition G) (t : Fin Q.card) :
    IsClosed (stepPayoffCell Q t) := by
  convert isClosed_payoffCell ( G.restrict ( thetaStep Q.C t ) ( thetaStep_nonempty t ( Q.C_nonempty t ) ) ( Q.thetaStep_subset t ) ) ( Q.C t ) _ _ using 1;
  · exact Q.C_nonempty t;
  · exact Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_rfl ⟩ )

/-
The payoff `Q.w t` is attainable with the fixed cell `Q.C t`.
-/
lemma w_mem_stepPayoffCell (Q : Partition G) (t : Fin Q.card) :
    Q.w t ∈ stepPayoffCell Q t := by
  refine' ⟨ _, _, _ ⟩;
  use Q.C t;
  exact Q.C_nonempty t;
  exact Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_rfl ⟩ );
  exact ⟨ fun θ m => ( Q.σ t ).σ θ m, ( Q.σ t ).mem ⟩;
  convert Q.exclusive t using 1;
  exact Q.w t;
  convert Q.payoff t using 1;
  all_goals norm_num [ Strategy.evidence, Strategy.coalitionBelief ];
  grind +suggestions

/-- Pad a length-`n` payoff vector to a `Fin (G.Θ.card) → ℝ` vector with zeros. -/
noncomputable def padVec {n : ℕ} (w : Fin n → ℝ) (i : Fin G.Θ.card) : ℝ :=
  if h : (i : ℕ) < n then w ⟨i, h⟩ else 0

/-
**Assembly.** Given a cell structure `Q` and a payoff vector `w` that is
fixed-cell attainable at every step, individually rational, and antitone, there
is a PBE partition with those cells and payoffs; hence `padVec w ∈ padWSet`.
-/
lemma pbe_of_payoffs (Q : Partition G) (w : Fin Q.card → ℝ)
    (hstep : ∀ t, w t ∈ stepPayoffCell Q t)
    (hIR : ∀ t, ∀ θ ∈ Q.C t, G.skeptical θ ≤ w t)
    (hanti : Antitone w) :
    padVec w ∈ padWSet G := by
  unfold padVec padWSet;
  choose K hK₁ hK₂ using fun t => hstep t;
  obtain ⟨τ, hτ⟩ : ∃ τ : ∀ t : Fin Q.card, Strategy (G.restrict (Q.C t) (Q.C_nonempty t) (Q.C_subset t)), ∀ t : Fin Q.card, (τ t).evidence = (K t).σ.evidence ∧ ∀ m, (τ t).coalitionBelief m = (K t).σ.coalitionBelief m := by
    have h_restrict_eq : ∀ t : Fin Q.card, (G.restrict (thetaStep Q.C t) (thetaStep_nonempty t (Q.C_nonempty t)) (Q.thetaStep_subset t)).restrict (K t).C (K t).C_nonempty (K t).C_subset = G.restrict (Q.C t) (Q.C_nonempty t) (Q.C_subset t) := by
      intro t; exact (by
      convert restrict_restrict _ _ _ _ using 1;
      grind +splitImp);
    exact ⟨ fun t => Classical.choose ( gp_strategy_of_eq ( h_restrict_eq t ) ( K t |>.σ ) ), fun t => Classical.choose_spec ( gp_strategy_of_eq ( h_restrict_eq t ) ( K t |>.σ ) ) ⟩;
  use ⟨ Q.card, Q.C, Q.C_nonempty, Q.C_disjoint, Q.C_subset, Q.C_cover, τ, w, by
    intro t
    have := (K t).exclusive
    simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ], by
    intro t m hm
    have := (K t).payoff m
    simp_all +decide [ DisclosureGame.restrict_V ] ⟩
  generalize_proofs at *;
  exact ⟨ ⟨ hIR, hanti ⟩, rfl ⟩

/-- Signature of a partition's cell structure, valued in a finite type. -/
noncomputable def sigOf (Q : Partition G) :
    Fin (G.Θ.card + 1) × (Fin G.Θ.card → Finset T) :=
  (⟨Q.card, Nat.lt_succ_of_le Q.card_le⟩,
   fun i => if h : (i : ℕ) < Q.card then Q.C ⟨i, h⟩ else ∅)

/-
Equal signatures give equal cardinalities.
-/
lemma card_eq_of_sig {Q Q' : Partition G} (h : sigOf Q = sigOf Q') :
    Q.card = Q'.card := by
  convert congr_arg ( fun x : Fin ( G.Θ.card + 1 ) × ( Fin G.Θ.card → Finset T ) => x.1.val ) h using 1

/-
Equal signatures give equal cells at matching indices.
-/
lemma C_eq_of_sig {Q Q' : Partition G} (h : sigOf Q = sigOf Q')
    {t : Fin Q.card} {t' : Fin Q'.card} (ht : (t : ℕ) = (t' : ℕ)) :
    Q.C t = Q'.C t' := by
  convert congr_arg ( fun x : Fin ( G.Θ.card + 1 ) × ( Fin G.Θ.card → Finset T ) => x.2 ⟨ t, by
    exact lt_of_lt_of_le t.2 Q.card_le ⟩ ) h using 1
  generalize_proofs at *
  all_goals generalize_proofs at *;
  · simp +decide [ sigOf ];
  · unfold sigOf; aesop;

/-
Equal signatures give equal fixed-cell residual payoff sets.
-/
lemma stepPayoffCell_eq_of_sig {Q Q' : Partition G} (h : sigOf Q = sigOf Q')
    {t : Fin Q.card} {t' : Fin Q'.card} (ht : (t : ℕ) = (t' : ℕ)) :
    stepPayoffCell Q t = stepPayoffCell Q' t' := by
  have hR : thetaStep Q.C t = thetaStep Q'.C t' := by
    apply thetaStep_agree_of_prefix ht
    exact fun s s' hss _ => (C_eq_of_sig h hss).symm
  convert Set.ext _;
  intro x
  simp [stepPayoffCell, hR];
  rw [ C_eq_of_sig h ht ];
  grind +extAll

/-! ### Compactness of `padWSet` -/

/-
A uniform bound on all partition payoffs.
-/
lemma exists_payoff_bound (G : DisclosureGame T Msg) :
    ∃ M : ℝ, ∀ P : Partition G, ∀ t : Fin P.card, |P.w t| ≤ M := by
  obtain ⟨ M, hM ⟩ := exists_bound_V G;
  refine' ⟨ M, fun P t => _ ⟩;
  -- `P.w t ∈ G.V ((P.σ t).coalitionBelief m)` for some on-path `m ∈ (P.σ t).evidence`.
  obtain ⟨m, hm⟩ : ∃ m ∈ (P.σ t).evidence, P.w t ∈ G.V ((P.σ t).coalitionBelief m) := by
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ P.C t, ∃ m ∈ G.M θ₀, m ∈ (P.σ t).evidence := by
      obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ P.C t, θ₀ ∈ G.preimageSetFull (P.σ t).evidence := by
        refine P.C_nonempty t |> fun ⟨ θ₀, hθ₀ ⟩ => ⟨ θ₀, hθ₀, ?_ ⟩
        exact coalitionStrategy_subset_preimage (P.C_nonempty t) (P.C_subset t) (P.σ t) hθ₀
      simp_all +decide [ DisclosureGame.preimageSetFull ];
      simp_all +decide [ DisclosureGame.preimageSet ];
      exact ⟨ θ₀, hθ₀.1, by obtain ⟨ m, hm ⟩ := hθ₀.2.2; exact ⟨ m, by aesop ⟩ ⟩;
    exact ⟨ hθ₀.2.choose, hθ₀.2.choose_spec.2, P.payoff t _ hθ₀.2.choose_spec.2 ⟩;
  refine' hM _ _ _ hm.2;
  have := (P.σ t).belief_mem_simplex hm.1;
  convert zeroExt_mem_simplex ( P.C_subset t ) this using 1

/-
`padWSet` is bounded.
-/
lemma padWSet_bounded : Bornology.IsBounded (padWSet G) := by
  obtain ⟨ M, hM ⟩ := exists_payoff_bound G;
  refine' isBounded_iff_forall_norm_le.mpr ⟨ Max.max M 0, _ ⟩;
  rintro v ⟨ P, hP, rfl ⟩
  rw [ pi_norm_le_iff_of_nonneg ( by positivity ) ]
  intro i
  by_cases hi : ( i : ℕ ) < P.card <;> simp +decide [ *, padW ]

/-- `padWSet` is closed. -/
lemma padWSet_closed : IsClosed (padWSet G) := by
  apply isClosed_of_closure_subset
  intro v hv
  obtain ⟨vs, hmem, hlim⟩ := mem_closure_iff_seq_limit.mp hv
  choose P hP hPeq using hmem
  -- Pigeonhole: some cell signature occurs infinitely often along the sequence.
  obtain ⟨sig, hsig⟩ : ∃ b, {k | sigOf (P k) = b}.Infinite := by
    by_contra h; push_neg at h
    have huniv : (⋃ b, {k | sigOf (P k) = b}) = Set.univ := by ext k; simp
    exact Set.infinite_univ (huniv ▸ Set.finite_iUnion (fun b => h b))
  obtain ⟨ns, hns_tend, hns_sig⟩ :=
    Filter.exists_seq_forall_of_frequently (Nat.frequently_atTop_iff_infinite.mpr hsig)
  set Q := P (ns 0) with hQ
  have hsigQ : ∀ k, sigOf (P (ns k)) = sigOf Q := fun k => by rw [hns_sig k, hQ, hns_sig 0]
  have hcardk : ∀ k, (P (ns k)).card = Q.card := fun k => card_eq_of_sig (hsigQ k)
  have hΘ : Q.card ≤ G.Θ.card := Q.card_le
  have hvns : Filter.Tendsto (fun k => vs (ns k)) Filter.atTop (nhds v) := hlim.comp hns_tend
  set w : Fin Q.card → ℝ := fun t => v ⟨(t : ℕ), lt_of_lt_of_le t.2 hΘ⟩ with hwdef
  -- The step-`t` payoff sequence converges to `w t`.
  have hgtend : ∀ t : Fin Q.card,
      Filter.Tendsto (fun k => vs (ns k) ⟨(t : ℕ), lt_of_lt_of_le t.2 hΘ⟩)
        Filter.atTop (nhds (w t)) := by
    intro t
    have hc := (continuous_apply
      (⟨(t : ℕ), lt_of_lt_of_le t.2 hΘ⟩ : Fin G.Θ.card)).continuousAt.tendsto.comp hvns
    simpa [hwdef] using hc
  -- Each coordinate value equals the corresponding partition payoff.
  have hval : ∀ k, ∀ t : Fin Q.card,
      vs (ns k) ⟨(t : ℕ), lt_of_lt_of_le t.2 hΘ⟩
        = (P (ns k)).w ⟨(t : ℕ), by rw [hcardk k]; exact t.2⟩ := by
    intro k t
    rw [← hPeq (ns k), padW_apply (by rw [hcardk k]; exact t.2)]
  have hstep : ∀ t, w t ∈ stepPayoffCell Q t := by
    intro t
    refine (isClosed_stepPayoffCell Q t).mem_of_tendsto (hgtend t) ?_
    filter_upwards with k
    rw [hval k t]
    have hmem := w_mem_stepPayoffCell (P (ns k)) ⟨(t : ℕ), by rw [hcardk k]; exact t.2⟩
    rwa [stepPayoffCell_eq_of_sig (hsigQ k) rfl] at hmem
  have hIR : ∀ t, ∀ θ ∈ Q.C t, G.skeptical θ ≤ w t := by
    intro t θ hθ
    refine ge_of_tendsto (hgtend t) ?_
    filter_upwards with k
    rw [hval k t]
    refine (hP (ns k)).1 ⟨(t : ℕ), by rw [hcardk k]; exact t.2⟩ θ ?_
    rw [C_eq_of_sig (hsigQ k) rfl]; exact hθ
  have hanti : Antitone w := by
    intro i j hij
    refine le_of_tendsto_of_tendsto (hgtend j) (hgtend i) ?_
    filter_upwards with k
    rw [hval k j, hval k i]
    exact (hP (ns k)).2 (Fin.mk_le_mk.mpr hij)
  have hvw : v = padVec w := by
    funext i
    by_cases hi : (i : ℕ) < Q.card
    · rw [padVec, dif_pos hi]
    · rw [padVec, dif_neg hi]
      have hz : (fun k => vs (ns k) i) = fun _ => (0 : ℝ) := by
        funext k
        rw [← hPeq (ns k)]
        simp only [padW]
        rw [dif_neg (by rw [hcardk k]; exact hi)]
      have htend : Filter.Tendsto (fun k => vs (ns k) i) Filter.atTop (nhds (v i)) :=
        (continuous_apply i).continuousAt.tendsto.comp hvns
      rw [hz] at htend
      exact tendsto_nhds_unique htend tendsto_const_nhds
  rw [hvw]; exact pbe_of_payoffs Q w hstep hIR hanti

/-- `padWSet` is compact. -/
lemma padWSet_compact : IsCompact (padWSet G) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨padWSet_closed, padWSet_bounded⟩

end DisclosureGame

end CPD
