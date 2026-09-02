import CPD.Theorem2

/-!
# Theorem 2 under betweenness and genericity

This module proves the genericity branch of Theorem 2: with `V`
single-valued, `v̄` satisfying plain betweenness (B), and `G` generic
(Definition 12), the entire greedy theory (Algorithm 3) goes through with the
B*-only no-merge-up step (`btw_merging_impossible`) replaced by the
three-line generic bound (Lemma 6 `btw_merging` + Lemma 4 `value_id` +
`Generic` injectivity).

* `btw_generic_noHalt` / `btw_generic_existence` (**(i)**): no run of the greedy
  algorithm halts; every greedy prefix extends to a greedy partition; a
  coalition-proof PBE exists.
* `btw_generic_cppbe_iff_coe` (**(ii)**): a partition is a coalition-proof PBE
  partition iff it is a COE partition (`w_t = max 𝒲_t` and `w_t ≤ w_{t-1}` at
  every step).
* `btw_generic_unique` (**(iii)**): the coalition-proof PBE partition is
  essentially unique — same length, cells, and payoffs.

The private helpers below are fresh copies of the corresponding `Theorem2.lean`
machinery, re-derived under `Betweenness` + `Generic` in place of
`StrictBetweenness`, with `btw_no_merge` proved via the generic bound.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ### Generic no-merge bound and private infrastructure -/

/-- **No merging up under B + genericity.** Removing a coalition attaining
`max 𝒲_R` cannot raise the residual maximum. Replaces `btw_merging_impossible`
by `btw_merging` + `value_id` (`btw_attained_le`) + `Generic` injectivity. -/
private lemma btw_no_merge (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic)
    {Θt : Finset T} (hΘne : Θt.Nonempty) (hΘsub : Θt ⊆ G.Θ)
    (K : (G.restrict Θt hΘne hΘsub).Coalition)
    (hw : IsGreatest (G.restrict Θt hΘne hΘsub).coalitionPayoffs K.w)
    (hne' : (Θt \ K.C).Nonempty) (hsub' : (Θt \ K.C) ⊆ G.Θ) {w' : ℝ}
    (hw' : IsGreatest (G.restrict (Θt \ K.C) hne' hsub').coalitionPayoffs w') :
    w' ≤ K.w := by
  by_contra h
  obtain ⟨K', hK'⟩ := hw'.1
  subst hK'
  have hgt : K.w < K'.w := lt_of_not_ge h
  obtain ⟨_, hval⟩ := btw_merging hSV hB hΘne hΘsub K hw hne' K' hgt
  have hKval : G.vbar (G.condPrior K.C) = K.w :=
    (btw_attained_le hSV hB hΘne hΘsub K).1.symm
  have hunion : K.C ∪ K'.C = K.C := by
    apply hGen
    · exact ⟨K.C_nonempty.mono Finset.subset_union_left,
        Finset.union_subset (K.C_subset.trans hΘsub) (K'.C_subset.trans hsub')⟩
    · exact ⟨K.C_nonempty, K.C_subset.trans hΘsub⟩
    · exact hval.trans hKval.symm
  have hK'sub : K'.C ⊆ K.C := Finset.Subset.trans Finset.subset_union_right hunion.le
  obtain ⟨x, hx⟩ := K'.C_nonempty
  exact (Finset.mem_sdiff.mp (K'.C_subset hx)).2 (hK'sub hx)

/-- Under B + genericity, every greedy-prefix payoff equals the residual maximum.
Mirror of `btw_prefix_stepMax`, using the generic `btw_no_merge`. -/
private lemma btw_prefix_stepMax (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic)
    (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) (t : Fin Q.card) :
    Q.w t = sSup (Q.stepPayoffs t) := by
  revert t
  intro t
  induction' t with t ih
  induction' t using Nat.strong_induction_on with t ih
  refine' IsGreatest.unique ( hQ ⟨ t, ih ⟩ ) ⟨ _, fun x hx => _ ⟩
  · refine' ⟨ _, _, _ ⟩
    · exact isGreatest_sSup_coalitionPayoffs _ |>.1
    · apply Q.genResidual_greedyLower_le_sSup
      grind +qlia
    · intro t' ht'
      obtain ⟨K, hKC, hKw⟩ := prefix_cell_coalition Q t'
      have hKmax : IsGreatest (G.restrict (prefixResidual G.Θ Q.C t') (Q.prefixResidual_nonempty t') (Q.prefixResidual_subset t')).coalitionPayoffs K.w := by
        convert isGreatest_sSup_coalitionPayoffs _ using 1
        grind
      have hKmax' : IsGreatest (G.restrict (prefixResidual G.Θ Q.C t' \ K.C) (by
      have hKmax' : prefixResidual G.Θ Q.C t' \ K.C = prefixResidual G.Θ Q.C ⟨t, ih⟩ := by
        rw [ hKC, prefix_residual_step Q ht' ]
      exact hKmax'.symm ▸ Q.prefixResidual_nonempty ⟨ t, ih ⟩) (by
      exact fun x hx => Finset.mem_sdiff.mp hx |>.1 |> Finset.mem_sdiff.mp |>.1)).coalitionPayoffs (sSup (Q.stepPayoffs ⟨t, ih⟩)) := by
        have hKmax' : IsGreatest (G.restrict (prefixResidual G.Θ Q.C ⟨t, ih⟩) (Q.prefixResidual_nonempty ⟨t, ih⟩) (Q.prefixResidual_subset ⟨t, ih⟩)).coalitionPayoffs (sSup (Q.stepPayoffs ⟨t, ih⟩)) := by
          convert isGreatest_sSup_coalitionPayoffs _ using 1
        generalize_proofs at *
        convert hKmax' using 1
        convert Partition.restrict_eq_of_eq _ _ _ _ _ using 2
        any_goals exact prefixResidual G.Θ Q.C ⟨ t, ih ⟩
        any_goals assumption
        · simp +decide [ hKC, prefix_residual_step Q ht' ]
        · rfl
      generalize_proofs at *
      have := btw_no_merge hSV hB hGen ‹_› ‹_› K hKmax ‹_› ‹_› hKmax'
      linarith
  · exact ( isGreatest_sSup_coalitionPayoffs _ ).2 hx.1

/-- **Extension step under B + genericity.** Every greedy prefix has a non-empty
greedy constraint set at its final residual. Mirror of `two_prefix_extends`. -/
private theorem gen_prefix_extends (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic)
    (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) :
    Q.extensionConstraint.Nonempty := by
  have hRne := Q.finalResidual_nonempty
  have hRsub := Q.finalResidual_subset
  have h_gL_le_sSup : Q.finalResidual.sup' hRne G.skeptical ≤
      sSup ((G.restrict Q.finalResidual hRne hRsub).coalitionPayoffs) :=
    Q.genResidual_greedyLower_le_sSup Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
  by_cases hcard : Q.card = 0
  · refine ⟨sSup ((G.restrict Q.finalResidual hRne hRsub).coalitionPayoffs),
      (isGreatest_sSup_coalitionPayoffs _).1, h_gL_le_sSup, ?_⟩
    intro t ht; exact absurd ht (by omega)
  · have hpos : 0 < Q.card := Nat.pos_of_ne_zero hcard
    set lastIdx : Fin Q.card := ⟨Q.card - 1, by omega⟩ with hlast
    have hlasteq : (lastIdx : ℕ) + 1 = Q.card := by simp only [hlast]; omega
    have hwmax : Q.w lastIdx = sSup (Q.stepPayoffs lastIdx) :=
      btw_prefix_stepMax hSV hB hGen Q hQ lastIdx
    obtain ⟨K0, hK0C, hK0w⟩ := prefix_cell_coalition Q lastIdx
    have hK0great : IsGreatest
        (G.restrict (prefixResidual G.Θ Q.C lastIdx) (Q.prefixResidual_nonempty lastIdx)
          (Q.prefixResidual_subset lastIdx)).coalitionPayoffs K0.w := by
      rw [hK0w, hwmax]
      exact isGreatest_sSup_coalitionPayoffs _
    have hfinEq : prefixResidual G.Θ Q.C lastIdx \ K0.C = Q.finalResidual := by
      rw [hK0C]; exact (finalResidual_eq_step Q hlasteq).symm
    have hne' : (prefixResidual G.Θ Q.C lastIdx \ K0.C).Nonempty := by rw [hfinEq]; exact hRne
    have hsub' : (prefixResidual G.Θ Q.C lastIdx \ K0.C) ⊆ G.Θ :=
      Finset.sdiff_subset.trans (Q.prefixResidual_subset lastIdx)
    have hw'great : IsGreatest
        (G.restrict (prefixResidual G.Θ Q.C lastIdx \ K0.C) hne' hsub').coalitionPayoffs
        (sSup ((G.restrict (prefixResidual G.Θ Q.C lastIdx \ K0.C) hne' hsub').coalitionPayoffs)) :=
      isGreatest_sSup_coalitionPayoffs _
    have hle := btw_no_merge hSV hB hGen (Q.prefixResidual_nonempty lastIdx)
      (Q.prefixResidual_subset lastIdx) K0 hK0great hne' hsub' hw'great
    have hgameEq : G.restrict (prefixResidual G.Θ Q.C lastIdx \ K0.C) hne' hsub'
        = G.restrict Q.finalResidual hRne hRsub :=
      Partition.restrict_eq_of_eq hfinEq hne' hsub' hRne hRsub
    rw [hgameEq, hK0w] at hle
    refine ⟨sSup ((G.restrict Q.finalResidual hRne hRsub).coalitionPayoffs),
      (isGreatest_sSup_coalitionPayoffs _).1, h_gL_le_sSup, ?_⟩
    intro t ht
    have hte : t = lastIdx := by apply Fin.ext; simp only [hlast]; omega
    rw [hte]; exact hle

/-! ### Partition-level `stepMax` (the greedy step characterization) -/

/-- Transport a strategy along an equality of games. -/
private lemma btw_strategy_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂)
    (s : Strategy g₁) :
    ∃ s' : Strategy g₂, s'.evidence = s.evidence ∧
      ∀ m, s'.coalitionBelief m = s.coalitionBelief m := by
  subst h; exact ⟨s, rfl, fun _ => rfl⟩

/-- Coalition-payoff sets agree for equal games. -/
private lemma btw_coalitionPayoffs_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) :
    g₁.coalitionPayoffs = g₂.coalitionPayoffs := by
  subst h; rfl

/-- The cell `C_t` viewed as a coalition of the residual game `G|_{R_t}`. -/
private lemma btw_cell_coalition (P : Partition G) (t : Fin P.card) :
    ∃ K : (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t))
        (P.thetaStep_subset t)).Coalition,
      K.C = P.C t ∧ K.w = P.w t := by
  obtain ⟨K, hK⟩ : ∃ K : Coalition (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)), K.C = P.C t ∧ K.w = P.w t := by
    have h_eq : (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)).restrict (P.C t) (P.C_nonempty t) (by
    exact Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by rfl ⟩ ) |> Finset.Subset.trans <| Finset.Subset.refl _) = G.restrict (P.C t) (P.C_nonempty t) (P.C_subset t) := by
      exact restrict_restrict _ _ _ _
    obtain ⟨σ', hσ'⟩ := btw_strategy_of_eq h_eq.symm (P.σ t)
    refine' ⟨ ⟨ P.C t, _, _, σ', _, P.w t, _ ⟩, rfl, rfl ⟩ <;> simp_all +decide [ DisclosureGame.Coalition ]
    · convert P.exclusive t using 1
    · exact P.payoff t
  generalize_proofs at *
  use K

/-- The cell's pooling value equals its payoff (from `btw_attained_le`/`value_id`). -/
private lemma btw_cell_vbar (hSV : G.SingleValued) (hB : G.Betweenness)
    (P : Partition G) (t : Fin P.card) :
    G.vbar (G.condPrior (P.C t)) = P.w t := by
  obtain ⟨K, hKC, hKw⟩ := btw_cell_coalition P t
  have h := btw_attained_le hSV hB (thetaStep_nonempty t (P.C_nonempty t))
    (P.thetaStep_subset t) K
  rw [← hKC, ← hKw]; exact h.1.symm

/-- The `ℕ`-indexed residual `R_n := ⋃_{(s:ℕ) ≥ n} C_s`. -/
private noncomputable def btwRn (P : Partition G) (n : ℕ) : Finset T :=
  (Finset.univ.filter (fun s : Fin P.card => n ≤ (s : ℕ))).biUnion P.C

private lemma btw_thetaStep_eq_Rn (P : Partition G) (t : Fin P.card) :
    thetaStep P.C t = btwRn P (t : ℕ) := by
  ext; simp [thetaStep, btwRn]

private lemma btwRn_zero (P : Partition G) : btwRn P 0 = G.Θ := by
  unfold btwRn; simp +decide [ P.cover_eq ]

private lemma btwRn_nonempty_iff (P : Partition G) (n : ℕ) :
    (btwRn P n).Nonempty ↔ n < P.card := by
  constructor <;> intro hn
  · obtain ⟨ θ, hθ ⟩ := hn
    obtain ⟨ s, hs, hθ ⟩ := Finset.mem_biUnion.mp hθ
    exact lt_of_le_of_lt ( Finset.mem_filter.mp hs |>.2 ) ( Fin.is_lt s )
  · exact ⟨ _, Finset.mem_biUnion.mpr ⟨ ⟨ n, hn ⟩, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_rfl ⟩, Finset.mem_coe.mpr ( P.C_nonempty ⟨ n, hn ⟩ |> Classical.choose_spec ) ⟩ ⟩

private lemma btwRn_succ (P : Partition G) {n : ℕ} (h : n < P.card) :
    btwRn P (n + 1) = btwRn P n \ P.C ⟨n, h⟩ := by
  refine' Finset.Subset.antisymm _ _
  · intro x hx; simp_all +decide [ btwRn ]
    obtain ⟨ a, ha₁, ha₂ ⟩ := hx; refine' ⟨ ⟨ a, le_of_lt ha₁, ha₂ ⟩, _ ⟩; intro ha₃; have := P.C_disjoint a ⟨ n, h ⟩; simp_all +decide [ Fin.ext_iff ]
    exact Finset.disjoint_left.mp ( this ( ne_of_gt ha₁ ) ) ha₂ ha₃
  · intro x hx; simp_all +decide [ btwRn ]
    obtain ⟨ ⟨ a, ha₁, ha₂ ⟩, ha₃ ⟩ := hx; exact ⟨ a, lt_of_le_of_ne ha₁ ( Ne.symm <| by rintro rfl; exact ha₃ ha₂ ), ha₂ ⟩

/-- **Step characterization under B + genericity.** Every greedy partition
attains the unconstrained residual maximum at every step. Mirror of
`two_greedy_stepMax`. -/
private theorem gen_greedy_stepMax (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic)
    (P : Partition G) (hP : P.IsGreedy) (t : Fin P.card) :
    P.w t = P.stepMax t := by
  induction' t with t ih
  induction' t using Nat.strong_induction_on with t ih generalizing P
  have := hP ⟨ t, ih ⟩
  refine' this.unique ⟨ _, fun w hw => _ ⟩
  · refine' ⟨ _, _, _ ⟩
    · exact P.isGreatest_stepMax ⟨ t, ih ⟩ |>.1
    · exact P.greedyLower_le_stepMax ⟨ t, ih ⟩
    · intro t' ht'
      obtain ⟨K, hKC, hKw⟩ := btw_cell_coalition P t'
      have h_ne : (thetaStep P.C t' \ K.C).Nonempty := by
        convert thetaStep_nonempty ⟨ t, ih ⟩ ( P.C_nonempty ⟨ t, ih ⟩ ) using 1
        rw [ hKC, btw_thetaStep_eq_Rn, btw_thetaStep_eq_Rn ]
        rw [ ← ht', btwRn_succ ]
      have h_sub : (thetaStep P.C t' \ K.C) ⊆ G.Θ := by
        exact Finset.sdiff_subset.trans ( P.thetaStep_subset t' )
      have h_w : IsGreatest (G.restrict (thetaStep P.C t' \ K.C) h_ne h_sub).coalitionPayoffs (P.stepMax ⟨t, ih⟩) := by
        convert P.isGreatest_stepMax ⟨ t, ih ⟩ using 1
        convert btw_coalitionPayoffs_of_eq _ using 2
        congr! 1
        rw [ hKC, btw_thetaStep_eq_Rn, btw_thetaStep_eq_Rn ]
        exact btwRn_succ P ( by linarith ) ▸ by aesop
      have h_no_merge_up : ∀ w', IsGreatest (G.restrict (thetaStep P.C t' \ K.C) h_ne h_sub).coalitionPayoffs w' → w' ≤ K.w := by
        apply btw_no_merge
        · exact hSV
        · exact hB
        · exact hGen
        · convert P.isGreatest_stepMax t' using 1
          rw [ hKw, ‹∀ m < t, ∀ ( P : G.Partition ), P.IsGreedy → ∀ ( ih : m < P.card ), P.w ⟨ m, ih ⟩ = P.stepMax ⟨ m, ih ⟩ › _ ( by linarith ) _ hP ( by linarith ) ]
      exact le_trans ( h_no_merge_up _ h_w ) ( by linarith )
  · exact P.isGreatest_stepMax ⟨ t, ih ⟩ |>.2 hw.1

/-! ### COE uniqueness -/

/-- If two COE partitions share the residual at level `n`, their `n`-th cells and
payoffs coincide. Mirror of `btw_coe_cell_match`. -/
private lemma btw_coe_cell_match (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic)
    (P P' : Partition G) (hP : P.IsCOE) (hP' : P'.IsCOE) {n : ℕ}
    (hres : btwRn P n = btwRn P' n) (hPlt : n < P.card) (hP'lt : n < P'.card) :
    P.C ⟨n, hPlt⟩ = P'.C ⟨n, hP'lt⟩ ∧ P.w ⟨n, hPlt⟩ = P'.w ⟨n, hP'lt⟩ := by
  have h_stepPayoffs_eq : P.stepPayoffs ⟨n, hPlt⟩ = P'.stepPayoffs ⟨n, hP'lt⟩ := by
    convert btw_coalitionPayoffs_of_eq _
    congr! 1
  have h_payoff_eq : P.w ⟨n, hPlt⟩ = P'.w ⟨n, hP'lt⟩ := by
    exact IsGreatest.unique ( hP ⟨ n, hPlt ⟩ |>.1 ) ( h_stepPayoffs_eq ▸ hP' ⟨ n, hP'lt ⟩ |>.1 )
  have h_cell_eq : G.vbar (G.condPrior (P.C ⟨n, hPlt⟩)) = G.vbar (G.condPrior (P'.C ⟨n, hP'lt⟩)) := by
    convert h_payoff_eq using 1
    · exact btw_cell_vbar hSV hB P ⟨ n, hPlt ⟩
    · exact btw_cell_vbar hSV hB P' ⟨ n, hP'lt ⟩
  have := hGen ( show P.C ⟨ n, hPlt ⟩ ∈ { C : Finset T | C.Nonempty ∧ C ⊆ G.Θ } from ⟨ P.C_nonempty _, P.C_subset _ ⟩ ) ( show P'.C ⟨ n, hP'lt ⟩ ∈ { C : Finset T | C.Nonempty ∧ C ⊆ G.Θ } from ⟨ P'.C_nonempty _, P'.C_subset _ ⟩ ); aesop

/-- Two COE partitions have the same residuals at every level. Mirror of
`btw_coe_residual_eq`. -/
private lemma btw_coe_residual_eq (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic)
    (P P' : Partition G) (hP : P.IsCOE) (hP' : P'.IsCOE) (n : ℕ) :
    btwRn P n = btwRn P' n := by
  induction' n with n ih
  · rw [ btwRn_zero, btwRn_zero ]
  · by_cases hn : n < P.card <;> by_cases hn' : n < P'.card
    · rw [ btwRn_succ P hn, btwRn_succ P' hn', ih ]
      rw [ btw_coe_cell_match hSV hB hGen P P' hP hP' ih hn hn' |>.1 ]
    · have := btwRn_nonempty_iff P n; have := btwRn_nonempty_iff P' n; simp_all +decide
      linarith
    · simp_all +decide
      have h_empty : btwRn P n = ∅ := by
        exact Finset.eq_empty_of_forall_notMem fun x hx => by have := btwRn_nonempty_iff P n; exact this.mp ⟨ x, hx ⟩ |> not_lt_of_ge hn
      simp_all +decide [ Finset.ext_iff ]
      simp_all +decide [ btwRn ]
      grind
    · rw [ show btwRn P ( n + 1 ) = ∅ from Finset.not_nonempty_iff_eq_empty.mp ( by simpa using btwRn_nonempty_iff P ( n + 1 ) |>.not.mpr ( by linarith ) ), show btwRn P' ( n + 1 ) = ∅ from Finset.not_nonempty_iff_eq_empty.mp ( by simpa using btwRn_nonempty_iff P' ( n + 1 ) |>.not.mpr ( by linarith ) ) ]

/-- Essential uniqueness for COE partitions under genericity. Mirror of
`btw_coe_unique`. -/
private lemma btw_coe_unique (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic)
    (P P' : Partition G) (hP : P.IsCOE) (hP' : P'.IsCOE) :
    P.card = P'.card ∧
      ∀ (t : Fin P.card) (t' : Fin P'.card), (t : ℕ) = (t' : ℕ) →
        P.C t = P'.C t' ∧ P.w t = P'.w t' := by
  have hcard : P.card = P'.card := by
    have hiff : ∀ n : ℕ, n < P.card ↔ n < P'.card := by
      intro n
      rw [← btwRn_nonempty_iff P n, ← btwRn_nonempty_iff P' n,
        btw_coe_residual_eq hSV hB hGen P P' hP hP' n]
    rcases lt_trichotomy P.card P'.card with h | h | h
    · exact absurd ((hiff P.card).mpr h) (lt_irrefl _)
    · exact h
    · exact absurd ((hiff P'.card).mp h) (lt_irrefl _)
  refine ⟨hcard, ?_⟩
  intro t t' htt'
  have hPlt : (t : ℕ) < P.card := t.isLt
  have hP'lt : (t : ℕ) < P'.card := by have := t'.isLt; omega
  have hmatch := btw_coe_cell_match hSV hB hGen P P' hP hP'
    (btw_coe_residual_eq hSV hB hGen P P' hP hP' (t : ℕ)) hPlt hP'lt
  have ht : t = (⟨(t : ℕ), hPlt⟩ : Fin P.card) := by ext; rfl
  have ht' : t' = (⟨(t : ℕ), hP'lt⟩ : Fin P'.card) := by ext; exact htt'.symm
  rw [ht, ht']
  exact hmatch

/-! ### Empty greedy prefix -/

/-- The empty greedy prefix (`card = 0`), whose residual is all of `Θ`. -/
private noncomputable def btwEmptyPrefix : G.GreedyPrefix where
  card := 0
  C := Fin.elim0
  C_nonempty := fun t => t.elim0
  C_disjoint := fun s => s.elim0
  C_subset := fun t => t.elim0
  residual_nonempty := by simpa using G.Θ_nonempty
  σ := fun t => t.elim0
  w := fun t => t.elim0
  exclusive := fun t => t.elim0
  payoff := fun t => t.elim0

private lemma btwEmptyPrefix_isGreedy : (btwEmptyPrefix (G := G)).IsGreedy :=
  fun t => t.elim0

/-! ### Theorem 2 under betweenness and genericity -/

/-- **Theorem 2(i), genericity branch, no-halt form.** Under single-valued `V`, B,
and genericity, every greedy prefix extends to a greedy partition of `G`; no
run of the greedy algorithm halts. -/
theorem btw_generic_noHalt (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic) (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) :
    ∃ P : Partition G, P.IsGreedy ∧ Q.card ≤ P.card ∧
      ∀ (s : Fin Q.card) (t : Fin P.card), (s : ℕ) = (t : ℕ) →
        P.C t = Q.C s ∧ P.w t = Q.w s :=
  extend_engine (fun Q' hQ' => gen_prefix_extends hSV hB hGen Q' hQ') Q hQ

/-- **Theorem 2(i), genericity branch.** Under single-valued `V`, B, and
genericity, a coalition-proof PBE exists. -/
theorem btw_generic_existence (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic) :
    ∃ P : Partition G, P.IsCPPBEPartition := by
  obtain ⟨P, hP, _, _⟩ := btw_generic_noHalt hSV hB hGen btwEmptyPrefix btwEmptyPrefix_isGreedy
  exact ⟨P, P.cppbe_characterization.mpr hP⟩

/-- **Theorem 2(ii), genericity branch.** Under single-valued `V`, B, and
genericity, a partition is a coalition-proof PBE partition iff it is a COE
partition: `w_t = max 𝒲_t` and `w_t ≤ w_{t-1}` at every step. -/
theorem btw_generic_cppbe_iff_coe (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic) (P : Partition G) :
    P.IsCPPBEPartition ↔ P.IsCOE := by
  constructor
  · intro h
    have hg := P.cppbe_characterization.mp h
    refine (Partition.isCOE_iff_of_greedy hg).mpr ?_
    intro t t' ht'
    rw [← gen_greedy_stepMax hSV hB hGen P hg t]
    exact (hg t).1.2.2 t' ht'
  · intro h
    exact h.isCPPBEPartition

/-- **Theorem 2, essential uniqueness under genericity.** Under single-valued `V`, B, and
genericity, the coalition-proof PBE partition is essentially unique: any two
have the same length, the same cells, and the same payoffs. -/
theorem btw_generic_unique (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic) (P P' : Partition G)
    (hP : P.IsCPPBEPartition) (hP' : P'.IsCPPBEPartition) :
    P.card = P'.card ∧
      ∀ (t : Fin P.card) (t' : Fin P'.card), (t : ℕ) = (t' : ℕ) →
        P.C t = P'.C t' ∧ P.w t = P'.w t' := by
  have hPg : P.IsGreedy := P.cppbe_characterization.mp hP
  have hP'g : P'.IsGreedy := P'.cppbe_characterization.mp hP'
  refine btw_coe_unique hSV hB hGen P P' ?_ ?_
  · refine (Partition.isCOE_iff_of_greedy hPg).mpr ?_
    intro t t' ht'
    rw [← gen_greedy_stepMax hSV hB hGen P hPg t]
    exact (hPg t).1.2.2 t' ht'
  · refine (Partition.isCOE_iff_of_greedy hP'g).mpr ?_
    intro t t' ht'
    rw [← gen_greedy_stepMax hSV hB hGen P' hP'g t]
    exact (hP'g t).1.2.2 t' ht'

end DisclosureGame

end CPD
