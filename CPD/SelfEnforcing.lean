import CPD.Theorem2
import Mathlib

/-!
# Self-enforcing blocking (Definition 22, Proposition 6)

This file proves robustness of the one-shot blocking test: under each of the existence regimes
(QC* + M-C; QC + M-C + genericity; single-valued `V` + B*), a PBE partition is
coalition-proof iff it admits no *self-enforcing* blocking coalition — one
that is itself the first coalition of a coalition-proof PBE partition of the
residual game it addresses.

"First coalition" is encoded as agreement of the index-0 cell and payoff (the
strategy lives in a cell-dependent type; the results below consume only
cell + payoff, as elsewhere in this development).
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

namespace Partition

variable {P : Partition G}

/-- **Definition 22** (self-enforcing blocking coalition). A
blocking coalition `(C̃, σ̃, w̃)` of `Π` is *self-enforcing* if it is the first
coalition of some coalition-proof PBE partition of `G|_{Θ(w̃)}`. -/
def BlockingCoalition.SelfEnforcing (B : P.BlockingCoalition) : Prop :=
  ∃ P' : Partition (G.restrict (P.thetaBelow B.wtil) B.theta_ne
      (P.thetaBelow_subset B.wtil)),
    P'.IsCPPBEPartition ∧
    ∃ h0 : 0 < P'.card,
      P'.C ⟨0, h0⟩ = B.K.C ∧ P'.w ⟨0, h0⟩ = B.K.w

end Partition

/-! ## Helper infrastructure for the self-enforcing-blocking proposition -/

/-- Coalition-payoff sets agree for equal games. -/
private lemma se_coalitionPayoffs_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) :
    g₁.coalitionPayoffs = g₂.coalitionPayoffs := by
  subst h; rfl

/-- Transport a coalition along an equality of games, preserving cell and payoff. -/
private lemma se_coalition_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂)
    (K : g₁.Coalition) : ∃ K' : g₂.Coalition, K'.C = K.C ∧ K'.w = K.w := by
  subst h; exact ⟨K, rfl, rfl⟩

/-- QC* implies QC. -/
private lemma se_qcStar_qc (hQCs : G.QCStar) : G.QC := by
  intro μ hμ μ' hμ' l hl
  by_cases h : μ = μ'
  · simp +decide [h, ← add_mul]
  · exact le_of_lt (hQCs μ hμ μ' hμ' h l hl)

/-- Single-valuedness is inherited by restricted games. -/
private lemma se_restrict_singleValued {S : Finset T} (hne : S.Nonempty)
    (hsub : S ⊆ G.Θ) (hSV : G.SingleValued) :
    (G.restrict S hne hsub).SingleValued := by
  intro μ hμ
  have hGμ : μ ∈ simplexOn G.Θ := simplexOn_mono hsub hμ
  convert hSV μ hGμ using 1

/-- Every partition has at least one cell. -/
private lemma se_card_pos {H : DisclosureGame T Msg} (Q : Partition H) : 0 < Q.card := by
  rcases Nat.eq_zero_or_pos Q.card with h0 | h
  · exfalso
    obtain ⟨θ, hθ⟩ := H.Θ_nonempty
    have hcov := Q.C_cover hθ
    rw [Finset.mem_biUnion] at hcov
    obtain ⟨t, -, -⟩ := hcov
    have := t.isLt; omega
  · exact h

/-- The residual set of the successor step is the residual set minus the current
cell. -/
private lemma se_thetaStep_succ (P : Partition G) {n : ℕ} (h1 : n < P.card)
    (h2 : n + 1 < P.card) :
    thetaStep P.C ⟨n + 1, h2⟩ = thetaStep P.C ⟨n, h1⟩ \ P.C ⟨n, h1⟩ := by
  ext x
  simp only [thetaStep, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff, Fin.le_def]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨⟨s, by omega, hx⟩, ?_⟩
    intro hxn
    have hval : (s : ℕ) ≠ n := by omega
    exact Finset.disjoint_left.mp
      (P.C_disjoint ⟨n, h1⟩ s (fun he => hval (by rw [← he]))) hxn hx
  · rintro ⟨⟨s, hs, hx⟩, hxn⟩
    refine ⟨s, ?_, hx⟩
    rcases Nat.lt_or_ge (s : ℕ) (n + 1) with hlt | hge
    · exfalso
      have hsn : s = ⟨n, h1⟩ := Fin.ext (by change (s : ℕ) = n; omega)
      exact hxn (hsn ▸ hx)
    · omega

/-- Transport a strategy along an equality of games, preserving evidence and
beliefs. -/
private lemma se_strategy_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂)
    (s : Strategy g₁) :
    ∃ s' : Strategy g₂, s'.evidence = s.evidence ∧
      ∀ m, s'.coalitionBelief m = s.coalitionBelief m := by
  subst h; exact ⟨s, rfl, fun _ => rfl⟩

/-- The cell at step `t` of a partition, viewed as a coalition of the residual
game `G|_{R_t}`. -/
private lemma se_cell_coalition (P : Partition G) (t : Fin P.card) :
    ∃ K : (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t))
        (P.thetaStep_subset t)).Coalition,
      K.C = P.C t ∧ K.w = P.w t := by
  obtain ⟨K, hK⟩ : ∃ K : Coalition (G.restrict (thetaStep P.C t)
      (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)),
      K.C = P.C t ∧ K.w = P.w t := by
    have h_eq : (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t))
        (P.thetaStep_subset t)).restrict (P.C t) (P.C_nonempty t) (by
          exact Finset.subset_biUnion_of_mem _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rfl⟩) |> Finset.Subset.trans <|
            Finset.Subset.refl _) = G.restrict (P.C t) (P.C_nonempty t) (P.C_subset t) := by
      exact restrict_restrict _ _ _ _
    obtain ⟨σ', hσ'⟩ := se_strategy_of_eq h_eq.symm (P.σ t)
    refine' ⟨⟨P.C t, _, _, σ', _, P.w t, _⟩, rfl, rfl⟩ <;>
      simp_all +decide
    · convert P.exclusive t using 1
    · exact P.payoff t
  generalize_proofs at *
  use K

/-- The first cell of a partition, viewed as a coalition of the whole game. -/
private lemma se_first_coalition {H : DisclosureGame T Msg} (Q : Partition H)
    (h0 : 0 < Q.card) :
    ∃ K : H.Coalition, K.C = Q.C ⟨0, h0⟩ ∧ K.w = Q.w ⟨0, h0⟩ := by
  have hfilter : (Finset.univ.filter
      (fun s : Fin Q.card => (⟨0, h0⟩ : Fin Q.card) ≤ s)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro s _
    rw [Fin.le_def]; exact Nat.zero_le _
  have hset : thetaStep Q.C ⟨0, h0⟩ = H.Θ := by
    rw [thetaStep, hfilter, ← Q.cover_eq]
  have hgame : H.restrict (thetaStep Q.C ⟨0, h0⟩)
      (thetaStep_nonempty ⟨0, h0⟩ (Q.C_nonempty ⟨0, h0⟩)) (Q.thetaStep_subset ⟨0, h0⟩) = H := by
    rw [Partition.restrict_eq_of_eq (G := H) hset
      (thetaStep_nonempty ⟨0, h0⟩ (Q.C_nonempty ⟨0, h0⟩)) (Q.thetaStep_subset ⟨0, h0⟩)
      H.Θ_nonempty subset_rfl]
    exact restrict_self
  obtain ⟨K0, hK0C, hK0w⟩ := se_cell_coalition Q ⟨0, h0⟩
  obtain ⟨K, hKC, hKw⟩ := se_coalition_of_eq hgame K0
  exact ⟨K, hKC.trans hK0C, hKw.trans hK0w⟩

/-- For a greedy partition, the first payoff equals the (unconstrained) residual
maximum, since the step-1 window carries no upper constraint. -/
private lemma se_greedy_first_stepMax {H : DisclosureGame T Msg} {Q : Partition H}
    (hg : Q.IsGreedy) (h0 : 0 < Q.card) :
    Q.w ⟨0, h0⟩ = Q.stepMax ⟨0, h0⟩ := by
  have hg0 := hg ⟨0, h0⟩
  refine le_antisymm ?_ ?_
  · exact (Q.isGreatest_stepMax ⟨0, h0⟩).2 hg0.1.1
  · apply hg0.2
    refine ⟨(Q.isGreatest_stepMax ⟨0, h0⟩).1, Q.greedyLower_le_stepMax ⟨0, h0⟩, ?_⟩
    intro t' ht'
    exact absurd ht' (by simp)

/-- The "no merging up" property: removing a cell attaining the residual maximum
cannot raise the residual maximum. -/
private def NoMergeUp (G : DisclosureGame T Msg) : Prop :=
  ∀ (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (K : (G.restrict S hne hsub).Coalition),
    IsGreatest (G.restrict S hne hsub).coalitionPayoffs K.w →
    ∀ (hne' : (S \ K.C).Nonempty) {w' : ℝ},
    IsGreatest (G.restrict (S \ K.C) hne'
        (Finset.sdiff_subset.trans hsub)).coalitionPayoffs w' →
    w' ≤ K.w

/-- Genericity gives the no-merging-up property (reproves `no_merge_up`). -/
private lemma se_noMergeUp_generic (hQC : G.QC) (hMC : G.MC) (hGen : G.Generic) :
    NoMergeUp G := by
  intro S hne hsub K hw hne' w' hw'
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨Kt, hss, hKtw, hvbarK, hvbarKt⟩ := merging hQC hMC hne hsub K hw hne' hw' hcon
  have hne_Kt : Kt.C.Nonempty := K.C_nonempty.mono hss.subset
  have hEq : K.C = Kt.C :=
    hGen ⟨K.C_nonempty, K.C_subset.trans hsub⟩ ⟨hne_Kt, Kt.C_subset.trans hsub⟩
      (by simp only; rw [hvbarK, hvbarKt])
  exact hss.ne hEq

/-- QC* gives the no-merging-up property. -/
private lemma se_noMergeUp_qcstar (hMC : G.MC) (hQCs : G.QCStar) : NoMergeUp G := by
  intro S hne hsub K hw hne' w' hw'
  exact qcstar_no_merge (se_qcStar_qc hQCs) hMC hQCs hne hsub K hw hne'
    (Finset.sdiff_subset.trans hsub) hw'

/-- B* (with single-valued `V`) gives the no-merging-up property. -/
private lemma se_noMergeUp_bstar (hSV : G.SingleValued) (hB : G.StrictBetweenness) :
    NoMergeUp G := by
  intro S hne hsub K hw hne' w' hw'
  obtain ⟨K', hK'⟩ := hw'.1
  have := btw_merging_impossible hSV hB hne hsub K hw hne' K'
  rwa [hK'] at this

/-- Under `NoMergeUp` and antitone payoffs, the residual maximum at a successor
step is bounded by the payoff of the current step, provided that step already
attains its own residual maximum. -/
private lemma se_stepMax_le_pred (P : Partition G)
    (hNM : NoMergeUp G) {n : ℕ} (h1 : n < P.card) (h2 : n + 1 < P.card)
    (hpred : P.w ⟨n, h1⟩ = P.stepMax ⟨n, h1⟩) :
    P.stepMax ⟨n + 1, h2⟩ ≤ P.w ⟨n, h1⟩ := by
  obtain ⟨K, hKC, hKw⟩ := se_cell_coalition P ⟨n, h1⟩
  have hmax : IsGreatest (G.restrict (thetaStep P.C ⟨n, h1⟩)
      (thetaStep_nonempty ⟨n, h1⟩ (P.C_nonempty ⟨n, h1⟩))
      (P.thetaStep_subset ⟨n, h1⟩)).coalitionPayoffs K.w := by
    rw [hKw, hpred]; exact P.isGreatest_stepMax ⟨n, h1⟩
  have hsucc : thetaStep P.C ⟨n, h1⟩ \ K.C = thetaStep P.C ⟨n + 1, h2⟩ := by
    rw [hKC]; exact (se_thetaStep_succ P h1 h2).symm
  have hne' : (thetaStep P.C ⟨n, h1⟩ \ K.C).Nonempty := by
    rw [hsucc]; exact thetaStep_nonempty ⟨n + 1, h2⟩ (P.C_nonempty ⟨n + 1, h2⟩)
  have hw' : IsGreatest (G.restrict (thetaStep P.C ⟨n, h1⟩ \ K.C) hne'
      (Finset.sdiff_subset.trans (P.thetaStep_subset ⟨n, h1⟩))).coalitionPayoffs
      (P.stepMax ⟨n + 1, h2⟩) := by
    have hg2 : G.restrict (thetaStep P.C ⟨n, h1⟩ \ K.C) hne'
        (Finset.sdiff_subset.trans (P.thetaStep_subset ⟨n, h1⟩))
        = G.restrict (thetaStep P.C ⟨n + 1, h2⟩)
          (thetaStep_nonempty ⟨n + 1, h2⟩ (P.C_nonempty ⟨n + 1, h2⟩))
          (P.thetaStep_subset ⟨n + 1, h2⟩) :=
      Partition.restrict_eq_of_eq (G := G) hsucc _ _ _ _
    rw [se_coalitionPayoffs_of_eq hg2]
    exact P.isGreatest_stepMax ⟨n + 1, h2⟩
  have hfin := hNM (thetaStep P.C ⟨n, h1⟩)
    (thetaStep_nonempty ⟨n, h1⟩ (P.C_nonempty ⟨n, h1⟩)) (P.thetaStep_subset ⟨n, h1⟩)
    K hmax hne' hw'
  rw [hKw] at hfin
  exact hfin

/-- The residual coalition-payoff set of the first step of a CPPBE partition of
`G|_{Θ(w̃)}` coincides with the step-`t₀` residual coalition-payoff set of `P`,
when `Θ(w̃) = R_{t₀}`. -/
private lemma se_stepPayoffs_eq (P : Partition G) {wt : ℝ} {t0 : Fin P.card}
    (theta_ne : (P.thetaBelow wt).Nonempty)
    (hheq : P.thetaBelow wt = thetaStep P.C t0)
    (Q : Partition (G.restrict (P.thetaBelow wt) theta_ne (P.thetaBelow_subset wt)))
    (h0 : 0 < Q.card) :
    Q.stepPayoffs ⟨0, h0⟩ = P.stepPayoffs t0 := by
  have hfilter : (Finset.univ.filter
      (fun s : Fin Q.card => (⟨0, h0⟩ : Fin Q.card) ≤ s)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro s _
    rw [Fin.le_def]; exact Nat.zero_le _
  have hsetQ : thetaStep Q.C ⟨0, h0⟩ = P.thetaBelow wt := by
    rw [thetaStep, hfilter]; exact Q.cover_eq.symm
  have hgameQ : (G.restrict (P.thetaBelow wt) theta_ne (P.thetaBelow_subset wt)).restrict
      (thetaStep Q.C ⟨0, h0⟩) (thetaStep_nonempty ⟨0, h0⟩ (Q.C_nonempty ⟨0, h0⟩))
      (Q.thetaStep_subset ⟨0, h0⟩)
      = G.restrict (P.thetaBelow wt) theta_ne (P.thetaBelow_subset wt) := by
    rw [restrict_restrict]
    exact Partition.restrict_eq_of_eq (G := G) hsetQ _ _ theta_ne (P.thetaBelow_subset wt)
  have hgameP : G.restrict (thetaStep P.C t0)
      (thetaStep_nonempty t0 (P.C_nonempty t0)) (P.thetaStep_subset t0)
      = G.restrict (P.thetaBelow wt) theta_ne (P.thetaBelow_subset wt) :=
    Partition.restrict_eq_of_eq (G := G) hheq.symm _ _ theta_ne (P.thetaBelow_subset wt)
  have e1 : Q.stepPayoffs ⟨0, h0⟩
      = (G.restrict (P.thetaBelow wt) theta_ne (P.thetaBelow_subset wt)).coalitionPayoffs :=
    se_coalitionPayoffs_of_eq hgameQ
  have e2 : P.stepPayoffs t0
      = (G.restrict (P.thetaBelow wt) theta_ne (P.thetaBelow_subset wt)).coalitionPayoffs :=
    se_coalitionPayoffs_of_eq hgameP
  rw [e1, e2]

/-- **Core of the self-enforcing-blocking proposition.** Under `NoMergeUp` and
existence of a CPPBE partition of every restricted game, a PBE partition that
is not coalition-proof admits a self-enforcing blocking coalition. -/
private lemma se_exists_selfEnforcing (P : Partition G) (hP : P.IsPBEPartition)
    (hExist : ∀ (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ),
        ∃ Q : Partition (G.restrict S hne hsub), Q.IsCPPBEPartition)
    (hNM : NoMergeUp G) (hncp : ¬ P.IsCoalitionProof) :
    ∃ B : P.BlockingCoalition, B.SelfEnforcing := by
  -- Step 1: some step fails to attain its residual maximum.
  have hviol : ∃ t : Fin P.card, P.w t < P.stepMax t := by
    by_contra hall
    push_neg at hall
    have hcoe : P.IsCOE := by
      intro t
      have hle1 : P.w t ≤ P.stepMax t := (P.isGreatest_stepMax t).2 (P.w_mem_stepPayoffs t)
      have heq : P.w t = P.stepMax t := le_antisymm hle1 (hall t)
      refine ⟨?_, ?_⟩
      · rw [heq]; exact P.isGreatest_stepMax t
      · intro t' ht'
        exact hP.2 (show t' ≤ t by rw [Fin.le_def]; omega)
    exact hncp hcoe.isCPPBEPartition.2
  -- Step 2: take the first such step.
  obtain ⟨t0, ht0lt, ht0min⟩ :
      ∃ t0 : Fin P.card, P.w t0 < P.stepMax t0 ∧
        ∀ s : Fin P.card, P.w s < P.stepMax s → t0 ≤ s := by
    have hne : (Finset.univ.filter (fun t : Fin P.card => P.w t < P.stepMax t)).Nonempty := by
      obtain ⟨t, ht⟩ := hviol
      exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
    refine ⟨_, (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2, ?_⟩
    intro s hs
    exact Finset.min'_le _ s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  set wt := P.stepMax t0 with hwt
  -- Step 3: `Θ(w̃) = R_{t0}`.
  have hmin : ∀ s : Fin P.card, P.w s < wt → t0 ≤ s := by
    intro s hs
    by_contra hcon
    rw [not_le] at hcon
    have hslt : (s : ℕ) < (t0 : ℕ) := hcon
    have ht0pos : 1 ≤ (t0 : ℕ) := by omega
    have h1 : (t0 : ℕ) - 1 < P.card := by have := t0.isLt; omega
    have h2 : ((t0 : ℕ) - 1) + 1 < P.card := by have := t0.isLt; omega
    have hpred : P.w ⟨(t0 : ℕ) - 1, h1⟩ = P.stepMax ⟨(t0 : ℕ) - 1, h1⟩ := by
      by_contra hne
      have hlt' : P.w ⟨(t0 : ℕ) - 1, h1⟩ < P.stepMax ⟨(t0 : ℕ) - 1, h1⟩ :=
        lt_of_le_of_ne ((P.isGreatest_stepMax _).2 (P.w_mem_stepPayoffs _)) hne
      have hle := ht0min _ hlt'
      have hle' : (t0 : ℕ) ≤ (t0 : ℕ) - 1 := hle
      omega
    have hstep := se_stepMax_le_pred P hNM h1 h2 hpred
    have ht0eq : (⟨(t0 : ℕ) - 1 + 1, h2⟩ : Fin P.card) = t0 := by
      apply Fin.ext; change (t0 : ℕ) - 1 + 1 = (t0 : ℕ); omega
    rw [ht0eq, ← hwt] at hstep
    have hsle : s ≤ (⟨(t0 : ℕ) - 1, h1⟩ : Fin P.card) := by
      rw [Fin.le_def]; change (s : ℕ) ≤ (t0 : ℕ) - 1; omega
    have hws := hP.2 hsle
    linarith
  have hheq : P.thetaBelow wt = thetaStep P.C t0 :=
    P.thetaBelow_eq_thetaStep hP.2 ht0lt hmin
  -- Step 4: build the self-enforcing blocking coalition from the residual game.
  have theta_ne : (P.thetaBelow wt).Nonempty := by
    rw [hheq]; exact thetaStep_nonempty t0 (P.C_nonempty t0)
  obtain ⟨Q, hQcp⟩ := hExist (P.thetaBelow wt) theta_ne (P.thetaBelow_subset wt)
  have hQg : Q.IsGreedy := Q.cppbe_characterization.mp hQcp
  have h0 : 0 < Q.card := se_card_pos Q
  obtain ⟨K, hKC, hKw⟩ := se_first_coalition Q h0
  have hw0 : Q.w ⟨0, h0⟩ = wt := by
    rw [se_greedy_first_stepMax hQg h0]
    change sSup (Q.stepPayoffs ⟨0, h0⟩) = sSup (P.stepPayoffs t0)
    rw [se_stepPayoffs_eq P theta_ne hheq Q h0]
  refine ⟨⟨wt, theta_ne, K, hKw.trans hw0⟩, ?_⟩
  exact ⟨Q, hQcp, h0, hKC.symm, hKw.symm⟩

/-- Package: the biconditional follows from `NoMergeUp` and restricted existence. -/
private lemma se_iff_of_regime (P : Partition G) (hP : P.IsPBEPartition)
    (hExist : ∀ (S : Finset T) (hne : S.Nonempty) (hsub : S ⊆ G.Θ),
        ∃ Q : Partition (G.restrict S hne hsub), Q.IsCPPBEPartition)
    (hNM : NoMergeUp G) :
    P.IsCPPBEPartition ↔ ∀ B : P.BlockingCoalition, ¬ B.SelfEnforcing := by
  constructor
  · rintro ⟨_, hcp⟩ B _
    exact hcp.elim B
  · intro h
    refine ⟨hP, ?_⟩
    by_contra hncp
    obtain ⟨B, hB⟩ := se_exists_selfEnforcing P hP hExist hNM hncp
    exact h B hB

/-- **Proposition 6(a).** Under
M-C and QC*, a PBE partition is coalition-proof iff it admits no
self-enforcing blocking coalition. -/
theorem cppbe_iff_no_selfEnforcing_qcstar (hMC : G.MC) (hQCs : G.QCStar)
    (P : Partition G) (hP : P.IsPBEPartition) :
    P.IsCPPBEPartition ↔ ∀ B : P.BlockingCoalition, ¬ B.SelfEnforcing := by
  refine se_iff_of_regime P hP (fun S hne hsub => ?_) (se_noMergeUp_qcstar hMC hQCs)
  exact one_existence (restrict_MC hne hsub hMC) (gp_restrict_QC hne hsub (se_qcStar_qc hQCs))

/-- **Proposition 6(b).** Under
M-C, QC, and genericity, a PBE partition is coalition-proof iff it admits no
self-enforcing blocking coalition. -/
theorem cppbe_iff_no_selfEnforcing_generic (hMC : G.MC) (hQC : G.QC)
    (hGen : G.Generic) (P : Partition G) (hP : P.IsPBEPartition) :
    P.IsCPPBEPartition ↔ ∀ B : P.BlockingCoalition, ¬ B.SelfEnforcing := by
  refine se_iff_of_regime P hP (fun S hne hsub => ?_) (se_noMergeUp_generic hQC hMC hGen)
  exact one_existence (restrict_MC hne hsub hMC) (gp_restrict_QC hne hsub hQC)

/-- **Proposition 6(c).** Under
single-valued `V` and strict betweenness, a PBE partition is coalition-proof
iff it admits no self-enforcing blocking coalition. -/
theorem cppbe_iff_no_selfEnforcing_bstar (hSV : G.SingleValued)
    (hB : G.StrictBetweenness)
    (P : Partition G) (hP : P.IsPBEPartition) :
    P.IsCPPBEPartition ↔ ∀ B : P.BlockingCoalition, ¬ B.SelfEnforcing := by
  refine se_iff_of_regime P hP (fun S hne hsub => ?_) (se_noMergeUp_bstar hSV hB)
  exact two_existence (se_restrict_singleValued hne hsub hSV)
    (restrict_StrictBetweenness hne hsub hB)

end DisclosureGame

end CPD
