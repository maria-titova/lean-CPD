import CPD.CoalitionProof
import CPD.PBEExistence
import CPD.LexMaxAux

/-!
# Lexicographically maximal PBE partitions (Definition 11, Proposition 3)

When no coalition-proof PBE exists, lexicographic maximality provides an
always-available fallback. The predicate `IsLexMax` formalizes a strengthening
of **Definition 11**: a competing PBE partition need only agree on the earlier
cells and payoffs, whereas Definition 11 also requires agreement of the earlier
strategies. Consequently, every `IsLexMax` partition is lexicographically
maximal in the paper's sense.

The file proves all three parts of **Proposition 3**: `lexmax_exists` gives an
`IsLexMax` partition; `isLexMax_of_isCPPBE` shows that every coalition-proof
PBE partition is `IsLexMax`; and `cppbe_iff_lexmax_cp` characterizes existence
of coalition-proof PBE by the existence of a coalition-proof `IsLexMax`
partition. These stronger statements imply the corresponding paper claims.

The axiom-free machinery (compactness, lexicographic maxima, residual
agreement) lives in `CPD.LexMaxAux`; here we assemble it, using
`exists_PBE` (which depends on the `kakutani` fixed-point axiom) only to
produce one PBE partition.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

namespace Partition

variable (P : Partition G)

/-- A strengthening of **Definition 11** (lexicographically maximal PBE
partition): no PBE partition that agrees on all earlier cells and payoffs pays
strictly more at the current step. The paper additionally requires the earlier
strategies to agree, so this predicate implies its definition. -/
def IsLexMax : Prop :=
  P.IsPBEPartition ∧
  ¬ ∃ (P' : Partition G) (_ : P'.IsPBEPartition)
      (t : Fin P.card) (t' : Fin P'.card),
      (t : ℕ) = (t' : ℕ) ∧
      (∀ (s : Fin P.card) (s' : Fin P'.card),
        (s : ℕ) = (s' : ℕ) → (s : ℕ) < (t : ℕ) →
          P'.C s' = P.C s ∧ P'.w s' = P.w s) ∧
      P.w t < P'.w t'

end Partition

/-! ### Existence of a lexicographically maximal PBE partition

A PBE partition is lexicographically maximal as soon as its *padded payoff
vector* is greatest under the lexicographic order among the padded payoff
vectors of all PBE partitions.  (The cell-agreement clause in `IsLexMax` only
*restricts* which competitors count, so a payoff-vector maximizer is a fortiori
a lex-maximizer.)  Such a maximizer exists because the set of padded payoff
vectors (`padWSet`, from `LexMaxAux`) is nonempty and compact. -/

/-- Some PBE partition exists. -/
private lemma exists_pbe_partition : ∃ P : Partition G, P.IsPBEPartition := by
  obtain ⟨s, hs⟩ := exists_PBE G
  set s0 : Strategy G :=
    ⟨fun θ m => if θ ∈ G.Θ then s.σ θ m else 0,
     fun θ hθ => by simpa [hθ] using s.mem θ hθ⟩ with hs0def
  have hagree : ∀ θ ∈ G.Θ, s.σ θ = s0.σ θ := by
    intro θ hθ; funext m; simp [hs0def, hθ]
  have hpbe0 : G.IsPBE s0 := isPBE_of_eqOn hagree hs
  have hsupp : ∀ θ ∉ G.Θ, s0.σ θ = 0 := by
    intro θ hθ; funext m; simp [hs0def, hθ]
  obtain ⟨P, hP, _⟩ := exists_isPBEPartition_of_isPBE hsupp hpbe0
  exact ⟨P, hP⟩

/-- `padWSet` is nonempty. -/
private lemma padWSet_nonempty : (padWSet G).Nonempty := by
  obtain ⟨P, hP⟩ := exists_pbe_partition (G := G)
  exact ⟨padW P, P, hP, rfl⟩

/-- If `P`'s padded payoff vector is lexicographically greatest among PBE
partitions, then `P` is lexicographically maximal. -/
private lemma isLexMax_of_padW_greatest {P : Partition G} (hP : P.IsPBEPartition)
    (hmax : ∀ P' : Partition G, P'.IsPBEPartition →
      toLex (padW P') ≤ toLex (padW P)) : P.IsLexMax := by
  refine ⟨hP, ?_⟩
  rintro ⟨P', hP', t, t', htt', hagree, hlt⟩
  have hPle := hmax P' hP'
  have htN : (t : ℕ) < G.Θ.card := lt_of_lt_of_le t.2 P.card_le
  have htP' : (t : ℕ) < P'.card := by have := t'.2; omega
  have hlt2 : toLex (padW P) < toLex (padW P') := by
    refine ⟨⟨(t : ℕ), htN⟩, ?_, ?_⟩
    · intro j hji
      have hjt : (j : ℕ) < (t : ℕ) := hji
      have hjP : (j : ℕ) < P.card := lt_trans hjt t.2
      have hjP' : (j : ℕ) < P'.card := by omega
      have e := (hagree ⟨(j : ℕ), hjP⟩ ⟨(j : ℕ), hjP'⟩ rfl hjt).2
      change padW P j = padW P' j
      rw [padW_apply hjP, padW_apply hjP']
      exact e.symm
    · change padW P ⟨(t : ℕ), htN⟩ < padW P' ⟨(t : ℕ), htN⟩
      rw [padW_apply (show ((⟨(t : ℕ), htN⟩ : Fin G.Θ.card) : ℕ) < P.card from t.2),
          padW_apply (show ((⟨(t : ℕ), htN⟩ : Fin G.Θ.card) : ℕ) < P'.card from htP')]
      have h1 : (⟨(t : ℕ), t.2⟩ : Fin P.card) = t := by ext; rfl
      have h2 : (⟨(t : ℕ), htP'⟩ : Fin P'.card) = t' := by ext; exact htt'
      rw [h1, h2]; exact hlt
  exact absurd hPle (not_le.mpr hlt2)

/-- **Proposition 3(i).** Every disclosure game admits a lexicographically
maximal PBE partition. -/
theorem lexmax_exists : ∃ P : Partition G, P.IsLexMax := by
  obtain ⟨v, hv, hgreat⟩ :=
    exists_lex_isGreatest (padWSet G) padWSet_nonempty padWSet_compact
  obtain ⟨P, hP, rfl⟩ := hv
  exact ⟨P, isLexMax_of_padW_greatest hP
    (fun P' hP' => hgreat _ ⟨P', hP', rfl⟩)⟩

/-- **Proposition 3(ii).** Every coalition-proof PBE partition is lexicographically
maximal. -/
theorem isLexMax_of_isCPPBE (P : Partition G) (h : P.IsCPPBEPartition) :
    P.IsLexMax := by
  have hg : P.IsGreedy := P.isGreedy_of_isCPPBEPartition h
  refine ⟨h.1, ?_⟩
  rintro ⟨P', hpbe', t, t', htt', hagree, hlt⟩
  have hR : thetaStep P.C t = thetaStep P'.C t' :=
    thetaStep_agree_of_prefix htt' (fun s s' hs hst => (hagree s s' hs hst).1)
  -- (a) `P'.w t'` is an attainable residual payoff at step `t`.
  have ha : P'.w t' ∈ P.stepPayoffs t := by
    rw [stepPayoffs_agree_of_prefix hR]; exact P'.w_mem_stepPayoffs t'
  -- (b) `P'.w t'` clears the greedy lower bound.
  have hb : P.greedyLower t ≤ P'.w t' := by
    rw [greedyLower_agree_of_prefix hR]
    simp only [Partition.greedyLower]
    apply Finset.sup'_le
    intro θ hθ
    exact (P'.isIR_iff_sup_le hpbe'.2 |>.1 hpbe'.1 t' θ hθ)
  -- (c) `P'.w t'` respects the predecessor constraint.
  have hc : ∀ s : Fin P.card, (s : ℕ) + 1 = (t : ℕ) → P'.w t' ≤ P.w s := by
    intro s hs
    have hslt : (s : ℕ) < (t : ℕ) := by omega
    have hscard' : (s : ℕ) < P'.card := by
      have : (t' : ℕ) < P'.card := t'.2
      omega
    let s' : Fin P'.card := ⟨(s : ℕ), hscard'⟩
    have heq : P'.w s' = P.w s := (hagree s s' rfl hslt).2
    have hs'lt : s' < t' := by
      simp only [s', Fin.lt_def]; omega
    have : P'.w t' ≤ P'.w s' := hpbe'.2 hs'lt.le
    rw [heq] at this; exact this
  have hle : P'.w t' ≤ P.w t := (hg t).2 ⟨ha, hb, hc⟩
  exact absurd hle (not_le.mpr hlt)

/-- **Proposition 3(iii).** A coalition-proof PBE exists iff some lexicographically
maximal PBE partition is coalition-proof. -/
theorem cppbe_iff_lexmax_cp :
    (∃ P : Partition G, P.IsCPPBEPartition) ↔
      (∃ P : Partition G, P.IsLexMax ∧ P.IsCPPBEPartition) := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P, isLexMax_of_isCPPBE P hP, hP⟩
  · rintro ⟨P, _, hP⟩
    exact ⟨P, hP⟩

end DisclosureGame

end CPD
