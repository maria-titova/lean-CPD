import CPD.Theorem1
import CPD.Degrading

/-!
# Greedy prefixes and the "no run of the greedy algorithm halts" theorems

Algorithm 3 (the greedy algorithm, Appendix C) builds a partition by
repeatedly choosing, on the current residual set of types, a coalition
attaining the greedy equation `w_t = max(𝒲_{R_t} ∩ [max u̲, w_{t-1}])`. A
**greedy prefix** (`GreedyPrefix`) formalizes an unfinished run of the
algorithm: a finite sequence of coalitions of successive residual games,
pairwise disjoint cells, and a *non-empty* final residual (the run has not
yet exhausted `Θ`). The run **extends** past a greedy prefix exactly when the
greedy constraint set at the final residual is non-empty
(`GreedyPrefix.extensionConstraint`).

This file shows that, under the hypotheses of Theorem 1(i) (M-C and QC*) or
of Theorem 5 (the payoff-degradation property), every greedy prefix extends,
and hence every run of the greedy algorithm terminates in a coalition-proof
PBE partition:

* **Theorem 1(i), full form** (`one_noHalt_full`): under M-C and QC*, no run
  of the greedy algorithm halts (`qcstar_prefix_extends` is the extension
  step, reusing the merging machinery of `Existence.lean`/`Theorem1.lean`
  reproved locally so this file needs only the `QC`/`QCStar`/`MC` API).
* **Theorem 5, full form** (`degrade_noHalt_full`): under the
  payoff-degradation property, no run of the greedy algorithm halts
  (`degrade_prefix_extends` is the extension step).

Both extension steps feed into `extend_engine`, a single recursion (on the
size of the final residual) that repeatedly snocs a realizing coalition onto
the prefix until the residual is exhausted, producing a genuine
`Partition G`.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-- The **residual type space before step `t` of a prefix**:
`R_t := Θ ∖ ⋃_{s<t} C_s`. (For a full partition this agrees with `thetaStep`
via the cover condition; a prefix has no cover condition.) -/
noncomputable def prefixResidual (Θ : Finset T) {n : ℕ} (C : Fin n → Finset T)
    (t : Fin n) : Finset T :=
  Θ \ (Finset.univ.filter (fun s => s < t)).biUnion C

variable (G) in
/-- **Algorithm 3** (Appendix C), unfinished run: a **greedy-algorithm
prefix** is finitely many pairwise-disjoint non-empty cells
`C_0, …, C_{card-1} ⊆ Θ` with a *non-empty final residual*
`Θ ∖ ⋃_t C_t`, each `(C_t, σ_t, w_t)` a coalition of the residual game
`G|_{R_t}` (exclusivity relative to `R_t`, common payoff `w_t`). Greediness of
the payoffs is the separate property `GreedyPrefix.IsGreedy`. -/
structure GreedyPrefix where
  /-- The number of completed steps. -/
  card : ℕ
  /-- The cells `C_0, …, C_{card-1}`. -/
  C : Fin card → Finset T
  /-- Each cell is non-empty. -/
  C_nonempty : ∀ t, (C t).Nonempty
  /-- The cells are pairwise disjoint. -/
  C_disjoint : ∀ s t, s ≠ t → Disjoint (C s) (C t)
  /-- Each cell is a set of types. -/
  C_subset : ∀ t, C t ⊆ G.Θ
  /-- The final residual `Θ ∖ ⋃_t C_t` is non-empty (the run has not ended). -/
  residual_nonempty : (G.Θ \ Finset.univ.biUnion C).Nonempty
  /-- A coalition strategy on each cell. -/
  σ : ∀ t, Strategy (G.restrict (C t) (C_nonempty t) (C_subset t))
  /-- The common payoffs `w_0, …, w_{card-1}`. -/
  w : Fin card → ℝ
  /-- Exclusivity at step `t`, relative to the residual `R_t`. -/
  exclusive : ∀ t, G.preimageSet (prefixResidual G.Θ C t) (σ t).evidence ⊆ C t
  /-- The payoff condition at each step. -/
  payoff : ∀ t, ∀ m ∈ (σ t).evidence, w t ∈ G.V ((σ t).coalitionBelief m)

namespace GreedyPrefix

variable (Q : G.GreedyPrefix)

/-- The final residual `R_card = Θ ∖ ⋃_t C_t`. -/
noncomputable def finalResidual : Finset T := G.Θ \ Finset.univ.biUnion Q.C

lemma finalResidual_nonempty : Q.finalResidual.Nonempty := Q.residual_nonempty

lemma finalResidual_subset : Q.finalResidual ⊆ G.Θ := Finset.sdiff_subset

lemma prefixResidual_subset (t : Fin Q.card) :
    prefixResidual G.Θ Q.C t ⊆ G.Θ := Finset.sdiff_subset

/-- The final residual is contained in every intermediate residual. -/
lemma finalResidual_subset_prefixResidual (t : Fin Q.card) :
    Q.finalResidual ⊆ prefixResidual G.Θ Q.C t := by
  unfold finalResidual prefixResidual
  apply Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _)

/-- Every intermediate residual contains the final one, hence is non-empty. -/
lemma prefixResidual_nonempty (t : Fin Q.card) :
    (prefixResidual G.Θ Q.C t).Nonempty :=
  Q.finalResidual_nonempty.mono (Q.finalResidual_subset_prefixResidual t)

/-- `𝒲_{R_t}` for the prefix. -/
noncomputable def stepPayoffs (t : Fin Q.card) : Set ℝ :=
  (G.restrict (prefixResidual G.Θ Q.C t) (Q.prefixResidual_nonempty t)
    (Q.prefixResidual_subset t)).coalitionPayoffs

/-- The greedy lower bound `max_{θ ∈ R_t} u̲(θ)` for the prefix. -/
noncomputable def greedyLower (t : Fin Q.card) : ℝ :=
  (prefixResidual G.Θ Q.C t).sup' (Q.prefixResidual_nonempty t) G.skeptical

/-- The greedy constraint set `𝒲_{R_t} ∩ [max_{θ∈R_t} u̲(θ), w_{t-1}]` for the
prefix (no upper constraint at `t = 0`, i.e. `w_{-1} = ∞`). -/
noncomputable def greedyConstraint (t : Fin Q.card) : Set ℝ :=
  {x | x ∈ Q.stepPayoffs t ∧ Q.greedyLower t ≤ x ∧
       ∀ t' : Fin Q.card, (t' : ℕ) + 1 = (t : ℕ) → x ≤ Q.w t'}

/-- A prefix is **greedy** when every payoff attains the greedy equation. -/
def IsGreedy : Prop := ∀ t, IsGreatest (Q.greedyConstraint t) (Q.w t)

/-- The greedy constraint set **at the final residual** — the feasible set of
the algorithm's next step (`w_{card-1}` is the upper bound; none if
`card = 0`). The prefix *extends* iff this set is non-empty. -/
noncomputable def extensionConstraint : Set ℝ :=
  {x | x ∈ (G.restrict Q.finalResidual Q.finalResidual_nonempty
              Q.finalResidual_subset).coalitionPayoffs ∧
       Q.finalResidual.sup' Q.finalResidual_nonempty G.skeptical ≤ x ∧
       ∀ t : Fin Q.card, (t : ℕ) + 1 = Q.card → x ≤ Q.w t}

/-! ### Generic residuals `R_J := Θ ∖ ⋃_{s∈J} C_s` for downward-closed `J`

Both `prefixResidual G.Θ Q.C t` (with `J = {s | s < t}`) and `finalResidual`
(with `J = univ`) are of this form; we prove the key feasibility/skeptical facts
once, mirroring `Partition.forced_subset_thetaStep`,
`Partition.condPrior_inter_mem_feasibleBeliefs`, and
`Partition.greedyLower_le_stepMax` from `COE.lean`. -/

/-- The generic residual `Θ ∖ ⋃_{s∈J} C_s` is contained in `Θ`. -/
lemma genResidual_subset (J : Finset (Fin Q.card)) :
    G.Θ \ J.biUnion Q.C ⊆ G.Θ := Finset.sdiff_subset

/-- The generic residual contains the (non-empty) final residual, hence is
non-empty. -/
lemma genResidual_nonempty (J : Finset (Fin Q.card)) :
    (G.Θ \ J.biUnion Q.C).Nonempty := by
  refine Q.finalResidual_nonempty.mono ?_
  unfold finalResidual
  exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
    (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_univ _))

/-
**Forced types of a residual message stay in the residual.**  Mirror of
`Partition.forced_subset_thetaStep` using the prefix's exclusivity.
-/
lemma genResidual_forced_subset (J : Finset (Fin Q.card))
    (hJ : ∀ a b : Fin Q.card, a ≤ b → b ∈ J → a ∈ J) {m : Msg}
    (hm : m ∈ G.restrictMsgSpace (G.Θ \ J.biUnion Q.C)) :
    G.forced m ⊆ G.Θ \ J.biUnion Q.C := by
  simp_all +decide [ DisclosureGame.restrictMsgSpace, DisclosureGame.forced ];
  intro θ hθ;
  by_contra h_contra;
  -- Since θ is in Q.C t for some t in J, we have m ∈ (Q.σ t).evidence.
  obtain ⟨t, htJ, ht⟩ : ∃ t ∈ J, θ ∈ Q.C t := by
    grind
  have hm_evidence : m ∈ (Q.σ t).evidence := by
    have hpm : (Q.σ t).σ θ ∈ simplexOn {m} := by
      convert ( Q.σ t ).mem θ ht using 1;
      simp_all +decide [ DisclosureGame.restrict, DisclosureGame.M ];
    simp_all +decide [ Strategy.evidence, Strategy.msgSupport ];
    exact ⟨ θ, ht, by rw [ show ( Q.σ t ).σ θ m = 1 by rw [ ← hpm.2.1, Finset.sum_eq_single m ] <;> aesop ] ; norm_num ⟩;
  obtain ⟨a, ha₁, ha₂⟩ := hm
  have ha₃ : a ∈ prefixResidual G.Θ Q.C t := by
    exact Finset.mem_sdiff.mpr ⟨ ha₁.1, fun h => by obtain ⟨ s, hs₁, hs₂ ⟩ := Finset.mem_biUnion.mp h; exact ha₁.2 s ( hJ _ _ ( Finset.mem_filter.mp hs₁ |>.2.le ) htJ ) hs₂ ⟩
  have ha₄ : a ∈ G.preimageSet (prefixResidual G.Θ Q.C t) (Q.σ t).evidence := by
    simp_all +decide [ DisclosureGame.preimageSet ];
    exact ⟨ m, by aesop ⟩
  have ha₅ : a ∈ Q.C t := by
    exact Q.exclusive t ha₄
  exact ha₁.right t htJ ha₅

/-
**The conditional prior on `P(m) ∩ R_J` is a feasible belief.** Mirror of
`Partition.condPrior_inter_mem_feasibleBeliefs`.
-/
lemma genResidual_condPrior_feasible (J : Finset (Fin Q.card))
    (hJ : ∀ a b : Fin Q.card, a ≤ b → b ∈ J → a ∈ J) {m : Msg}
    (hm : m ∈ G.restrictMsgSpace (G.Θ \ J.biUnion Q.C)) :
    G.condPrior (G.canSend m ∩ (G.Θ \ J.biUnion Q.C)) ∈ G.feasibleBeliefs m := by
  rw [G.feasibleBeliefs_eq_polytope];
  · refine' ⟨ _, _, _, _ ⟩;
    · refine' ⟨ _, _, _ ⟩;
      · intro θ; by_cases hθ : θ ∈ G.canSend m ∩ ( G.Θ \ J.biUnion Q.C ) <;> simp +decide [ hθ, condPrior_of_mem, condPrior_of_not_mem ] ; exact div_nonneg ( G.μ0_mem.1 θ ) ( Finset.sum_nonneg fun _ _ => G.μ0_mem.1 _ ) ;
      · convert G.condPrior_mem_simplex _ _ |> fun h => h.2.1;
        · simp_all +decide [ DisclosureGame.restrictMsgSpace ];
          exact ⟨ hm.choose, Finset.mem_inter.mpr ⟨ Finset.mem_filter.mpr ⟨ by exact hm.choose_spec.1.1, by exact ⟨ m, Finset.mem_inter.mpr ⟨ hm.choose_spec.2, Finset.mem_singleton_self _ ⟩ ⟩ ⟩, Finset.mem_sdiff.mpr ⟨ hm.choose_spec.1.1, by simpa using hm.choose_spec.1.2 ⟩ ⟩ ⟩;
        · grind +splitImp;
      · exact fun θ hθ => DisclosureGame.condPrior_of_not_mem ( Finset.notMem_mono ( Finset.inter_subset_right.trans ( Finset.sdiff_subset ) ) hθ );
    · exact fun θ hθ => DisclosureGame.condPrior_of_not_mem ( Finset.notMem_mono ( Finset.inter_subset_left ) hθ );
    · intro θ hθ θ' hθ'
      by_cases hθC : θ ∈ G.canSend m ∩ (G.Θ \ J.biUnion Q.C)
      by_cases hθ'C : θ' ∈ G.canSend m ∩ (G.Θ \ J.biUnion Q.C);
      · rw [ DisclosureGame.condPrior_of_mem hθC, DisclosureGame.condPrior_of_mem hθ'C ] ; ring;
      · contrapose! hθ'C;
        exact Finset.mem_inter.mpr ⟨ by
          simp_all +decide [ DisclosureGame.canSend, DisclosureGame.forced, DisclosureGame.preimageFull, preimage ], by
          exact Q.genResidual_forced_subset J hJ hm hθ' ⟩;
      · contrapose! hθC;
        exact Finset.mem_inter.mpr ⟨ by
          simp_all +decide [ DisclosureGame.canSend, DisclosureGame.forced ];
          exact Finset.mem_filter.mpr ⟨ hθ.1, by simp +decide [ hθ.2 ] ⟩, by
          exact Q.genResidual_forced_subset J hJ hm hθ ⟩;
    · intro θ hθ θF hθF
      simp_all +decide [ DisclosureGame.condPrior_of_not_mem, DisclosureGame.condPrior_of_mem ];
      simp_all +decide [ DisclosureGame.condPrior, DisclosureGame.forced ];
      split_ifs <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      · have := Q.genResidual_forced_subset J hJ hm; simp_all +decide [ DisclosureGame.canSend, DisclosureGame.forced ] ;
        simp_all +decide [ Finset.subset_iff, DisclosureGame.preimageFull ];
        simp_all +decide [ preimage ];
        grind;
      · exact mul_nonneg ( inv_nonneg.2 ( Finset.sum_nonneg fun _ _ => G.μ0_mem.1 _ ) ) ( mul_nonneg ( G.μ0_mem.1 _ ) ( G.μ0_mem.1 _ ) );
  · exact G.restrictMsgSpace_subset ( Q.genResidual_subset J ) hm

/-
**The greedy lower bound is dominated by the residual coalition max.**
Mirror of `Partition.greedyLower_le_stepMax`, per type.
-/
lemma genResidual_skeptical_le_sSup (J : Finset (Fin Q.card))
    (hJ : ∀ a b : Fin Q.card, a ≤ b → b ∈ J → a ∈ J) {θ : T}
    (hθ : θ ∈ G.Θ \ J.biUnion Q.C) :
    G.skeptical θ ≤ sSup ((G.restrict (G.Θ \ J.biUnion Q.C)
      (Q.genResidual_nonempty J) (Q.genResidual_subset J)).coalitionPayoffs) := by
  obtain ⟨m, hm⟩ : ∃ m ∈ G.M θ, ∃ μ ∈ G.feasibleBeliefs m, IsMinOn G.vlow (G.feasibleBeliefs m) μ ∧ G.skeptical θ = G.vlow μ := by
    obtain ⟨ m, hm, h ⟩ := G.skeptical_isWellDefined ( Finset.mem_sdiff.mp hθ |>.1 );
    exact ⟨ m, hm, h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.2 ⟩
  generalize_proofs at *;
  -- Let ν := G.condPrior (G.canSend m ∩ R). Show ν ∈ G.feasibleBeliefs m.
  set R := G.Θ \ J.biUnion Q.C
  set ν := G.condPrior (G.canSend m ∩ R)
  have hν_feasible : ν ∈ G.feasibleBeliefs m := by
    exact Q.genResidual_condPrior_feasible J hJ ( show m ∈ G.restrictMsgSpace R from Finset.mem_biUnion.mpr ⟨ θ, hθ, hm.1 ⟩ )
  generalize_proofs at *;
  -- From IsMinOn μ (feasible Beliefs m) (ν ∈ feasibleBeliefs m) we get G.vlow μ ≤ G.vlow ν.
  have hμ_le_ν : G.vlow hm.right.choose ≤ G.vlow ν := by
    exact hm.2.choose_spec.2.1 hν_feasible
  generalize_proofs at *; (
  -- From vlow_condPrior_canSend_mem_coalitionPayoffs, we get G.vlow ν ∈ H.coalitionPayoffs.
  have hν_coalitionPayoffs : G.vlow ν ∈ (G.restrict R ‹_› ‹_›).coalitionPayoffs := by
    have hν_coalitionPayoffs : m ∈ (G.restrict R ‹_› ‹_›).𝓜 := by
      exact Finset.mem_biUnion.mpr ⟨ θ, hθ, hm.1 ⟩
    generalize_proofs at *; (
    have hν_coalitionPayoffs : (G.restrict R ‹_› ‹_›).vlow ((G.restrict R ‹_› ‹_›).condPrior ((G.restrict R ‹_› ‹_›).canSend m)) ∈ (G.restrict R ‹_› ‹_›).coalitionPayoffs := by
      grind +suggestions
    generalize_proofs at *; (
    convert hν_coalitionPayoffs using 1
    generalize_proofs at *; (
    have hν_coalitionPayoffs : (G.restrict R ‹_› ‹_›).condPrior ((G.restrict R ‹_› ‹_›).canSend m) = G.condPrior (G.canSend m ∩ R) := by
      expose_names; exact Partition.condPrior_canSend_restrict pf_2 pf_3 m
    generalize_proofs at *; (
    exact hν_coalitionPayoffs.symm ▸ rfl))))
  generalize_proofs at *; (
  exact hm.2.choose_spec.2.2.symm ▸ hμ_le_ν.trans ( le_csSup ( by exact ( G.restrict R ‹_› ‹_› ).isCompact_coalitionPayoffs.bddAbove ) hν_coalitionPayoffs )))

/-- The `sup'`-form greedy lower bound of a residual is dominated by its
coalition max. -/
lemma genResidual_greedyLower_le_sSup (J : Finset (Fin Q.card))
    (hJ : ∀ a b : Fin Q.card, a ≤ b → b ∈ J → a ∈ J) :
    (G.Θ \ J.biUnion Q.C).sup' (Q.genResidual_nonempty J) G.skeptical
      ≤ sSup ((G.restrict (G.Θ \ J.biUnion Q.C)
          (Q.genResidual_nonempty J) (Q.genResidual_subset J)).coalitionPayoffs) :=
  Finset.sup'_le _ _ (fun _ hθ => Q.genResidual_skeptical_le_sSup J hJ hθ)

/-! ### Residuals of a snoc'd cell family -/

/-
Union of a snoc'd cell family.
-/
lemma snoc_biUnion (D : Finset T) :
    Finset.univ.biUnion (Fin.snoc Q.C D : Fin (Q.card + 1) → Finset T)
      = Finset.univ.biUnion Q.C ∪ D := by
  ext x
  simp [Fin.snoc];
  constructor;
  · grind;
  · rintro ( ⟨ a, ha ⟩ | hx );
    · exact ⟨ Fin.castSucc a, by simpa using ha ⟩;
    · exact ⟨ ⟨ Q.card, Nat.lt_succ_self _ ⟩, by simpa using hx ⟩

/-
Residual of a snoc'd family at an old index equals the old residual.
-/
lemma snoc_prefixResidual_castSucc (D : Finset T) (j : Fin Q.card) :
    prefixResidual G.Θ (Fin.snoc Q.C D : Fin (Q.card + 1) → Finset T) j.castSucc
      = prefixResidual G.Θ Q.C j := by
  refine' congr_arg _ ( Finset.ext fun x => _ );
  simp +decide [ Fin.snoc, Fin.exists_iff ];
  constructor;
  · rintro ⟨ i, hi, hij, hx ⟩;
    exact ⟨ i, lt_of_lt_of_le hij ( Nat.le_of_lt_succ ( by simp +decide [ Fin.castSucc ] ) ), hij, by simpa [ show i < Q.card from lt_of_lt_of_le hij ( Nat.le_of_lt_succ ( by simp +decide [ Fin.castSucc ] ) ) ] using hx ⟩;
  · rintro ⟨ i, hi, hij, hx ⟩;
    exact ⟨ i, hi.le, hij, by simpa [ hi ] using hx ⟩

/-
Residual of a snoc'd family at the last index equals the final residual.
-/
lemma snoc_prefixResidual_last (D : Finset T) :
    prefixResidual G.Θ (Fin.snoc Q.C D : Fin (Q.card + 1) → Finset T) (Fin.last Q.card)
      = Q.finalResidual := by
  refine' congr_arg _ ( Finset.ext fun x => _ );
  simp +decide [ Fin.lt_def, Fin.snoc ];
  exact ⟨ fun ⟨ a, ha, hx ⟩ => ⟨ a.castLT ha, by simpa [ ha ] using hx ⟩, fun ⟨ a, ha ⟩ => ⟨ ⟨ a, by linarith [ Fin.is_lt a ] ⟩, by simp +decide, by simpa ⟩ ⟩

end GreedyPrefix

/-! ### Auxiliary lemmas for the extension theorems -/

/-- The supremum of the coalition-payoff set is its greatest element. -/
lemma isGreatest_sSup_coalitionPayoffs (H : DisclosureGame T Msg) :
    IsGreatest H.coalitionPayoffs (sSup H.coalitionPayoffs) :=
  ⟨(H.isCompact_coalitionPayoffs).sSup_mem (H.coalitionPayoffs_nonempty),
    fun _ hx => le_csSup (H.isCompact_coalitionPayoffs).bddAbove hx⟩

/-- `v_min ≤ v̲(μ)` for every belief. -/
lemma greedyprefix_vMin_le_vlow {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.vMin ≤ G.vlow μ := by
  obtain ⟨M, hM⟩ := exists_bound_V G
  exact csInf_le ⟨-M, Set.forall_mem_image.2 fun ν hν =>
    neg_le_of_abs_le (hM ν hν _ (vlow_mem hν))⟩ ⟨μ, hμ, rfl⟩

/-- `v_min ≤ u̲(θ)`, the skeptical payoff dominates the floor. -/
lemma greedyprefix_vMin_le_skeptical {θ : T} (hθ : θ ∈ G.Θ) :
    G.vMin ≤ G.skeptical θ := by
  obtain ⟨m, _, μ, hμ, _, _, heq⟩ := G.skeptical_isWellDefined hθ
  rw [heq]
  exact greedyprefix_vMin_le_vlow (G.feasibleBeliefs_subset_simplex m hμ)

/-
**Degradation realizability.** Under the payoff-degradation property, every
value in `[v_min, max 𝒲_R]` is an attainable coalition payoff of the residual
game `G|_R`.
-/
lemma deg_realize (hdeg : G.DegradationProperty) {R : Finset T}
    (hRne : R.Nonempty) (hRsub : R ⊆ G.Θ) {w : ℝ}
    (hlo : G.vMin ≤ w)
    (hhi : w ≤ sSup (G.restrict R hRne hRsub).coalitionPayoffs) :
    w ∈ (G.restrict R hRne hRsub).coalitionPayoffs := by
  obtain ⟨Kmax, hKmax⟩ : ∃ Kmax : (G.restrict R hRne hRsub).Coalition, Kmax.w = sSup (G.restrict R hRne hRsub).coalitionPayoffs := by
    have := isGreatest_sSup_coalitionPayoffs ( G.restrict R hRne hRsub );
    exact this.1;
  exact hdeg hRne hRsub Kmax w ⟨ hlo, hKmax ▸ hhi ⟩ |> fun ⟨ K', hK' ⟩ => ⟨ K', hK'.2 ⟩

/-! ### The extension engine (shared by both no-halt theorems) -/

/-- Transport a strategy along an equality of games, preserving evidence and
coalition beliefs. -/
lemma gp_strategy_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂)
    (s : Strategy g₁) :
    ∃ s' : Strategy g₂, s'.evidence = s.evidence ∧
      ∀ m, s'.coalitionBelief m = s.coalitionBelief m := by
  subst h; exact ⟨s, rfl, fun _ => rfl⟩

/-
The extension constraint set has a greatest element whenever it is
non-empty (it is a closed subset of the compact coalition-payoff set).
-/
lemma extensionConstraint_greatest (Q : G.GreedyPrefix)
    (hne : Q.extensionConstraint.Nonempty) :
    ∃ w, IsGreatest Q.extensionConstraint w := by
  have h_closed : IsClosed Q.extensionConstraint := by
    apply_rules [ IsClosed.inter, isClosed_const, isClosed_le, continuous_id ];
    · convert DisclosureGame.isClosed_coalitionPayoffs ( G.restrict Q.finalResidual Q.finalResidual_nonempty Q.finalResidual_subset );
    · exact isClosed_Ici;
    · simp +decide only [isClosed_iff_clusterPt];
      intro x hx t ht; contrapose! hx; simp_all +decide [ ClusterPt ] ;
      rw [ Filter.inf_principal_eq_bot ];
      filter_upwards [ lt_mem_nhds hx ] with y hy using fun h => by linarith [ h t ht ] ;
  obtain ⟨H, hH⟩ : ∃ H : DisclosureGame T Msg, H = G.restrict Q.finalResidual Q.finalResidual_nonempty Q.finalResidual_subset := by
    exact ⟨ _, rfl ⟩;
  have h_compact : IsCompact Q.extensionConstraint := by
    refine' IsCompact.of_isClosed_subset ( DisclosureGame.isCompact_coalitionPayoffs H ) h_closed _;
    exact fun x hx => hH ▸ hx.1;
  exact h_compact.exists_isGreatest hne

lemma snocGreedyPrefix (Q : G.GreedyPrefix) (hQ : Q.IsGreedy)
    (K : (G.restrict Q.finalResidual Q.finalResidual_nonempty
            Q.finalResidual_subset).Coalition)
    (hK : IsGreatest Q.extensionConstraint K.w)
    (hne' : (Q.finalResidual \ K.C).Nonempty) :
    ∃ Q' : G.GreedyPrefix, Q'.card = Q.card + 1 ∧ Q'.IsGreedy ∧
      Q'.finalResidual = Q.finalResidual \ K.C ∧
      (∀ (s : Fin Q.card) (t : Fin Q'.card), (s : ℕ) = (t : ℕ) →
        Q'.C t = Q.C s ∧ Q'.w t = Q.w s) := by
  classical
  have hRne := Q.finalResidual_nonempty
  have hRsub := Q.finalResidual_subset
  set C' : Fin (Q.card + 1) → Finset T := Fin.snoc Q.C K.C with hC'
  have hCcast : ∀ j : Fin Q.card, C' j.castSucc = Q.C j := by
    intro j; rw [hC']; exact Fin.snoc_castSucc _ _ j
  have hClast : C' (Fin.last Q.card) = K.C := by rw [hC']; exact Fin.snoc_last _ _
  have hwcast : ∀ j : Fin Q.card, (Fin.snoc Q.w K.w : Fin (Q.card + 1) → ℝ) j.castSucc = Q.w j :=
    fun j => Fin.snoc_castSucc _ _ j
  have hwlast : (Fin.snoc Q.w K.w : Fin (Q.card + 1) → ℝ) (Fin.last Q.card) = K.w :=
    Fin.snoc_last _ _
  have hCne : ∀ t, (C' t).Nonempty := by
    refine Fin.lastCases ?_ ?_
    · rw [hClast]; exact K.C_nonempty
    · intro j; rw [hCcast]; exact Q.C_nonempty j
  have hCsub : ∀ t, C' t ⊆ G.Θ := by
    refine Fin.lastCases ?_ ?_
    · rw [hClast]; exact K.C_subset.trans hRsub
    · intro j; rw [hCcast]; exact Q.C_subset j
  have hpr_cast : ∀ j : Fin Q.card,
      prefixResidual G.Θ C' j.castSucc = prefixResidual G.Θ Q.C j := by
    intro j; rw [hC']; exact Q.snoc_prefixResidual_castSucc K.C j
  have hpr_last : prefixResidual G.Θ C' (Fin.last Q.card) = Q.finalResidual := by
    rw [hC']; exact Q.snoc_prefixResidual_last K.C
  have hbiU : Finset.univ.biUnion C' = Finset.univ.biUnion Q.C ∪ K.C := by
    rw [hC']; exact Q.snoc_biUnion K.C
  have hdisjL : ∀ i : Fin Q.card, Disjoint (Q.C i) K.C := by
    intro i
    refine Finset.disjoint_left.mpr (fun x hxi hxK => ?_)
    have hx : x ∈ Q.finalResidual := K.C_subset hxK
    simp only [GreedyPrefix.finalResidual, Finset.mem_sdiff] at hx
    exact hx.2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hxi⟩)
  have hset : G.Θ \ (Finset.univ.biUnion Q.C ∪ K.C) = Q.finalResidual \ K.C := by
    simp only [GreedyPrefix.finalResidual]; ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
  -- transported strategies
  have hsC := fun j : Fin Q.card =>
    gp_strategy_of_eq (Partition.restrict_eq_of_eq (hCcast j).symm (Q.C_nonempty j) (Q.C_subset j)
      (hCne j.castSucc) (hCsub j.castSucc)) (Q.σ j)
  choose sC hsCev hsCbel using hsC
  obtain ⟨sL, hsLev, hsLbel⟩ := gp_strategy_of_eq
    ((restrict_restrict hRne hRsub K.C_nonempty K.C_subset).trans
      (Partition.restrict_eq_of_eq hClast.symm K.C_nonempty (K.C_subset.trans hRsub)
        (hCne (Fin.last Q.card)) (hCsub (Fin.last Q.card)))) K.σ
  -- structure fields
  have hdisj : ∀ s t : Fin (Q.card + 1), s ≠ t → Disjoint (C' s) (C' t) := by
    refine Fin.lastCases ?_ ?_
    · refine Fin.lastCases ?_ ?_
      · intro h; exact absurd rfl h
      · intro j _; rw [hClast, hCcast]; exact (hdisjL j).symm
    · intro i
      refine Fin.lastCases ?_ ?_
      · intro _; rw [hCcast, hClast]; exact hdisjL i
      · intro j h; rw [hCcast, hCcast]; exact Q.C_disjoint i j (fun e => h (by rw [e]))
  have hresne : (G.Θ \ Finset.univ.biUnion C').Nonempty := by
    rw [hbiU, hset]; exact hne'
  have hpsf : (G.restrict Q.finalResidual hRne hRsub).preimageSetFull K.σ.evidence
      = G.preimageSet Q.finalResidual K.σ.evidence := by
    unfold DisclosureGame.preimageSetFull DisclosureGame.preimageSet
    simp only [restrict_Θ, restrict_M]
  set σ' : ∀ t : Fin (Q.card + 1), Strategy (G.restrict (C' t) (hCne t) (hCsub t)) :=
    Fin.lastCases (motive := fun t => Strategy (G.restrict (C' t) (hCne t) (hCsub t))) sL sC
    with hσ'
  have hσ'last : σ' (Fin.last Q.card) = sL := by simp only [hσ', Fin.lastCases_last]
  have hσ'cast : ∀ j : Fin Q.card, σ' j.castSucc = sC j := by
    intro j; simp only [hσ', Fin.lastCases_castSucc]
  have hexcl : ∀ t : Fin (Q.card + 1),
      G.preimageSet (prefixResidual G.Θ C' t) (σ' t).evidence ⊆ C' t := by
    refine Fin.lastCases (motive := fun t =>
      G.preimageSet (prefixResidual G.Θ C' t) (σ' t).evidence ⊆ C' t) ?_ ?_
    · dsimp only; rw [hσ'last, hpr_last, hsLev, hClast, ← hpsf]; exact K.exclusive
    · intro j; dsimp only; rw [hσ'cast, hpr_cast, hsCev, hCcast]; exact Q.exclusive j
  have hpay : ∀ t : Fin (Q.card + 1), ∀ m ∈ (σ' t).evidence,
      (Fin.snoc Q.w K.w : Fin (Q.card + 1) → ℝ) t
        ∈ G.V ((σ' t).coalitionBelief m) := by
    refine Fin.lastCases (motive := fun t => ∀ m ∈ (σ' t).evidence,
      (Fin.snoc Q.w K.w : Fin (Q.card + 1) → ℝ) t
        ∈ G.V ((σ' t).coalitionBelief m)) ?_ ?_
    · dsimp only; rw [hσ'last, hwlast]
      intro m hm; rw [hsLev] at hm; rw [hsLbel]
      have := K.payoff m hm; rwa [restrict_V] at this
    · intro j; dsimp only; rw [hσ'cast, hwcast]
      intro m hm; rw [hsCev] at hm; rw [hsCbel]
      exact Q.payoff j m hm
  set Q' : G.GreedyPrefix :=
    ⟨Q.card + 1, C', hCne, hdisj, hCsub, hresne, σ', Fin.snoc Q.w K.w,
      hexcl, hpay⟩ with hQ'
  have hQ'C : Q'.C = C' := rfl
  have hQ'w : Q'.w = Fin.snoc Q.w K.w := rfl
  have hsp_cast : ∀ j : Fin Q.card, Q'.stepPayoffs j.castSucc = Q.stepPayoffs j := by
    intro j
    unfold GreedyPrefix.stepPayoffs
    rw [Partition.restrict_eq_of_eq (hpr_cast j) (Q'.prefixResidual_nonempty _)
      (Q'.prefixResidual_subset _) (Q.prefixResidual_nonempty j) (Q.prefixResidual_subset j)]
  have hgl_cast : ∀ j : Fin Q.card, Q'.greedyLower j.castSucc = Q.greedyLower j := by
    intro j
    unfold GreedyPrefix.greedyLower
    exact Finset.sup'_congr _ (hpr_cast j) (fun _ _ => rfl)
  have hsp_last : Q'.stepPayoffs (Fin.last Q.card)
      = (G.restrict Q.finalResidual hRne hRsub).coalitionPayoffs := by
    unfold GreedyPrefix.stepPayoffs
    rw [Partition.restrict_eq_of_eq hpr_last (Q'.prefixResidual_nonempty _)
      (Q'.prefixResidual_subset _) hRne hRsub]
  have hgl_last : Q'.greedyLower (Fin.last Q.card)
      = Q.finalResidual.sup' hRne G.skeptical := by
    unfold GreedyPrefix.greedyLower
    exact Finset.sup'_congr _ hpr_last (fun _ _ => rfl)
  have hgreedy : Q'.IsGreedy := by
    refine Fin.lastCases ?_ ?_
    · have hgc : Q'.greedyConstraint (Fin.last Q.card) = Q.extensionConstraint := by
        ext x
        simp only [GreedyPrefix.greedyConstraint, GreedyPrefix.extensionConstraint,
          Set.mem_setOf_eq, hsp_last, hgl_last]
        refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
        constructor
        · intro h t' ht'
          have := h t'.castSucc (by simpa using ht')
          rwa [hQ'w, hwcast] at this
        · intro h t' ht'
          simp only [Fin.val_last] at ht'
          have ht'lt : (t' : ℕ) < Q.card := by omega
          have hte : t' = (Fin.castSucc ⟨t', ht'lt⟩) := by ext; simp
          rw [hte, hQ'w, hwcast]
          exact h ⟨t', ht'lt⟩ (by simpa using ht')
      rw [show Q'.w (Fin.last Q.card) = K.w from by rw [hQ'w]; exact hwlast, hgc]
      exact hK
    · intro j
      have hgc : Q'.greedyConstraint j.castSucc = Q.greedyConstraint j := by
        ext x
        simp only [GreedyPrefix.greedyConstraint, Set.mem_setOf_eq, hsp_cast j, hgl_cast j]
        refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
        constructor
        · intro h t' ht'
          have := h t'.castSucc (by simpa using ht')
          rwa [hQ'w, hwcast] at this
        · intro h t' ht'
          simp only [Fin.coe_castSucc] at ht'
          have ht'lt : (t' : ℕ) < Q.card := by have := j.isLt; omega
          have hte : t' = (Fin.castSucc ⟨t', ht'lt⟩) := by ext; simp
          rw [hte, hQ'w, hwcast]
          exact h ⟨t', ht'lt⟩ (by simpa using ht')
      rw [show Q'.w j.castSucc = Q.w j from by rw [hQ'w]; exact hwcast j, hgc]
      exact hQ j
  refine ⟨Q', rfl, hgreedy, ?_, ?_⟩
  · show G.Θ \ Finset.univ.biUnion Q'.C = Q.finalResidual \ K.C
    rw [hQ'C, hbiU, hset]
  · intro s t hst
    have hts : t = Fin.castSucc ⟨s, s.isLt⟩ := by ext; simpa using hst.symm
    subst hts
    rw [hQ'C, hCcast, hQ'w, hwcast]
    exact ⟨rfl, rfl⟩


/-- For a covering, pairwise-disjoint cell family, the `thetaStep` residual
`⋃_{s≥t} C_s` coincides with the prefix residual `Θ ∖ ⋃_{s<t} C_s`. -/
lemma thetaStep_eq_prefixResidual {n : ℕ} (C : Fin n → Finset T)
    (hcov : G.Θ = Finset.univ.biUnion C) (hsub : ∀ t, C t ⊆ G.Θ)
    (hdisj : ∀ s t : Fin n, s ≠ t → Disjoint (C s) (C t)) (t : Fin n) :
    thetaStep C t = prefixResidual G.Θ C t := by
  ext x
  simp only [thetaStep, prefixResidual, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨s, hts, hxs⟩
    refine ⟨hsub s hxs, ?_⟩
    rintro ⟨s', hs't, hxs'⟩
    exact Finset.disjoint_left.mp (hdisj s s' (fun e => absurd (e ▸ hs't) (not_lt.mpr hts))) hxs hxs'
  · rintro ⟨hxΘ, hx⟩
    obtain ⟨s, _, hxs⟩ := Finset.mem_biUnion.mp (hcov ▸ hxΘ)
    exact ⟨s, by_contra (fun hts => hx ⟨s, not_le.mp hts, hxs⟩), hxs⟩

/-- **Snoc a final greedy cell onto a prefix (residual exhausted).** If the
realizing coalition's cell covers the whole final residual, the result is a
greedy partition of `G` extending the prefix. -/
lemma snocPartition (Q : G.GreedyPrefix) (hQ : Q.IsGreedy)
    (K : (G.restrict Q.finalResidual Q.finalResidual_nonempty
            Q.finalResidual_subset).Coalition)
    (hK : IsGreatest Q.extensionConstraint K.w)
    (hcov : Q.finalResidual ⊆ K.C) :
    ∃ P : Partition G, P.IsGreedy ∧ P.card = Q.card + 1 ∧
      (∀ (s : Fin Q.card) (t : Fin P.card), (s : ℕ) = (t : ℕ) →
        P.C t = Q.C s ∧ P.w t = Q.w s) := by
  classical
  have hRne := Q.finalResidual_nonempty
  have hRsub := Q.finalResidual_subset
  have hKCeq : K.C = Q.finalResidual := Finset.Subset.antisymm K.C_subset hcov
  set C' : Fin (Q.card + 1) → Finset T := Fin.snoc Q.C K.C with hC'
  have hCcast : ∀ j : Fin Q.card, C' j.castSucc = Q.C j := by
    intro j; rw [hC']; exact Fin.snoc_castSucc _ _ j
  have hClast : C' (Fin.last Q.card) = K.C := by rw [hC']; exact Fin.snoc_last _ _
  have hwcast : ∀ j : Fin Q.card, (Fin.snoc Q.w K.w : Fin (Q.card + 1) → ℝ) j.castSucc = Q.w j :=
    fun j => Fin.snoc_castSucc _ _ j
  have hwlast : (Fin.snoc Q.w K.w : Fin (Q.card + 1) → ℝ) (Fin.last Q.card) = K.w :=
    Fin.snoc_last _ _
  have hCne : ∀ t, (C' t).Nonempty := by
    refine Fin.lastCases ?_ ?_
    · rw [hClast]; exact K.C_nonempty
    · intro j; rw [hCcast]; exact Q.C_nonempty j
  have hCsub : ∀ t, C' t ⊆ G.Θ := by
    refine Fin.lastCases ?_ ?_
    · rw [hClast]; exact K.C_subset.trans hRsub
    · intro j; rw [hCcast]; exact Q.C_subset j
  have hpr_cast : ∀ j : Fin Q.card,
      prefixResidual G.Θ C' j.castSucc = prefixResidual G.Θ Q.C j := by
    intro j; rw [hC']; exact Q.snoc_prefixResidual_castSucc K.C j
  have hpr_last : prefixResidual G.Θ C' (Fin.last Q.card) = Q.finalResidual := by
    rw [hC']; exact Q.snoc_prefixResidual_last K.C
  have hbiU : Finset.univ.biUnion C' = Finset.univ.biUnion Q.C ∪ K.C := by
    rw [hC']; exact Q.snoc_biUnion K.C
  have hdisjL : ∀ i : Fin Q.card, Disjoint (Q.C i) K.C := by
    intro i
    refine Finset.disjoint_left.mpr (fun x hxi hxK => ?_)
    have hx : x ∈ Q.finalResidual := K.C_subset hxK
    simp only [GreedyPrefix.finalResidual, Finset.mem_sdiff] at hx
    exact hx.2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hxi⟩)
  have hcovereq : G.Θ = Finset.univ.biUnion C' := by
    rw [hbiU, hKCeq]
    simp only [GreedyPrefix.finalResidual]
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx; by_cases h : x ∈ Finset.univ.biUnion Q.C
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | ⟨hx, _⟩)
      · obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp h; exact Q.C_subset s hs
      · exact hx
  have hdisj : ∀ s t : Fin (Q.card + 1), s ≠ t → Disjoint (C' s) (C' t) := by
    refine Fin.lastCases ?_ ?_
    · refine Fin.lastCases ?_ ?_
      · intro h; exact absurd rfl h
      · intro j _; rw [hClast, hCcast]; exact (hdisjL j).symm
    · intro i
      refine Fin.lastCases ?_ ?_
      · intro _; rw [hCcast, hClast]; exact hdisjL i
      · intro j h; rw [hCcast, hCcast]; exact Q.C_disjoint i j (fun e => h (by rw [e]))
  have hts : ∀ t : Fin (Q.card + 1), thetaStep C' t = prefixResidual G.Θ C' t :=
    fun t => thetaStep_eq_prefixResidual C' hcovereq hCsub hdisj t
  have hpsf : (G.restrict Q.finalResidual hRne hRsub).preimageSetFull K.σ.evidence
      = G.preimageSet Q.finalResidual K.σ.evidence := by
    unfold DisclosureGame.preimageSetFull DisclosureGame.preimageSet
    simp only [restrict_Θ, restrict_M]
  have hsC := fun j : Fin Q.card =>
    gp_strategy_of_eq (Partition.restrict_eq_of_eq (hCcast j).symm (Q.C_nonempty j) (Q.C_subset j)
      (hCne j.castSucc) (hCsub j.castSucc)) (Q.σ j)
  choose sC hsCev hsCbel using hsC
  obtain ⟨sL, hsLev, hsLbel⟩ := gp_strategy_of_eq
    ((restrict_restrict hRne hRsub K.C_nonempty K.C_subset).trans
      (Partition.restrict_eq_of_eq hClast.symm K.C_nonempty (K.C_subset.trans hRsub)
        (hCne (Fin.last Q.card)) (hCsub (Fin.last Q.card)))) K.σ
  set σ' : ∀ t : Fin (Q.card + 1), Strategy (G.restrict (C' t) (hCne t) (hCsub t)) :=
    Fin.lastCases (motive := fun t => Strategy (G.restrict (C' t) (hCne t) (hCsub t))) sL sC
    with hσ'
  have hσ'last : σ' (Fin.last Q.card) = sL := by simp only [hσ', Fin.lastCases_last]
  have hσ'cast : ∀ j : Fin Q.card, σ' j.castSucc = sC j := by
    intro j; simp only [hσ', Fin.lastCases_castSucc]
  have hexcl : ∀ t : Fin (Q.card + 1),
      G.preimageSet (thetaStep C' t) (σ' t).evidence ⊆ C' t := by
    refine Fin.lastCases (motive := fun t =>
      G.preimageSet (thetaStep C' t) (σ' t).evidence ⊆ C' t) ?_ ?_
    · dsimp only; rw [hts, hpr_last, hσ'last, hsLev, hClast, ← hpsf]; exact K.exclusive
    · intro j; dsimp only; rw [hts, hpr_cast, hσ'cast, hsCev, hCcast]; exact Q.exclusive j
  have hpay : ∀ t : Fin (Q.card + 1), ∀ m ∈ (σ' t).evidence,
      (Fin.snoc Q.w K.w : Fin (Q.card + 1) → ℝ) t
        ∈ G.V ((σ' t).coalitionBelief m) := by
    refine Fin.lastCases (motive := fun t => ∀ m ∈ (σ' t).evidence,
      (Fin.snoc Q.w K.w : Fin (Q.card + 1) → ℝ) t
        ∈ G.V ((σ' t).coalitionBelief m)) ?_ ?_
    · dsimp only; rw [hσ'last, hwlast]
      intro m hm; rw [hsLev] at hm; rw [hsLbel]
      have := K.payoff m hm; rwa [restrict_V] at this
    · intro j; dsimp only; rw [hσ'cast, hwcast]
      intro m hm; rw [hsCev] at hm; rw [hsCbel]
      exact Q.payoff j m hm
  set P : Partition G :=
    ⟨Q.card + 1, C', hCne, hdisj, hCsub, hcovereq.le, σ', Fin.snoc Q.w K.w, hexcl, hpay⟩ with hP
  have hPC : P.C = C' := rfl
  have hPw : P.w = Fin.snoc Q.w K.w := rfl
  have hPsp_cast : ∀ j : Fin Q.card, P.stepPayoffs j.castSucc = Q.stepPayoffs j := by
    intro j
    unfold Partition.stepPayoffs GreedyPrefix.stepPayoffs
    congr 1
    exact Partition.restrict_eq_of_eq ((hts j.castSucc).trans (hpr_cast j)) _ _
      (Q.prefixResidual_nonempty j) (Q.prefixResidual_subset j)
  have hPgl_cast : ∀ j : Fin Q.card, P.greedyLower j.castSucc = Q.greedyLower j := by
    intro j
    unfold Partition.greedyLower GreedyPrefix.greedyLower
    exact Finset.sup'_congr _ ((hts j.castSucc).trans (hpr_cast j)) (fun _ _ => rfl)
  have hPsp_last : P.stepPayoffs (Fin.last Q.card)
      = (G.restrict Q.finalResidual hRne hRsub).coalitionPayoffs := by
    unfold Partition.stepPayoffs
    congr 1
    exact Partition.restrict_eq_of_eq ((hts (Fin.last Q.card)).trans hpr_last) _ _ hRne hRsub
  have hPgl_last : P.greedyLower (Fin.last Q.card)
      = Q.finalResidual.sup' hRne G.skeptical := by
    unfold Partition.greedyLower
    exact Finset.sup'_congr _ ((hts (Fin.last Q.card)).trans hpr_last) (fun _ _ => rfl)
  have hgreedy : P.IsGreedy := by
    refine Fin.lastCases ?_ ?_
    · have hgc : P.greedyConstraint (Fin.last Q.card) = Q.extensionConstraint := by
        ext x
        simp only [Partition.greedyConstraint, GreedyPrefix.extensionConstraint,
          Set.mem_setOf_eq, hPsp_last, hPgl_last]
        refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
        constructor
        · intro h t' ht'
          have := h t'.castSucc (by simpa using ht')
          rwa [hPw, hwcast] at this
        · intro h t' ht'
          simp only [Fin.val_last] at ht'
          have ht'lt : (t' : ℕ) < Q.card := by omega
          have hte : t' = (Fin.castSucc ⟨t', ht'lt⟩) := by ext; simp
          rw [hte, hPw, hwcast]
          exact h ⟨t', ht'lt⟩ (by simpa using ht')
      rw [show P.w (Fin.last Q.card) = K.w from by rw [hPw]; exact hwlast, hgc]
      exact hK
    · intro j
      have hgc : P.greedyConstraint j.castSucc = Q.greedyConstraint j := by
        ext x
        simp only [Partition.greedyConstraint, GreedyPrefix.greedyConstraint,
          Set.mem_setOf_eq, hPsp_cast j, hPgl_cast j]
        refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
        constructor
        · intro h t' ht'
          have := h t'.castSucc (by simpa using ht')
          rwa [hPw, hwcast] at this
        · intro h t' ht'
          simp only [Fin.coe_castSucc] at ht'
          have ht'lt : (t' : ℕ) < Q.card := by have := j.isLt; omega
          have hte : t' = (Fin.castSucc ⟨t', ht'lt⟩) := by ext; simp
          rw [hte, hPw, hwcast]
          exact h ⟨t', ht'lt⟩ (by simpa using ht')
      rw [show P.w j.castSucc = Q.w j from by rw [hPw]; exact hwcast j, hgc]
      exact hQ j
  refine ⟨P, hgreedy, rfl, ?_⟩
  intro s t hst
  have hts2 : t = Fin.castSucc ⟨s, s.isLt⟩ := by ext; simpa using hst.symm
  subst hts2
  rw [hPC, hCcast, hPw, hwcast]
  exact ⟨rfl, rfl⟩

/-
**The extension engine.** Given that every greedy prefix extends (its
extension constraint is non-empty), every greedy prefix extends to a greedy
partition of `G`. Proof by strong recursion on the size of the final
residual.
-/
lemma extend_engine
    (hext : ∀ Q' : G.GreedyPrefix, Q'.IsGreedy → Q'.extensionConstraint.Nonempty)
    (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) :
    ∃ P : Partition G, P.IsGreedy ∧ Q.card ≤ P.card ∧
      ∀ (s : Fin Q.card) (t : Fin P.card), (s : ℕ) = (t : ℕ) →
        P.C t = Q.C s ∧ P.w t = Q.w s := by
  revert Q hQ hext;
  intro hQext Q hQ
  suffices Hmain : ∀ n : ℕ, ∀ Q : G.GreedyPrefix, Q.IsGreedy → Q.finalResidual.card = n → (∃ P : Partition G, P.IsGreedy ∧ Q.card ≤ P.card ∧ ∀ (s : Fin Q.card) (t : Fin P.card), (s : ℕ) = (t : ℕ) → P.C t = Q.C s ∧ P.w t = Q.w s) by
    exact Hmain _ _ hQ rfl
  generalize_proofs at *;
  intro n;
  induction' n using Nat.strong_induction_on with n ih;
  intro Q hQ hn
  obtain ⟨w, hw⟩ := hQext Q hQ |> fun h => extensionConstraint_greatest Q h
  obtain ⟨K, hKw⟩ : ∃ K : (G.restrict Q.finalResidual Q.finalResidual_nonempty Q.finalResidual_subset).Coalition, K.w = w := by
    have := hw.1.1; simp_all +decide [ DisclosureGame.coalitionPayoffs ] ;
  have hKgreat : IsGreatest Q.extensionConstraint K.w := by
    exact hKw ▸ hw
  by_cases hemp : (Q.finalResidual \ K.C).Nonempty;
  · obtain ⟨Q', hcard', hQ'g, hres', hmatch'⟩ := snocGreedyPrefix Q hQ K hKgreat hemp
    generalize_proofs at *;
    obtain ⟨P, hPg, hcardle, hPmatch⟩ := ih (Q.finalResidual \ K.C).card (by
    rw [ ← hn ];
    apply Finset.card_lt_card;
    simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
    exact ⟨ fun x hx₁ hx₂ => hx₁, by obtain ⟨ x, hx ⟩ := K.C_nonempty; exact ⟨ x, K.C_subset hx, fun _ => hx ⟩ ⟩) Q' hQ'g (by
    rw [hres'])
    generalize_proofs at *;
    refine' ⟨ P, hPg, _, _ ⟩;
    · grind;
    · intro s t hst
      generalize_proofs at *;
      exact ⟨ hPmatch ⟨ s, by linarith [ Fin.is_lt s ] ⟩ t ( by simpa using hst ) |>.1.trans ( hmatch' s ⟨ s, by linarith [ Fin.is_lt s ] ⟩ rfl |>.1 ), hPmatch ⟨ s, by linarith [ Fin.is_lt s ] ⟩ t ( by simpa using hst ) |>.2.trans ( hmatch' s ⟨ s, by linarith [ Fin.is_lt s ] ⟩ rfl |>.2 ) ⟩;
  · obtain ⟨P, hPg, hPcard, hPmatch⟩ := snocPartition Q hQ K hKgreat (by
    exact fun x hx => Classical.not_not.1 fun hx' => hemp ⟨ x, Finset.mem_sdiff.2 ⟨ hx, hx' ⟩ ⟩)
    generalize_proofs at *;
    exact ⟨ P, hPg, by linarith, hPmatch ⟩

/-! ### QC* merging machinery for the extension step -/

/-- The cell `C_t` sits inside its residual `R_t`. -/
lemma prefix_cell_subset (Q : G.GreedyPrefix) (t : Fin Q.card) :
    Q.C t ⊆ prefixResidual G.Θ Q.C t := by
  intro x hx
  rw [prefixResidual, Finset.mem_sdiff]
  refine ⟨Q.C_subset t hx, ?_⟩
  rw [Finset.mem_biUnion]
  rintro ⟨s, hs, hxs⟩
  rw [Finset.mem_filter] at hs
  exact Finset.disjoint_left.mp
    (Q.C_disjoint t s (fun e => absurd (e ▸ hs.2) (lt_irrefl _))) hx hxs

/-
`R_t = R_{t'} ∖ C_{t'}` for consecutive indices `t' + 1 = t`.
-/
lemma prefix_residual_step (Q : G.GreedyPrefix) {t' t : Fin Q.card}
    (h : (t' : ℕ) + 1 = (t : ℕ)) :
    prefixResidual G.Θ Q.C t = prefixResidual G.Θ Q.C t' \ Q.C t' := by
  simp +decide [ prefixResidual ];
  grind

/-
The final residual is the last prefix residual minus the last cell.
-/
lemma finalResidual_eq_step (Q : G.GreedyPrefix) {t' : Fin Q.card}
    (h : (t' : ℕ) + 1 = Q.card) :
    Q.finalResidual = prefixResidual G.Θ Q.C t' \ Q.C t' := by
  have h_biUnion : Finset.univ.biUnion Q.C = (Finset.univ.filter (fun s : Fin Q.card => s < t')).biUnion Q.C ∪ Q.C t' := by
    grind;
  unfold prefixResidual;
  unfold GreedyPrefix.finalResidual; aesop;

/-
The cell `C_t` viewed as a coalition of the residual game `G|_{R_t}`.
-/
lemma prefix_cell_coalition (Q : G.GreedyPrefix) (t : Fin Q.card) :
    ∃ K : (G.restrict (prefixResidual G.Θ Q.C t) (Q.prefixResidual_nonempty t)
        (Q.prefixResidual_subset t)).Coalition, K.C = Q.C t ∧ K.w = Q.w t := by
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Strategy ((G.restrict (prefixResidual G.Θ Q.C t) (Q.prefixResidual_nonempty t) (Q.prefixResidual_subset t)).restrict (Q.C t) (Q.C_nonempty t) (prefix_cell_subset Q t)), σ'.evidence = (Q.σ t).evidence ∧ ∀ m, σ'.coalitionBelief m = (Q.σ t).coalitionBelief m := by
    apply gp_strategy_of_eq
    exact Eq.symm
      (restrict_restrict (GreedyPrefix.prefixResidual_nonempty Q t)
        (GreedyPrefix.prefixResidual_subset Q t) (Q.C_nonempty t) (prefix_cell_subset Q t))
  refine' ⟨ ⟨ Q.C t, Q.C_nonempty t, prefix_cell_subset Q t, σ', _, Q.w t, _ ⟩, rfl, rfl ⟩ <;> simp_all +decide [ DisclosureGame.preimageSetFull ];
  · convert Q.exclusive t using 1;
  · exact fun m hm => Q.payoff t m hm

/-
Restriction preserves QC (reproved locally).
-/
lemma gp_restrict_QC {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hQC : G.QC) : (G.restrict S hne hsub).QC := by
  intro μ hμ μ' hμ' l hl
  convert hQC μ (simplexOn_mono hsub hμ) μ' (simplexOn_mono hsub hμ') l hl using 1

/-
The conditional prior on a disjoint union is a convex combination
(reproved locally, cf. `condPrior_union_convexCombo`).
-/
lemma gp_condPrior_union {C D : Finset T}
    (hC : C.Nonempty) (hD : D.Nonempty) (hCΘ : C ⊆ G.Θ) (hDΘ : D ⊆ G.Θ)
    (hdisj : Disjoint C D) :
    ∃ l ∈ Set.Ioo (0 : ℝ) 1,
      G.condPrior (C ∪ D)
        = fun θ => l * G.condPrior C θ + (1 - l) * G.condPrior D θ := by
  refine' ⟨ G.priorMeasure C / ( G.priorMeasure C + G.priorMeasure D ), _, _ ⟩;
  · exact ⟨ div_pos ( priorMeasure_pos hC hCΘ ) ( add_pos ( priorMeasure_pos hC hCΘ ) ( priorMeasure_pos hD hDΘ ) ), by rw [ div_lt_iff₀ ( add_pos ( priorMeasure_pos hC hCΘ ) ( priorMeasure_pos hD hDΘ ) ) ] ; linarith [ priorMeasure_pos hC hCΘ, priorMeasure_pos hD hDΘ ] ⟩;
  · ext θ; by_cases hθC : θ ∈ C <;> by_cases hθD : θ ∈ D <;> simp +decide [ hθC, hθD, DisclosureGame.condPrior_of_mem, DisclosureGame.condPrior_of_not_mem ] ;
    · exact False.elim ( Finset.disjoint_left.mp hdisj hθC hθD );
    · rw [ show G.priorMeasure ( C ∪ D ) = G.priorMeasure C + G.priorMeasure D from ?_, div_mul_div_comm, mul_comm ];
      · rw [ mul_div_mul_right _ _ ( ne_of_gt ( DisclosureGame.priorMeasure_pos hC hCΘ ) ) ];
      · exact Finset.sum_union hdisj;
    · rw [ one_sub_div, div_mul_div_comm, div_eq_div_iff ];
      · simp +decide [ DisclosureGame.priorMeasure, Finset.sum_union hdisj ] ; ring;
      · exact ne_of_gt ( DisclosureGame.priorMeasure_pos ( Finset.Nonempty.mono ( Finset.subset_union_left ) hC ) ( Finset.union_subset hCΘ hDΘ ) );
      · exact mul_ne_zero ( ne_of_gt ( add_pos ( DisclosureGame.priorMeasure_pos hC hCΘ ) ( DisclosureGame.priorMeasure_pos hD hDΘ ) ) ) ( ne_of_gt ( DisclosureGame.priorMeasure_pos hD hDΘ ) );
      · exact ne_of_gt ( add_pos ( DisclosureGame.priorMeasure_pos hC hCΘ ) ( DisclosureGame.priorMeasure_pos hD hDΘ ) )

/-
A coalition attaining the residual maximum pools at its pooling value.
-/
lemma gp_coalition_vbar (hQC : G.QC) (hMC : G.MC) {S : Finset T}
    (hne : S.Nonempty) (hsub : S ⊆ G.Θ) (K : (G.restrict S hne hsub).Coalition)
    (hw : IsGreatest (G.restrict S hne hsub).coalitionPayoffs K.w) :
    G.vbar (G.condPrior K.C) = K.w := by
  -- Apply the public `coalition_attains_max` to the restricted game `H := G.restrict S hne hsub`, whose QC/MC come from `gp_restrict_QC hne hsub hQC` and `restrict_MC hne hsub hMC`. This gives `H.vbar (H.condPrior K.C) = K.w`.
  have h := coalition_attains_max (gp_restrict_QC hne hsub hQC) (restrict_MC hne hsub hMC) K hw;
  convert h using 1;
  rw [ DisclosureGame.vbar, DisclosureGame.vbar ];
  rw [ DisclosureGame.Partition.restrict_condPrior_eq ];
  · rw [ DisclosureGame.restrict_V ];
  · exact K.C_nonempty;
  · exact K.C_subset

/-
Pooling all senders of `m` on `m` yields an attainable coalition payoff
(reproved locally, cf. `vbar_pooling_mem`).
-/
lemma gp_vbar_pooling_mem (H : DisclosureGame T Msg) {m : Msg} (hm : m ∈ H.𝓜) :
    H.vbar (H.condPrior (H.canSend m)) ∈ H.coalitionPayoffs := by
  revert H;
  intro H hm
  set C := H.canSend m with hCdef
  have hC_nonempty : C.Nonempty := H.canSend_nonempty hm
  have hC_subset : C ⊆ H.Θ := Finset.filter_subset _ _
  set σ' : Strategy (H.restrict C hC_nonempty hC_subset) := ⟨fun θ m' => if m' = m then 1 else 0, by
    intro θ hθ
    simp [simplexOn];
    exact ⟨ fun _ => by split_ifs <;> norm_num, fun a ha => by rintro rfl; exact ha ( Finset.mem_filter.mp hθ |>.2 |> fun h => by aesop ) ⟩⟩ with hσ'def
  generalize_proofs at *;
  refine' ⟨ ⟨ C, hC_nonempty, hC_subset, σ', _, H.vbar ( H.condPrior C ), _ ⟩, rfl ⟩;
  · simp +decide [ Strategy.evidence, DisclosureGame.preimageSetFull ];
    simp +decide [ Finset.subset_iff, DisclosureGame.preimageSet, Strategy.msgSupport, σ' ];
    simp +decide [ C, DisclosureGame.canSend, simplexSupport ];
    simp +decide [ preimageFull, Set.Nonempty ];
    unfold preimage; aesop;
  · intro m' hm'
    have h_m'_eq_m : m' = m := by
      contrapose! hm'; simp_all +decide [ Strategy.evidence ] ;
      simp +decide [ Strategy.msgSupport, hm' ]
    rw [h_m'_eq_m]
    convert H.vbar_mem (zeroExt_mem_simplex hC_subset (DisclosureGame.condPrior_mem_simplex hC_nonempty hC_subset)) using 1
    congr! 1
    ext θ; simp [σ', Strategy.coalitionBelief]
    simp +decide [zeroExt, Strategy.belief, Strategy.onPathProb, DisclosureGame.condPrior]
    simp +decide [← Finset.sum_div _ _ _, DisclosureGame.priorMeasure]
    by_cases h : ∑ θ ∈ C, H.μ0 θ = 0 <;> simp +decide [h];
    rw [ zeroExt_eq_self ( DisclosureGame.condPrior_mem_simplex hC_nonempty hC_subset ) ]

/-
**Union pooling bound.** Under QC and M-C, pooling `K.C ∪ K'.C` (with `K`
attaining `max 𝒲_{Θt}` and `K'` a coalition of the residual `Θt ∖ K.C`) yields a
value not exceeding `K.w`. This is the middle of `merging`'s proof.
-/
lemma gp_union_payoff_le (hQC : G.QC) (hMC : G.MC)
    {Θt : Finset T} (hΘne : Θt.Nonempty) (hΘsub : Θt ⊆ G.Θ)
    (K : (G.restrict Θt hΘne hΘsub).Coalition)
    (hw : IsGreatest (G.restrict Θt hΘne hΘsub).coalitionPayoffs K.w)
    (hne' : (Θt \ K.C).Nonempty) (hsub' : (Θt \ K.C) ⊆ G.Θ)
    (K' : (G.restrict (Θt \ K.C) hne' hsub').Coalition) :
    G.vbar (G.condPrior (K.C ∪ K'.C)) ≤ K.w := by
  obtain ⟨m'', hm'', hm''eq⟩ : ∃ m'' ∈ (G.restrict Θt hΘne hΘsub).𝓜, (G.restrict Θt hΘne hΘsub).canSend m'' = K.C ∪ K'.C := by
    obtain ⟨⟨m, hm₁, hm₂⟩, _⟩ := pooling_dominance (gp_restrict_QC hΘne hΘsub hQC) (restrict_MC hΘne hΘsub hMC) K
    obtain ⟨m', hm'₁, hm'₂⟩ : ∃ m' ∈ (G.restrict (Θt \ K.C) hne' hsub').𝓜, (G.restrict (Θt \ K.C) hne' hsub').canSend m' = K'.C := by
      exact (pooling_dominance (gp_restrict_QC hne' hsub' hQC) (restrict_MC hne' hsub' hMC) K').1;
    obtain ⟨m'', hm''₁, hm''₂⟩ := restrict_MC hΘne hΘsub hMC m hm₁ m' (by
    simp_all +decide [ DisclosureGame.restrictMsgSpace ];
    exact ⟨ _, hm'₁.choose_spec.1.1, hm'₁.choose_spec.2 ⟩);
    simp_all +decide [ DisclosureGame.restrictMsgSpace, DisclosureGame.canSend, DisclosureGame.preimageFull ];
    simp_all +decide [ Finset.ext_iff, Set.ext_iff, preimage ];
    grind +splitImp;
  convert hw.2 _ using 1;
  convert gp_vbar_pooling_mem ( G.restrict Θt hΘne hΘsub ) hm'' using 1;
  rw [ hm''eq, DisclosureGame.vbar, DisclosureGame.vbar ];
  rw [ Partition.restrict_condPrior_eq ];
  · grind +qlia;
  · exact ⟨ _, Finset.mem_union_left _ ( K.C_nonempty.choose_spec ) ⟩;
  · exact Finset.union_subset ( K.C_subset ) ( K'.C_subset.trans ( Finset.sdiff_subset ) )

/-- **No merging up under QC\*.** Removing a coalition attaining `max 𝒲_R`
cannot raise the residual maximum. -/
lemma qcstar_no_merge (hQC : G.QC) (hMC : G.MC) (hQCs : G.QCStar)
    {Θt : Finset T} (hΘne : Θt.Nonempty) (hΘsub : Θt ⊆ G.Θ)
    (K : (G.restrict Θt hΘne hΘsub).Coalition)
    (hw : IsGreatest (G.restrict Θt hΘne hΘsub).coalitionPayoffs K.w)
    (hne' : (Θt \ K.C).Nonempty) (hsub' : (Θt \ K.C) ⊆ G.Θ) {w' : ℝ}
    (hw' : IsGreatest (G.restrict (Θt \ K.C) hne' hsub').coalitionPayoffs w') :
    w' ≤ K.w := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨K', hK'w⟩ : ∃ K' : (G.restrict (Θt \ K.C) hne' hsub').Coalition, K'.w = w' := hw'.1
  have hvK : G.vbar (G.condPrior K.C) = K.w := gp_coalition_vbar hQC hMC hΘne hΘsub K hw
  have hvK' : G.vbar (G.condPrior K'.C) = w' := by
    have := gp_coalition_vbar hQC hMC hne' hsub' K' (by rw [hK'w]; exact hw')
    rw [this, hK'w]
  have hle : G.vbar (G.condPrior (K.C ∪ K'.C)) ≤ K.w :=
    gp_union_payoff_le hQC hMC hΘne hΘsub K hw hne' hsub' K'
  have hKsubΘ : K.C ⊆ G.Θ := K.C_subset.trans hΘsub
  have hK'subΘ : K'.C ⊆ G.Θ := K'.C_subset.trans hsub'
  have hdisjCC' : Disjoint K.C K'.C := by
    refine Finset.disjoint_left.mpr (fun x hxK hxK' => ?_)
    exact (Finset.mem_sdiff.mp (K'.C_subset hxK')).2 hxK
  have hne_cp : G.condPrior K.C ≠ G.condPrior K'.C := by
    obtain ⟨θ, hθ⟩ := K.C_nonempty
    intro heq
    have h1 : 0 < G.condPrior K.C θ := condPrior_pos K.C_nonempty hKsubΘ hθ
    have h2 : G.condPrior K'.C θ = 0 :=
      condPrior_of_not_mem (fun hc => Finset.disjoint_left.mp hdisjCC' hθ hc)
    rw [heq, h2] at h1; exact lt_irrefl _ h1
  obtain ⟨l, hl, hunion⟩ := gp_condPrior_union K.C_nonempty K'.C_nonempty hKsubΘ hK'subΘ hdisjCC'
  have hqc := hQCs (G.condPrior K.C)
      (simplexOn_mono hKsubΘ (condPrior_mem_simplex K.C_nonempty hKsubΘ))
    (G.condPrior K'.C)
      (simplexOn_mono hK'subΘ (condPrior_mem_simplex K'.C_nonempty hK'subΘ)) hne_cp l hl
  rw [← hunion, hvK, hvK', min_eq_left hcon.le] at hqc
  linarith

/-
Under M-C and QC\*, every greedy-prefix payoff equals the residual maximum.
-/
lemma qcstar_prefix_stepMax (hMC : G.MC) (hQCs : G.QCStar) (Q : G.GreedyPrefix)
    (hQ : Q.IsGreedy) (t : Fin Q.card) :
    Q.w t = sSup (Q.stepPayoffs t) := by
  revert t;
  -- By definition of `QCStar`, we know that `QC` holds.
  have hQC : G.QC := by
    intro μ hμ μ' hμ' l hl
    by_cases h : μ = μ';
    · simp +decide [ h, ← add_mul ];
    · exact le_of_lt ( hQCs μ hμ μ' hμ' h l hl );
  intro t
  induction' t with t ih;
  induction' t using Nat.strong_induction_on with t ih;
  refine' IsGreatest.unique ( hQ ⟨ t, ih ⟩ ) ⟨ _, fun x hx => _ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · exact isGreatest_sSup_coalitionPayoffs _ |>.1;
    · apply Q.genResidual_greedyLower_le_sSup;
      grind +qlia;
    · intro t' ht'
      obtain ⟨K, hKC, hKw⟩ := prefix_cell_coalition Q t';
      have hKmax : IsGreatest (G.restrict (prefixResidual G.Θ Q.C t') (Q.prefixResidual_nonempty t') (Q.prefixResidual_subset t')).coalitionPayoffs K.w := by
        convert isGreatest_sSup_coalitionPayoffs _ using 1;
        grind;
      have hKmax' : IsGreatest (G.restrict (prefixResidual G.Θ Q.C t' \ K.C) (by
      have hKmax' : prefixResidual G.Θ Q.C t' \ K.C = prefixResidual G.Θ Q.C ⟨t, ih⟩ := by
        rw [ hKC, prefix_residual_step Q ht' ];
      exact hKmax'.symm ▸ Q.prefixResidual_nonempty ⟨ t, ih ⟩) (by
      exact fun x hx => Finset.mem_sdiff.mp hx |>.1 |> Finset.mem_sdiff.mp |>.1)).coalitionPayoffs (sSup (Q.stepPayoffs ⟨t, ih⟩)) := by
        have hKmax' : IsGreatest (G.restrict (prefixResidual G.Θ Q.C ⟨t, ih⟩) (Q.prefixResidual_nonempty ⟨t, ih⟩) (Q.prefixResidual_subset ⟨t, ih⟩)).coalitionPayoffs (sSup (Q.stepPayoffs ⟨t, ih⟩)) := by
          convert isGreatest_sSup_coalitionPayoffs _ using 1
        generalize_proofs at *;
        convert hKmax' using 1;
        convert Partition.restrict_eq_of_eq _ _ _ _ _ using 2;
        any_goals exact prefixResidual G.Θ Q.C ⟨ t, ih ⟩;
        any_goals assumption;
        · simp +decide [ hKC, prefix_residual_step Q ht' ];
        · rfl
      generalize_proofs at *;
      have := qcstar_no_merge hQC hMC hQCs ‹_› ‹_› K hKmax ‹_› ‹_› hKmax';
      linarith;
  · exact ( isGreatest_sSup_coalitionPayoffs _ ).2 hx.1

/-! ## Theorem 1(i), full "no run halts" form -/

/-- **Theorem 1(i)**, extension step. Under M-C and QC*, every greedy prefix
has a non-empty greedy constraint set at its final residual: no run of the
greedy algorithm halts. -/
theorem qcstar_prefix_extends (hMC : G.MC) (hQCs : G.QCStar)
    (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) :
    Q.extensionConstraint.Nonempty := by
  have hQC : G.QC := by
    intro μ hμ μ' hμ' l hl
    by_cases h : μ = μ'
    · rw [h]
      have hfe : (fun θ => l * μ' θ + (1 - l) * μ' θ) = μ' := by funext θ; ring
      rw [hfe, min_self]
    · exact le_of_lt (hQCs μ hμ μ' hμ' h l hl)
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
      qcstar_prefix_stepMax hMC hQCs Q hQ lastIdx
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
    have hle := qcstar_no_merge hQC hMC hQCs (Q.prefixResidual_nonempty lastIdx)
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

/-- **Theorem 1(i)**, full form. Under M-C and QC*, every greedy prefix
extends to a greedy partition of `G` (which is then a coalition-proof PBE
partition by `cppbe_characterization`): every run of the greedy algorithm
terminates in a coalition-proof PBE partition. -/
theorem one_noHalt_full (hMC : G.MC) (hQCs : G.QCStar)
    (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) :
    ∃ P : Partition G, P.IsGreedy ∧ Q.card ≤ P.card ∧
      ∀ (s : Fin Q.card) (t : Fin P.card), (s : ℕ) = (t : ℕ) →
        P.C t = Q.C s ∧ P.w t = Q.w s :=
  extend_engine (fun Q' hQ' => qcstar_prefix_extends hMC hQCs Q' hQ') Q hQ

/-! ## Theorem 5 (payoff degradation), full "no run halts" form -/

/-
**Theorem 5** (payoff degradation), extension step. Under the payoff-degradation
property, every greedy prefix has a non-empty greedy constraint set at its
final residual, already in prefix-extension form.
-/
theorem degrade_prefix_extends (hdeg : G.DegradationProperty)
    (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) :
    Q.extensionConstraint.Nonempty := by
  by_cases h : 0 < Q.card <;> simp_all +decide [ GreedyPrefix.extensionConstraint ];
  · refine' ⟨ Min.min ( sSup ( ( G.restrict Q.finalResidual Q.finalResidual_nonempty Q.finalResidual_subset ).coalitionPayoffs ) ) ( Q.w ⟨ Q.card - 1, Nat.sub_lt h zero_lt_one ⟩ ), _, _ ⟩ <;> simp +decide [ hQ, h ];
    · refine' ⟨ _, _ ⟩;
      · apply deg_realize hdeg Q.finalResidual_nonempty Q.finalResidual_subset
        generalize_proofs at *; (
        refine' le_min _ _;
        · obtain ⟨ θ, hθ ⟩ := ‹Q.finalResidual.Nonempty›
          generalize_proofs at *; (
          exact le_trans ( greedyprefix_vMin_le_skeptical ( by solve_by_elim ) ) ( Q.genResidual_skeptical_le_sSup Finset.univ ( fun _ _ _ _ => Finset.mem_univ _ ) hθ ) |> le_trans <| le_rfl;);
        · have := hQ ⟨ Q.card - 1, by omega ⟩;
          have := this.1.2.1; simp_all +decide [ GreedyPrefix.greedyLower ] ;
          exact le_trans ( greedyprefix_vMin_le_skeptical ( Q.finalResidual_nonempty.choose_spec |> fun h => Q.finalResidual_subset h ) ) ( this _ ( Q.finalResidual_subset_prefixResidual _ Q.finalResidual_nonempty.choose_spec ) ));
        exact min_le_left _ _;
      · intro b hb; refine' ⟨ _, _ ⟩;
        · convert Q.genResidual_skeptical_le_sSup Finset.univ ( fun _ _ _ _ => Finset.mem_univ _ ) hb using 1;
        · refine' le_trans _ ( hQ ⟨ Q.card - 1, Nat.sub_lt h zero_lt_one ⟩ |>.1 |>.2.1 );
          refine' Finset.le_sup' _ _;
          exact Q.finalResidual_subset_prefixResidual _ hb;
    · refine' ⟨ _, _ ⟩
      all_goals generalize_proofs at *;
      · apply deg_realize hdeg ‹_› ‹_› (by
        refine' le_min _ _;
        · refine' le_trans _ ( Q.genResidual_greedyLower_le_sSup Finset.univ ( fun _ _ _ _ => Finset.mem_univ _ ) );
          obtain ⟨ θ, hθ ⟩ := ‹Q.finalResidual.Nonempty›; exact le_trans ( greedyprefix_vMin_le_skeptical ( by aesop ) ) ( Finset.le_sup' ( fun x => G.skeptical x ) hθ ) ;
        · have := hQ ⟨ Q.card - 1, by omega ⟩;
          have := this.1.2.1; simp_all +decide [ GreedyPrefix.greedyLower ] ;
          exact le_trans ( greedyprefix_vMin_le_skeptical ( Q.finalResidual_subset ( Classical.choose_spec ( Q.finalResidual_nonempty ) ) ) ) ( this _ ( Classical.choose_spec ( Q.finalResidual_nonempty ) |> fun h => Q.finalResidual_subset_prefixResidual _ h ) )) (by
        exact min_le_left _ _);
      · grind +qlia;
  · refine' ⟨ _, _, _ ⟩;
    exact sSup ( ( G.restrict Q.finalResidual Q.finalResidual_nonempty Q.finalResidual_subset ).coalitionPayoffs );
    · exact isGreatest_sSup_coalitionPayoffs _ |>.1;
    · intro θ hθ;
      convert Q.genResidual_skeptical_le_sSup Finset.univ ( fun _ _ _ _ => Finset.mem_univ _ ) hθ using 1

/-- **Theorem 5** (payoff degradation), full form. Under the payoff-degradation
property, every greedy prefix extends to a greedy partition of `G`: no run of
the greedy algorithm halts. -/
theorem degrade_noHalt_full (hdeg : G.DegradationProperty)
    (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) :
    ∃ P : Partition G, P.IsGreedy ∧ Q.card ≤ P.card ∧
      ∀ (s : Fin Q.card) (t : Fin P.card), (s : ℕ) = (t : ℕ) →
        P.C t = Q.C s ∧ P.w t = Q.w s :=
  extend_engine (fun Q' hQ' => degrade_prefix_extends hdeg Q' hQ') Q hQ

end DisclosureGame

end CPD
