import CPD.PBEChar
import CPD.CoalitionPayoffs

/-!
# Coalition-proof PBE (§5)

For a PBE partition `Π` of `G` and a target payoff `w̃`, `Θ(w̃) := ⋃_{t : w_t <
w̃} C_t` collects every type currently getting less than `w̃`. This file
formalizes:

* **Definition 9** (blocking coalition): a coalition `(C̃,σ̃,w̃)` of the
  restricted game `G|_{Θ(w̃)}` (so `Θ(w̃)` must be non-empty), i.e. a group of
  types each earning below `w̃` under `Π` that could jointly deviate to a new
  message and secure `w̃` for all of them (`BlockingCoalition`).
  A partition is **coalition-proof** (`IsCoalitionProof`) when it admits no
  blocking coalition.
* **Lemma B.1** (blocking on path): a blocking coalition contains every on-path user,
  in any cell, of any message its deviation employs (`blocking_on_path`).
* **Definition 10** (greedy partition): the partition built by Algorithm 3,
  where at each step `w_t` is the greatest attainable payoff of the residual
  game `G|_{R_t}` subject to the individual-rationality floor
  `max_{θ ∈ R_t} u̲(θ)` and the previous payoff `w_{t-1}` (`IsGreedy`).
* **Proposition 2** (cppbe-characterization): a partition is a coalition-proof
  PBE partition iff it is greedy (`cppbe_characterization`,
  `isCPPBEStrategy_iff_associated_greedy` for the strategy-level form).
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

namespace Partition

variable (P : Partition G)

/-- `Θ(w̃) := ⋃_{t : w_t < w̃} C_t`. -/
noncomputable def thetaBelow (wt : ℝ) : Finset T :=
  (Finset.univ.filter (fun t => P.w t < wt)).biUnion P.C

/-- `Θ(w̃) ⊆ Θ`. -/
lemma thetaBelow_subset (wt : ℝ) : P.thetaBelow wt ⊆ G.Θ := by
  rw [thetaBelow, Finset.biUnion_subset]
  intro t _
  exact P.C_subset t

/-- **Definition 9** (blocking coalition): a blocking coalition `(C̃, σ̃, w̃)`
of `Π` consists of a non-empty `Θ(w̃)` together with a coalition `(C̃, σ̃, w̃)`
of `G|_{Θ(w̃)}` with payoff `w̃`. -/
structure BlockingCoalition where
  /-- The blocking payoff `w̃`. -/
  wtil : ℝ
  /-- `Θ(w̃) ≠ ∅`. -/
  theta_ne : (P.thetaBelow wtil).Nonempty
  /-- `(C̃, σ̃, w̃)` as a coalition of `G|_{Θ(w̃)}`. -/
  K : Coalition (G.restrict (P.thetaBelow wtil) theta_ne (P.thetaBelow_subset wtil))
  /-- Its payoff is `w̃`. -/
  K_w : K.w = wtil

namespace BlockingCoalition

variable {P}

/-- The **evidence** `X̃ := X(σ̃)` of a blocking coalition. -/
def evidence (B : P.BlockingCoalition) : Set Msg := B.K.σ.evidence

end BlockingCoalition

/-- **Definition 9** (coalition-proof): `Π` admits no blocking coalition. -/
def IsCoalitionProof : Prop := IsEmpty P.BlockingCoalition

/-- A **coalition-proof PBE partition**: a PBE partition that is coalition-proof. -/
def IsCPPBEPartition : Prop := P.IsPBEPartition ∧ P.IsCoalitionProof

/--
**Lemma B.1** (blocking on path): a blocking coalition contains every on-path user, in
any cell, of any message its deviation employs.
-/
lemma blocking_on_path (hmono : Antitone P.w) (B : P.BlockingCoalition)
    (t : Fin P.card) :
    G.preimageSetFull (B.evidence ∩ P.evidence t) ∩ P.C t ⊆ B.K.C := by
  intro θ; simp +decide [ Set.subset_def ] ;
  intro hθ hθt; have := B.K.exclusive; simp_all +decide [ Set.subset_def, Finset.subset_iff ] ;
  convert this _ ; simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ] ;
  obtain ⟨ m, hm ⟩ := hθ.2;
  refine' ⟨ _, _ ⟩;
  · refine' Finset.mem_biUnion.mpr ⟨ t, _, hθt ⟩;
    simp_all +decide [ Partition.evidence ];
    obtain ⟨ θ', hθ' ⟩ := hm.2.1;
    obtain ⟨ θ'', hθ'' ⟩ := hθ'.1;
    have := B.K.C_subset; simp_all +decide [ Finset.subset_iff ] ;
    have := this ( show θ'' ∈ B.K.C from by
                    contrapose! hθ'; aesop; ) ; simp_all +decide [ Partition.thetaBelow ] ;
    obtain ⟨ a, ha₁, ha₂ ⟩ := this; exact lt_of_le_of_lt ( hmono ( show a ≤ t from by
                                                                    contrapose! hm;
                                                                    intro hm₁ hm₂ hm₃; have := P.exclusive t; simp_all +decide [ Set.subset_def, Finset.subset_iff ] ;
                                                                    exact absurd ( this ( show θ'' ∈ G.preimageSet ( thetaStep P.C t ) ( P.σ t ).evidence from by
                                                                                            simp_all +decide [ DisclosureGame.preimageSet, thetaStep ];
                                                                                            exact ⟨ ⟨ a, le_of_lt hm, ha₂ ⟩, ⟨ m, by
                                                                                              simp_all +decide [ Set.ext_iff, Strategy.evidence ];
                                                                                              obtain ⟨ i, hi₁, hi₂ ⟩ := hm₃; specialize hθ'' m; simp_all +decide [ Strategy.msgSupport ] ;
                                                                                              have := B.K.σ.mem θ''; simp_all +decide [ Strategy.mem ] ;
                                                                                              exact Classical.not_not.1 fun h => hθ''.2.ne' ( this.2.2 m h ) ⟩ ⟩ ) ) ( by
                                                                                            exact fun h => hm.ne ( P.C_disjoint _ _ ( ne_of_gt hm ) |> fun h' => False.elim <| Finset.disjoint_left.mp h' ha₂ h ) ) ) ) ha₁;
  · exact ⟨ m, hm.1, by simpa using hm.2.1 ⟩

/-- `𝒲_{R_t}`, the coalition-payoff set of the residual game `G_t = G|_{R_t}`. -/
noncomputable def stepPayoffs (t : Fin P.card) : Set ℝ :=
  (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t))
    (P.thetaStep_subset t)).coalitionPayoffs

/-- The greedy lower bound `max_{θ ∈ R_t} u̲(θ)`. -/
noncomputable def greedyLower (t : Fin P.card) : ℝ :=
  (thetaStep P.C t).sup' (thetaStep_nonempty t (P.C_nonempty t)) G.skeptical

/-- The greedy constraint set `𝒲_{R_t} ∩ [max_{θ∈R_t} u̲(θ), w_{t-1}]`. -/
noncomputable def greedyConstraint (t : Fin P.card) : Set ℝ :=
  {w | w ∈ P.stepPayoffs t ∧ P.greedyLower t ≤ w ∧
       ∀ t' : Fin P.card, (t' : ℕ) + 1 = (t : ℕ) → w ≤ P.w t'}

/-- **Definition 10** (greedy partition): `w_t = max(𝒲_{R_t} ∩ [max u̲, w_{t-1}])`. -/
def IsGreedy : Prop := ∀ t, IsGreatest (P.greedyConstraint t) (P.w t)

/-- The restricted games agree when the underlying type sets agree. -/
lemma restrict_eq_of_eq {S S' : Finset T} (hSS' : S = S')
    (hne : S.Nonempty) (hsub : S ⊆ G.Θ) (hne' : S'.Nonempty) (hsub' : S' ⊆ G.Θ) :
    G.restrict S hne hsub = G.restrict S' hne' hsub' := by
  subst hSS'; rfl

/-- The conditional prior is unchanged under passing to a nested restriction. -/
lemma restrict_condPrior_eq {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    {C : Finset T} (hCne : C.Nonempty) (hCS : C ⊆ S) :
    (G.restrict S hne hsub).condPrior C = G.condPrior C := by
  simpa using congrArg DisclosureGame.μ0
    (restrict_restrict (G := G) hne hsub hCne hCS)

/--
Under antitone payoffs, the below-threshold set at the least violating index
equals the residual set: if `w_t < wt` and `t` is the least index with this
property, then `Θ(wt) = R_t`.
-/
lemma thetaBelow_eq_thetaStep (hmono : Antitone P.w) {wt : ℝ} {t : Fin P.card}
    (hlt : P.w t < wt) (hmin : ∀ s : Fin P.card, P.w s < wt → t ≤ s) :
    P.thetaBelow wt = thetaStep P.C t := by
  ext s;
  simp +decide [ thetaBelow, thetaStep ];
  constructor;
  · exact fun ⟨ a, ha, hs ⟩ => ⟨ a, hmin a ha, hs ⟩;
  · exact fun ⟨ a, ha, hs ⟩ => ⟨ a, lt_of_le_of_lt ( hmono ha ) hlt, hs ⟩

/--
The payoff of cell `t` is attainable in the residual game `G|_{R_t}`.
-/
lemma w_mem_stepPayoffs (t : Fin P.card) : P.w t ∈ P.stepPayoffs t := by
  refine' ⟨ _, _ ⟩;
  refine' ⟨ P.C t, _, _, _, _, P.w t, _ ⟩;
  exact P.C_nonempty t;
  exact Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_rfl ⟩ );
  refine' ⟨ _, _ ⟩;
  exact fun θ m => ( P.σ t ).σ θ m;
  all_goals simp +decide [ DisclosureGame.preimageSetFull ];
  exact fun θ hθ => ⟨ fun m => P.σ t |>.mem θ hθ |>.1 m, P.σ t |>.mem θ hθ |>.2.1, fun m hm => P.σ t |>.mem θ hθ |>.2.2 m ( by simpa using hm ) ⟩;
  · convert P.exclusive t using 1;
  · intro m hm;
    convert P.payoff t m hm using 1;
    congr! 2;
    · exact restrict_restrict (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)
        (P.C_nonempty t)
        (Finset.subset_biUnion_of_mem P.C (Finset.mem_filter.mpr ⟨Finset.mem_univ t, le_rfl⟩))
    · congr! 1

/--
Antitone payoffs follow from the greedy consecutive constraint.
-/
lemma antitone_of_isGreedy (h : P.IsGreedy) : Antitone P.w := by
  intro i j hij;
  induction' j with j hj generalizing i;
  induction' j with j ih generalizing i;
  · rw [ le_antisymm hij ( Nat.zero_le _ ) ];
  · by_cases hi : i = ⟨ j + 1, hj ⟩;
    · rw [ hi ];
    · have := h ⟨ j + 1, hj ⟩;
      exact this.1.2.2 _ ( by simpa [ Fin.ext_iff ] ) |> le_trans <| ih ( Nat.lt_of_succ_lt hj ) <| Nat.le_of_lt_succ <| hij.lt_of_ne hi

/--
Greedy partitions are individually rational.
-/
lemma isIR_of_isGreedy (h : P.IsGreedy) : P.IsIR := by
  intro t θ hθ;
  refine' le_trans _ ( h t |>.1 |>.2.1 );
  exact Finset.le_sup' ( fun x => G.skeptical x ) ( Finset.mem_biUnion.mpr ⟨ t, by simp +decide [ hθ ], by simp +decide [ hθ ] ⟩ )

/--
Greedy partitions are coalition-proof.
-/
lemma isCoalitionProof_of_isGreedy (h : P.IsGreedy) : P.IsCoalitionProof := by
  constructor;
  rintro ⟨ wtil, theta_ne, K, K_w ⟩;
  -- Let `t := S.min' hSne`. Then `t ∈ S` gives `hlt : P.w t < wtil`, and `Finset.min'_le` gives `hmin : ∀ s : Fin P.card, P.w s < wtil → t ≤ s`.
  obtain ⟨t, ht⟩ : ∃ t : Fin P.card, P.w t < wtil ∧ ∀ s : Fin P.card, P.w s < wtil → t ≤ s := by
    have h_filter_nonempty : (Finset.univ.filter (fun s => P.w s < wtil)).Nonempty := by
      grind +locals;
    exact ⟨ Finset.min' _ h_filter_nonempty, Finset.mem_filter.mp ( Finset.min'_mem _ h_filter_nonempty ) |>.2, fun s hs => Finset.min'_le _ _ ( by simpa using hs ) ⟩;
  -- By `restrict_eq_of_eq`, the two restricted games are equal.
  have hgame : G.restrict (P.thetaBelow wtil) theta_ne (P.thetaBelow_subset wtil) = G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t) := by
    apply restrict_eq_of_eq;
    apply P.thetaBelow_eq_thetaStep (P.antitone_of_isGreedy h) ht.left ht.right;
  -- By `hgame`, we have `wtil ∈ P.stepPayoffs t`.
  have hWmem : wtil ∈ P.stepPayoffs t := by
    have hWmem : wtil ∈ (G.restrict (P.thetaBelow wtil) theta_ne (P.thetaBelow_subset wtil)).coalitionPayoffs := by
      exact ⟨ K, K_w ⟩;
    aesop;
  obtain ⟨hlow, hpred⟩ : P.greedyLower t ≤ P.w t ∧ ∀ t' : Fin P.card, (t' : ℕ) + 1 = (t : ℕ) → P.w t ≤ P.w t' := by
    exact ⟨ h t |>.1.2.1, fun t' ht' => h t |>.1.2.2 t' ht' ⟩;
  have hBmem : wtil ∈ P.greedyConstraint t := by
    refine' ⟨ hWmem, _, _ ⟩;
    · linarith;
    · grind +qlia;
  exact ht.1.not_ge ( h t |>.2 hBmem )

/--
A coalition-proof PBE partition is greedy.
-/
lemma isGreedy_of_isCPPBEPartition (h : P.IsCPPBEPartition) : P.IsGreedy := by
  refine' fun t => ⟨ _, fun w hw => _ ⟩;
  · refine' ⟨ P.w_mem_stepPayoffs t, _, _ ⟩;
    · convert P.isIR_iff_sup_le ( h.1.2 ) |>.1 h.1.1 t;
      simp +decide [ DisclosureGame.Partition.greedyLower ];
    · exact fun t' ht' => h.1.2 ( show t' ≤ t from Nat.le_of_succ_le ( by simp +decide [ ht' ] ) );
  · obtain ⟨hwStep, hwLow, hwPred⟩ := hw;
    by_cases hlt : P.w t < w;
    · have hmin : ∀ s : Fin P.card, P.w s < w → t ≤ s := by
        intro s hs
        by_contra h_contra
        have h_lt : s < t := by
          exact lt_of_not_ge h_contra;
        have h_pred : ∃ t' : Fin P.card, (t' : ℕ) + 1 = (t : ℕ) ∧ s ≤ t' := by
          use ⟨t.val - 1, by
            exact lt_of_le_of_lt ( Nat.pred_le _ ) t.2⟩
          generalize_proofs at *;
          exact ⟨ Nat.succ_pred_eq_of_pos ( pos_of_gt h_lt ), Nat.le_pred_of_lt h_lt ⟩;
        obtain ⟨ t', ht', ht'' ⟩ := h_pred;
        linarith [ hwPred t' ht', h.1.2 ht'' ];
      have heq : P.thetaBelow w = thetaStep P.C t := by
        exact P.thetaBelow_eq_thetaStep h.1.2 hlt hmin;
      obtain ⟨K, hK⟩ : ∃ K : Coalition (G.restrict (P.thetaBelow w) (by
      exact heq.symm ▸ thetaStep_nonempty t ( P.C_nonempty t )) (by
      exact heq.symm ▸ P.thetaStep_subset t)), K.w = w := by
        obtain ⟨K, hK⟩ : ∃ K : Coalition (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)), K.w = w := by
          exact hwStep;
        grind
      generalize_proofs at *;
      exact False.elim ( h.2.elim ⟨ w, by assumption, K, hK ⟩ );
    · linarith

/-- **Proposition 2** (cppbe-characterization): a partition is a
coalition-proof PBE partition iff it is greedy. -/
theorem cppbe_characterization : P.IsCPPBEPartition ↔ P.IsGreedy :=
  ⟨P.isGreedy_of_isCPPBEPartition,
   fun h => ⟨⟨P.isIR_of_isGreedy h, P.antitone_of_isGreedy h⟩,
             P.isCoalitionProof_of_isGreedy h⟩⟩

end Partition

variable (G) in
/-- A **coalition-proof PBE strategy**: associated with some coalition-proof PBE
partition. -/
def IsCPPBEStrategy (s : Strategy G) : Prop :=
  ∃ P : Partition G, P.IsCPPBEPartition ∧ P.AssociatedWith s

/-- **Proposition 2**, strategy-level form. -/
theorem isCPPBEStrategy_iff_associated_greedy (s : Strategy G) :
    G.IsCPPBEStrategy s ↔ ∃ P : Partition G, P.IsGreedy ∧ P.AssociatedWith s := by
  constructor
  · rintro ⟨P, hcp, hassoc⟩
    exact ⟨P, (Partition.cppbe_characterization P).mp hcp, hassoc⟩
  · rintro ⟨P, hg, hassoc⟩
    exact ⟨P, (Partition.cppbe_characterization P).mpr hg, hassoc⟩

end DisclosureGame

end CPD
