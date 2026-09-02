import CPD.CoalitionProof

/-!
# Coalition-optimal equilibrium partitions (Appendix C)

Appendix C strengthens the greedy partition of §5 into a fully constructive
witness for Theorem 1's existence claim, by choosing at each step `t` a
coalition of the residual game `G|_{R_t}` that attains the *maximum* of the
coalition-payoff set `𝒲_{R_t}` (not merely something feasible and IR). This
file proves:

* **Lemma C.1** (remaining-games): for a message `m` on-path at step `t`
  (i.e. `m ∈ 𝓜_{R_t}`), the types forced to send `m` stay inside the residual
  `R_t` (`forced_subset_thetaStep`); the conditional prior on
  `P(m) ∩ R_t` is a feasible belief at `m` (`condPrior_inter_mem_feasibleBeliefs`);
  and `𝒲_{R_t}` is non-empty, compact, and its maximum `max 𝒲_{R_t}`
  (`stepMax`) dominates the residual skeptical floor `max_{θ ∈ R_t} u̲(θ)`
  (`isGreatest_stepMax`, `greedyLower_le_stepMax`).
* **Definition C.1** (COE partition): a partition where every step attains
  `w_t = max 𝒲_{R_t}` and payoffs are non-increasing (`IsCOE`).
* **Lemma C.2** (coe-greedy): every COE partition is greedy
  (`IsCOE.isGreedy`), and conversely a greedy partition is COE iff
  `max 𝒲_{R_t} ≤ w_{t-1}` for every `t` (`isCOE_iff_of_greedy`).
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

namespace Partition

variable (P : Partition G)

/-! ## Lemma remaining-games -/

/-
**(i)** For `m ∈ 𝓜_{R_t}`, the forced types of `m` lie in `R_t`.
-/
lemma forced_subset_thetaStep (t : Fin P.card) {m : Msg}
    (hm : m ∈ G.restrictMsgSpace (thetaStep P.C t)) :
    G.forced m ⊆ thetaStep P.C t := by
  -- By definition of `restrictMsgSpace`, there exists some θ₀ in `thetaStep P.C t` such that `m ∈ G.M θ₀`.
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ thetaStep P.C t, m ∈ G.M θ₀ := by
    unfold DisclosureGame.restrictMsgSpace at hm; aesop;
  intro θ hθ
  by_contra h_contra
  obtain ⟨s', hs'⟩ : ∃ s', θ ∈ P.C s' ∧ s' < t := by
    have hθ_in_C : θ ∈ G.Θ := by
      exact Finset.mem_filter.mp hθ |>.1
    have hθ_in_C' : ∃ s', θ ∈ P.C s' := by
      have := P.C_cover hθ_in_C; aesop;
    obtain ⟨s', hs'⟩ := hθ_in_C'
    have hs'_lt_t : s' < t := by
      exact lt_of_not_ge fun h => h_contra <| Finset.mem_biUnion.mpr ⟨ s', Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h ⟩, hs' ⟩
    use s';
  have h_mem_evidence : m ∈ (P.σ s').evidence := by
    have h_mem_evidence : (P.σ s').σ θ ∈ simplexOn {m} := by
      convert P.σ s' |>.mem θ _ using 1;
      · rw [ DisclosureGame.forced ] at hθ ; aesop;
      · exact hs'.1;
    have h_mem_evidence : (P.σ s').σ θ m > 0 := by
      have := h_mem_evidence.2; simp_all +decide [ Finset.sum_eq_single m ] ;
    exact Set.mem_iUnion₂.mpr ⟨ θ, hs'.1, h_mem_evidence ⟩;
  have h_mem_preimage : θ₀ ∈ G.preimageSet (thetaStep P.C s') (P.σ s').evidence := by
    refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
    · obtain ⟨ s'', hs'' ⟩ := Finset.mem_biUnion.mp hθ₀.1;
      exact Finset.mem_biUnion.mpr ⟨ s'', Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_trans hs'.2.le ( Finset.mem_filter.mp hs''.1 |>.2 ) ⟩, hs''.2 ⟩;
    · exact ⟨ m, hθ₀.2, h_mem_evidence ⟩;
  obtain ⟨s'', hs''⟩ : ∃ s'', t ≤ s'' ∧ θ₀ ∈ P.C s'' := by
    unfold thetaStep at hθ₀; aesop;
  have := P.exclusive s' h_mem_preimage;
  exact absurd ( P.C_disjoint s' s'' ( ne_of_lt ( lt_of_lt_of_le hs'.2 hs''.1 ) ) ) ( Finset.not_disjoint_iff.mpr ⟨ θ₀, this, hs''.2 ⟩ )

/-
**(ii)** For `m ∈ 𝓜_{R_t}`, the conditional prior on `P(m) ∩ R_t` is a
feasible belief: `μ⁰_{P(m)∩R_t} ∈ 𝓕(m)`.
-/
lemma condPrior_inter_mem_feasibleBeliefs (t : Fin P.card) {m : Msg}
    (hm : m ∈ G.restrictMsgSpace (thetaStep P.C t)) :
    G.condPrior (G.canSend m ∩ thetaStep P.C t) ∈ G.feasibleBeliefs m := by
  rw [G.feasibleBeliefs_eq_polytope];
  · refine' ⟨ _, _, _, _ ⟩;
    · refine' simplexOn_mono _ _;
      exact G.canSend m ∩ thetaStep P.C t;
      · exact Finset.inter_subset_left.trans ( Finset.filter_subset _ _ );
      · refine' ⟨ _, _, _ ⟩;
        · intro θ; by_cases hθ : θ ∈ G.canSend m ∩ thetaStep P.C t <;> simp +decide [ hθ, condPrior_of_mem, condPrior_of_not_mem ] ;
          exact div_nonneg ( G.μ0_mem.1 θ ) ( Finset.sum_nonneg fun _ _ => G.μ0_mem.1 _ );
        · convert G.condPrior_mem_simplex _ _ |> fun h => h.2.1;
          · simp_all +decide [ DisclosureGame.restrictMsgSpace ];
            exact ⟨ hm.choose, Finset.mem_inter.mpr ⟨ Finset.mem_filter.mpr ⟨ G.Θ_nonempty.choose_spec |> fun h => by
              exact P.thetaStep_subset t hm.choose_spec.1, by
              exact ⟨ m, Finset.mem_inter.mpr ⟨ hm.choose_spec.2, Finset.mem_singleton_self _ ⟩ ⟩ ⟩, hm.choose_spec.1 ⟩ ⟩;
          · exact Finset.inter_subset_left.trans ( Finset.filter_subset _ _ );
        · intro θ hθ; rw [ DisclosureGame.condPrior_of_not_mem ] ; aesop;
    · intro θ hθ; rw [ DisclosureGame.condPrior_of_not_mem ] ; aesop;
    · intro θ hθ θ' hθ'
      have hθ_in_C : θ ∈ G.canSend m ∩ thetaStep P.C t := by
        have hθC : θ ∈ G.canSend m := by
          simp_all +decide [ DisclosureGame.canSend, DisclosureGame.forced ];
          simp_all +decide [ DisclosureGame.preimageFull ];
          simp_all +decide [ preimage ];
        exact Finset.mem_inter.mpr ⟨ hθC, P.forced_subset_thetaStep t hm hθ ⟩
      have hθ'_in_C : θ' ∈ G.canSend m ∩ thetaStep P.C t := by
        exact Finset.mem_inter.mpr ⟨ Finset.mem_filter.mpr ⟨ G.Θ_nonempty.choose_spec |> fun h => by
          exact Finset.mem_filter.mp hθ' |>.1, by
          exact ⟨ m, by rw [ DisclosureGame.forced ] at hθ'; aesop ⟩ ⟩, by
          exact P.forced_subset_thetaStep t hm hθ' ⟩;
      rw [ DisclosureGame.condPrior_of_mem hθ_in_C, DisclosureGame.condPrior_of_mem hθ'_in_C ];
      ring;
    · intro θ hθ θF hθF;
      by_cases hθC : θ ∈ G.canSend m ∩ thetaStep P.C t <;> by_cases hθFC : θF ∈ G.canSend m ∩ thetaStep P.C t <;> simp_all +decide [ DisclosureGame.condPrior_of_mem, DisclosureGame.condPrior_of_not_mem ];
      · ring_nf; norm_num;
      · exact False.elim ( hθFC ( by
          exact Finset.mem_filter.mpr ⟨ G.Θ_nonempty.choose_spec |> fun h => by
            exact Finset.mem_filter.mp hθF |>.1, by
            unfold DisclosureGame.forced at hθF; aesop; ⟩ ) ( by
          exact P.forced_subset_thetaStep t hm hθF ) );
      · exact mul_nonneg ( G.μ0_mem.1 θ ) ( div_nonneg ( G.μ0_mem.1 θF ) ( Finset.sum_nonneg fun _ _ => G.μ0_mem.1 _ ) );
  · exact G.restrictMsgSpace_subset ( P.thetaStep_subset t ) hm

/-- **Lemma C.1**: `max 𝒲_{R_t}`, the maximum of the remaining
coalition-payoff set. -/
noncomputable def stepMax (t : Fin P.card) : ℝ := sSup (P.stepPayoffs t)

/-
**Lemma C.1(iii).** `𝒲_{R_t}` is non-empty and compact, and
`max 𝒲_{R_t} ≥ max_{θ∈R_t} u̲(θ)`.
-/
lemma isGreatest_stepMax (t : Fin P.card) :
    IsGreatest (P.stepPayoffs t) (P.stepMax t) := by
  refine' ⟨ _, fun x hx => _ ⟩;
  · apply_rules [ IsCompact.sSup_mem, isCompact_coalitionPayoffs ];
    convert coalitionPayoffs_nonempty _;
  · exact le_csSup ( by exact ( DisclosureGame.isCompact_coalitionPayoffs _ ).bddAbove ) hx

/-
For any game `H` and on-path-able message `m`, the lower-envelope value at
the conditional prior on `P(m)` is an attainable coalition payoff: the coalition
of all types able to send `m`, all sending `m`, has belief `μ⁰_{P(m)}`.
-/
lemma vlow_condPrior_canSend_mem_coalitionPayoffs (H : DisclosureGame T Msg)
    {m : Msg} (hm : m ∈ H.𝓜) :
    H.vlow (H.condPrior (H.canSend m)) ∈ H.coalitionPayoffs := by
  revert hm;
  intro hm
  set C := H.canSend m with hC_def
  have hC_nonempty : C.Nonempty := by
    have := H.cover;
    replace this := Set.ext_iff.mp this m; simp_all +decide [ Set.ext_iff ] ;
    exact ⟨ this.choose, Finset.mem_filter.mpr ⟨ this.choose_spec.1, ⟨ m, by simpa using this.choose_spec.2 ⟩ ⟩ ⟩
  have hC_subset : C ⊆ H.Θ := by
    exact Finset.filter_subset _ _
  set G' := H.restrict C hC_nonempty hC_subset with hG'_def
  set σ' : Strategy G' := { σ := fun θ m' => if m' = m then 1 else 0, mem := by
                              intro θ hθ
                              simp [simplexOn];
                              exact ⟨ fun _ => by split_ifs <;> norm_num, fun a ha => by rintro rfl; exact ha ( Finset.mem_filter.mp hθ |>.2 |> fun h => by aesop ) ⟩ } with hσ'_def
  generalize_proofs at *;
  -- Show that the coalition strategy σ' satisfies the conditions for being a valid strategy.
  have hσ'_valid : σ'.evidence = {m} := by
    ext m'
    simp [σ', Strategy.evidence, Strategy.msgSupport, simplexSupport];
    grind +splitIndPred
  have hσ'_belief : σ'.belief m = H.condPrior C := by
    ext θ; simp +decide [ Strategy.belief, Strategy.onPathProb ] ;
    simp +zetaDelta at *;
    have := H.condPrior_mem_simplex hC_nonempty hC_subset; simp_all +decide [ simplexOn ] ;
    rw [ Finset.sum_subset ( show C ⊆ Finset.univ from Finset.subset_univ _ ) fun x hx₁ hx₂ => this.2.2 x hx₂ ] ; aesop;
  -- Show that the coalition strategy σ' satisfies the conditions for being a valid coalition.
  have hσ'_coalition : H.preimageSetFull σ'.evidence ⊆ C := by
    simp +decide [ hσ'_valid, hC_def, DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
    simp +decide [ DisclosureGame.canSend, preimageFull, preimage ];
    simp +contextual [ Finset.subset_iff, Set.Nonempty ];
  refine' ⟨ ⟨ C, hC_nonempty, hC_subset, σ', hσ'_coalition, H.vlow ( σ'.coalitionBelief m ), _ ⟩, _ ⟩ <;> simp_all +decide [ Strategy.coalitionBelief ];
  · convert H.vlow_mem _ using 1;
    exact zeroExt_mem_simplex hC_subset ( condPrior_mem_simplex hC_nonempty hC_subset );
  · rw [ ← hσ'_belief, zeroExt_eq_self ];
    exact hσ'_belief.symm ▸ DisclosureGame.condPrior_mem_simplex hC_nonempty hC_subset

/-
In the restricted game `G|_S`, the conditional prior on the senders of `m`
equals the conditional prior (in `G`) on `P(m) ∩ S`.
-/
lemma condPrior_canSend_restrict {S : Finset T} (hne : S.Nonempty)
    (hsub : S ⊆ G.Θ) (m : Msg) :
    (G.restrict S hne hsub).condPrior ((G.restrict S hne hsub).canSend m)
      = G.condPrior (G.canSend m ∩ S) := by
  ext θ; by_cases hθ : θ ∈ G.canSend m ∩ S <;> simp +decide [ hθ, condPrior_of_mem, condPrior_of_not_mem ] ;
  · rw [ DisclosureGame.condPrior_of_mem ];
    · simp +decide [ DisclosureGame.restrict, DisclosureGame.priorMeasure ];
      simp +decide [ DisclosureGame.canSend, DisclosureGame.preimageFull ];
      rw [ show preimage G.M S { m } = preimage G.M G.Θ { m } ∩ S from ?_ ];
      · simp +decide [ DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
        rw [ ← Finset.sum_div _ _ _, div_div_div_cancel_right₀ ];
        · rw [ Finset.sum_congr rfl fun x hx => if_pos <| Finset.mem_of_mem_inter_right hx ] ; aesop;
        · exact ne_of_gt ( priorMeasure_pos hne hsub );
      · ext; simp [preimage];
        exact ⟨ fun h => ⟨ ⟨ hsub h.1, h.2 ⟩, h.1 ⟩, fun h => ⟨ h.2, h.1.2 ⟩ ⟩;
    · simp_all +decide [ DisclosureGame.canSend, DisclosureGame.preimageFull ];
      simp_all +decide [ preimage ];
  · rw [ DisclosureGame.condPrior_of_not_mem ];
    simp_all +decide [ DisclosureGame.canSend, DisclosureGame.preimageFull ];
    unfold preimage at *; aesop;

/-
**(iii, bound)** `max_{θ∈R_t} u̲(θ) ≤ max 𝒲_{R_t}`.
-/
lemma greedyLower_le_stepMax (t : Fin P.card) :
    P.greedyLower t ≤ P.stepMax t := by
  -- By definition of `greedyLower`, we know that for any θ ∈ thetaStep P.C t, G.s skeptics' θ ≤ P.stepMax t.
  have h_lower_bound : ∀ θ ∈ thetaStep P.C t, G.skeptical θ ≤ P.stepMax t := by
    intro θ hθ
    obtain ⟨m, hm₁, μ, hm₂, hmin, hsk⟩ := G.skeptical_isWellDefined (by
    exact P.thetaStep_subset t hθ : θ ∈ G.Θ)
    generalize_proofs at *;
    have hmR : m ∈ G.restrictMsgSpace (thetaStep P.C t) := by
      exact Finset.mem_biUnion.mpr ⟨ θ, hθ, hm₁ ⟩
    generalize_proofs at *;
    have hν : G.vlow (G.condPrior (G.canSend m ∩ thetaStep P.C t)) ∈ P.stepPayoffs t := by
      convert vlow_condPrior_canSend_mem_coalitionPayoffs ( G.restrict ( thetaStep P.C t ) ( thetaStep_nonempty t ( P.C_nonempty t ) ) ( P.thetaStep_subset t ) ) hmR using 1;
      simp +decide [ DisclosureGame.vlow, condPrior_canSend_restrict ]
    generalize_proofs at *;
    have hν_le : G.vlow μ ≤ G.vlow (G.condPrior (G.canSend m ∩ thetaStep P.C t)) := by
      exact hmin ( P.condPrior_inter_mem_feasibleBeliefs t hmR )
    generalize_proofs at *;
    exact hsk.2.symm ▸ hν_le.trans ( P.isGreatest_stepMax t |>.2 hν );
  exact Finset.sup'_le _ _ h_lower_bound

/-! ## COE partitions -/

/-- **Definition C.1** (COE partition): for every `t`, `w_t = max 𝒲_{R_t}` and
`w_t ≤ w_{t-1}`. -/
def IsCOE : Prop :=
  ∀ t, IsGreatest (P.stepPayoffs t) (P.w t) ∧
       ∀ t' : Fin P.card, (t' : ℕ) + 1 = (t : ℕ) → P.w t ≤ P.w t'

variable {P}

/-
For a COE partition, `w_t = max 𝒲_{R_t}`.
-/
lemma IsCOE.w_eq_stepMax (h : P.IsCOE) (t : Fin P.card) : P.w t = P.stepMax t := by
  exact IsGreatest.unique ( h t |>.1 ) ( P.isGreatest_stepMax t )

/-
**Lemma C.2(i)** (coe-greedy): every COE partition is greedy.
-/
lemma IsCOE.isGreedy (h : P.IsCOE) : P.IsGreedy := by
  intro t;
  refine' ⟨ _, fun x hx => _ ⟩;
  · exact ⟨ h t |>.1.1, by simpa only [ h.w_eq_stepMax t ] using P.greedyLower_le_stepMax t, h t |>.2 ⟩;
  · exact h t |>.1.2 hx.1

/-
Every COE partition is a coalition-proof PBE partition.
-/
lemma IsCOE.isCPPBEPartition (h : P.IsCOE) : P.IsCPPBEPartition := by
  -- By the characterization `cppbe_characterization : P.IsCPPBEPartition ↔ P.IsGreedy`, we use `h.isGreedy`.
  have hgreedy : P.IsGreedy := h.isGreedy
  exact ⟨P.cppbe_characterization.mpr hgreedy |>.1, P.cppbe_characterization.mpr hgreedy |>.2⟩

/-
**Lemma C.2(ii)** (coe-greedy): a greedy partition is COE iff
`max 𝒲_{R_t} ≤ w_{t-1}` for every `t`.
-/
lemma isCOE_iff_of_greedy (hg : P.IsGreedy) :
    P.IsCOE ↔ ∀ t : Fin P.card, ∀ t' : Fin P.card,
      (t' : ℕ) + 1 = (t : ℕ) → P.stepMax t ≤ P.w t' := by
  constructor <;> intro h <;> simp_all +decide [ Partition.IsCOE, Partition.IsGreedy ];
  · intros t t' ht'
    have := h t;
    convert this.2 t' ht' using 1;
    exact IsGreatest.unique ( isGreatest_stepMax P t ) ( this.1 );
  · intro t
    have h_w_eq_stepMax : P.w t = P.stepMax t := by
      apply le_antisymm;
      · exact hg t |>.1 |>.1 |> fun h => by simpa using P.isGreatest_stepMax t |>.2 h;
      · apply (hg t).2;
        constructor;
        · exact P.isGreatest_stepMax t |>.1;
        · exact ⟨ greedyLower_le_stepMax P t, h t ⟩
    refine ⟨?_, fun t' ht' => h_w_eq_stepMax ▸ h t t' ht'⟩
    rw [h_w_eq_stepMax]
    exact P.isGreatest_stepMax t

end Partition

end DisclosureGame

end CPD