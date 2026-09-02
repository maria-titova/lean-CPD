import CPD.Coalition

/-!
# Partitions  (§3: Coalitions and Partitions)

A **partition** `Π = {(C_t, σ_t, w_t)}_{t=1}^T` (**Definition 3**):
pairwise-disjoint non-empty cells covering `Θ`, each `(C_t, σ_t, w_t)` a
coalition of the **residual game** `G_t := G|_{R_t}` with `R_t := ⋃_{s≥t}
C_s` (`thetaStep`).  The **associated partition strategy** `σ^Π`
(**Definition 4**), its existence together with the step bound `T ≤ |Θ|`
(**Remark 2**: partitions exist), and the lemma that distinct steps use
disjoint evidence: for `m ∈ X_t` only types in `C_t` send `m`, so `m` is on
path and `μ_{σ^Π}(·|m) = μ^{C_t,σ_t}(·|m)`.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

/-- The **residual type space at step `t`**: `R_t := ⋃_{s≥t} C_s`. -/
noncomputable def thetaStep {n : ℕ} (C : Fin n → Finset T) (t : Fin n) : Finset T :=
  (Finset.univ.filter (fun s => t ≤ s)).biUnion C

/-
`R_t` is non-empty when its cell is.
-/
lemma thetaStep_nonempty {n : ℕ} {C : Fin n → Finset T} (t : Fin n)
    (h : (C t).Nonempty) : (thetaStep C t).Nonempty := by
  exact h.mono ( Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_rfl ⟩ ) )

variable (G : DisclosureGame T Msg)

/-- **Definition 3** (partition) of `G`: `Π = {(C_t, σ_t, w_t)}_{t=1}^T`. -/
structure Partition where
  /-- The number `T` of coalitions. -/
  card : ℕ
  /-- The coalition type sets `C_1, …, C_T`. -/
  C : Fin card → Finset T
  /-- Each `C_t` is non-empty. -/
  C_nonempty : ∀ t, (C t).Nonempty
  /-- The `C_t` are pairwise disjoint. -/
  C_disjoint : ∀ s t, s ≠ t → Disjoint (C s) (C t)
  /-- Each `C_t ⊆ Θ`. -/
  C_subset : ∀ t, C t ⊆ G.Θ
  /-- The `C_t` cover `Θ`. -/
  C_cover : G.Θ ⊆ Finset.univ.biUnion C
  /-- For each `t`, `σ_t` a coalition strategy on `C_t`. -/
  σ : ∀ t, Strategy (G.restrict (C t) (C_nonempty t) (C_subset t))
  /-- The common payoffs `w_t`. -/
  w : Fin card → ℝ
  /-- Exclusivity at step `t`: `M⁻¹_{R_t}(X_t) ⊆ C_t`. -/
  exclusive : ∀ t, G.preimageSet (thetaStep C t) (σ t).evidence ⊆ C t
  /-- The payoff `w_t ∈ V(μ^{C_t,σ_t}(·|m))` for every `m ∈ X_t`. -/
  payoff : ∀ t, ∀ m ∈ (σ t).evidence, w t ∈ G.V ((σ t).coalitionBelief m)

variable {G}

namespace Partition

variable (P : Partition G)

/-
The full cover equality `Θ = ⋃_t C_t`.
-/
lemma cover_eq : G.Θ = Finset.univ.biUnion P.C := by
  refine' Finset.Subset.antisymm P.C_cover _;
  exact Finset.biUnion_subset.mpr fun t _ => P.C_subset t

/-- The **evidence used at step `t`**, `X_t := X(σ_t)`. -/
def evidence (t : Fin P.card) : Set Msg := (P.σ t).evidence

/-
`R_t ⊆ Θ`.
-/
lemma thetaStep_subset (t : Fin P.card) : thetaStep P.C t ⊆ G.Θ := by
  exact Finset.biUnion_subset.mpr fun s hs => P.C_subset s

/-
**The step bound `T ≤ |Θ|`.**
-/
lemma card_le : P.card ≤ G.Θ.card := by
  have h_step_bound : (Finset.biUnion Finset.univ P.C).card ≥ P.card := by
    rw [ Finset.card_biUnion ];
    · exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun _ _ => Finset.card_pos.mpr ( P.C_nonempty _ ) );
    · exact fun i _ j _ hij => P.C_disjoint i j hij;
  exact h_step_bound.trans ( Finset.card_le_card <| by simp +decide [ P.cover_eq ] )

/-- **Definition 4** (partition strategy): the associated strategy
`σ^Π : Θ → Δ𝓜` of a partition `Π`. -/
noncomputable def partitionStrategy (θ : T) (m : Msg) : ℝ :=
  if h : ∃ t, θ ∈ P.C t then (P.σ h.choose).σ θ m else 0

/-
**`σ^Π` is a sender strategy of `G`.**
-/
lemma partitionStrategy_mem (θ : T) (hθ : θ ∈ G.Θ) :
    P.partitionStrategy θ ∈ simplexOn (G.M θ) := by
  unfold Partition.partitionStrategy;
  convert ( P.σ ( Classical.choose ( show ∃ t, θ ∈ P.C t from by
                                      replace := P.cover_eq ▸ hθ; aesop; ) ) ).mem θ ( Classical.choose_spec ( show ∃ t, θ ∈ P.C t from by
                                                                                                              replace := P.cover_eq ▸ hθ; aesop; ) ) using 1
  generalize_proofs at *;
  grind

/-- The associated partition strategy packaged as a `Strategy G`. -/
noncomputable def toSenderStrategy : Strategy G where
  σ := P.partitionStrategy
  mem := P.partitionStrategy_mem

/-
**(i) The evidence sets are pairwise disjoint.**
-/
lemma evidence_disjoint {s t : Fin P.card} (hst : s ≠ t) :
    Disjoint (P.evidence s) (P.evidence t) := by
  by_contra h_inter
  obtain ⟨m, hs, ht⟩ : ∃ m, m ∈ P.evidence s ∧ m ∈ P.evidence t := by
    exact Set.not_disjoint_iff.mp h_inter;
  -- By the linear order on `Fin P.card`, WLOG t < s (otherwise swap the roles of s,t, since `Disjoint` is symmetric — handle both cases of `lt_or_gt_of_ne hst`).
  wlog hts : t < s generalizing s t;
  · grind +suggestions;
  · obtain ⟨θ, hθ⟩ : ∃ θ ∈ P.C s, 0 < (P.σ s).σ θ m := by
      unfold Partition.evidence at hs;
      unfold Strategy.evidence at hs; aesop;
    have hθ_in_Rt : θ ∈ thetaStep P.C t := by
      exact Finset.mem_biUnion.mpr ⟨ s, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hts.le ⟩, hθ.1 ⟩;
    have hθ_in_preimage : θ ∈ G.preimageSet (thetaStep P.C t) (P.σ t).evidence := by
      apply mem_preimageSet.mpr;
      exact ⟨ hθ_in_Rt, m, by
        have := (P.σ s).mem θ hθ.1; simp_all +decide [ CPD.simplexOn ] ;
        exact ⟨ Classical.not_not.1 fun h => hθ.2.ne' ( this.2.2 m h ), ht ⟩ ⟩;
    exact Finset.disjoint_left.mp ( P.C_disjoint s t hst ) hθ.1 ( P.exclusive t hθ_in_preimage )

/-
**(i) `X(σ^Π) = ⋃_t X_t`.**
-/
lemma evidence_eq_iUnion :
    P.toSenderStrategy.evidence = ⋃ t, P.evidence t := by
  ext m; simp [Strategy.evidence, Partition.toSenderStrategy, Partition.partitionStrategy];
  constructor <;> intro h;
  · obtain ⟨ θ, hθ, hm ⟩ := h
    obtain ⟨ t, ht ⟩ : ∃ t, θ ∈ P.C t := by
      have := P.C_cover hθ; aesop;
    simp_all +decide [ Strategy.msgSupport, Partition.partitionStrategy ];
    split_ifs at hm <;> simp_all +decide [ Partition.evidence ];
    exact ⟨ _, Set.mem_iUnion₂.mpr ⟨ θ, by
      exact ‹∃ t, θ ∈ P.C t›.choose_spec, hm ⟩ ⟩;
  · obtain ⟨ t, ht ⟩ := h;
    obtain ⟨ θ, hθ ⟩ := Set.mem_iUnion₂.mp ht;
    refine' ⟨ θ, _, _ ⟩ <;> simp_all +decide [ Strategy.msgSupport, Partition.partitionStrategy ];
    · exact P.C_subset t hθ.1;
    · split_ifs with h;
      · have := P.C_disjoint h.choose t; simp_all +decide [ Finset.disjoint_left ] ;
        grind;
      · exact False.elim ( h ⟨ t, hθ.1 ⟩ )

/-
**(ii) Types sending `m ∈ X_t` lie in `C_t`.**
-/
lemma mem_C_of_partitionStrategy_pos {t : Fin P.card} {m : Msg}
    (hm : m ∈ P.evidence t) {θ : T} (hpos : 0 < P.partitionStrategy θ m) :
    θ ∈ P.C t := by
  obtain ⟨s, hs⟩ : ∃ s : Fin P.card, θ ∈ P.C s ∧ m ∈ (P.σ s).msgSupport θ := by
    contrapose! hpos; simp_all +decide [ Partition.partitionStrategy ] ;
    split_ifs <;> simp_all +decide [ Strategy.msgSupport ];
    exact hpos _ ( Classical.choose_spec ‹∃ t, θ ∈ P.C t› );
  by_cases hst : s = t;
  · aesop;
  · exact False.elim ( P.evidence_disjoint hst |> fun h => h.le_bot ⟨ hs.2 |> fun h => Set.mem_iUnion₂.mpr ⟨ _, hs.1, h ⟩, hm ⟩ )

/-
**(ii) `m ∈ X_t` is on path under `σ^Π`.**
-/
lemma onPath {t : Fin P.card} {m : Msg} (hm : m ∈ P.evidence t) :
    0 < P.toSenderStrategy.onPathProb m := by
  convert P.toSenderStrategy.onPathProb_pos_iff_mem_evidence m |>.2 _;
  exact Set.mem_iUnion.2 ⟨ t, hm ⟩ |> fun h => P.evidence_eq_iUnion.symm ▸ h

/-
**(ii) `μ_{σ^Π}(·|m) = μ^{C_t,σ_t}(·|m)` for `m ∈ X_t`.**
-/
lemma belief_eq {t : Fin P.card} {m : Msg} (hm : m ∈ P.evidence t) :
    P.toSenderStrategy.belief m = (P.σ t).coalitionBelief m := by
  ext θ;
  by_cases hθ : θ ∈ P.C t;
  · have h_partitionStrategy_eq : P.partitionStrategy θ m = (P.σ t).σ θ m := by
      unfold Partition.partitionStrategy;
      split_ifs with h;
      · have := h.choose_spec; have := P.C_disjoint h.choose t; simp_all +decide [ Finset.disjoint_left ] ;
        grind;
      · exact False.elim ( h ⟨ t, hθ ⟩ );
    have h_onPathProb_eq : ∑ θ' ∈ G.Θ, G.μ0 θ' * P.partitionStrategy θ' m = G.priorMeasure (P.C t) * ∑ θ' ∈ P.C t, G.condPrior (P.C t) θ' * (P.σ t).σ θ' m := by
      have h_onPathProb_eq : ∑ θ' ∈ G.Θ, G.μ0 θ' * P.partitionStrategy θ' m = ∑ θ' ∈ P.C t, G.μ0 θ' * (P.σ t).σ θ' m := by
        rw [ ← Finset.sum_subset ( P.C_subset t ) ];
        · refine' Finset.sum_congr rfl fun x hx => _;
          rw [ Partition.partitionStrategy ];
          split_ifs with h;
          · have := h.choose_spec;
            have := P.C_disjoint h.choose t; simp_all +decide [ Finset.disjoint_left ] ;
            grind +splitImp;
          · exact False.elim ( h ⟨ t, hx ⟩ );
        · intro x hx hx';
          contrapose! hx';
          apply P.mem_C_of_partitionStrategy_pos hm (lt_of_le_of_ne (by
          exact P.partitionStrategy_mem x hx |>.1 m) (Ne.symm (by
          aesop)));
      rw [ h_onPathProb_eq, Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun x hx => _;
      rw [ DisclosureGame.condPrior_of_mem hx ];
      rw [ ← mul_assoc, mul_div_cancel₀ _ ( ne_of_gt ( DisclosureGame.priorMeasure_pos ( P.C_nonempty t ) ( P.C_subset t ) ) ) ];
    simp_all +decide [ Strategy.belief, Strategy.coalitionBelief, DisclosureGame.condPrior_of_mem ];
    simp_all +decide [ Strategy.onPathProb, DisclosureGame.zeroExt ];
    simp_all +decide [ Strategy.belief, Partition.toSenderStrategy ];
    simp_all +decide [ DisclosureGame.condPrior, Strategy.onPathProb ];
    ring;
  · rw [ Strategy.belief, Strategy.coalitionBelief ];
    by_cases hθ' : θ ∈ G.Θ <;> simp_all +decide [ zeroExt ];
    · exact Or.inl <| Or.inr <| le_antisymm ( le_of_not_gt fun h => hθ <| P.mem_C_of_partitionStrategy_pos hm h ) ( P.partitionStrategy_mem θ hθ' |>.1 m );
    · exact Or.inl <| Or.inl <| G.μ0_mem.2.2 θ hθ'

/-
**(ii, final) `w_t ∈ V(μ_{σ^Π}(·|m))` for every `m ∈ X_t`.**
-/
lemma payoff_mem_V {t : Fin P.card} {m : Msg} (hm : m ∈ P.evidence t) :
    P.w t ∈ G.V (P.toSenderStrategy.belief m) := by
  rw [ P.belief_eq hm ] ; exact P.payoff t m hm;

end Partition

variable (G) in
/-- Auxiliary: a *partition of a sub-population* `R ⊆ Θ`.  Identical to a
`Partition` except it covers only `R`; the strategies live directly in
`G.restrict (C t)`. -/
structure PartitionOn (R : Finset T) (hRsub : R ⊆ G.Θ) where
  /-- The number of cells. -/
  card : ℕ
  /-- The cells. -/
  C : Fin card → Finset T
  /-- Each cell is non-empty. -/
  C_nonempty : ∀ t, (C t).Nonempty
  /-- The cells are pairwise disjoint. -/
  C_disjoint : ∀ s t, s ≠ t → Disjoint (C s) (C t)
  /-- Each cell is contained in `R`. -/
  C_subset : ∀ t, C t ⊆ R
  /-- The cells cover `R`. -/
  C_cover : R ⊆ Finset.univ.biUnion C
  /-- A coalition strategy on each cell. -/
  σ : ∀ t, Strategy (G.restrict (C t) (C_nonempty t) ((C_subset t).trans hRsub))
  /-- The common payoffs. -/
  w : Fin card → ℝ
  /-- Residual exclusivity at step `t`. -/
  exclusive : ∀ t, G.preimageSet (thetaStep C t) (σ t).evidence ⊆ C t
  /-- The payoff condition. -/
  payoff : ∀ t, ∀ m ∈ (σ t).evidence, w t ∈ G.V ((σ t).coalitionBelief m)

/-
**A first cell exists within any non-empty `R ⊆ Θ`.**  Pool all types of `R`
that can send a fixed message `m*`.
-/
lemma exists_first_cell (R : Finset T) (hRne : R.Nonempty) (hRsub : R ⊆ G.Θ) :
    ∃ (D : Finset T) (hDne : D.Nonempty) (hDR : D ⊆ R),
      ∃ (τ : Strategy (G.restrict D hDne (hDR.trans hRsub))) (v : ℝ),
        G.preimageSet R τ.evidence ⊆ D ∧
        ∀ m ∈ τ.evidence, v ∈ G.V (τ.coalitionBelief m) := by
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ ∈ R := hRne;
  -- Since θ₀ ∈ R ⊆ G.Θ, `(G.M θ₀)` is nonempty (`G.M_nonempty θ₀ (hRsub hθ₀)`), so pick m* ∈ G.M θ₀.
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ ∈ G.M θ₀ := G.M_nonempty θ₀ (hRsub hθ₀);
  refine' ⟨ R.filter ( fun θ => m₀ ∈ G.M θ ), _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  exact ⟨ θ₀, Finset.mem_filter.mpr ⟨ hθ₀, hm₀ ⟩ ⟩;
  -- Define τ : Strategy (G.restrict D hDne (hDR.trans hRsub)) with τ.σ := fun _ => (fun a => if a = m₀ then (1:ℝ) else 0) (point mass δ_{m₀}).
  obtain ⟨τ, hτ⟩ : ∃ τ : Strategy (G.restrict (R.filter (fun θ => m₀ ∈ G.M θ)) (by
  exact ⟨ θ₀, Finset.mem_filter.mpr ⟨ hθ₀, hm₀ ⟩ ⟩) (by
  exact fun x hx => hRsub ( Finset.mem_filter.mp hx |>.1 ))), τ.evidence = {m₀} := by
    refine' ⟨ ⟨ fun θ m => if m = m₀ then 1 else 0, _ ⟩, _ ⟩ <;> simp +decide [ Strategy.evidence ];
    grind;
    simp +decide [ Set.ext_iff, Strategy.msgSupport ];
    grind
  generalize_proofs at *;
  refine' ⟨ τ, _, _ ⟩ <;> simp_all +decide [ DisclosureGame.preimageSet ];
  exact G.V_nonempty _ ( τ.belief_mem_simplex ( by simp +decide [ hτ ] ) |> fun h => DisclosureGame.zeroExt_mem_simplex ( by tauto ) h ) |> fun ⟨ x, hx ⟩ => ⟨ x, hx ⟩

/-
**Existence of a sub-population partition**, by strong induction on `R.card`.
-/
lemma exists_partitionOn (R : Finset T) (hRne : R.Nonempty) (hRsub : R ⊆ G.Θ) :
    Nonempty (PartitionOn G R hRsub) := by
  -- By induction on $R.card$, we can construct a partition for any nonempty $R \subseteq G.Θ$.
  have h_ind : ∀ k : ℕ, ∀ (R : Finset T) (hRne : R.Nonempty) (hRsub : R ⊆ G.Θ), R.card = k → Nonempty (DisclosureGame.PartitionOn G R hRsub) := by
    intro k
    induction' k using Nat.strong_induction_on with k ih;
    intro R hRne hRsub hk_card
    obtain ⟨D, hDne, hDR, τ, v, hexcl, hpay⟩ := exists_first_cell R hRne hRsub
    set R' := R \ D with hR'D
    by_cases hR'ne : R'.Nonempty;
    · have hR'card : R'.card < k := by
        grind;
      obtain ⟨ Q' ⟩ := ih _ hR'card _ hR'ne ( Finset.sdiff_subset.trans hRsub ) rfl;
      use Q'.card + 1, Fin.cons D Q'.C, by
        exact fun t => Fin.cases hDne ( fun t => Q'.C_nonempty t ) t, by
        simp +decide [ Fin.forall_fin_succ, Fin.cons ];
        exact ⟨ fun i _ => Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( Q'.C_subset i hx' ) |>.2 hx, fun i => ⟨ Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( Q'.C_subset i hx ) |>.2 hx', fun j hij => Q'.C_disjoint i j hij ⟩ ⟩, by
        exact fun t => Fin.cases hDR ( fun t => Finset.Subset.trans ( Q'.C_subset t ) ( Finset.sdiff_subset ) ) t, by
        intro x hx; by_cases hx' : x ∈ D <;> simp_all +decide [ Finset.subset_iff ] ;
        · exact ⟨ 0, hx' ⟩;
        · have := Q'.C_cover ( show x ∈ R' from Finset.mem_sdiff.mpr ⟨ hx, hx' ⟩ ) ; simp_all +decide [ Fin.exists_fin_succ ] ;, Fin.cons τ Q'.σ, Fin.cons v Q'.w, by
        all_goals generalize_proofs at *;
        intro t
        by_cases ht : t = 0;
        · simp +decide [ ht, thetaStep ];
          convert hexcl using 1;
          congr! 1;
          · simp +decide [ Finset.ext_iff, Finset.mem_biUnion ];
            intro a; constructor <;> intro ha <;> simp_all +decide [ Fin.exists_fin_succ ] ;
            · exact ha.elim ( fun ha => hDR ha ) fun ⟨ i, hi ⟩ => Finset.mem_sdiff.mp ( Q'.C_subset i hi ) |>.1;
            · exact Classical.or_iff_not_imp_left.2 fun h => by have := Q'.C_cover ( Finset.mem_sdiff.2 ⟨ ha, h ⟩ ) ; aesop;
          · exact ht.symm ▸ rfl;
        · obtain ⟨ j, rfl ⟩ := Fin.eq_succ_of_ne_zero ht;
          intro θ hθ
          simp [thetaStep] at hθ;
          have := Q'.exclusive j;
          simp_all +decide [ Finset.subset_iff, DisclosureGame.preimageSet ];
          obtain ⟨ ⟨ a, ha₁, ha₂ ⟩, ha₃ ⟩ := hθ;
          cases a using Fin.inductionOn <;> simp_all +decide [ Fin.cons ];
          exact this ( Finset.mem_biUnion.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ha₁ ⟩, ha₂ ⟩ ) ha₃, by
        intro t m hm; induction t using Fin.inductionOn <;> simp_all +decide ;
        exact Q'.payoff _ _ hm;
    · refine' ⟨ 1, fun _ => D, _, _, _, _, fun _ => τ, fun _ => v, _, _ ⟩ <;> simp_all +decide [ Finset.nonempty_iff_ne_empty ];
      simp_all +decide [ Finset.ext_iff, thetaStep ];
      exact fun x hx => Finset.mem_filter.mp hx |>.1;
  exact h_ind _ _ hRne hRsub rfl

/-- **Remark 2** (partitions exist): every disclosure game admits a
partition. -/
theorem exists_partition (G : DisclosureGame T Msg) : Nonempty (Partition G) := by
  have := @exists_partitionOn;
  obtain ⟨ Q ⟩ := this G.Θ G.Θ_nonempty ( subset_rfl );
  refine' ⟨ ⟨ Q.card, Q.C, Q.C_nonempty, Q.C_disjoint, Q.C_subset, Q.C_cover, Q.σ, Q.w, Q.exclusive, Q.payoff ⟩ ⟩

end DisclosureGame

end CPD