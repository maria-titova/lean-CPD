import CPD.BetweennessRank
import CPD.BetweennessCore
import CPD.GreedyPrefix

/-!
# Theorem 3: existence under plain betweenness (§6.2 Betweenness)

Under plain betweenness (B) the merged pool of Lemma 6 (btw-merging) can sit
exactly on the level set `{v = max 𝒲_R}`, and existence depends on *which*
payoff-maximal coalition is selected. This module provides the tie-breaking
selection — **Lemma E.1 (btw-order)**, packaged in-game as `btw_order` on the
level set `levelSet y = {μ ∈ ΔΘ | v̄(μ) = y}` — and uses it to prove
**Theorem 3** (`three_existence`): under single-valued `V` and plain
betweenness, with no message-completeness or strict-betweenness assumption, a
coalition-proof PBE exists. This is the paper's hardest existence result.
-/

open Set Topology
open scoped Classical
open scoped Pointwise

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

variable (G) in
/-- **Lemma E.1 setup.** The level set `L = {μ ∈ ΔΘ | v(μ) = y}`. -/
def levelSet (y : ℝ) : Set (T → ℝ) :=
  {μ ∈ simplexOn G.Θ | G.vbar μ = y}

/-- **Lemma E.1 (btw-order), packaged in-game.** Under single-valued `V` and
B, every level set `L = {v = y}` carries a complete transitive relation `⪰`
such that (i) moving from `x ∈ L` strictly toward the upper level set, while
staying in `L`, strictly improves the rank, and (ii) every positive finite
convex decomposition of `μ̄ ∈ L` into beliefs of value `≤ y` contains a
component in `L` ranked at least `μ̄`. -/
lemma btw_order (hSV : G.SingleValued) (hB : G.Betweenness) (y : ℝ) :
    ∃ ord : (T → ℝ) → (T → ℝ) → Prop,
      (∀ x ∈ G.levelSet y, ∀ x' ∈ G.levelSet y, ord x x' ∨ ord x' x) ∧
      (∀ x ∈ G.levelSet y, ∀ x' ∈ G.levelSet y, ∀ x'' ∈ G.levelSet y,
        ord x x' → ord x' x'' → ord x x'') ∧
      (∀ x ∈ G.levelSet y, ∀ u ∈ simplexOn G.Θ, y < G.vbar u →
        ∀ α ∈ Set.Ioo (0 : ℝ) 1,
          (fun θ => α * x θ + (1 - α) * u θ) ∈ G.levelSet y →
            ord (fun θ => α * x θ + (1 - α) * u θ) x ∧
            ¬ ord x (fun θ => α * x θ + (1 - α) * u θ)) ∧
      (∀ μbar ∈ G.levelSet y, ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
        (∀ z, 0 < a z) → (∑ z, a z = 1) →
        (∀ z, μs z ∈ simplexOn G.Θ ∧ G.vbar (μs z) ≤ y) →
        (μbar = fun θ => ∑ z, a z * μs z θ) →
          ∃ z, μs z ∈ G.levelSet y ∧ ord (μs z) μbar) := by
  obtain ⟨ord, hcomp, htrans, hi, hii⟩ :=
    btw_order_aux (btwc_vbar_continuousOn hSV).upperSemicontinuousOn hB y (simplexOn G.Θ) (simplexOn_convex' G.Θ)
      (subset_refl _)
  have hlevel : ∀ x, x ∈ G.levelSet y ↔ (x ∈ simplexOn G.Θ ∧ G.vbar x = y) :=
    fun x => Iff.rfl
  refine ⟨ord, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx'
    exact hcomp x ((hlevel x).1 hx).1 ((hlevel x).1 hx).2 x' ((hlevel x').1 hx').1
      ((hlevel x').1 hx').2
  · intro x hx x' hx' x'' hx''
    exact htrans x ((hlevel x).1 hx).1 ((hlevel x).1 hx).2 x' ((hlevel x').1 hx').1
      ((hlevel x').1 hx').2 x'' ((hlevel x'').1 hx'').1 ((hlevel x'').1 hx'').2
  · intro x hx u hu hlt α hα hz
    exact hi x ((hlevel x).1 hx).1 ((hlevel x).1 hx).2 u hu hlt α hα
      ((hlevel _).1 hz).1 ((hlevel _).1 hz).2
  · intro μbar hμbar n a μs hpos hsum hmem hcomb
    obtain ⟨z, ⟨hzmem, hzval⟩, hord⟩ :=
      hii μbar ((hlevel μbar).1 hμbar).1 ((hlevel μbar).1 hμbar).2 n a μs hpos hsum
        (fun z => ⟨(hmem z).1, (hmem z).2⟩) hcomb
    exact ⟨z, (hlevel _).2 ⟨hzmem, hzval⟩, hord⟩

/-- Single-valuedness is inherited by restricted games (private local copy of
`btwc_restrict_singleValued`). -/
private lemma two_B_restrict_SV {H : DisclosureGame T Msg} {R : Finset T}
    (hne : R.Nonempty) (hsub : R ⊆ H.Θ) (hSV : H.SingleValued) :
    (H.restrict R hne hsub).SingleValued := by
  intro μ hμ
  have hHμ : μ ∈ simplexOn H.Θ := by
    simp only [restrict_Θ] at hμ
    exact simplexOn_mono hsub hμ
  simpa using hSV μ hHμ

/-
**Preimage of the union evidence is the merged cell.** Mirrors the first
half of `btw_merging`.
-/
private lemma two_B_merged_preimage {H : DisclosureGame T Msg}
    (K : H.Coalition) (hne' : (H.Θ \ K.C).Nonempty) (hsub' : (H.Θ \ K.C) ⊆ H.Θ)
    (K' : Coalition (H.restrict (H.Θ \ K.C) hne' hsub')) :
    H.preimageSetFull (K.σ.evidence ∪ K'.σ.evidence) = K.C ∪ K'.C := by
  have h_preimage : H.preimageSetFull (K.σ.evidence ∪ K'.σ.evidence) = H.preimageSetFull K.σ.evidence ∪ H.preimageSetFull K'.σ.evidence := by
    simp +decide [ DisclosureGame.preimageSetFull, Finset.filter_union ];
    ext; simp [DisclosureGame.preimageSet];
    simp +decide [ Set.Nonempty, Finset.Nonempty ];
    grind;
  have h_preimage_K' : H.preimageSetFull K'.σ.evidence ∩ (H.Θ \ K.C) = K'.C := by
    convert K'.preimage_eq using 1;
    ext; simp [DisclosureGame.preimageSetFull, DisclosureGame.preimageSet];
    tauto;
  have h_preimage_K : H.preimageSetFull K.σ.evidence = K.C := by
    exact K.preimage_eq;
  ext x; by_cases hx : x ∈ K.C <;> simp_all +decide [ Finset.ext_iff ];
  specialize h_preimage_K' x; specialize h_preimage_K x; simp_all +decide [DisclosureGame.preimageSetFull];
  by_cases hx' : x ∈ H.Θ <;> simp_all +decide [ DisclosureGame.preimageSet ]

/-- Value of `K'` transported to `H`: `H.vbar (H.condPrior K'.C) = K'.w`. -/
private lemma two_B_Kprime_value {H : DisclosureGame T Msg}
    (hSV : H.SingleValued) (hB : H.Betweenness)
    (K : H.Coalition)
    (hne' : (H.Θ \ K.C).Nonempty) (hsub' : (H.Θ \ K.C) ⊆ H.Θ)
    (K' : Coalition (H.restrict (H.Θ \ K.C) hne' hsub')) :
    H.vbar (H.condPrior K'.C) = K'.w :=
  (btw_attained_le hSV hB hne' hsub' K').1.symm

/-
Lower bound of `two_B_merged_value`: betweenness convex combination.
-/
private lemma two_B_merged_value_ge {H : DisclosureGame T Msg}
    (hSV : H.SingleValued) (hB : H.Betweenness)
    (K : H.Coalition)
    (hne' : (H.Θ \ K.C).Nonempty) (hsub' : (H.Θ \ K.C) ⊆ H.Θ)
    (K' : Coalition (H.restrict (H.Θ \ K.C) hne' hsub'))
    (hgt : K.w < K'.w) :
    K.w ≤ H.vbar (H.condPrior (K.C ∪ K'.C)) := by
  obtain ⟨l, hl, heq⟩ := gp_condPrior_union K.C_nonempty K'.C_nonempty K.C_subset (K'.C_subset.trans hsub') (by
  exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( K'.C_subset hx' ) |>.2 hx);
  convert ( hB ( H.condPrior K.C ) _ ( H.condPrior K'.C ) _ l hl ).1 using 1 <;> simp_all +decide [ min_eq_left ];
  · grind +suggestions;
  · exact ⟨ fun θ => by
      exact div_nonneg ( by
        split_ifs <;> simp +decide [ *, H.μ0_mem.1 ] ) ( by
        exact Finset.sum_nonneg fun _ _ => H.μ0_mem.1 _ ), by
      convert H.condPrior_mem_simplex K.C_nonempty K.C_subset |> fun h => h.2 using 1;
      simp +decide [ DisclosureGame.condPrior ];
      exact fun _ a ha => Or.inl fun h => False.elim <| ha h, fun θ hθ => by
      unfold DisclosureGame.condPrior; simp +decide [ hθ ];
      exact Or.inl fun h => False.elim <| hθ <| K.C_subset h ⟩;
  · convert condPrior_mem_simplex K'.C_nonempty ( K'.C_subset.trans hsub' ) using 1;
    simp +decide [ simplexOn, K'.C_subset.trans hsub' ];
    intro h₁ h₂; constructor <;> intro h <;> intro a ha <;> by_cases ha' : a ∈ K'.C <;> simp_all +decide [ DisclosureGame.condPrior ];
    exact False.elim ( ha ( K'.C_subset ha' |> fun h => hsub' h ) )

/-
Upper bound of `two_B_merged_value`: realize the pool as a coalition payoff.
-/
private lemma two_B_merged_value_le {H : DisclosureGame T Msg}
    (hSV : H.SingleValued) (hB : H.Betweenness)
    (K : H.Coalition) (hmax : IsGreatest H.coalitionPayoffs K.w)
    (hne' : (H.Θ \ K.C).Nonempty) (hsub' : (H.Θ \ K.C) ⊆ H.Θ)
    (K' : Coalition (H.restrict (H.Θ \ K.C) hne' hsub')) :
    H.vbar (H.condPrior (K.C ∪ K'.C)) ≤ K.w := by
  -- Let $X = \{m \in \text{restrictMsgSpace } H.Θ | m \in K.σ.evidence ∪ K'.σ.evidence\}$.
  set X := (H.restrictMsgSpace H.Θ).filter (fun m => m ∈ K.σ.evidence ∪ K'.σ.evidence) with hX;
  -- By `two_B_merged_preimage`, `preimage H.M H.Θ X = K.C ∪ K'.C`.
  have hpre : H.preimageSet H.Θ X = K.C ∪ K'.C := by
    convert two_B_merged_preimage K hne' hsub' K' using 1;
    ext; simp [X, DisclosureGame.preimageSet, DisclosureGame.preimageSetFull];
    intro hθ; constructor <;> rintro ⟨ m, hm₁, hm₂ ⟩ <;> use m <;> simp_all +decide [ Set.Nonempty ];
    exact Finset.mem_biUnion.mpr ⟨ _, hθ, hm₁ ⟩;
  refine' le_trans _ ( hmax.2 _ );
  convert ( vstar_isGreatest H.Θ_nonempty ( le_refl H.Θ ) ).2 _ using 1;
  · refine' ⟨ X, Finset.filter_subset _ _, _, _ ⟩;
    · contrapose! hpre; simp_all +decide [ Finset.ext_iff ];
      obtain ⟨ x, hx ⟩ := K.C_nonempty; use x; simp_all +decide [ DisclosureGame.preimageSet ];
      simp_all +decide [ Set.Nonempty ];
    · convert rfl;
      convert hpre using 1;
      ext; simp [preimage, DisclosureGame.preimageSet];
      simp +decide [ Finset.Nonempty, Set.Nonempty ];
  · convert ( btw_attained hSV hB H.Θ_nonempty ( le_refl H.Θ ) ).1 using 1;
    rw [ DisclosureGame.restrict_self ]

/-- **Value of the merged pool.** Mirrors the value half of `btw_merging`. -/
private lemma two_B_merged_value {H : DisclosureGame T Msg}
    (hSV : H.SingleValued) (hB : H.Betweenness)
    (K : H.Coalition) (hmax : IsGreatest H.coalitionPayoffs K.w)
    (hne' : (H.Θ \ K.C).Nonempty) (hsub' : (H.Θ \ K.C) ⊆ H.Θ)
    (K' : Coalition (H.restrict (H.Θ \ K.C) hne' hsub'))
    (hgt : K.w < K'.w) :
    H.vbar (H.condPrior (K.C ∪ K'.C)) = K.w :=
  le_antisymm (two_B_merged_value_le hSV hB K hmax hne' hsub' K')
    (two_B_merged_value_ge hSV hB K hne' hsub' K' hgt)

/-! ### Private infrastructure for the order-based proof of `two_B_max_cell`

The auxiliary game on the merged pool and its PBE partition, mirroring the
`private` `btwcAux` development of `CPD.BetweennessCore` (cloned here
because those helpers are private to that module), together with a finite
maximal-element selection for the total transitive relation of `btw_order`. -/

/-- Every non-empty finite set carries a maximal element for a relation that is
total and transitive on the set. -/
private lemma two_B_finite_max {α : Type*} (ord : α → α → Prop) (s : Finset α) :
    s.Nonempty →
    (∀ x ∈ s, ∀ y ∈ s, ord x y ∨ ord y x) →
    (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, ord x y → ord y z → ord x z) →
    ∃ x ∈ s, ∀ y ∈ s, ord x y := by
  classical
  induction s using Finset.cons_induction with
  | empty => intro h _ _; exact absurd h (by simp)
  | cons a t ha ih =>
    intro _ htotal htrans
    have hmem : ∀ x ∈ t, x ∈ Finset.cons a t ha := fun x hx => Finset.mem_cons_of_mem hx
    have haa : ord a a := by
      rcases htotal a (Finset.mem_cons_self a t) a (Finset.mem_cons_self a t) with h | h <;>
        exact h
    by_cases hte : t.Nonempty
    · obtain ⟨x, hxt, hx⟩ := ih hte
        (fun x hx y hy => htotal x (hmem x hx) y (hmem y hy))
        (fun x hx y hy z hz hxy hyz =>
          htrans x (hmem x hx) y (hmem y hy) z (hmem z hz) hxy hyz)
      rcases htotal x (hmem x hxt) a (Finset.mem_cons_self a t) with h | h
      · refine ⟨x, hmem x hxt, fun y hy => ?_⟩
        rcases Finset.mem_cons.mp hy with rfl | hy
        · exact h
        · exact hx y hy
      · refine ⟨a, Finset.mem_cons_self a t, fun y hy => ?_⟩
        rcases Finset.mem_cons.mp hy with rfl | hy
        · exact haa
        · exact htrans a (Finset.mem_cons_self a t) x (hmem x hxt) y (hmem y hy) h (hx y hy)
    · rw [Finset.not_nonempty_iff_eq_empty] at hte
      subst hte
      refine ⟨a, Finset.mem_cons_self a ∅, fun y hy => ?_⟩
      rcases Finset.mem_cons.mp hy with rfl | hy
      · exact haa
      · exact absurd hy (by simp)

/-
The restricted conditional prior on a subset agrees with `G`'s (clone of
`btwc_restrict_condPrior`).
-/
private lemma btwc_restrict_condPrior {R : Finset T} (hne : R.Nonempty)
    (hsub : R ⊆ G.Θ) {C : Finset T} (hC : C.Nonempty) (hCR : C ⊆ R) :
    (G.restrict R hne hsub).condPrior C = G.condPrior C := by
  ext θ;
  by_cases hθ : θ ∈ C <;> simp_all +decide [ DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
  rw [ ← Finset.sum_div _ _ _, if_pos ( hCR hθ ), div_div_div_cancel_right₀ ];
  · rw [ Finset.sum_congr rfl fun x hx => if_pos ( hCR hx ) ];
  · exact ne_of_gt ( Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( hsub hx ) ) hne )

/-- Bayes plausibility: the prior is the average of the induced beliefs, with
weights summing to one (clone of `btwc_bayes`). -/
private lemma btwc_bayes {H : DisclosureGame T Msg} (s : Strategy H) :
    (∀ θ, H.μ0 θ
        = ∑ m ∈ Finset.univ.filter (fun m => m ∈ s.evidence),
            s.onPathProb m * s.belief m θ) ∧
      (∑ m ∈ Finset.univ.filter (fun m => m ∈ s.evidence), s.onPathProb m = 1) := by
  refine' ⟨ fun θ => _, _ ⟩;
  · by_cases hθ : θ ∈ H.Θ <;> simp_all +decide [ Strategy.belief ];
    · rw [ Finset.sum_congr rfl fun x hx => by rw [ mul_div_cancel₀ _ ( ne_of_gt ( s.onPathProb_pos_iff_mem_evidence x |>.2 ( by simpa using hx ) ) ) ] ];
      have h_sum : ∑ m ∈ Finset.univ.filter (fun m => m ∈ s.evidence), s.σ θ m = 1 := by
        have h_key : ∑ m ∈ Finset.univ, s.σ θ m = 1 := by
          exact s.mem θ hθ |>.2.1;
        rw [ ← h_key, ← Finset.sum_subset ( Finset.subset_univ _ ) ];
        simp +contextual [ Strategy.evidence, Strategy.msgSupport ];
        exact fun m hm => le_antisymm ( hm θ hθ ) ( s.mem θ hθ |>.1 m );
      rw [ ← Finset.mul_sum _ _ _, h_sum, mul_one ];
    · have := H.μ0_mem.2.2 θ hθ; aesop;
  · unfold Strategy.onPathProb;
    rw [ Finset.sum_comm ];
    have h_sum : ∀ θ ∈ H.Θ, ∑ m ∈ Finset.univ.filter (fun m => m ∈ s.evidence), s.σ θ m = 1 := by
      intro θ hθ;
      have h_key : ∑ m ∈ Finset.univ, s.σ θ m = 1 := by
        exact s.mem θ hθ |>.2.1;
      rw [ ← h_key, ← Finset.sum_subset ( Finset.subset_univ _ ) ];
      simp +contextual [ Strategy.evidence, Strategy.msgSupport ];
      exact fun m hm => le_antisymm ( hm θ hθ ) ( s.mem θ hθ |>.1 m );
    convert H.priorMeasure_self using 1;
    exact Finset.sum_congr rfl fun x hx => by rw [ ← Finset.mul_sum _ _ _, h_sum x hx, mul_one ];

/-
Under betweenness, sub-level sets of `v̄` are convex (clone of
`btwc_sublevel_convex`).
-/
private lemma btwc_sublevel_convex (hB : G.Betweenness) (c : ℝ) :
    Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} := by
  intro μ hμ ν hν a b ha hb hab;
  by_cases ha0 : a = 0;
  · simp_all +decide [ show b = 1 by linarith ];
  · by_cases hb0 : b = 0;
    · simp_all +decide [ show a = 1 by linarith ];
    · have := hB μ hμ.1 ν hν.1 ( a ) ⟨ lt_of_le_of_ne ha ( Ne.symm ha0 ), by linarith [ show 0 < b by positivity ] ⟩; simp_all +decide [ ← eq_sub_iff_add_eq' ];
      exact ⟨ ⟨ fun x => add_nonneg ( mul_nonneg ha ( hμ.1.1 x ) ) ( mul_nonneg ( sub_nonneg.2 hb ) ( hν.1.1 x ) ), by simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, hμ.1.2.1, hν.1.2.1 ] ⟩, by cases this.2 <;> linarith! ⟩

/-
Finite betweenness (upper): `v̄` of a convex combination is bounded above by
the max of the values (clone of `btwc_convexCombo_le`).
-/
private lemma btwc_convexCombo_le (hB : G.Betweenness) {E : Finset Msg}
    (x : Msg → (T → ℝ)) (a : Msg → ℝ)
    (hx : ∀ m ∈ E, x m ∈ simplexOn G.Θ)
    (ha : ∀ m ∈ E, 0 ≤ a m) (hsum : ∑ m ∈ E, a m = 1)
    {c : ℝ} (hc : ∀ m ∈ E, G.vbar (x m) ≤ c) :
    G.vbar (fun θ => ∑ m ∈ E, a m * x m θ) ≤ c := by
  have h_convex : Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} :=
    btwc_sublevel_convex hB c
  convert h_convex.sum_mem ( fun m _ => ha m ‹_› ) hsum ( fun m _ => ⟨ hx m ‹_›, hc m ‹_› ⟩ ) |> fun h => h.2 using 1; simp +decide [ Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum ]; ring;
  exact congr_arg _ ( funext fun θ => by simp +decide [ mul_comm, Finset.mul_sum _ _ _ ] )

/-
Finite quasiconcavity: `v̄` of a convex combination dominates the min (clone of
`btwc_convexCombo_ge`).
-/
private lemma btwc_convexCombo_ge (hQC : G.QC) {E : Finset Msg}
    (x : Msg → (T → ℝ)) (a : Msg → ℝ)
    (hx : ∀ m ∈ E, x m ∈ simplexOn G.Θ)
    (ha : ∀ m ∈ E, 0 ≤ a m) (hsum : ∑ m ∈ E, a m = 1)
    {c : ℝ} (hc : ∀ m ∈ E, c ≤ G.vbar (x m)) :
    c ≤ G.vbar (fun θ => ∑ m ∈ E, a m * x m θ) := by
  have := @CPD.DisclosureGame.vbar_superlevel_convex;
  specialize this hQC c;
  have h_convex_comb : (∑ m ∈ E, a m • (x m)) ∈ {μ | μ ∈ simplexOn G.Θ ∧ c ≤ G.vbar μ} := by
    apply this.sum_mem;
    · exact ha;
    · exact hsum;
    · exact fun m hm => ⟨ hx m hm, hc m hm ⟩;
  convert h_convex_comb.2 using 1;
  exact congr_arg _ ( funext fun θ => by simp +decide [ Finset.sum_apply, Pi.smul_apply ] )

/-
A relative preimage of a non-empty set of available messages is non-empty
(clone of `btwc_preimage_nonempty`).
-/
private lemma btwc_preimage_nonempty {R : Finset T} {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (preimage G.M R X).Nonempty := by
  obtain ⟨ m, hm ⟩ := hXne;
  obtain ⟨ θ, hθ ⟩ := Finset.mem_biUnion.mp ( hX hm );
  exact ⟨ θ, Finset.mem_filter.mpr ⟨ hθ.1, ⟨ m, by aesop ⟩ ⟩ ⟩

/-
On-path probabilities are non-negative (clone of `btwc_onPathProb_nonneg`).
-/
private lemma btwc_onPathProb_nonneg {H : DisclosureGame T Msg} (s : Strategy H)
    (m : Msg) : 0 ≤ s.onPathProb m := by
  apply Finset.sum_nonneg;
  exact fun i hi => mul_nonneg ( H.μ0_mem.1 i ) ( s.mem i hi |>.1 m )

/-- `M⁻¹_R(X) ⊆ R` (clone of `btwcAux_preimage_subset`). -/
private lemma btwcAux_preimage_subset {R : Finset T} {X : Finset Msg} :
    preimage G.M R X ⊆ R := Finset.filter_subset _ _

/-
Cover condition for the auxiliary game `G'`: `X = ⋃_{θ ∈ M⁻¹_R(X)} (M θ ∩ X)`
(clone of `btwcAux_cover`).
-/
private lemma btwcAux_cover {R : Finset T}
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) :
    (↑X : Set Msg) = ⋃ θ ∈ preimage G.M R X, ((G.M θ ∩ X : Finset Msg) : Set Msg) := by
  ext m; simp [preimage];
  by_cases hm : m ∈ X <;> simp_all +decide [ Finset.subset_iff, DisclosureGame.restrictMsgSpace ];
  exact Exists.elim ( hX hm ) fun x hx => ⟨ x, hx.2, hx.1, ⟨ m, Finset.mem_inter_of_mem hx.2 hm ⟩ ⟩

/-- **The auxiliary game `G'`**, used in the proof of `two_B_max_cell`: cut the
message space down to a fixed non-empty `X ⊆ 𝓜_R`. `G'.Θ := M⁻¹_R(X)`,
`G'.𝓜 := X`, `G'.M θ := M θ ∩ X`, `G'.μ⁰ := μ⁰_{M⁻¹_R(X)}`, `G'.V := G.V`
(clone of the private `btwcAux` of `BetweennessCore`). -/
private noncomputable def btwcAux {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    DisclosureGame T Msg where
  Θ := preimage G.M R X
  𝓜 := X
  Θ_nonempty := btwc_preimage_nonempty hX hXne
  𝓜_nonempty := hXne
  M := fun θ => G.M θ ∩ X
  M_subset := fun θ _ => Finset.inter_subset_right
  M_nonempty := fun θ hθ => (mem_preimage.mp hθ).2
  cover := btwcAux_cover hX
  μ0 := G.condPrior (preimage G.M R X)
  μ0_mem := condPrior_mem_simplex (btwc_preimage_nonempty hX hXne)
    (btwcAux_preimage_subset.trans hsub)
  μ0_fullSupport := fun θ hθ => condPrior_pos (btwc_preimage_nonempty hX hXne)
    (btwcAux_preimage_subset.trans hsub) hθ
  V := G.V
  V_nonempty := fun μ hμ => G.V_nonempty μ (simplexOn_mono (btwcAux_preimage_subset.trans hsub) hμ)
  V_isCompact := fun μ hμ => G.V_isCompact μ (simplexOn_mono (btwcAux_preimage_subset.trans hsub) hμ)
  V_ordConnected := fun μ hμ =>
    G.V_ordConnected μ (simplexOn_mono (btwcAux_preimage_subset.trans hsub) hμ)
  V_uhc := G.V_uhc.mono (simplexOn_mono (btwcAux_preimage_subset.trans hsub))

@[simp] private lemma btwcAux_Θ {R : Finset T} (hsub : R ⊆ G.Θ) {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).Θ = preimage G.M R X := rfl

@[simp] private lemma btwcAux_M {R : Finset T} (hsub : R ⊆ G.Θ) {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).M = fun θ => G.M θ ∩ X := rfl

@[simp] private lemma btwcAux_𝓜 {R : Finset T} (hsub : R ⊆ G.Θ) {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).𝓜 = X := rfl

@[simp] private lemma btwcAux_V {R : Finset T} (hsub : R ⊆ G.Θ) {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).V = G.V := rfl

@[simp] private lemma btwcAux_μ0 {R : Finset T} (hsub : R ⊆ G.Θ) {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).μ0 = G.condPrior (preimage G.M R X) := rfl

/-- `G'` has the same upper envelope as `G` (clone of `btwcAux_vbar`). -/
private lemma btwcAux_vbar {R : Finset T} (hsub : R ⊆ G.Θ) {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) (μ : T → ℝ) :
    (btwcAux hsub hX hXne).vbar μ = G.vbar μ := rfl

/-
`G'` inherits single-valuedness of `V` (clone of `btwcAux_singleValued`).
-/
private lemma btwcAux_singleValued (hSV : G.SingleValued) {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).SingleValued := by
  intro μ hμ;
  convert hSV μ _ using 1;
  convert simplexOn_mono (btwcAux_preimage_subset.trans hsub) hμ

/-
`G'` inherits betweenness (clone of `btwcAux_betweenness`).
-/
private lemma btwcAux_betweenness (hB : G.Betweenness) {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).Betweenness := by
  intro μ hμ μ' hμ' l hl;
  convert hB μ ( simplexOn_mono ( btwcAux_preimage_subset.trans hsub ) ( by simpa using hμ ) ) μ' ( simplexOn_mono ( btwcAux_preimage_subset.trans hsub ) ( by simpa using hμ' ) ) l hl using 1

/-
Conditioning `G'`'s prior further on `C ⊆ M⁻¹_R(X)` agrees with `G`'s (clone of
`btwcAux_condPrior`).
-/
private lemma btwcAux_condPrior {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty)
    {C : Finset T} (hCne : C.Nonempty) (hCsub : C ⊆ preimage G.M R X) :
    (btwcAux hsub hX hXne).condPrior C = G.condPrior C := by
  ext θ; by_cases hθ : θ ∈ C <;> simp_all +decide [ condPrior_of_mem, condPrior_of_not_mem ];
  simp +decide [ priorMeasure, condPrior, hCsub hθ ];
  rw [ ← Finset.sum_div _ _ _, div_div_div_cancel_right₀ ];
  · exact congr_arg _ ( Finset.sum_congr rfl fun x hx => if_pos ( hCsub hx ) );
  · exact ne_of_gt ( Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( btwcAux_preimage_subset.trans hsub hx ) ) ( btwc_preimage_nonempty hX hXne ) )

/-
The coalition-induced belief depends only on the type space, prior, and
strategy (clone of `btwc_coalitionBelief_congr`).
-/
private lemma btwc_coalitionBelief_congr {g₁ g₂ : DisclosureGame T Msg} (hΘ : g₁.Θ = g₂.Θ)
    (hμ0 : g₁.μ0 = g₂.μ0) (s₁ : Strategy g₁) (s₂ : Strategy g₂) (hσ : s₁.σ = s₂.σ) (m : Msg) :
    s₁.coalitionBelief m = s₂.coalitionBelief m := by
  unfold Strategy.coalitionBelief Strategy.belief Strategy.onPathProb;
  unfold zeroExt; aesop;

/-- Raw version of the conditional-prior decomposition for a bare cell strategy
(clone of `btwc_condPrior_decomp_raw`). -/
private lemma btwc_condPrior_decomp_raw {H : DisclosureGame T Msg} {C : Finset T}
    (hCne : C.Nonempty) (hCsub : C ⊆ H.Θ) (σ : Strategy (H.restrict C hCne hCsub)) :
    H.condPrior C = fun θ =>
      ∑ m ∈ Finset.univ.filter (fun m => m ∈ σ.evidence),
        σ.onPathProb m * σ.coalitionBelief m θ := by
  funext θ;
  convert ( btwc_bayes σ ).1 θ using 1;
  refine' Finset.sum_congr rfl fun m hm => _;
  simp +decide [ Strategy.coalitionBelief, Strategy.belief ] at hm ⊢;
  by_cases hθ : θ ∈ C <;> simp +decide [ hθ, zeroExt ];
  · convert Or.inl rfl using 1;
  · rw [ DisclosureGame.condPrior_of_not_mem ] <;> simp +decide [ hθ ]

/-- Raw version of the coalition-belief membership for a bare cell strategy
(clone of `btwc_coalitionBelief_mem_raw`). -/
private lemma btwc_coalitionBelief_mem_raw {H : DisclosureGame T Msg} {C : Finset T}
    (hCne : C.Nonempty) (hCsub : C ⊆ H.Θ) (σ : Strategy (H.restrict C hCne hCsub))
    {m : Msg} (hm : m ∈ σ.evidence) : σ.coalitionBelief m ∈ simplexOn H.Θ := by
  convert zeroExt_mem_simplex hCsub _
  exact σ.belief_mem_simplex hm

/-- Raw version of the on-path value identification for a bare cell strategy
(clone of `btwc_value_eq_raw`). -/
private lemma btwc_value_eq_raw {H : DisclosureGame T Msg} (hSV : H.SingleValued)
    {C : Finset T} (hCne : C.Nonempty) (hCsub : C ⊆ H.Θ)
    (σ : Strategy (H.restrict C hCne hCsub)) (w : ℝ)
    (hpay : ∀ m ∈ σ.evidence, w ∈ H.V (σ.coalitionBelief m))
    {m : Msg} (hm : m ∈ σ.evidence) :
    H.vbar (σ.coalitionBelief m) = w := by
  have h_mem := hpay m hm
  convert Set.mem_singleton_iff.mp
    ( hSV _ ( btwc_coalitionBelief_mem_raw hCne hCsub σ hm ) ▸ h_mem ) |> Eq.symm

/-- **Value identification for a bare cell.** Under single-valued `V` and betweenness,
any `(C, σ, w)` with the coalition payoff condition satisfies `w = v̄(μ⁰_C)`
(clone of `btwc_cell_value`). -/
private lemma btwc_cell_value {H : DisclosureGame T Msg} (hSV : H.SingleValued)
    (hB : H.Betweenness) {C : Finset T} (hCne : C.Nonempty) (hCsub : C ⊆ H.Θ)
    (σ : Strategy (H.restrict C hCne hCsub)) (w : ℝ)
    (hpay : ∀ m ∈ σ.evidence, w ∈ H.V (σ.coalitionBelief m)) :
    w = H.vbar (H.condPrior C) := by
  have h_condPrior_decomp : H.condPrior C = fun θ =>
      ∑ m ∈ Finset.univ.filter (fun m => m ∈ σ.evidence),
        σ.onPathProb m * σ.coalitionBelief m θ := btwc_condPrior_decomp_raw hCne hCsub σ
  refine' le_antisymm _ _;
  · convert btwc_convexCombo_ge ( Betweenness.qc hB ) _ _ _ _ _ _;
    convert congr_fun h_condPrior_decomp _ using 1;
    · exact fun m hm => btwc_coalitionBelief_mem_raw hCne hCsub σ ( Finset.mem_filter.mp hm |>.2 );
    · exact fun m hm => btwc_onPathProb_nonneg _ _;
    · exact ( btwc_bayes σ ).2;
    · exact fun m hm => by
        rw [ btwc_value_eq_raw hSV hCne hCsub σ w hpay ( Finset.mem_filter.mp hm |>.2 ) ];
  · convert btwc_convexCombo_le hB ( fun m => σ.coalitionBelief m ) ( fun m => σ.onPathProb m ) _ _ _ _;
    · exact fun m hm => btwc_coalitionBelief_mem_raw hCne hCsub σ ( Finset.mem_filter.mp hm |>.2 );
    · exact fun m hm => btwc_onPathProb_nonneg σ m;
    · exact ( btwc_bayes σ ).2;
    · exact fun m hm =>
        le_of_eq ( btwc_value_eq_raw hSV hCne hCsub σ w hpay ( Finset.mem_filter.mp hm |>.2 ) )

/-
Zeroing a PBE strategy off `Θ` preserves the PBE property (clone of
`btwc_isPBE_zero`).
-/
private lemma btwc_isPBE_zero {H : DisclosureGame T Msg} {s : Strategy H} (hs : H.IsPBE s) :
    ∃ s' : Strategy H, H.IsPBE s' ∧ (∀ θ ∉ H.Θ, s'.σ θ = 0) := by
  -- By definition of $s'$, we know that $s' = s$ on $H.Θ$.
  obtain ⟨μ, r, h⟩ := hs
  use ⟨fun θ => if θ ∈ H.Θ then s.σ θ else 0, by
    exact fun θ hθ => by simpa [ hθ ] using s.mem θ;⟩
  generalize_proofs at *;
  refine' ⟨ ⟨ μ, r, _ ⟩, fun θ hθ => if_neg hθ ⟩
  generalize_proofs at *;
  refine' ⟨ h.1, h.2, _, _, _ ⟩;
  · intro m hm; convert h.bayesian m _ using 1;
    · unfold Strategy.belief;
      ext θ; by_cases hθ : θ ∈ H.Θ <;> simp +decide [ hθ ];
      · unfold Strategy.onPathProb; aesop;
      · rw [ show H.μ0 θ = 0 from _ ]; ring;
        exact H.μ0_fullSupport θ |> fun h => by have := H.μ0_mem; exact (by
        exact this.2.2 θ hθ);
    · grind +suggestions;
  · exact h.payoff_compat;
  · intro θ hθ
    simp [Strategy.msgSupport, h.seq_optimal θ hθ];
    simpa [ hθ ] using h.seq_optimal θ hθ

/-- `G'` admits a PBE partition with **strictly decreasing** payoffs: normalize
a PBE strategy off `Θ'` and take the forward partition of `pbe_characterization`,
whose payoff levels are the distinct equilibrium payoffs in decreasing order
(`fwdW_strictAnti`). -/
private lemma btwcAux_exists_partition {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    ∃ P : Partition (btwcAux hsub hX hXne), StrictAnti P.w := by
  obtain ⟨s, hs⟩ := exists_PBE (btwcAux hsub hX hXne)
  obtain ⟨s', hs', hsupp⟩ := btwc_isPBE_zero hs
  obtain ⟨μ, r, hsup⟩ := hs'
  exact ⟨forwardPartition hsup hsupp, fwdW_strictAnti⟩

/-
The conditional prior on a set `C` partitioned into disjoint nonempty cells is a
positive convex combination of the conditional priors of the cells (clone of
`btwc_condPrior_partition`).
-/
private lemma btwc_condPrior_partition {C : Finset T} {n : ℕ} (D : Fin n → Finset T)
    (hDne : ∀ i, (D i).Nonempty) (hDsub : ∀ i, D i ⊆ G.Θ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (hCne : C.Nonempty) (hcover : C = Finset.univ.biUnion D) :
    (∀ i, (0:ℝ) < G.priorMeasure (D i) / G.priorMeasure C) ∧
    (∑ i, G.priorMeasure (D i) / G.priorMeasure C = 1) ∧
    (G.condPrior C = fun θ =>
      ∑ i, (G.priorMeasure (D i) / G.priorMeasure C) * G.condPrior (D i) θ) := by
  refine' ⟨ _, _, _ ⟩;
  · exact fun i => div_pos ( DisclosureGame.priorMeasure_pos ( hDne i ) ( hDsub i ) ) ( DisclosureGame.priorMeasure_pos hCne ( hcover ▸ Finset.biUnion_subset.mpr fun _ _ => hDsub _ ) );
  · rw [ ← Finset.sum_div, div_eq_iff ];
    · unfold DisclosureGame.priorMeasure;
      rw [ hcover, one_mul, Finset.sum_biUnion ];
      exact fun i _ j _ hij => hdisj i j hij;
    · exact ne_of_gt ( priorMeasure_pos hCne ( by simp +decide [ hcover, hDsub ] ) );
  · ext θ; simp +decide [ *, DisclosureGame.condPrior ];
    by_cases hθ : ∃ i, θ ∈ D i <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.sum_ite ];
    obtain ⟨ i, hi ⟩ := hθ; rw [ Finset.sum_eq_single i ] <;> simp_all +decide [ Finset.disjoint_left ];
    · rw [ ← mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( priorMeasure_pos ( hDne i ) ( hDsub i ) ) ), one_mul ];
    · grind

/-
Finite (index-form) upper betweenness bound: `v̄` of a convex combination is
bounded above by the common upper bound of the values (clone of
`btwc_convexCombo_le_index`).
-/
private lemma btwc_convexCombo_le_index (hB : G.Betweenness) {n : ℕ}
    (x : Fin n → (T → ℝ)) (a : Fin n → ℝ)
    (hx : ∀ i, x i ∈ simplexOn G.Θ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1)
    {c : ℝ} (hc : ∀ i, G.vbar (x i) ≤ c) :
    G.vbar (fun θ => ∑ i, a i * x i θ) ≤ c := by
  contrapose! hB;
  intro h;
  have h_convex : Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} := by
    convert btwc_sublevel_convex h c using 1;
  have h_sum_mem : ∑ i, a i • x i ∈ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} := by
    exact h_convex.sum_mem ( fun i _ => ha i ) ( by simp +decide [ hsum ] ) ( fun i _ => ⟨ hx i, hc i ⟩ );
  convert hB.not_ge _;
  convert h_sum_mem.2 using 1;
  exact congr_arg _ ( by ext; simp +decide [ Finset.sum_apply, Pi.smul_apply ] )

/-
The evidence used by a partition cell of `G'` consists of messages in `X`
(clone of `btwc_cell_evidence_subset`).
-/
private lemma btwc_cell_evidence_subset {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty)
    (P : Partition (btwcAux hsub hX hXne)) (t : Fin P.card) :
    ((P.σ t).evidence : Set Msg) ⊆ (X : Set Msg) := by
  intro m hm;
  rw [ Strategy.evidence ] at hm;
  simp_all +decide [ Set.subset_def, DisclosureGame.restrict, Strategy.msgSupport ];
  obtain ⟨ i, hi, hm ⟩ := hm;
  have := ( P.σ t ).mem i;
  contrapose! hm; aesop;

/-
**Top-cell realization, coalition form.** A cell of `G'` whose residual type
space is all of `M⁻¹_R(X)` (e.g. the first cell) yields a coalition of `G|_R`
with the same cell and payoff (variant of `btwc_top_cell_mem` exposing the
cell and payoff of the realizing coalition).
-/
private lemma two_B_top_cell {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty)
    (P : Partition (btwcAux hsub hX hXne)) (t : Fin P.card)
    (ht : thetaStep P.C t = preimage G.M R X) :
    ∃ K₂ : Coalition (G.restrict R hne hsub), K₂.C = P.C t ∧ K₂.w = P.w t := by
  refine' ⟨ ⟨ P.C t, _, _, ⟨ ( P.σ t ).σ, _ ⟩, _, P.w t, _ ⟩, rfl, rfl ⟩;
  exact P.C_nonempty t;
  exact P.C_subset t |> Finset.Subset.trans <| btwcAux_preimage_subset;
  exact fun θ hθ => simplexOn_mono ( Finset.inter_subset_left ) ( P.σ t |>.mem θ hθ );
  · intro θ hθ;
    simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
    convert P.exclusive t _;
    simp_all +decide [ DisclosureGame.preimageSet ];
    simp_all +decide [ preimage, Set.Nonempty ];
    obtain ⟨ x, hx₁, hx₂ ⟩ := hθ.2;
    have := btwc_cell_evidence_subset hsub hX hXne P t;
    exact ⟨ ⟨ x, Finset.mem_inter.mpr ⟨ hx₁, this hx₂ ⟩ ⟩, x, ⟨ hx₁, this hx₂ ⟩, hx₂ ⟩;
  · intro m hm;
    convert P.payoff t m hm using 1;
    simp +decide [ restrict_V, btwcAux_V ];
    congr! 1;
    convert btwc_coalitionBelief_congr _ _ _ _ _ _;
    · rfl;
    · convert btwc_restrict_condPrior hne hsub _ _;
      · convert btwcAux_condPrior hsub hX hXne _ _;
        · exact P.C_nonempty t;
        · grind +locals;
      · exact P.C_nonempty t;
      · exact P.C_subset t |> Finset.Subset.trans <| btwcAux_preimage_subset;
    · rfl

/-- **Maximal cell under single-valued `V` and plain betweenness (B).** There is
a coalition attaining the greatest coalition payoff whose removal cannot raise
the greatest coalition payoff on the residual types. This is the plain-B
analogue of `betweenness_max_cell`, proved without message completeness.

Proof (the tie-breaking construction): let `y = max 𝒲`.  `btw_order` provides a
complete transitive relation `⪰` on the level set `{v̄ = y}`, satisfying (i)
strict improvement toward the upper level set and (ii) decomposition.  Among the
finitely many conditional priors of cells of coalitions attaining `y`, choose
(by `two_B_finite_max`) a `⪰`-maximal one, attained by `K`.  Suppose a residual
coalition `K'` paid `w' > y`.  The merged pool `D = K.C ∪ K'.C` sits on the
level set (`two_B_merged_value`) and is a strict convex combination of
`μ⁰_{K.C}` and `μ⁰_{K'.C}` with `v̄(μ⁰_{K'.C}) = w' > y`, so property (i) ranks
`μ⁰_D` strictly above `μ⁰_{K.C}`.  A PBE partition with strictly decreasing
payoffs (via `forwardPartition`) of the auxiliary game `G'` on `D` (message
space cut to the union evidence, so evidence preimages stay inside `D`)
decomposes `μ⁰_D` into the cell priors, whose values are `≤ y` with equality
exactly at the top cell; the top cell lifts to a coalition of `H` attaining `y`
(`two_B_top_cell`).  Property (ii) then ranks the top-cell prior `⪰ μ⁰_D`, and
transitivity contradicts the `⪰`-maximality of `μ⁰_{K.C}`. -/
private lemma two_B_max_cell {H : DisclosureGame T Msg}
    (hSV : H.SingleValued) (hB : H.Betweenness) :
    ∃ K : H.Coalition, IsGreatest H.coalitionPayoffs K.w ∧
      ∀ (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ) (w' : ℝ),
        IsGreatest (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs w' →
          w' ≤ K.w := by
  classical
  set y := sSup H.coalitionPayoffs with hy_def
  have hy : IsGreatest H.coalitionPayoffs y := isGreatest_sSup_coalitionPayoffs H
  obtain ⟨ord, hcomp, htrans, hi, hii⟩ := btw_order hSV hB y
  -- Attaining priors lie on the level set.
  have hlevel_of : ∀ K0 : H.Coalition, K0.w = y → H.condPrior K0.C ∈ H.levelSet y := by
    intro K0 hK0
    have h1 : H.condPrior K0.C ∈ simplexOn H.Θ :=
      simplexOn_mono K0.C_subset (condPrior_mem_simplex K0.C_nonempty K0.C_subset)
    have h2 : H.vbar (H.condPrior K0.C) = y := by
      rw [← value_id hSV hB K0]
      exact hK0
    exact ⟨h1, h2⟩
  -- The finitely many attaining cells and their conditional priors.
  set cells : Finset (Finset T) :=
    H.Θ.powerset.filter (fun C => C.Nonempty ∧ ∃ K : H.Coalition, K.w = y ∧ K.C = C)
    with hcells_def
  have hcell_iff : ∀ C, C ∈ cells ↔
      (C ⊆ H.Θ ∧ C.Nonempty ∧ ∃ K : H.Coalition, K.w = y ∧ K.C = C) := by
    intro C
    rw [hcells_def, Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨K0, hK0⟩ : ∃ K0 : H.Coalition, K0.w = y := hy.1
  have hcells_ne : cells.Nonempty :=
    ⟨K0.C, (hcell_iff K0.C).mpr ⟨K0.C_subset, K0.C_nonempty, K0, hK0, rfl⟩⟩
  set A : Finset (T → ℝ) := cells.image (fun C => H.condPrior C) with hA_def
  have hA_level : ∀ p ∈ A, p ∈ H.levelSet y := by
    intro p hp
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨-, -, K1, hK1w, hK1C⟩ := (hcell_iff C).mp hC
    exact hK1C ▸ hlevel_of K1 hK1w
  -- Select an `ord`-maximal attaining prior.
  obtain ⟨pbar, hpbarA, hpbar⟩ :=
    two_B_finite_max ord A (hcells_ne.image _)
      (fun p hp q hq => hcomp p (hA_level p hp) q (hA_level q hq))
      (fun p hp q hq r hr => htrans p (hA_level p hp) q (hA_level q hq) r (hA_level r hr))
  obtain ⟨Cbar, hCbar_mem, hpbar_eq⟩ := Finset.mem_image.mp hpbarA
  obtain ⟨hCbarsub, hCbarne, K, hKw, hKC⟩ := (hcell_iff Cbar).mp hCbar_mem
  have hKmax : IsGreatest H.coalitionPayoffs K.w := hKw ▸ hy
  have hKlevel : H.condPrior K.C ∈ H.levelSet y := hlevel_of K hKw
  have hKmax_ord : ∀ K1 : H.Coalition, K1.w = y →
      ord (H.condPrior K.C) (H.condPrior K1.C) := by
    intro K1 hK1
    have hmem : H.condPrior K1.C ∈ A :=
      Finset.mem_image.mpr ⟨K1.C,
        (hcell_iff K1.C).mpr ⟨K1.C_subset, K1.C_nonempty, K1, hK1, rfl⟩, rfl⟩
    have h := hpbar _ hmem
    rwa [← hpbar_eq, ← hKC] at h
  refine ⟨K, hKmax, ?_⟩
  intro hne hsub w' hw'
  by_contra hcon
  rw [not_le] at hcon
  have hyw' : y < w' := hKw ▸ hcon
  obtain ⟨K', hK'w⟩ : ∃ K' : (H.restrict (H.Θ \ K.C) hne hsub).Coalition, K'.w = w' := hw'.1
  have hgtKK' : K.w < K'.w := by rw [hKw, hK'w]; exact hyw'
  -- Facts about the merged pool `K.C ∪ K'.C`.
  have hK'CsubΘ : K'.C ⊆ H.Θ := K'.C_subset.trans hsub
  have hDsub : K.C ∪ K'.C ⊆ H.Θ := Finset.union_subset K.C_subset hK'CsubΘ
  have hDne : (K.C ∪ K'.C).Nonempty :=
    ⟨K.C_nonempty.choose, Finset.mem_union_left _ K.C_nonempty.choose_spec⟩
  have hdisj : Disjoint K.C K'.C := by
    rw [Finset.disjoint_left]
    intro x hxK hxK'
    exact (Finset.mem_sdiff.mp (K'.C_subset hxK')).2 hxK
  have hDval : H.vbar (H.condPrior (K.C ∪ K'.C)) = y := by
    rw [two_B_merged_value hSV hB K hKmax hne hsub K' hgtKK']
    exact hKw
  have hDlevel : H.condPrior (K.C ∪ K'.C) ∈ H.levelSet y :=
    ⟨simplexOn_mono hDsub (condPrior_mem_simplex hDne hDsub), hDval⟩
  -- Property (i): the pool ranks strictly above `K`'s prior.
  have hK'val : H.vbar (H.condPrior K'.C) = w' := by
    rw [two_B_Kprime_value hSV hB K hne hsub K']
    exact hK'w
  have hK'simplex : H.condPrior K'.C ∈ simplexOn H.Θ :=
    simplexOn_mono hK'CsubΘ (condPrior_mem_simplex K'.C_nonempty hK'CsubΘ)
  obtain ⟨l, hl, hlcomb⟩ :=
    gp_condPrior_union K.C_nonempty K'.C_nonempty K.C_subset hK'CsubΘ hdisj
  have hnotord : ¬ ord (H.condPrior K.C) (H.condPrior (K.C ∪ K'.C)) := by
    have hmem : (fun θ => l * H.condPrior K.C θ + (1 - l) * H.condPrior K'.C θ)
        ∈ H.levelSet y := by
      rw [← hlcomb]
      exact hDlevel
    have hpair := hi (H.condPrior K.C) hKlevel (H.condPrior K'.C) hK'simplex
      (by rw [hK'val]; exact hyw') l hl hmem
    intro hord
    apply hpair.2
    rw [hlcomb] at hord
    exact hord
  -- The auxiliary game on the merged pool, with the union evidence as messages.
  set X : Finset Msg :=
    (H.restrictMsgSpace H.Θ).filter (fun m => m ∈ K.σ.evidence ∪ K'.σ.evidence) with hX_def
  have hXsub : X ⊆ H.restrictMsgSpace H.Θ := Finset.filter_subset _ _
  have hpreF : preimage H.M H.Θ X = K.C ∪ K'.C := by
    rw [← two_B_merged_preimage K hne hsub K']
    ext θ
    simp only [mem_preimage, DisclosureGame.preimageSetFull, DisclosureGame.preimageSet,
      Finset.mem_filter, hX_def]
    constructor
    · rintro ⟨hθ, m, hm⟩
      rw [Finset.mem_inter, Finset.mem_filter] at hm
      exact ⟨hθ, m, Finset.mem_coe.mpr hm.1, hm.2.2⟩
    · rintro ⟨hθ, m, hmM, hmE⟩
      exact ⟨hθ, m, Finset.mem_inter.mpr ⟨Finset.mem_coe.mp hmM, Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨θ, hθ, Finset.mem_coe.mp hmM⟩, hmE⟩⟩⟩
  have hXne : X.Nonempty := by
    obtain ⟨θ, hθ⟩ := hDne
    have hθ' : θ ∈ preimage H.M H.Θ X := by rw [hpreF]; exact hθ
    obtain ⟨m, hm⟩ := (mem_preimage.mp hθ').2
    exact ⟨m, (Finset.mem_inter.mp hm).2⟩
  -- A PBE partition of the auxiliary game with strictly decreasing payoffs.
  obtain ⟨P, hPstrict⟩ := btwcAux_exists_partition (subset_refl H.Θ) hXsub hXne
  have hPanti : Antitone P.w := hPstrict.antitone
  have hcover : preimage H.M H.Θ X = Finset.univ.biUnion P.C := P.cover_eq
  have hCsub' : ∀ i, P.C i ⊆ preimage H.M H.Θ X := fun i => P.C_subset i
  have hCsubΘ : ∀ i, P.C i ⊆ H.Θ := fun i => (hCsub' i).trans btwcAux_preimage_subset
  have hcard : 0 < P.card := by
    obtain ⟨θ, hθ⟩ : (preimage H.M H.Θ X).Nonempty := by rw [hpreF]; exact hDne
    obtain ⟨i, -, -⟩ := Finset.mem_biUnion.mp (hcover ▸ hθ)
    exact lt_of_le_of_lt (Nat.zero_le _) i.isLt
  set t0 : Fin P.card := ⟨0, hcard⟩ with ht0def
  have ht0 : thetaStep P.C t0 = preimage H.M H.Θ X := by
    have hfilter : (Finset.univ.filter (fun s : Fin P.card => t0 ≤ s)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro s _
      rw [Fin.le_def]
      exact Nat.zero_le _
    rw [thetaStep, hfilter, ← hcover]
  -- Value identification for every cell.
  have hval : ∀ z, P.w z = H.vbar (H.condPrior (P.C z)) := by
    intro z
    have hz := btwc_cell_value (btwcAux_singleValued hSV (subset_refl H.Θ) hXsub hXne)
      (btwcAux_betweenness hB (subset_refl H.Θ) hXsub hXne) (P.C_nonempty z) (P.C_subset z)
      (P.σ z) (P.w z) (P.payoff z)
    rw [btwcAux_vbar,
      btwcAux_condPrior (subset_refl H.Θ) hXsub hXne (P.C_nonempty z) (hCsub' z)] at hz
    exact hz
  -- Decomposition of the pool prior over the cells.
  have hcoverD : K.C ∪ K'.C = Finset.univ.biUnion P.C := by rw [← hpreF]; exact hcover
  obtain ⟨hpos, hsum, hcomb⟩ := btwc_condPrior_partition (G := H) P.C P.C_nonempty
    hCsubΘ P.C_disjoint hDne hcoverD
  -- The top-cell payoff dominates the pool value.
  have hle1 : H.vbar (H.condPrior (K.C ∪ K'.C)) ≤ P.w t0 := by
    rw [hcomb]
    refine btwc_convexCombo_le_index hB (fun z => H.condPrior (P.C z))
      (fun z => H.priorMeasure (P.C z) / H.priorMeasure (K.C ∪ K'.C))
      (fun z => simplexOn_mono (hCsubΘ z) (condPrior_mem_simplex (P.C_nonempty z) (hCsubΘ z)))
      (fun z => le_of_lt (hpos z)) hsum ?_
    intro z
    rw [← hval z]
    exact hPanti (by rw [Fin.le_def]; exact Nat.zero_le _)
  -- Realize the top cell as a coalition of `H`.
  obtain ⟨K₂, hK₂C, hK₂w⟩ : ∃ K₂ : H.Coalition, K₂.C = P.C t0 ∧ K₂.w = P.w t0 := by
    have h := two_B_top_cell H.Θ_nonempty (subset_refl H.Θ) hXsub hXne P t0 ht0
    rwa [restrict_self] at h
  have hwt0 : P.w t0 = y := le_antisymm (hy.2 ⟨K₂, hK₂w⟩) (by rw [← hDval]; exact hle1)
  -- Property (ii): some on-level cell prior ranks weakly above the pool prior.
  obtain ⟨z, hzlevel, hzord⟩ := hii (H.condPrior (K.C ∪ K'.C)) hDlevel P.card
    (fun z => H.priorMeasure (P.C z) / H.priorMeasure (K.C ∪ K'.C))
    (fun z => H.condPrior (P.C z)) hpos hsum
    (fun z => ⟨simplexOn_mono (hCsubΘ z) (condPrior_mem_simplex (P.C_nonempty z) (hCsubΘ z)),
      by rw [← hval z, ← hwt0]; exact hPanti (by rw [Fin.le_def]; exact Nat.zero_le _)⟩)
    hcomb
  -- Strictly decreasing payoffs force the on-level cell to be the top cell.
  have hz_t0 : z = t0 := by
    by_contra hzne
    have h0z : t0 < z :=
      lt_of_le_of_ne (by rw [Fin.le_def]; exact Nat.zero_le _) (Ne.symm hzne)
    have hlt : P.w z < P.w t0 := hPstrict h0z
    have hzy : P.w z = y := by rw [hval z]; exact hzlevel.2
    rw [hwt0] at hlt
    exact absurd hzy (ne_of_lt hlt)
  rw [hz_t0] at hzlevel hzord
  -- `K₂` attains `y`, so `ord`-maximality plus transitivity yields a contradiction.
  have hmaxord : ord (H.condPrior K.C) (H.condPrior (P.C t0)) := by
    have h := hKmax_ord K₂ (by rw [hK₂w]; exact hwt0)
    rwa [hK₂C] at h
  exact hnotord (htrans (H.condPrior K.C) hKlevel (H.condPrior (P.C t0)) hzlevel
    (H.condPrior (K.C ∪ K'.C)) hDlevel hmaxord hzord)

/-- **Existence of a COE partition under single-valued `V` and plain B**, by
strong induction on `|Θ|`, mirroring `betweenness_exists_coe` but selecting the
maximal cell via `two_B_max_cell` (no message completeness needed). -/
private lemma two_B_exists_coe (H : DisclosureGame T Msg)
    (hSV : H.SingleValued) (hB : H.Betweenness) :
    ∃ P : Partition H, P.IsCOE := by
  induction' n : H.Θ.card using Nat.strong_induction_on with k ih generalizing H
  obtain ⟨K, hKmax, hbound⟩ := two_B_max_cell hSV hB
  by_cases hempty : H.Θ \ K.C = ∅
  · exact t4_single_cell_coe H K hempty hKmax
  · obtain ⟨hne, hsub⟩ : (H.Θ \ K.C).Nonempty ∧ (H.Θ \ K.C) ⊆ H.Θ :=
      ⟨Finset.nonempty_of_ne_empty hempty, Finset.sdiff_subset⟩
    have hcard : (H.restrict (H.Θ \ K.C) hne hsub).Θ.card < k := by
      convert Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩) using 1
      · exact n.symm
      · simp_all +decide [Finset.ext_iff]
        exact Finset.not_disjoint_iff.mpr
          ⟨_, Finset.mem_of_subset K.C_subset K.C_nonempty.choose_spec, K.C_nonempty.choose_spec⟩
    exact ih _ hcard _ (two_B_restrict_SV hne hsub hSV) (restrict_Betweenness hne hsub hB) rfl
      |> fun ⟨P, hP⟩ => t4_prepend_coe H K hKmax hne hsub (hbound hne hsub) P hP

/-- **Theorem 3 (plain betweenness ⇒ existence).** Assume `V` is
single-valued. If `v̄` satisfies plain betweenness (B), then a
coalition-proof PBE exists. -/
theorem three_existence (hSV : G.SingleValued) (hB : G.Betweenness) :
    ∃ P : Partition G, P.IsCPPBEPartition := by
  obtain ⟨P, hP⟩ := two_B_exists_coe G hSV hB
  exact ⟨P, hP.isCPPBEPartition⟩


end DisclosureGame

end CPD
