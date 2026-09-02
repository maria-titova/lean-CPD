import CPD.Degrading

/-!
# Existence via Free Disposal and Revelation Aversion

Formalizes two cases of Proposition 4 in Section 6.4 of the paper,
built on top of the payoff-degradation machinery of `Degrading`:

* `free_disposal_existence` — free disposal (Definition 19) alone gives
  existence of a coalition-proof PBE, with no assumption on the message
  mapping.
* `ra_degradable_existence` — cheap-talk copies (M-CT) together with
  revelation aversion (Definition 21) give existence, since revelation
  aversion implies decomposability (Definition 20).
-/

open Set
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ## A connectedness helper -/

/-- Two closed sets covering `[a,b]`, one containing `a` and the other `b`, must
intersect inside `[a,b]`. -/
private lemma icc_closed_cover_inter {a b : ℝ} (hab : a ≤ b) {u v : Set ℝ}
    (hu : IsClosed u) (hv : IsClosed v) (hcover : Set.Icc a b ⊆ u ∪ v)
    (hau : a ∈ u) (hbv : b ∈ v) : ∃ c ∈ Set.Icc a b, c ∈ u ∧ c ∈ v := by
  by_contra h
  push_neg at h
  have hpc : IsPreconnected (Set.Icc a b) := isPreconnected_Icc
  have key := hpc uᶜ vᶜ hu.isOpen_compl hv.isOpen_compl
  have hc2 : Set.Icc a b ⊆ uᶜ ∪ vᶜ := by
    intro x hx
    rcases em (x ∈ u) with hxu | hxu
    · right; intro hxv; exact (h x hx hxu) hxv
    · left; exact hxu
  have ha' : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb' : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have hnv : (Set.Icc a b ∩ vᶜ).Nonempty := ⟨a, ha', fun hav => (h a ha' hau) hav⟩
  have hnu : (Set.Icc a b ∩ uᶜ).Nonempty := ⟨b, hb', fun hbu => (h b hb' hbu) hbv⟩
  obtain ⟨x, hx, hxu, hxv⟩ := key hc2 hnu hnv
  rcases hcover hx with h1 | h1
  · exact hxu h1
  · exact hxv h1

/-! ## The segment beliefs `(1-t)·q + t·δ_θ` -/

/-- The belief obtained by moving `q` a fraction `t` towards the point mass at `θ`. -/
private noncomputable def segBelief (q : T → ℝ) (θ : T) (t : ℝ) : T → ℝ :=
  fun x => (1 - t) * q x + t * pointMass θ x

omit [Fintype T] [Fintype Msg] in
private lemma segBelief_zero (q : T → ℝ) (θ : T) : segBelief q θ 0 = q := by
  funext x; simp [segBelief]

omit [Fintype T] [Fintype Msg] in
private lemma segBelief_one (q : T → ℝ) (θ : T) : segBelief q θ 1 = pointMass θ := by
  funext x; simp [segBelief]

private lemma pointMass_mem_simplex {θ : T} (hθ : θ ∈ G.Θ) :
    pointMass θ ∈ simplexOn G.Θ := by
  refine ⟨fun x => ?_, ?_, fun x hx => ?_⟩
  · unfold pointMass; split_ifs <;> norm_num
  · simp [pointMass]
  · unfold pointMass; rw [if_neg]; rintro rfl; exact hx hθ

private lemma segBelief_mem_simplex {q : T → ℝ} (hq : q ∈ simplexOn G.Θ) {θ : T}
    (hθ : θ ∈ G.Θ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segBelief q θ t ∈ simplexOn G.Θ := by
  obtain ⟨ht0, ht1⟩ := ht
  have hpm := pointMass_mem_simplex (G := G) hθ
  refine ⟨fun x => ?_, ?_, fun x hx => ?_⟩
  · exact add_nonneg (mul_nonneg (by linarith) (hq.1 x)) (mul_nonneg (by linarith) (hpm.1 x))
  · simp only [segBelief]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq.2.1, hpm.2.1]
    ring
  · simp only [segBelief, hq.2.2 x hx, hpm.2.2 x hx]; ring

omit [Fintype T] [Fintype Msg] in
private lemma segBelief_support {q : T → ℝ} {θ : T} (hθq : θ ∈ simplexSupport q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : ∀ x, 0 ≤ q x) :
    simplexSupport (segBelief q θ t) ⊆ simplexSupport q := by
  obtain ⟨ht0, ht1⟩ := ht
  intro x hx
  simp only [mem_simplexSupport, segBelief] at hx ⊢
  by_cases hxθ : x = θ
  · subst hxθ; exact hθq
  · have hpm : pointMass θ x = 0 := by unfold pointMass; rw [if_neg hxθ]
    rw [hpm, mul_zero, add_zero] at hx
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h] at hx; norm_num at hx
    · have h1t : 0 < 1 - t := by linarith
      nlinarith [hx, h1t, hq x]

/-! ## Revelation aversion implies decomposability (Proposition 4, analytic core) -/

/-- Along the segment from `q` to `δ_θ`, some belief realizes `w'`. -/
private lemma exists_seg_mem_V (hRA : G.RevelationAverse) {q : T → ℝ}
    (hq : q ∈ simplexOn G.Θ) {w' : ℝ} (hw'low : G.vMin ≤ w') (hw'high : w' ≤ G.vbar q)
    {θ : T} (hθ : θ ∈ G.Θ) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, w' ∈ G.V (segBelief q θ t) := by
  have hcont : ContinuousOn (fun t : ℝ => segBelief q θ t) (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    apply continuous_pi
    intro x
    unfold segBelief
    fun_prop
  have hmaps : MapsTo (fun t : ℝ => segBelief q θ t) (Set.Icc 0 1) (simplexOn G.Θ) :=
    fun t ht => segBelief_mem_simplex hq hθ ht
  have husc : UpperSemicontinuousOn (fun t : ℝ => G.vbar (segBelief q θ t)) (Set.Icc 0 1) :=
    (vbar_upperSemicontinuousOn (G := G)).comp hcont hmaps
  have hlsc : LowerSemicontinuousOn (fun t : ℝ => G.vlow (segBelief q θ t)) (Set.Icc 0 1) :=
    (vlow_lowerSemicontinuousOn (G := G)).comp hcont hmaps
  set u : Set ℝ := Set.Icc 0 1 ∩ {t | w' ≤ G.vbar (segBelief q θ t)} with hu_def
  set v : Set ℝ := Set.Icc 0 1 ∩ {t | G.vlow (segBelief q θ t) ≤ w'} with hv_def
  have hu_closed : IsClosed u := by
    obtain ⟨V, hVc, hVE⟩ := (upperSemicontinuousOn_iff_preimage_Ici.mp husc) w'
    have huv : u = Set.Icc 0 1 ∩ V := by rw [hu_def, ← hVE]; rfl
    rw [huv]; exact isClosed_Icc.inter hVc
  have hv_closed : IsClosed v := by
    obtain ⟨V, hVc, hVE⟩ := (lowerSemicontinuousOn_iff_preimage_Iic.mp hlsc) w'
    have huv : v = Set.Icc 0 1 ∩ V := by rw [hv_def, ← hVE]; rfl
    rw [huv]; exact isClosed_Icc.inter hVc
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ u ∪ v := by
    intro t ht
    have hmem := hmaps ht
    have hle : G.vlow (segBelief q θ t) ≤ G.vbar (segBelief q θ t) :=
      G.vlow_le hmem (vbar_mem hmem)
    by_cases h : w' ≤ G.vbar (segBelief q θ t)
    · exact Or.inl ⟨ht, h⟩
    · push_neg at h; exact Or.inr ⟨ht, le_of_lt (lt_of_le_of_lt hle h)⟩
  have h0u : (0 : ℝ) ∈ u := by
    refine ⟨⟨le_refl 0, by norm_num⟩, ?_⟩
    simp only [Set.mem_setOf_eq, segBelief_zero]; exact hw'high
  have h1v : (1:ℝ) ∈ v := by
    refine ⟨⟨by norm_num, le_refl 1⟩, ?_⟩
    simp only [Set.mem_setOf_eq, segBelief_one, hRA θ hθ]; exact hw'low
  obtain ⟨c, hc, hcu, hcv⟩ :=
    icc_closed_cover_inter (by norm_num) hu_closed hv_closed hcover h0u h1v
  refine ⟨c, hc, ?_⟩
  rw [V_eq_Icc (hmaps hc)]
  exact ⟨hcv.2, hcu.2⟩

/-- Revelation aversion (Definition 21) implies decomposability
(Definition 20); part of Proposition 4. -/
private lemma revelationAverse_degradable (hRA : G.RevelationAverse) : G.Degradable := by
  intro q hq w' hw'
  obtain ⟨hw'low, hw'high⟩ := hw'
  set A : Set (T → ℝ) :=
    {μ | μ ∈ simplexOn G.Θ ∧ simplexSupport μ ⊆ simplexSupport q ∧ w' ∈ G.V μ} with hA_def
  by_cases hqA : w' ∈ G.V q
  · exact subset_convexHull ℝ A ⟨hq, fun x hx => hx, hqA⟩
  · set Sq : Finset T := G.Θ.filter (fun θ => 0 < q θ) with hSq_def
    have hSq_mem : ∀ θ, θ ∈ Sq ↔ θ ∈ G.Θ ∧ 0 < q θ := by
      intro θ; rw [hSq_def, Finset.mem_filter]
    have hSq_supp : ∀ θ ∈ Sq, θ ∈ simplexSupport q :=
      fun θ hθ => (hSq_mem θ).mp hθ |>.2
    have hex : ∀ θ ∈ Sq, ∃ t ∈ Set.Icc (0 : ℝ) 1, w' ∈ G.V (segBelief q θ t) :=
      fun θ hθ => exists_seg_mem_V hRA hq hw'low hw'high ((hSq_mem θ).mp hθ).1
    choose! tf htf_mem htf_V using hex
    have htf_pos : ∀ θ ∈ Sq, 0 < tf θ := by
      intro θ hθ
      rcases lt_or_eq_of_le (htf_mem θ hθ).1 with h | h
      · exact h
      · exfalso; apply hqA
        have hv := htf_V θ hθ
        rw [← h, segBelief_zero] at hv
        exact hv
    have hz : ∀ θ ∈ Sq, segBelief q θ (tf θ) ∈ A := by
      intro θ hθ
      refine ⟨segBelief_mem_simplex hq ((hSq_mem θ).mp hθ).1 (htf_mem θ hθ), ?_, htf_V θ hθ⟩
      exact segBelief_support (hSq_supp θ hθ) (htf_mem θ hθ) hq.1
    set wf : T → ℝ := fun θ => q θ / tf θ with hwf_def
    have hwf_nonneg : ∀ θ ∈ Sq, 0 ≤ wf θ :=
      fun θ hθ => div_nonneg (hq.1 θ) (le_of_lt (htf_pos θ hθ))
    have hq_zero : ∀ x ∉ Sq, q x = 0 := by
      intro x hx
      rw [hSq_mem] at hx; push_neg at hx
      by_cases hxΘ : x ∈ G.Θ
      · exact le_antisymm (hx hxΘ) (hq.1 x)
      · exact hq.2.2 x hxΘ
    have hSq_nonempty : Sq.Nonempty := by
      rcases Finset.eq_empty_or_nonempty Sq with hempty | h
      · exfalso
        have : (1:ℝ) = 0 := by
          rw [← hq.2.1, Finset.sum_eq_zero (fun x _ => hq_zero x (by rw [hempty]; simp))]
        norm_num at this
      · exact h
    have hws : 0 < ∑ θ ∈ Sq, wf θ := by
      obtain ⟨θ₀, hθ₀⟩ := hSq_nonempty
      exact Finset.sum_pos' hwf_nonneg
        ⟨θ₀, hθ₀, div_pos ((hSq_mem θ₀).mp hθ₀).2 (htf_pos θ₀ hθ₀)⟩
    have hsum_q_Sq : ∑ θ ∈ Sq, q θ = 1 := by
      have hsub : ∑ θ ∈ Sq, q θ = ∑ θ, q θ :=
        Finset.sum_subset (Finset.subset_univ Sq) (fun x _ hx => hq_zero x hx)
      rw [hsub, hq.2.1]
    have hcm : Sq.centerMass wf (fun θ => segBelief q θ (tf θ)) = q := by
      rw [Finset.centerMass]
      have hkey : ∑ θ ∈ Sq, wf θ • segBelief q θ (tf θ) = (∑ θ ∈ Sq, wf θ) • q := by
        funext x
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hwf_def]
        have hstep : ∀ θ ∈ Sq, q θ / tf θ * segBelief q θ (tf θ) x
            = q θ / tf θ * (1 - tf θ) * q x + q θ * pointMass θ x := by
          intro θ hθ
          have htfne : tf θ ≠ 0 := ne_of_gt (htf_pos θ hθ)
          simp only [segBelief]
          field_simp
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.sum_mul]
        have hpm : ∑ θ ∈ Sq, q θ * pointMass θ x = if x ∈ Sq then q x else 0 := by
          simp only [pointMass, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq Sq x q]
        have hb_eq : (∑ θ ∈ Sq, q θ / tf θ * (1 - tf θ)) = (∑ θ ∈ Sq, q θ / tf θ) - 1 := by
          have hstep2 : (∑ θ ∈ Sq, q θ / tf θ * (1 - tf θ))
              = (∑ θ ∈ Sq, q θ / tf θ) - (∑ θ ∈ Sq, q θ) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro θ hθ
            have htfne : tf θ ≠ 0 := ne_of_gt (htf_pos θ hθ)
            field_simp
          rw [hstep2, hsum_q_Sq]
        rw [hpm, hb_eq]
        by_cases hxSq : x ∈ Sq
        · rw [if_pos hxSq]; ring
        · rw [if_neg hxSq, hq_zero x hxSq]; ring
      rw [hkey, smul_smul, inv_mul_cancel₀ (ne_of_gt hws), one_smul]
    rw [← hcm]
    exact Finset.centerMass_mem_convexHull Sq hwf_nonneg hws hz

/-! ## The corollaries -/

/-- **Free disposal gives the degradation property.** -/
private lemma freeDisposal_degradationProperty (hFD : G.FreeDisposal) :
    G.DegradationProperty := by
  intro R hne hsub K w' hw'
  refine ⟨{ C := K.C, C_nonempty := K.C_nonempty, C_subset := K.C_subset,
            σ := K.σ, exclusive := K.exclusive, w := w', payoff := ?_ }, rfl, rfl⟩
  intro m hm
  have hμ : K.σ.coalitionBelief m ∈ simplexOn G.Θ :=
    zeroExt_mem_simplex (K.C_subset.trans hsub) (K.σ.belief_mem_simplex hm)
  have hKpay := K.payoff m hm
  rw [restrict_V] at hKpay ⊢
  rw [V_eq_Icc hμ] at hKpay ⊢
  obtain ⟨hlow, hhigh⟩ := hKpay
  obtain ⟨hw'lo, hw'hi⟩ := hw'
  have hfd : G.vlow (K.σ.coalitionBelief m) = G.vMin := hFD _ hμ
  exact ⟨by rw [hfd]; exact hw'lo, le_trans hw'hi hhigh⟩

/-- **Proposition 4** (free disposal): if the sender has free disposal
(Definition 19), a coalition-proof PBE exists, with no assumption on the
message mapping. -/
theorem free_disposal_existence (hFD : G.FreeDisposal) :
    ∃ P : Partition G, P.IsCPPBEPartition :=
  degrade_halts (freeDisposal_degradationProperty hFD)

/-- **Proposition 4** (revelation averse): if the message mapping has
cheap-talk copies (M-CT) and the sender is revelation averse
(Definition 21), a coalition-proof PBE exists. -/
theorem ra_degradable_existence (hMCT : G.MCT) (hRA : G.RevelationAverse) :
    ∃ P : Partition G, P.IsCPPBEPartition :=
  degrade_halts (degrade_general hMCT (revelationAverse_degradable hRA))

end DisclosureGame

end CPD
