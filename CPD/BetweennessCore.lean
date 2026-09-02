import CPD.Betweenness
import CPD.PBEExistence

/-!
# Betweenness core: Lemmas 4–6 (§6.2 Betweenness)

The single-valued betweenness development of §6.2: value identification
(**Lemma 4**, `value_id`), the largest pooling value over relative preimages
`v*(R)` (`vstar`, `vstar_isGreatest`), attainment (**Lemma 5**, `btw_attained`,
`btw_attained_le`, with the auxiliary-game realization step `btwc_key_le`), and
the merging lemma (**Lemma 6**, `btw_merging`, `btw_merging_impossible`,
construction and B*-impossibility halves).

Throughout, `V` is single-valued (`SingleValued`, this file's standing
assumption): at every belief `μ ∈ ΔΘ`, `V(μ) = {v̄(μ)}`, so the upper and lower
envelopes coincide, `v := v̄ = v̲`. Betweenness (B) and strict betweenness (B*)
themselves are `Betweenness` / `StrictBetweenness`, defined in
`CPD/Betweenness.lean`.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ## Single-valued payoff correspondence -/

variable (G) in
/-- **`V` is single-valued** (the standing assumption of §6.2, Betweenness):
at every belief in `ΔΘ`, `V(μ)` is the singleton `{v̄(μ)}` (so `v := v̄ = v̲`). -/
def SingleValued : Prop :=
  ∀ μ ∈ simplexOn G.Θ, G.V μ = {G.vbar μ}

/-! ## Private infrastructure for the core lemmas -/

/-- Restriction does not change the upper envelope. -/
private lemma btwc_restrict_vbar {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (μ : T → ℝ) : (G.restrict R hne hsub).vbar μ = G.vbar μ := rfl

/-
Single-valuedness is inherited by restricted games.
-/
private lemma btwc_restrict_singleValued {R : Finset T} (hne : R.Nonempty)
    (hsub : R ⊆ G.Θ) (hSV : G.SingleValued) :
    (G.restrict R hne hsub).SingleValued := by
  intro μ hμ
  have hGμ : μ ∈ simplexOn G.Θ := by
    grind +suggestions;
  convert hSV μ hGμ using 1

/-
The restricted conditional prior on a subset agrees with `G`'s.
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
weights summing to one. -/
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
    exact Finset.sum_congr rfl fun x hx => by rw [ ← Finset.mul_sum _ _ _, h_sum x hx, mul_one ] ;

/-
Under betweenness, sub-level sets of `v̄` are convex (the upper half of
betweenness).
-/
private lemma btwc_sublevel_convex (hB : G.Betweenness) (c : ℝ) :
    Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} := by
  intro μ hμ ν hν a b ha hb hab;
  by_cases ha0 : a = 0;
  · simp_all +decide [ show b = 1 by linarith ];
  · by_cases hb0 : b = 0;
    · simp_all +decide [ show a = 1 by linarith ];
    · have := hB μ hμ.1 ν hν.1 ( a ) ⟨ lt_of_le_of_ne ha ( Ne.symm ha0 ), by linarith [ show 0 < b by positivity ] ⟩ ; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
      exact ⟨ ⟨ fun x => add_nonneg ( mul_nonneg ha ( hμ.1.1 x ) ) ( mul_nonneg ( sub_nonneg.2 hb ) ( hν.1.1 x ) ), by simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, hμ.1.2.1, hν.1.2.1 ] ⟩, by cases this.2 <;> linarith! ⟩

/-
Finite betweenness (upper): `v̄` of a convex combination is bounded above by
the max of the values.
-/
private lemma btwc_convexCombo_le (hB : G.Betweenness) {E : Finset Msg}
    (x : Msg → (T → ℝ)) (a : Msg → ℝ)
    (hx : ∀ m ∈ E, x m ∈ simplexOn G.Θ)
    (ha : ∀ m ∈ E, 0 ≤ a m) (hsum : ∑ m ∈ E, a m = 1)
    {c : ℝ} (hc : ∀ m ∈ E, G.vbar (x m) ≤ c) :
    G.vbar (fun θ => ∑ m ∈ E, a m * x m θ) ≤ c := by
  have h_convex : Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} :=
    btwc_sublevel_convex hB c
  convert h_convex.sum_mem ( fun m _ => ha m ‹_› ) hsum ( fun m _ => ⟨ hx m ‹_›, hc m ‹_› ⟩ ) |> fun h => h.2 using 1 ; simp +decide [ Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum ] ; ring;
  exact congr_arg _ ( funext fun θ => by simp +decide [ mul_comm, Finset.mul_sum _ _ _ ] )

/-
Finite quasiconcavity: `v̄` of a convex combination dominates the min.
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
The conditional prior of a coalition cell decomposes as the average of the
coalition-induced beliefs over the on-path messages.
-/
private lemma btwc_condPrior_decomp {H : DisclosureGame T Msg} (K : H.Coalition) :
    H.condPrior K.C = fun θ =>
      ∑ m ∈ Finset.univ.filter (fun m => m ∈ K.σ.evidence),
        K.σ.onPathProb m * K.σ.coalitionBelief m θ := by
  funext θ;
  convert ( btwc_bayes K.σ ).1 θ using 1;
  refine' Finset.sum_congr rfl fun m hm => _;
  simp +decide [ Strategy.coalitionBelief, Strategy.belief ] at hm ⊢;
  by_cases hθ : θ ∈ K.C <;> simp +decide [ hθ, zeroExt ];
  · convert Or.inl rfl using 1;
  · rw [ DisclosureGame.condPrior_of_not_mem ] <;> simp +decide [ hθ ]

/-
The conditional prior on a disjoint union is a convex combination.
-/
private lemma btwc_condPrior_union {C D : Finset T}
    (hC : C.Nonempty) (hD : D.Nonempty) (hCΘ : C ⊆ G.Θ) (hDΘ : D ⊆ G.Θ)
    (hdisj : Disjoint C D) :
    ∃ l ∈ Set.Ioo (0 : ℝ) 1,
      G.condPrior (C ∪ D)
        = fun θ => l * G.condPrior C θ + (1 - l) * G.condPrior D θ := by
  refine' ⟨ G.priorMeasure C / ( G.priorMeasure C + G.priorMeasure D ), _, _ ⟩;
  · exact ⟨ div_pos ( G.priorMeasure_pos hC hCΘ ) ( add_pos ( G.priorMeasure_pos hC hCΘ ) ( G.priorMeasure_pos hD hDΘ ) ), by rw [ div_lt_iff₀ ] <;> linarith [ G.priorMeasure_pos hC hCΘ, G.priorMeasure_pos hD hDΘ ] ⟩;
  · ext θ; by_cases hθC : θ ∈ C <;> by_cases hθD : θ ∈ D <;> simp +decide [ *, div_eq_inv_mul ] ;
    · exact False.elim ( Finset.disjoint_left.mp hdisj hθC hθD );
    · simp_all +decide [ DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
      rw [ Finset.sum_union hdisj ] ; ring;
      by_cases h : ∑ x ∈ C, G.μ0 x = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      exact Or.inr ( by rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => G.μ0_mem.1 _ ] at h; aesop );
    · simp +decide [ *, DisclosureGame.condPrior, DisclosureGame.priorMeasure ];
      rw [ Finset.sum_union hdisj ];
      field_simp;
      rw [ one_sub_div, mul_div_assoc' ];
      · rw [ eq_div_iff ] <;> ring ; simp +decide [ *, Finset.sum_eq_zero_iff_of_nonneg, G.μ0_mem, G.μ0_fullSupport ];
        exact ne_of_gt ( Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( hDΘ hx ) ) hD );
      · exact ne_of_gt ( add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => G.μ0_mem.1 _ ) ( Finset.sum_pos ( fun _ _ => G.μ0_fullSupport _ ( hDΘ ‹_› ) ) hD ) );
    · simp +decide [ DisclosureGame.condPrior, hθC, hθD ]

/-
A relative preimage of a non-empty set of available messages is non-empty.
-/
private lemma btwc_preimage_nonempty {R : Finset T} {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (preimage G.M R X).Nonempty := by
  obtain ⟨ m, hm ⟩ := hXne;
  obtain ⟨ θ, hθ ⟩ := Finset.mem_biUnion.mp ( hX hm );
  exact ⟨ θ, Finset.mem_filter.mpr ⟨ hθ.1, ⟨ m, by aesop ⟩ ⟩ ⟩

/-
For a coalition of `G|_R`, its cell is the relative preimage of a non-empty
finite set of available messages (the evidence, intersected with `𝓜_R`).
-/
private lemma btwc_exists_evidence_finset {R : Finset T} (hne : R.Nonempty)
    (hsub : R ⊆ G.Θ) (K : Coalition (G.restrict R hne hsub)) :
    ∃ X : Finset Msg, X ⊆ G.restrictMsgSpace R ∧ X.Nonempty ∧
      preimage G.M R X = K.C := by
  refine' ⟨ Finset.filter ( fun m => m ∈ K.σ.evidence ) ( G.restrictMsgSpace R ), _, _, _ ⟩;
  · exact Finset.filter_subset _ _;
  · refine' Finset.nonempty_of_ne_empty _;
    obtain ⟨ θ, hθ ⟩ := K.preimage_eq.symm ▸ K.C_nonempty;
    simp_all +decide [ Finset.ext_iff, Set.ext_iff, DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
    obtain ⟨ m, hm ⟩ := hθ.2; use m; simp_all +decide [ DisclosureGame.restrictMsgSpace, Finset.subset_iff ] ;
    exact ⟨ θ, hθ.1, hm.1 ⟩;
  · refine' Finset.Subset.antisymm _ _ <;> intro θ hθ <;> simp_all +decide [ preimage, Finset.ext_iff ];
    · obtain ⟨ m, hm ⟩ := hθ.2;
      have := K.preimage_eq; simp_all +decide [ Finset.ext_iff, preimageSet ] ;
      specialize this θ; simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ] ;
      exact this.mp ⟨ m, by aesop ⟩;
    · have := K.preimage_eq;
      replace this := Finset.ext_iff.mp this θ; simp_all +decide [ DisclosureGame.preimageSetFull ] ;
      simp_all +decide [ DisclosureGame.preimageSet, Finset.Nonempty ];
      obtain ⟨ x, hx ⟩ := this.2; use x; simp_all +decide [ DisclosureGame.restrictMsgSpace ] ;
      exact ⟨ θ, this.1, hx.1 ⟩

/-
On-path probabilities are non-negative.
-/
private lemma btwc_onPathProb_nonneg {H : DisclosureGame T Msg} (s : Strategy H)
    (m : Msg) : 0 ≤ s.onPathProb m := by
  apply Finset.sum_nonneg;
  exact fun i hi => mul_nonneg ( H.μ0_mem.1 i ) ( s.mem i hi |>.1 m )

/-
The coalition-induced belief at an on-path message lies in the full simplex.
-/
private lemma btwc_coalitionBelief_mem {H : DisclosureGame T Msg} (K : H.Coalition)
    {m : Msg} (hm : m ∈ K.σ.evidence) : K.σ.coalitionBelief m ∈ simplexOn H.Θ := by
  convert zeroExt_mem_simplex (DisclosureGame.Coalition.C_subset K) _;
  exact K.σ.belief_mem_simplex hm

/-
Under single-valued `V`, every on-path coalition belief has upper-envelope
value equal to the coalition payoff.
-/
private lemma btwc_value_eq {H : DisclosureGame T Msg} (hSV : H.SingleValued)
    (K : H.Coalition) {m : Msg} (hm : m ∈ K.σ.evidence) :
    H.vbar (K.σ.coalitionBelief m) = K.w := by
  have h_mem := K.payoff m hm;
  convert Set.mem_singleton_iff.mp ( hSV _ ( btwc_coalitionBelief_mem K hm ) ▸ h_mem ) |> Eq.symm

/-
Under single-valued `V`, the lower envelope equals the upper envelope.
-/
private lemma btwc_vbar_eq_vlow (hSV : G.SingleValued) {μ : T → ℝ}
    (hμ : μ ∈ simplexOn G.Θ) : G.vlow μ = G.vbar μ := by
  convert Set.ext_iff.mp ( hSV μ hμ ) ( G.vbar μ ) using 1 ; simp +decide [ CPD.DisclosureGame.vlow ];
  constructor <;> intro h <;> have := hSV μ hμ <;> aesop ( simp_config := { singlePass := true } ) ;

/-
Under single-valued `V`, the upper envelope is continuous on the simplex.
-/
lemma btwc_vbar_continuousOn (hSV : G.SingleValued) :
    ContinuousOn G.vbar (simplexOn G.Θ) := by
  intro μ hμ;
  refine' tendsto_order.2 ⟨ _, _ ⟩;
  · intro a' ha';
    have := G.vlow_lowerSemicontinuousOn μ hμ a' (by
    grind +suggestions);
    filter_upwards [ this, self_mem_nhdsWithin ] with x' hx' hx'' using by simpa only [ btwc_vbar_eq_vlow hSV hx'' ] using hx';
  · intro a ha;
    have := G.vbar_upperSemicontinuousOn μ hμ;
    exact this a ha

/-- The single-message pooling coalition (MC-free): everyone able to send `m`
sends `m`. Mirrors `pooling_coalition` (private, in Existence.lean). -/
private lemma btwc_pooling_coalition (H : DisclosureGame T Msg) {m : Msg} (hm : m ∈ H.𝓜) :
    ∃ K : Coalition H, K.C = H.canSend m ∧
      K.w = H.vbar (H.condPrior (H.canSend m)) := by
  set C := H.canSend m
  have hC_nonempty : C.Nonempty := H.canSend_nonempty hm
  have hC_subset : C ⊆ H.Θ := by
    exact Finset.filter_subset _ _;
  set σ' : Strategy (H.restrict C hC_nonempty hC_subset) := ⟨fun θ m' => if m' = m then 1 else 0, by
    intro θ hθ
    simp [simplexOn];
    exact ⟨ fun _ => by split_ifs <;> norm_num, fun a ha => by rintro rfl; exact ha ( Finset.mem_filter.mp hθ |>.2 |> fun h => by aesop ) ⟩⟩
  generalize_proofs at *;
  refine' ⟨ ⟨ C, hC_nonempty, hC_subset, σ', _, H.vbar ( H.condPrior C ), _ ⟩, rfl, rfl ⟩;
  · simp +decide [ Strategy.evidence, DisclosureGame.preimageSetFull ];
    simp +decide [ Finset.subset_iff, DisclosureGame.preimageSet, Strategy.msgSupport ];
    simp +decide [ C, DisclosureGame.canSend, Finset.Nonempty, Set.Nonempty ];
    simp +decide [ σ', DisclosureGame.preimageFull ];
    simp +contextual [ preimage ];
    aesop;
  · intro m' hm'
    have h_m'_eq_m : m' = m := by
      contrapose! hm'; simp_all +decide [ Strategy.evidence ] ;
      simp +decide [ σ', Strategy.msgSupport, hm' ]
    rw [h_m'_eq_m];
    convert H.vbar_mem ( zeroExt_mem_simplex hC_subset (DisclosureGame.condPrior_mem_simplex hC_nonempty hC_subset) ) using 1;
    · congr! 1;
      ext θ; simp [σ', Strategy.coalitionBelief];
      simp +decide [ zeroExt, Strategy.belief, Strategy.onPathProb, DisclosureGame.condPrior ];
      simp +decide [ ← Finset.sum_div _ _ _, DisclosureGame.priorMeasure ];
      by_cases h : ∑ θ ∈ C, H.μ0 θ = 0 <;> simp +decide [ h ];
    · rw [ zeroExt_eq_self ( DisclosureGame.condPrior_mem_simplex hC_nonempty hC_subset ) ]

/-- `v̄(μ⁰_{P(m)})` is an attainable coalition payoff. Mirrors `vbar_pooling_mem`. -/
private lemma btwc_pooling_mem (H : DisclosureGame T Msg) {m : Msg} (hm : m ∈ H.𝓜) :
    H.vbar (H.condPrior (H.canSend m)) ∈ H.coalitionPayoffs := by
  obtain ⟨K, _, hKw⟩ := btwc_pooling_coalition H hm
  exact ⟨K, hKw⟩

/-- **Single-message pooling (MC-free).** For an available message `m`, the
pooling value on its relative preimage cell is an attainable coalition payoff of
`G|_R`: everyone in `M⁻¹_R({m})` sends `m`, inducing belief `μ⁰_{M⁻¹_R({m})}`. -/
private lemma btwc_single_pool_mem {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    {m : Msg} (hm : m ∈ G.restrictMsgSpace R) :
    G.vbar (G.condPrior (preimage G.M R {m})) ∈
      (G.restrict R hne hsub).coalitionPayoffs := by
  have hmem : m ∈ (G.restrict R hne hsub).𝓜 := by simpa using hm
  have hcanSend : (G.restrict R hne hsub).canSend m = preimage G.M R {m} := by
    simp [DisclosureGame.canSend, DisclosureGame.preimageFull]
  have hpool := btwc_pooling_mem (G.restrict R hne hsub) hmem
  rw [hcanSend, btwc_restrict_vbar,
    btwc_restrict_condPrior hne hsub (btwc_preimage_nonempty (by
      simpa using Finset.singleton_subset_iff.mpr hm) (Finset.singleton_nonempty m))
      (by intro x hx; exact (mem_preimage.mp hx).1)] at hpool
  exact hpool

/-! ## Auxiliary game and realization (`btwc_key_le`) infrastructure -/

/-- `M⁻¹_R(X) ⊆ R`. -/
private lemma btwcAux_preimage_subset {R : Finset T} {X : Finset Msg} :
    preimage G.M R X ⊆ R := Finset.filter_subset _ _

/-
Cover condition for the auxiliary game `G'`: `X = ⋃_{θ ∈ M⁻¹_R(X)} (M θ ∩ X)`.
-/
private lemma btwcAux_cover {R : Finset T}
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) :
    (↑X : Set Msg) = ⋃ θ ∈ preimage G.M R X, ((G.M θ ∩ X : Finset Msg) : Set Msg) := by
  ext m; simp [preimage];
  by_cases hm : m ∈ X <;> simp_all +decide [ Finset.subset_iff, DisclosureGame.restrictMsgSpace ];
  exact Exists.elim ( hX hm ) fun x hx => ⟨ x, hx.2, hx.1, ⟨ m, Finset.mem_inter_of_mem hx.2 hm ⟩ ⟩

/-- **The auxiliary game `G'`**, used in the proof of Lemma 5: cut the message
space down to a fixed non-empty `X ⊆ 𝓜_R`. `G'.Θ := M⁻¹_R(X)`, `G'.𝓜 := X`,
`G'.M θ := M θ ∩ X`, `G'.μ⁰ := μ⁰_{M⁻¹_R(X)}`, `G'.V := G.V`. -/
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

/-- `G'` has the same upper envelope as `G`. -/
private lemma btwcAux_vbar {R : Finset T} (hsub : R ⊆ G.Θ) {X : Finset Msg}
    (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) (μ : T → ℝ) :
    (btwcAux hsub hX hXne).vbar μ = G.vbar μ := rfl

/-
`G'` inherits single-valuedness of `V`.
-/
private lemma btwcAux_singleValued (hSV : G.SingleValued) {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).SingleValued := by
  intro μ hμ;
  convert hSV μ _ using 1;
  convert simplexOn_mono (btwcAux_preimage_subset.trans hsub) hμ

/-
`G'` inherits betweenness.
-/
private lemma btwcAux_betweenness (hB : G.Betweenness) {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    (btwcAux hsub hX hXne).Betweenness := by
  intro μ hμ μ' hμ' l hl;
  convert hB μ ( simplexOn_mono ( btwcAux_preimage_subset.trans hsub ) ( by simpa using hμ ) ) μ' ( simplexOn_mono ( btwcAux_preimage_subset.trans hsub ) ( by simpa using hμ' ) ) l hl using 1

/-
Conditioning `G'`'s prior further on `C ⊆ M⁻¹_R(X)` agrees with `G`'s.
-/
private lemma btwcAux_condPrior {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty)
    {C : Finset T} (hCne : C.Nonempty) (hCsub : C ⊆ preimage G.M R X) :
    (btwcAux hsub hX hXne).condPrior C = G.condPrior C := by
  ext θ; by_cases hθ : θ ∈ C <;> simp_all +decide [ condPrior_of_mem, condPrior_of_not_mem ] ;
  simp +decide [ priorMeasure, condPrior, hCsub hθ ];
  rw [ ← Finset.sum_div _ _ _, div_div_div_cancel_right₀ ];
  · exact congr_arg _ ( Finset.sum_congr rfl fun x hx => if_pos ( hCsub hx ) );
  · exact ne_of_gt ( Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( btwcAux_preimage_subset.trans hsub hx ) ) ( btwc_preimage_nonempty hX hXne ) )

/-
Evidence depends only on the type space and strategy function.
-/
private lemma btwc_evidence_congr {g₁ g₂ : DisclosureGame T Msg} (hΘ : g₁.Θ = g₂.Θ)
    (s₁ : Strategy g₁) (s₂ : Strategy g₂) (hσ : s₁.σ = s₂.σ) :
    s₁.evidence = s₂.evidence := by
  simp [Strategy.evidence, hσ];
  simp +decide [ Strategy.msgSupport, hσ, hΘ ]

/-
The coalition-induced belief depends only on the type space, prior, and strategy.
-/
private lemma btwc_coalitionBelief_congr {g₁ g₂ : DisclosureGame T Msg} (hΘ : g₁.Θ = g₂.Θ)
    (hμ0 : g₁.μ0 = g₂.μ0) (s₁ : Strategy g₁) (s₂ : Strategy g₂) (hσ : s₁.σ = s₂.σ) (m : Msg) :
    s₁.coalitionBelief m = s₂.coalitionBelief m := by
  unfold Strategy.coalitionBelief Strategy.belief Strategy.onPathProb;
  unfold zeroExt; aesop;

/-- Raw version of `btwc_condPrior_decomp` for a bare cell strategy. -/
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

/-- Raw version of `btwc_coalitionBelief_mem` for a bare cell strategy. -/
private lemma btwc_coalitionBelief_mem_raw {H : DisclosureGame T Msg} {C : Finset T}
    (hCne : C.Nonempty) (hCsub : C ⊆ H.Θ) (σ : Strategy (H.restrict C hCne hCsub))
    {m : Msg} (hm : m ∈ σ.evidence) : σ.coalitionBelief m ∈ simplexOn H.Θ := by
  convert zeroExt_mem_simplex hCsub _
  exact σ.belief_mem_simplex hm

/-- Raw version of `btwc_value_eq` for a bare cell strategy. -/
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
any `(C, σ, w)` with the coalition payoff condition satisfies `w = v̄(μ⁰_C)`. -/
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
        rw [ btwc_value_eq_raw hSV hCne hCsub σ w hpay ( Finset.mem_filter.mp hm |>.2 ) ] ;
  · convert btwc_convexCombo_le hB ( fun m => σ.coalitionBelief m ) ( fun m => σ.onPathProb m ) _ _ _ _;
    · exact fun m hm => btwc_coalitionBelief_mem_raw hCne hCsub σ ( Finset.mem_filter.mp hm |>.2 );
    · exact fun m hm => btwc_onPathProb_nonneg σ m;
    · exact ( btwc_bayes σ ).2;
    · exact fun m hm =>
        le_of_eq ( btwc_value_eq_raw hSV hCne hCsub σ w hpay ( Finset.mem_filter.mp hm |>.2 ) )

/-
Zeroing a PBE strategy off `Θ` preserves the PBE property.
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
      ext θ; by_cases hθ : θ ∈ H.Θ <;> simp +decide [ hθ ] ;
      · unfold Strategy.onPathProb; aesop;
      · rw [ show H.μ0 θ = 0 from _ ] ; ring;
        exact H.μ0_fullSupport θ |> fun h => by have := H.μ0_mem; exact (by
        exact this.2.2 θ hθ);
    · grind +suggestions;
  · exact h.payoff_compat;
  · intro θ hθ
    simp [Strategy.msgSupport, h.seq_optimal θ hθ];
    simpa [ hθ ] using h.seq_optimal θ hθ

/-- `G'` admits a PBE partition; in particular a partition with non-increasing payoffs. -/
private lemma btwcAux_exists_partition {R : Finset T} (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    ∃ P : Partition (btwcAux hsub hX hXne), Antitone P.w := by
  obtain ⟨s, hs⟩ := exists_PBE (btwcAux hsub hX hXne)
  obtain ⟨s', hs', hsupp⟩ := btwc_isPBE_zero hs
  obtain ⟨P, hP, _⟩ := (pbe_characterization hsupp).mp hs'
  exact ⟨P, hP.2⟩

/-
The conditional prior on a set `C` partitioned into disjoint nonempty cells is a
positive convex combination of the conditional priors of the cells.
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
  · ext θ; simp +decide [ *, DisclosureGame.condPrior ] ;
    by_cases hθ : ∃ i, θ ∈ D i <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.sum_ite ];
    obtain ⟨ i, hi ⟩ := hθ; rw [ Finset.sum_eq_single i ] <;> simp_all +decide [ Finset.disjoint_left ] ;
    · rw [ ← mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( priorMeasure_pos ( hDne i ) ( hDsub i ) ) ), one_mul ];
    · grind

/-
Finite (index-form) upper betweenness bound: `v̄` of a convex combination is
bounded above by the common upper bound of the values.
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
The evidence used by a partition cell of `G'` consists of messages in `X`.
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
**Top-cell realization.** A cell of `G'` whose residual type space is all of
`M⁻¹_R(X)` (e.g. the first cell under `Antitone` payoffs) yields a coalition of
`G|_R`, so its payoff is an attainable coalition payoff of `G|_R`.
-/
private lemma btwc_top_cell_mem {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty)
    (P : Partition (btwcAux hsub hX hXne)) (t : Fin P.card)
    (ht : thetaStep P.C t = preimage G.M R X) :
    P.w t ∈ (G.restrict R hne hsub).coalitionPayoffs := by
  refine' ⟨ ⟨ P.C t, _, _, ⟨ ( P.σ t ).σ, _ ⟩, _, P.w t, _ ⟩, rfl ⟩;
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

/-- **Lemma 5 core: the realization step.** Under single-valued `V` and
betweenness, the pooling value of every relative-preimage cell is bounded by
the greatest attainable coalition payoff of `G|_R`.

This is the message-completeness-free *realization* step behind Lemma 5: the
pooling value `v̄(μ⁰_{M⁻¹_R(X)})` of a relative-preimage cell is dominated by an
attainable coalition payoff. The auxiliary game `G'` (`btwcAux`) that cuts the
message space down to `X` admits a PBE partition with non-increasing payoffs
(`btwcAux_exists_partition`); its top cell has residual type space all of
`M⁻¹_R(X)`, so it realizes the pooling value as a coalition payoff of `G|_R`
(`btwc_top_cell_mem`), and the betweenness convex-combination bound
(`btwc_convexCombo_le_index`) shows this top-cell payoff dominates
`v̄(μ⁰_{M⁻¹_R(X)})`. -/
private lemma btwc_key_le (hSV : G.SingleValued) (hB : G.Betweenness)
    {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    {X : Finset Msg} (hX : X ⊆ G.restrictMsgSpace R) (hXne : X.Nonempty) :
    G.vbar (G.condPrior (preimage G.M R X)) ≤
      sSup (G.restrict R hne hsub).coalitionPayoffs := by
  set C := preimage G.M R X with hC
  have hCne : C.Nonempty := btwc_preimage_nonempty hX hXne
  have hCsub : C ⊆ G.Θ := btwcAux_preimage_subset.trans hsub
  -- A PBE partition of the auxiliary game, with non-increasing payoffs.
  obtain ⟨P, hPmono⟩ := btwcAux_exists_partition hsub hX hXne
  -- The cells cover `C = M⁻¹_R(X)`.
  have hcover : C = Finset.univ.biUnion P.C := P.cover_eq
  have hCsub' : ∀ i, P.C i ⊆ C := fun i => P.C_subset i
  -- There is at least one cell.
  have hcard : 0 < P.card := by
    obtain ⟨θ, hθ⟩ := hCne
    have hθ' : θ ∈ Finset.univ.biUnion P.C := hcover ▸ hθ
    obtain ⟨i, _, _⟩ := Finset.mem_biUnion.mp hθ'
    exact lt_of_le_of_lt (Nat.zero_le _) i.isLt
  set t0 : Fin P.card := ⟨0, hcard⟩ with ht0def
  -- The first cell's residual type space is all of `C`.
  have ht0 : thetaStep P.C t0 = C := by
    have hfilter : (Finset.univ.filter (fun s : Fin P.card => t0 ≤ s)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro s _
      rw [Fin.le_def]
      exact Nat.zero_le _
    rw [thetaStep, hfilter, ← hcover]
  -- Value identification for every cell.
  have hval : ∀ z, P.w z = G.vbar (G.condPrior (P.C z)) := by
    intro z
    have hz := btwc_cell_value (btwcAux_singleValued hSV hsub hX hXne)
      (btwcAux_betweenness hB hsub hX hXne) (P.C_nonempty z) (P.C_subset z) (P.σ z) (P.w z)
      (P.payoff z)
    rw [btwcAux_vbar, btwcAux_condPrior hsub hX hXne (P.C_nonempty z) (hCsub' z)] at hz
    exact hz
  -- Conditional-prior convex-combination decomposition over the cells.
  obtain ⟨hpos, hsum, hcomb⟩ := btwc_condPrior_partition (G := G) P.C P.C_nonempty
    (fun i => (hCsub' i).trans hCsub) P.C_disjoint hCne hcover
  -- Betweenness bound: `v̄(μ⁰_C) ≤ w t0` (the top cell payoff).
  have hle1 : G.vbar (G.condPrior C) ≤ P.w t0 := by
    rw [hcomb]
    refine btwc_convexCombo_le_index hB (fun z => G.condPrior (P.C z))
      (fun z => G.priorMeasure (P.C z) / G.priorMeasure C)
      (fun z => simplexOn_mono ((hCsub' z).trans hCsub)
        (condPrior_mem_simplex (P.C_nonempty z) ((hCsub' z).trans hCsub)))
      (fun z => le_of_lt (hpos z)) hsum ?_
    intro z
    rw [← hval z]
    exact hPmono (by rw [Fin.le_def]; exact Nat.zero_le _)
  -- The top-cell payoff is an attainable coalition payoff of `G|_R`.
  have hmem : P.w t0 ∈ (G.restrict R hne hsub).coalitionPayoffs :=
    btwc_top_cell_mem hne hsub hX hXne P t0 ht0
  calc G.vbar (G.condPrior C) ≤ P.w t0 := hle1
    _ ≤ sSup (G.restrict R hne hsub).coalitionPayoffs :=
        le_csSup (isCompact_coalitionPayoffs (G.restrict R hne hsub)).bddAbove hmem

/-! ## Value identification (Lemma 4) -/

/-- **Lemma 4 (value identification).** Assume `V` is single-valued and `v̄`
satisfies betweenness (B). Then every coalition `(C, σ, w)` of `G` pays exactly
the pooling value of its own cell: `w = v(μ⁰_C)`. -/
lemma value_id (hSV : G.SingleValued) (hB : G.Betweenness) (K : G.Coalition) :
    K.w = G.vbar (G.condPrior K.C) := by
  have h_condPrior_decomp : G.condPrior K.C = fun θ => ∑ m ∈ Finset.univ.filter (fun m => m ∈ K.σ.evidence), K.σ.onPathProb m * K.σ.coalitionBelief m θ := by
    convert btwc_condPrior_decomp K using 1;
  refine' le_antisymm _ _;
  · convert btwc_convexCombo_ge ( Betweenness.qc hB ) _ _ _ _ _ _;
    convert congr_fun h_condPrior_decomp _ using 1;
    · exact fun m hm => btwc_coalitionBelief_mem K ( Finset.mem_filter.mp hm |>.2 );
    · exact fun m hm => btwc_onPathProb_nonneg _ _;
    · exact ( btwc_bayes K.σ ).2;
    · exact fun m hm => by rw [ btwc_value_eq hSV K ( Finset.mem_filter.mp hm |>.2 ) ] ;
  · convert btwc_convexCombo_le hB ( fun m => K.σ.coalitionBelief m ) ( fun m => K.σ.onPathProb m ) _ _ _ _;
    · exact fun m hm => btwc_coalitionBelief_mem K ( Finset.mem_filter.mp hm |>.2 );
    · exact fun m hm => btwc_onPathProb_nonneg K.σ m;
    · exact ( btwc_bayes K.σ ).2;
    · exact fun m hm => le_of_eq ( btwc_value_eq hSV K ( Finset.mem_filter.mp hm |>.2 ) )

/-! ## The largest pooling value over relative preimages (Lemma 5 setup) -/

variable (G) in
/-- **Lemma 5 setup: `v*(R)`.** `v*(R) := max_{∅ ≠ X ⊆ 𝓜_R} v(μ⁰_{M⁻¹_R(X)})`,
the largest pooling value over relative preimages of `R` (encoded as an
`sSup`; the max over the finitely many non-empty `X ⊆ 𝓜_R` is attained, see
`vstar_isGreatest`). -/
noncomputable def vstar (R : Finset T) : ℝ :=
  sSup {w | ∃ X : Finset Msg, X ⊆ G.restrictMsgSpace R ∧ X.Nonempty ∧
    w = G.vbar (G.condPrior (preimage G.M R X))}

/-- **Lemma 5 setup.** The maximum defining `v*(R)` is attained: the candidate
set is a non-empty finite set of reals (every `m ∈ 𝓜_R` is available to some
type in `R`, so every relative preimage is non-empty). -/
lemma vstar_isGreatest {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ) :
    IsGreatest {w | ∃ X : Finset Msg, X ⊆ G.restrictMsgSpace R ∧ X.Nonempty ∧
      w = G.vbar (G.condPrior (preimage G.M R X))} (G.vstar R) := by
  refine' ⟨ _, fun w hw => le_csSup _ hw ⟩;
  · have h_finite : Set.Finite {w | ∃ X : Finset Msg, X ⊆ G.restrictMsgSpace R ∧ X.Nonempty ∧ w = G.vbar (G.condPrior (preimage G.M R X))} := by
      exact Set.Finite.subset ( Set.toFinite ( Set.range fun X : Finset Msg => G.vbar ( G.condPrior ( preimage G.M R X ) ) ) ) fun x hx => by obtain ⟨ X, hX₁, hX₂, rfl ⟩ := hx; exact Set.mem_range_self X;
    convert h_finite.isCompact.sSup_mem _;
    have h_nonempty : (G.restrictMsgSpace R).Nonempty := by
      exact Finset.Nonempty.biUnion hne fun x hx => G.M_nonempty x ( hsub hx );
    exact ⟨ _, ⟨ { h_nonempty.choose }, Finset.singleton_subset_iff.mpr h_nonempty.choose_spec, Finset.singleton_nonempty _, rfl ⟩ ⟩;
  · exact Set.Finite.bddAbove ( Set.Finite.subset ( Set.toFinite ( Set.range fun X : Finset Msg => G.vbar ( G.condPrior ( preimage G.M R X ) ) ) ) fun x hx => by aesop )

/-! ## Attainment (Lemma 5) -/

/-- **Lemma 5, bound half.** Assume `V` is single-valued and `v̄` satisfies B.
Every coalition `(C, σ, w)` of `G|_R` satisfies `w = v(μ⁰_C)` (Lemma 4 applied
to the restricted game) and `w ≤ v*(R)`. -/
lemma btw_attained_le (hSV : G.SingleValued) (hB : G.Betweenness)
    {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (K : Coalition (G.restrict R hne hsub)) :
    K.w = G.vbar (G.condPrior K.C) ∧ K.w ≤ G.vstar R := by
  have hKw : K.w = G.vbar (G.condPrior K.C) := by
    convert value_id _ _ K using 1;
    · convert btwc_restrict_vbar hne hsub _ |> Eq.symm using 2;
      exact btwc_restrict_condPrior hne hsub K.C_nonempty K.C_subset;
    · exact btwc_restrict_singleValued hne hsub hSV;
    · exact restrict_Betweenness hne hsub hB
  exact ⟨hKw, by
    obtain ⟨ X, hX₁, hX₂, hX₃ ⟩ := btwc_exists_evidence_finset hne hsub K;
    exact hKw.symm ▸ hX₃ ▸ ( vstar_isGreatest hne hsub ).2 ⟨ X, hX₁, hX₂, rfl ⟩⟩

/-- **Lemma 5 (btw-attained).** Assume `V` is single-valued and `v̄` satisfies
B. Then `max 𝒲_R = v*(R)`: the largest pooling value over relative preimages
is attained as a coalition payoff of `G|_R`, and no coalition payoff exceeds
it. -/
lemma btw_attained (hSV : G.SingleValued) (hB : G.Betweenness)
    {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ) :
    IsGreatest (G.restrict R hne hsub).coalitionPayoffs (G.vstar R) := by
  refine ⟨?_, ?_⟩
  · -- Membership: the largest pooling value is attained as a coalition payoff.
    obtain ⟨X₀, hX₀sub, hX₀ne, hX₀eq⟩ := (vstar_isGreatest hne hsub).1
    have hWne : (G.restrict R hne hsub).coalitionPayoffs.Nonempty :=
      coalitionPayoffs_nonempty _
    have hsup_mem : sSup (G.restrict R hne hsub).coalitionPayoffs ∈
        (G.restrict R hne hsub).coalitionPayoffs :=
      (isCompact_coalitionPayoffs (G.restrict R hne hsub)).sSup_mem hWne
    have hle : G.vstar R ≤ sSup (G.restrict R hne hsub).coalitionPayoffs := by
      rw [hX₀eq]; exact btwc_key_le hSV hB hne hsub hX₀sub hX₀ne
    have hge : sSup (G.restrict R hne hsub).coalitionPayoffs ≤ G.vstar R := by
      obtain ⟨K, hK⟩ := hsup_mem
      exact hK ▸ (btw_attained_le hSV hB hne hsub K).2
    have hEq : G.vstar R = sSup (G.restrict R hne hsub).coalitionPayoffs :=
      le_antisymm hle hge
    rw [hEq]; exact hsup_mem
  · rintro w ⟨ K, rfl ⟩
    exact (btw_attained_le hSV hB hne hsub K).2

/-! ## Merging (Lemma 6) -/

/-- **Lemma 6, construction half (btw-merging).** Assume `V` is single-valued
and `v̄` satisfies B. Let `(C, σ, w)` be a coalition of `G|_R` with
`w = max 𝒲_R`, and suppose `R' := R ∖ C` is non-empty and `G|_{R'}` admits a
coalition `(C', σ', w')` with `w' > w`. Then the merged pool is pinned:
`M⁻¹_R(X(σ) ∪ X(σ')) = C ∪ C'` and `v(μ⁰_{C ∪ C'}) = w`. -/
lemma btw_merging (hSV : G.SingleValued) (hB : G.Betweenness)
    {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (K : Coalition (G.restrict R hne hsub))
    (hmax : IsGreatest (G.restrict R hne hsub).coalitionPayoffs K.w)
    (hne' : (R \ K.C).Nonempty)
    (K' : Coalition (G.restrict (R \ K.C) hne' (Finset.sdiff_subset.trans hsub)))
    (hgt : K.w < K'.w) :
    G.preimageSet R (K.σ.evidence ∪ K'.σ.evidence) = K.C ∪ K'.C ∧
    G.vbar (G.condPrior (K.C ∪ K'.C)) = K.w := by
  refine' ⟨ _, le_antisymm _ _ ⟩;
  · have h_preimage_eq : G.preimageSet R K.σ.evidence = K.C ∧ G.preimageSet (R \ K.C) K'.σ.evidence = K'.C := by
      exact ⟨ K.preimage_eq, K'.preimage_eq ⟩;
    simp_all +decide [ Finset.subset_iff, DisclosureGame.preimageSet ];
    simp_all +decide [ Finset.Nonempty, Set.Nonempty ];
    grind;
  · obtain ⟨X_u, hX_u⟩ : ∃ X_u : Finset Msg, X_u ⊆ G.restrictMsgSpace R ∧ X_u.Nonempty ∧ preimage G.M R X_u = K.C ∪ K'.C := by
      obtain ⟨X, hX⟩ : ∃ X : Finset Msg, X ⊆ G.restrictMsgSpace R ∧ X.Nonempty ∧ preimage G.M R X = K.C := by
        convert btwc_exists_evidence_finset hne hsub K;
      obtain ⟨X', hX'⟩ : ∃ X' : Finset Msg, X' ⊆ G.restrictMsgSpace (R \ K.C) ∧ X'.Nonempty ∧ preimage G.M (R \ K.C) X' = K'.C := by
        apply btwc_exists_evidence_finset hne' (Finset.sdiff_subset.trans hsub) K';
      refine' ⟨ X ∪ X', _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, preimage ];
      · simp_all +decide [ Finset.subset_iff, DisclosureGame.restrictMsgSpace ];
        rintro x ( hx | hx ) <;> [ exact hX.1 hx; exact hX'.1 hx |> fun ⟨ a, ha, ha' ⟩ => ⟨ a, ha.1, ha' ⟩ ];
      · simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
        intro a; specialize hX; specialize hX'; simp_all +decide [ Finset.Nonempty, Finset.ext_iff ] ;
        grind +suggestions;
    have hle_sup : G.vbar (G.condPrior (K.C ∪ K'.C)) ≤
        sSup (G.restrict R hne hsub).coalitionPayoffs := by
      rw [← hX_u.2.2]
      exact btwc_key_le hSV hB hne hsub hX_u.1 hX_u.2.1
    rw [hmax.csSup_eq] at hle_sup; exact hle_sup
  · have := btwc_condPrior_union ( show K.C.Nonempty from K.C_nonempty ) ( show K'.C.Nonempty from K'.C_nonempty ) ( show K.C ⊆ G.Θ from Finset.Subset.trans K.C_subset hsub ) ( show K'.C ⊆ G.Θ from Finset.Subset.trans K'.C_subset ( Finset.sdiff_subset.trans hsub ) ) ?_;
    · obtain ⟨ l, hl, hl' ⟩ := this;
      have := hB ( G.condPrior K.C ) ?_ ( G.condPrior K'.C ) ?_ l hl <;> simp_all +decide [ IsGreatest ];
      · grind +suggestions;
      · have := condPrior_mem_simplex K.C_nonempty ( Finset.Subset.trans K.C_subset hsub ) ; simp_all +decide [ mem_simplexOn ] ;
        exact fun a ha => this.2.2 a ( fun ha' => ha ( hsub ( K.C_subset ha' ) ) );
      · exact ⟨ fun _ => by
          exact G.condPrior_mem_simplex K'.C_nonempty ( Finset.Subset.trans K'.C_subset ( Finset.sdiff_subset.trans hsub ) ) |> fun h => h.1 _, by
          convert condPrior_mem_simplex ( show K'.C.Nonempty from K'.C_nonempty ) ( show K'.C ⊆ G.Θ from Finset.Subset.trans K'.C_subset ( Finset.sdiff_subset.trans hsub ) ) |>.2.1 using 1, fun _ _ => by
          simp +decide [ DisclosureGame.condPrior, * ];
          exact Or.inl fun h => False.elim <| ‹¬_› <| Finset.mem_of_subset ( Finset.Subset.trans K'.C_subset <| Finset.sdiff_subset.trans hsub ) h ⟩;
    · exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( K'.C_subset hx' ) |>.2 hx

/-- **Lemma 6, impossibility half.** Under strict betweenness (B*) the
configuration of `btw_merging` is impossible: no residual coalition pays
strictly more than the maximal payoff `w`. -/
lemma btw_merging_impossible (hSV : G.SingleValued) (hB : G.StrictBetweenness)
    {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (K : Coalition (G.restrict R hne hsub))
    (hmax : IsGreatest (G.restrict R hne hsub).coalitionPayoffs K.w)
    (hne' : (R \ K.C).Nonempty)
    (K' : Coalition (G.restrict (R \ K.C) hne' (Finset.sdiff_subset.trans hsub))) :
    K'.w ≤ K.w := by
  -- By contradiction, assume ¬ (K'.w ≤ K.w), i.e. K.w < K'.w.
  by_contra h_contra
  have hK'_gt_K : K.w < K'.w := by
    exact lt_of_not_ge h_contra;
  obtain ⟨l, hl⟩ := btwc_condPrior_union K.C_nonempty K'.C_nonempty (K.C_subset.trans hsub) (K'.C_subset.trans (Finset.sdiff_subset.trans hsub)) (by
  exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( K'.C_subset hx' ) |>.2 hx);
  -- By `btw_merging`, we have G.vbar (G.condPrior (K.C ∪ K'.C)) = K.w.
  have h_vbar_union : G.vbar (G.condPrior (K.C ∪ K'.C)) = K.w := by
    apply (btw_merging hSV hB.1 hne hsub K hmax hne' K' hK'_gt_K).right;
  have := hB.2 ( G.condPrior K.C ) ?_ ( G.condPrior K'.C ) ?_ ?_ l hl.1 <;> simp_all +decide [ min_def, max_def ];
  · split_ifs at this <;> linarith [ btw_attained_le hSV hB.1 hne hsub K, btw_attained_le hSV hB.1 hne' ( Finset.sdiff_subset.trans hsub ) K' ];
  · convert condPrior_mem_simplex K.C_nonempty ( K.C_subset.trans hsub ) using 1;
    simp +decide [ simplexOn, condPrior ];
    exact fun _ _ => iff_of_true ( fun a ha => Or.inl fun ha' => False.elim <| ha <| K.C_subset ha' |> fun h => hsub h ) ( fun a ha => Or.inl fun ha' => False.elim <| ha ha' );
  · have := condPrior_mem_simplex K'.C_nonempty ( K'.C_subset.trans ( Finset.sdiff_subset.trans hsub ) ) ; simp_all +decide [ simplexOn ] ;
    exact fun θ hθ => this.2.2 θ ( fun hθ' => hθ ( hsub ( Finset.mem_sdiff.mp ( K'.C_subset hθ' ) |>.1 ) ) );
  · linarith [ ( btw_attained_le hSV hB.1 hne hsub K ).1, ( btw_attained_le hSV hB.1 hne' ( Finset.sdiff_subset.trans hsub ) K' ).1 ]

end DisclosureGame

end CPD
