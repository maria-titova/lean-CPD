import CPD.COE

/-!
# Existence of coalition-proof PBE: quasiconcavity and message completeness (§6.1)

Theorem 1 shows that a coalition-proof PBE exists whenever the game satisfies
message completeness and its payoffs are quasiconcave. This file sets up the
two conditions and the two lemmas the existence proof is built on. Throughout,
`P(m)` is `G.canSend m` (the types that can send `m`), `μ⁰_C` is
`G.condPrior C` (the prior conditioned on `C`), `v̄` is `G.vbar` (the upper
envelope of the payoff correspondence `V`), and `𝒲` is `G.coalitionPayoffs`.

* **Definition 12** (generic): the map `C ↦ v̄(μ⁰_C)` is injective over
  non-empty `C ⊆ Θ` (`Generic`).
* **Definition 13** (QC, QC*): `v̄` is quasiconcave on the simplex `ΔΘ`
  (`QC`), respectively strictly quasiconcave (`QCStar`).
* **Definition 14** (M-C): the message mapping is complete — for any two
  messages `m, m'` there is a message `m''` with `P(m'') = P(m) ∪ P(m')`
  (`MC`).
* **Lemma 3** (pooling): under QC and M-C, every coalition `(C,σ,w)` has a
  message `m*` with `P(m*) = C`, its payoff is dominated by the pooling value
  `v̄(μ⁰_C)` (`pooling_dominance`), the greatest coalition payoff equals the
  greatest pooling payoff (`isGreatest_coalitionPayoffs_iff`), and any
  coalition attaining `max 𝒲` has pooling value equal to that maximum
  (`coalition_attains_max`).
* **Lemma D.1** (merging, Appendix D): under QC and M-C, from a coalition of
  `G|_R` attaining `max 𝒲_R` and a strictly higher-paying coalition on
  `R ∖ C`, one can build a strictly larger coalition of `G|_R` with the same
  payoff and pooling value (`merging`); this is impossible under QC* or
  genericity, which is what rules out the residual maximum rising once a
  maximal cell is removed.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ## Definitions: conditions QC, QC*, M-C; genericity -/

variable (G) in
/-- **Definition 13** (QC): `v̄` is *quasiconcave* on `ΔΘ`. -/
def QC : Prop :=
  ∀ μ ∈ simplexOn G.Θ, ∀ μ' ∈ simplexOn G.Θ, ∀ l : ℝ, l ∈ Set.Ioo (0 : ℝ) 1 →
    min (G.vbar μ) (G.vbar μ') ≤ G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ)

variable (G) in
/-- **Definition 13** (QC*): the inequality in (QC) is strict whenever
`μ ≠ μ'`. -/
def QCStar : Prop :=
  ∀ μ ∈ simplexOn G.Θ, ∀ μ' ∈ simplexOn G.Θ, μ ≠ μ' → ∀ l : ℝ, l ∈ Set.Ioo (0 : ℝ) 1 →
    min (G.vbar μ) (G.vbar μ') < G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ)

variable (G) in
/-- **Definition 14** (M-C): the message structure is *complete*: for all
`m, m' ∈ 𝓜` there is `m'' ∈ 𝓜` with `P(m'') = P(m) ∪ P(m')`. -/
def MC : Prop :=
  ∀ m ∈ G.𝓜, ∀ m' ∈ G.𝓜, ∃ m'' ∈ G.𝓜, G.canSend m'' = G.canSend m ∪ G.canSend m'

variable (G) in
/-- **Definition 12** (generic): `C ↦ v̄(μ⁰_C)` is injective on non-empty
subsets `C ⊆ Θ`. -/
def Generic : Prop :=
  Set.InjOn (fun C : Finset T => G.vbar (G.condPrior C))
    {C : Finset T | C.Nonempty ∧ C ⊆ G.Θ}

/-! ## Private helper lemmas -/

/-
A strategy's evidence lies in the game's message space.
-/
private lemma evidence_mem_msgSpace (H : DisclosureGame T Msg) (s : Strategy H)
    {m : Msg} (hm : m ∈ s.evidence) : m ∈ H.𝓜 := by
  obtain ⟨ θ, hθ ⟩ := Set.mem_iUnion₂.mp hm; simp_all +decide [ Strategy.msgSupport, mem_simplexSupport ] ;
  have := s.mem θ hθ.1; simp_all +decide [ simplexOn ] ;
  exact H.M_subset θ hθ.1 ( by contrapose! hθ; aesop )

/-
Preimage of a set of messages as a union of `canSend`.
-/
private lemma preimageSetFull_eq_biUnion (H : DisclosureGame T Msg) (X : Set Msg) :
    H.preimageSetFull X = (Finset.univ.filter (fun m => m ∈ X)).biUnion H.canSend := by
  ext x; simp [DisclosureGame.preimageSetFull, DisclosureGame.canSend, DisclosureGame.preimageFull];
  simp +decide [ DisclosureGame.mem_preimageSet, Set.inter_nonempty, Finset.Nonempty ];
  simp +decide [ preimage, and_comm, and_left_comm, and_assoc ];
  simp +decide [ Finset.Nonempty, Set.Nonempty ]

/-
Message completeness merges finitely many `canSend` sets.
-/
private lemma mc_merge_canSend (H : DisclosureGame T Msg) (hMC : H.MC)
    {E : Finset Msg} (hne : E.Nonempty) (hE : ∀ m ∈ E, m ∈ H.𝓜) :
    ∃ m ∈ H.𝓜, H.canSend m = E.biUnion H.canSend := by
  induction' hne using Finset.Nonempty.cons_induction with m hm ih;
  · aesop;
  · obtain ⟨ m', hm', hm'' ⟩ := ‹ ( ∀ m ∈ ih, m ∈ H.𝓜 ) → ∃ m ∈ H.𝓜, H.canSend m = ih.biUnion H.canSend › ( fun m hm' => hE m ( Finset.mem_cons_of_mem hm' ) );
    obtain ⟨ m'', hm'', hm''' ⟩ := hMC hm ( hE hm ( Finset.mem_cons_self _ _ ) ) m' hm';
    aesop

/-
Bayes plausibility: the prior is the average of induced beliefs, with weights
summing to one.
-/
private lemma bayes_plausibility (H : DisclosureGame T Msg) (s : Strategy H) :
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
The super-level set of `v̄` is convex under QC.
-/
lemma vbar_superlevel_convex (hQC : G.QC) (c : ℝ) :
    Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ c ≤ G.vbar μ} := by
  intro x hx y hy a b ha hb hab;
  by_cases ha0 : a = 0;
  · aesop;
  · by_cases hb0 : b = 0;
    · simp_all +decide [ show a = 1 by linarith ];
    · refine' ⟨ _, _ ⟩;
      · exact ⟨ fun θ => by exact add_nonneg ( mul_nonneg ha ( hx.1.1 θ ) ) ( mul_nonneg hb ( hy.1.1 θ ) ), by simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hab, hx.1.2.1, hy.1.2.1 ], fun θ hθ => by simp +decide [ hx.1.2.2 θ hθ, hy.1.2.2 θ hθ ] ⟩;
      · have := hQC x hx.1 y hy.1 a ⟨ lt_of_le_of_ne ha ( Ne.symm ha0 ), by linarith [ show a < 1 from lt_of_le_of_ne ( by linarith ) ( by aesop ) ] ⟩;
        simpa [ ← hab ] using le_trans ( le_min hx.2 hy.2 ) this

/-
Finite quasiconcavity: `v̄` of a convex combination dominates the min.
-/
private lemma vbar_convexCombo_ge (hQC : G.QC) {E : Finset Msg}
    (x : Msg → (T → ℝ)) (a : Msg → ℝ)
    (hx : ∀ m ∈ E, x m ∈ simplexOn G.Θ)
    (ha : ∀ m ∈ E, 0 ≤ a m) (hsum : ∑ m ∈ E, a m = 1)
    {c : ℝ} (hc : ∀ m ∈ E, c ≤ G.vbar (x m)) :
    c ≤ G.vbar (fun θ => ∑ m ∈ E, a m * x m θ) := by
  have h_convex : Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ c ≤ G.vbar μ} :=
    vbar_superlevel_convex hQC c
  have h_convex_comb : (∑ m ∈ E, a m • x m) ∈ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ c ≤ G.vbar μ} := by
    exact h_convex.sum_mem ( fun m hm => ha m hm ) hsum fun m hm => ⟨ hx m hm, hc m hm ⟩;
  convert h_convex_comb.2 using 1;
  exact congr_arg _ ( funext fun θ => by simp +decide [ Finset.sum_apply, Pi.smul_apply ] )

/-
The pooling coalition: all senders of `m` pool on `m`, with payoff
`v̄(μ⁰_{P(m)})`.
-/
private lemma pooling_coalition (H : DisclosureGame T Msg) {m : Msg} (hm : m ∈ H.𝓜) :
    ∃ K : Coalition H, K.C = H.canSend m ∧
      K.w = H.vbar (H.condPrior (H.canSend m)) := by
  -- Set C := H.canSend m. Then C is nonempty (canSend_nonempty hm) and C ⊆ H.Θ (it is Θ.filter ..., so filter_subset).
  set C := H.canSend m
  have hC_nonempty : C.Nonempty := H.canSend_nonempty hm
  have hC_subset : C ⊆ H.Θ := by
    exact Finset.filter_subset _ _;
  -- Build the strategy `σ' : Strategy (H.restrict C hC_nonempty hC_subset)` with `σ' := { σ := fun θ m' => if m' = m then 1 else 0, mem := ... }` (each row is the point mass `δ_m`; the membership obligation holds because for `θ ∈ C`, `m ∈ H.M θ`).
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

/-- `v̄(μ⁰_{P(m)})` is an attainable coalition payoff. -/
private lemma vbar_pooling_mem (H : DisclosureGame T Msg) {m : Msg} (hm : m ∈ H.𝓜) :
    H.vbar (H.condPrior (H.canSend m)) ∈ H.coalitionPayoffs := by
  obtain ⟨K, _, hKw⟩ := pooling_coalition H hm
  exact ⟨K, hKw⟩

/-
Restriction preserves quasiconcavity.
-/
private lemma restrict_QC {S : Finset T} (hne : S.Nonempty)
    (hsub : S ⊆ G.Θ) (hQC : G.QC) : (G.restrict S hne hsub).QC := by
  intro μ hμ μ' hμ' l hl;
  convert hQC μ ( simplexOn_mono hsub hμ ) μ' ( simplexOn_mono hsub hμ' ) l hl using 1

/-
Restriction preserves message completeness.
-/
lemma restrict_MC {S : Finset T} (hne : S.Nonempty)
    (hsub : S ⊆ G.Θ) (hMC : G.MC) : (G.restrict S hne hsub).MC := by
  intro m hm m' hm';
  obtain ⟨m'', hm'', hm''_eq⟩ : ∃ m'' ∈ G.𝓜, G.canSend m'' = G.canSend m ∪ G.canSend m' := hMC m (DisclosureGame.restrictMsgSpace_subset hsub hm) m' (DisclosureGame.restrictMsgSpace_subset hsub hm');
  refine' ⟨ m'', _, _ ⟩;
  · simp_all +decide [ DisclosureGame.restrictMsgSpace ];
    obtain ⟨ a, ha, ha' ⟩ := hm; obtain ⟨ b, hb, hb' ⟩ := hm'; simp_all +decide [ Finset.ext_iff, DisclosureGame.canSend ] ;
    specialize hm''_eq a; simp_all +decide [ DisclosureGame.preimageFull, DisclosureGame.canSend ] ;
    simp_all +decide [ preimage ];
    grind;
  · simp_all +decide [ Finset.ext_iff, Set.ext_iff, DisclosureGame.canSend ];
    simp_all +decide [ DisclosureGame.preimageFull, DisclosureGame.preimageSet ];
    simp_all +decide [ preimage ];
    grind

/-
The restricted conditional prior on a subset agrees with `G`'s.
-/
private lemma restrict_condPrior {S : Finset T} (hne : S.Nonempty)
    (hsub : S ⊆ G.Θ) {C : Finset T} (hC : C.Nonempty) (hCS : C ⊆ S) :
    (G.restrict S hne hsub).condPrior C = G.condPrior C := by
  have h_condPrior_eq : ∀ θ, (G.restrict S hne hsub).condPrior C θ = G.condPrior C θ := by
    intro θ; by_cases hθ : θ ∈ C <;> simp +decide [ *, DisclosureGame.condPrior, DisclosureGame.priorMeasure ] ;
    simp +decide [ ← Finset.sum_div, ← Finset.sum_filter, hCS hθ ];
    rw [ Finset.inter_eq_left.mpr hCS, div_div_div_cancel_right₀ ( ne_of_gt ( Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( hsub hx ) ) hne ) ) ];
  exact funext h_condPrior_eq

/-
The conditional prior on a disjoint union is a convex combination.
-/
private lemma condPrior_union_convexCombo {C D : Finset T}
    (hC : C.Nonempty) (hD : D.Nonempty) (hCΘ : C ⊆ G.Θ) (hDΘ : D ⊆ G.Θ)
    (hdisj : Disjoint C D) :
    ∃ l ∈ Set.Ioo (0 : ℝ) 1,
      G.condPrior (C ∪ D)
        = fun θ => l * G.condPrior C θ + (1 - l) * G.condPrior D θ := by
  refine' ⟨ G.priorMeasure C / ( G.priorMeasure C + G.priorMeasure D ), _, _ ⟩;
  · exact ⟨ div_pos ( priorMeasure_pos hC hCΘ ) ( add_pos ( priorMeasure_pos hC hCΘ ) ( priorMeasure_pos hD hDΘ ) ), by rw [ div_lt_one ( add_pos ( priorMeasure_pos hC hCΘ ) ( priorMeasure_pos hD hDΘ ) ) ] ; exact lt_add_of_pos_right _ ( priorMeasure_pos hD hDΘ ) ⟩;
  · ext θ; by_cases hθC : θ ∈ C <;> by_cases hθD : θ ∈ D <;> simp +decide [ hθC, hθD, DisclosureGame.condPrior_of_mem, DisclosureGame.condPrior_of_not_mem ] ;
    · exact False.elim ( Finset.disjoint_left.mp hdisj hθC hθD );
    · rw [ div_mul_div_comm, div_eq_div_iff ];
      · rw [ DisclosureGame.priorMeasure, DisclosureGame.priorMeasure, DisclosureGame.priorMeasure, Finset.sum_union ( Finset.disjoint_left.mpr fun x hx hx' => Finset.disjoint_left.mp hdisj hx hx' ) ] ; ring;
      · exact ne_of_gt ( priorMeasure_pos ( Finset.Nonempty.mono ( Finset.subset_union_left ) hC ) ( Finset.union_subset hCΘ hDΘ ) );
      · exact mul_ne_zero ( ne_of_gt ( add_pos ( DisclosureGame.priorMeasure_pos hC hCΘ ) ( DisclosureGame.priorMeasure_pos hD hDΘ ) ) ) ( ne_of_gt ( DisclosureGame.priorMeasure_pos hC hCΘ ) );
    · rw [ one_sub_div, div_mul_div_comm, div_eq_div_iff ];
      · simp +decide [ DisclosureGame.priorMeasure, Finset.sum_union hdisj ] ; ring;
      · exact ne_of_gt ( G.priorMeasure_pos ( Finset.Nonempty.mono ( Finset.subset_union_left ) hC ) ( Finset.union_subset hCΘ hDΘ ) );
      · exact mul_ne_zero ( ne_of_gt ( add_pos ( DisclosureGame.priorMeasure_pos hC hCΘ ) ( DisclosureGame.priorMeasure_pos hD hDΘ ) ) ) ( ne_of_gt ( DisclosureGame.priorMeasure_pos hD hDΘ ) );
      · exact ne_of_gt ( add_pos ( DisclosureGame.priorMeasure_pos hC hCΘ ) ( DisclosureGame.priorMeasure_pos hD hDΘ ) )

/-! ## Lemma 3 (pooling): pooling dominance and its consequences -/

variable (G) in
/-- The set of **pooling payoffs** `{v̄(μ⁰_{P(m)}) | m ∈ 𝓜}`. -/
noncomputable def poolingPayoffs : Set ℝ :=
  (fun m => G.vbar (G.condPrior (G.canSend m))) '' (G.𝓜 : Set Msg)

/-
**Lemma 3** (pooling, main part). Under QC and M-C, every coalition
`(C, σ, w)` admits a message `m*` with `P(m*) = C`, and `w` is dominated by
`v̄(μ⁰_C)`.
-/
theorem pooling_dominance (hQC : G.QC) (hMC : G.MC) (K : Coalition G) :
    (∃ m ∈ G.𝓜, G.canSend m = K.C) ∧ K.w ≤ G.vbar (G.condPrior K.C) := by
  constructor;
  · obtain ⟨E, hE⟩ : ∃ E : Finset Msg, K.C = E.biUnion G.canSend ∧ E.Nonempty ∧ ∀ m ∈ E, m ∈ (G.restrict K.C K.C_nonempty K.C_subset).𝓜 := by
      refine' ⟨ Finset.univ.filter fun m => m ∈ K.σ.evidence, _, _, _ ⟩;
      · convert K.preimage_eq.symm using 1;
        exact (preimageSetFull_eq_biUnion G K.σ.evidence).symm;
      · have := K.preimage_eq;
        contrapose! this; simp_all +decide [ DisclosureGame.preimageSetFull ] ;
        simp_all +decide [ DisclosureGame.preimageSet ];
        simp_all +decide [ Set.Nonempty, Finset.ext_iff ];
        exact K.C_nonempty;
      · exact fun m hm => evidence_mem_msgSpace _ _ ( Finset.mem_filter.mp hm |>.2 );
    have := mc_merge_canSend G hMC hE.2.1 ( fun m hm => by
      exact G.restrictMsgSpace_subset K.C_subset ( hE.2.2 m hm ) );
    grind;
  · set G' := G.restrict K.C K.C_nonempty K.C_subset with hG'
    set s := K.σ with hs
    set E := Finset.univ.filter (fun m => m ∈ s.evidence) with hE;
    have hbel : ∀ θ, G'.μ0 θ = ∑ m ∈ E, s.onPathProb m * s.belief m θ := by
      convert bayes_plausibility G' s |>.1 using 1;
    have hconvexCombo : G.vbar (fun θ => ∑ m ∈ E, s.onPathProb m * s.belief m θ) ≥ K.w := by
      apply vbar_convexCombo_ge hQC (fun m => s.belief m) (fun m => s.onPathProb m);
      · intro m hm;
        exact Strategy.belief_mem_simplex s ( by aesop ) |> fun h => simplexOn_mono K.C_subset h;
      · intro m hm; exact (by
        exact Finset.sum_nonneg fun _ _ => mul_nonneg ( G'.μ0_mem.1 _ ) ( s.mem _ ( by aesop ) |>.1 _ ));
      · convert bayes_plausibility G' s |>.2 using 1;
      · intro m hm
        have hpay : K.w ∈ G.V (s.coalitionBelief m) := by
          exact K.payoff m ( by simpa [ hE ] using hm )
        have hbel : s.coalitionBelief m = s.belief m := by
          apply zeroExt_eq_self;
          exact Strategy.belief_mem_simplex _ ( by aesop )
        rw [hbel] at hpay
        exact le_vbar (by
        exact Strategy.belief_mem_simplex s ( by aesop ) |> fun h => simplexOn_mono K.C_subset h) hpay;
    convert hconvexCombo.le using 2;
    ext θ; specialize hbel θ; aesop;

/-
**Lemma 3** (pooling, identity). Under QC and M-C, the greatest coalition
payoff is the greatest pooling payoff: `max 𝒲_Θ = max_{m∈𝓜} v̄(μ⁰_{P(m)})`.
-/
theorem isGreatest_coalitionPayoffs_iff (hQC : G.QC) (hMC : G.MC) {w : ℝ} :
    IsGreatest G.coalitionPayoffs w ↔ IsGreatest G.poolingPayoffs w := by
  constructor <;> intro h' <;> (have := h' ; simp_all +decide [ IsGreatest, mem_upperBounds ] ;);
  · obtain ⟨ K, rfl ⟩ := h'.1;
    -- By `pooling_dominance`, there exists `m ∈ G.𝓜` such that `G.canSend m = K.C` and `K.w ≤ G.vbar (G.condPrior K.C)`.
    obtain ⟨m, hm_mem, hm_eq⟩ : ∃ m ∈ G.𝓜, G.canSend m = K.C ∧ K.w ≤ G.vbar (G.condPrior K.C) := by
      have := pooling_dominance hQC hMC K; aesop;
    refine' ⟨ _, _ ⟩;
    · exact ⟨ m, hm_mem, by simpa [ hm_eq.1 ] using le_antisymm ( h'.2 _ ( vbar_pooling_mem G hm_mem ) ) ( by simpa [ hm_eq.1 ] using hm_eq.2 ) ⟩;
    · rintro _ ⟨ m', hm'_mem, rfl ⟩ ; exact h'.2 _ ( vbar_pooling_mem G hm'_mem ) ;
  · rcases h' with ⟨ ⟨ m, hm ⟩, h ⟩;
    refine' ⟨ _, _ ⟩;
    · exact hm.2 ▸ vbar_pooling_mem G hm.1;
    · intro x hx
      obtain ⟨ K, hKw ⟩ := hx
      have := pooling_dominance hQC hMC K
      obtain ⟨ m', hm', hcs ⟩ := this.left
      have := h (G.vbar (G.condPrior (G.canSend m'))) (by
      exact Set.mem_image_of_mem _ hm');
      grind

/-
**Lemma 3** (pooling, last claim). Under QC and M-C, every coalition
attaining `max 𝒲_Θ` has `v̄(μ⁰_C) = max 𝒲_Θ`.
-/
theorem coalition_attains_max (hQC : G.QC) (hMC : G.MC) (K : Coalition G)
    (hK : IsGreatest G.coalitionPayoffs K.w) :
    G.vbar (G.condPrior K.C) = K.w := by
  -- From `pooling_dominance hQC hMC K` obtain `⟨⟨m, hm, hcs⟩, hle⟩` where `hm : m ∈ G.𝓜`, `hcs : G.canSend m = K.C`, and `hle : K.w ≤ G.vbar (G.condPrior K.C)`.
  obtain ⟨⟨m, hm, hcs⟩, hle⟩ := (pooling_dominance hQC hMC K);
  exact le_antisymm ( hK.2 ( by convert vbar_pooling_mem G hm using 1; aesop ) ) hle

/-! ## Lemma D.1 (merging) -/

/-
**Lemma D.1** (merging, Appendix D). Under QC and M-C, from a coalition of
`G|_R` attaining `max 𝒲_R` and a strictly higher-paying coalition on `R ∖ C`,
one builds a strictly larger coalition of `G|_R` with the same payoff and
equal pooling value; under QC* or genericity this is impossible (so removing
a cell attaining `max 𝒲_R` cannot raise the residual maximum).
-/
lemma merging (hQC : G.QC) (hMC : G.MC)
    {Θt : Finset T} (hΘne : Θt.Nonempty) (hΘsub : Θt ⊆ G.Θ)
    (K : Coalition (G.restrict Θt hΘne hΘsub))
    (hw : IsGreatest (G.restrict Θt hΘne hΘsub).coalitionPayoffs K.w)
    (hΘt'ne : (Θt \ K.C).Nonempty)
    {w' : ℝ}
    (hw' : IsGreatest
        (G.restrict (Θt \ K.C) hΘt'ne (Finset.sdiff_subset.trans hΘsub)).coalitionPayoffs w')
    (hlt : K.w < w') :
    ∃ Kt : Coalition (G.restrict Θt hΘne hΘsub),
      K.C ⊂ Kt.C ∧ Kt.w = K.w ∧
      G.vbar (G.condPrior K.C) = K.w ∧ G.vbar (G.condPrior Kt.C) = K.w := by
  revert K hw w' hw' hlt;
  intro K hK hΘt'ne w' hw' hlt;
  have hKt : G.vbar (G.condPrior K.C) = K.w := by
    convert coalition_attains_max _ _ K hK using 1;
    · rw [ restrict_condPrior hΘne hΘsub K.C_nonempty K.C_subset ];
      rfl;
    · exact restrict_QC hΘne hΘsub hQC;
    · exact restrict_MC hΘne hΘsub hMC;
  obtain ⟨K', hK'⟩ : ∃ K' : Coalition (G.restrict (Θt \ K.C) hΘt'ne (Finset.sdiff_subset.trans hΘsub)), K'.C.Nonempty ∧ K'.w = w' ∧ G.vbar (G.condPrior K'.C) = w' := by
    obtain ⟨K', hK'⟩ : ∃ K' : Coalition (G.restrict (Θt \ K.C) hΘt'ne (Finset.sdiff_subset.trans hΘsub)), K'.w = w' := by
      exact hw'.1;
    have := coalition_attains_max ( restrict_QC hΘt'ne ( Finset.sdiff_subset.trans hΘsub ) hQC ) ( restrict_MC hΘt'ne ( Finset.sdiff_subset.trans hΘsub ) hMC ) K' ( by aesop );
    use K';
    rw [ ← hK', ← this, restrict_condPrior ];
    · exact ⟨ K'.C_nonempty, rfl, rfl ⟩;
    · exact K'.C_nonempty;
    · exact K'.C_subset;
  obtain ⟨m_C, hm_C⟩ : ∃ m_C ∈ (G.restrict Θt hΘne hΘsub).𝓜, (G.restrict Θt hΘne hΘsub).canSend m_C = K.C := by
    have := pooling_dominance ( restrict_QC hΘne hΘsub hQC ) ( restrict_MC hΘne hΘsub hMC ) K;
    exact this.1
  obtain ⟨m_D, hm_D⟩ : ∃ m_D ∈ (G.restrict (Θt \ K.C) hΘt'ne (Finset.sdiff_subset.trans hΘsub)).𝓜, (G.restrict (Θt \ K.C) hΘt'ne (Finset.sdiff_subset.trans hΘsub)).canSend m_D = K'.C := by
    have := pooling_dominance ( restrict_QC hΘt'ne ( Finset.sdiff_subset.trans hΘsub ) hQC ) ( restrict_MC hΘt'ne ( Finset.sdiff_subset.trans hΘsub ) hMC ) K';
    exact this.1
  obtain ⟨m'', hm''⟩ : ∃ m'' ∈ (G.restrict Θt hΘne hΘsub).𝓜, (G.restrict Θt hΘne hΘsub).canSend m'' = K.C ∪ K'.C := by
    have hMC_restrict : (G.restrict Θt hΘne hΘsub).MC := by
      exact restrict_MC hΘne hΘsub hMC;
    have := hMC_restrict m_C hm_C.1 m_D ?_;
    · simp_all +decide [ DisclosureGame.canSend ];
      simp_all +decide [ DisclosureGame.preimageFull ];
      simp_all +decide [ preimage ];
      grind;
    · exact Finset.mem_biUnion.mpr ( by obtain ⟨ θ, hθ ⟩ := Finset.mem_biUnion.mp hm_D.1; exact ⟨ θ, Finset.mem_sdiff.mp hθ.1 |>.1, hθ.2 ⟩ );
  have hCD_eq : G.vbar (G.condPrior (K.C ∪ K'.C)) = K.w := by
    refine' le_antisymm _ _;
    · have hCD_eq : G.vbar (G.condPrior (K.C ∪ K'.C)) ∈ (G.restrict Θt hΘne hΘsub).coalitionPayoffs := by
        convert vbar_pooling_mem ( G.restrict Θt hΘne hΘsub ) hm''.1 using 1;
        rw [ hm''.2, restrict_condPrior hΘne hΘsub ];
        · rfl;
        · exact ⟨ _, Finset.mem_union_left _ ( K.C_nonempty.choose_spec ) ⟩;
        · exact Finset.union_subset ( K.C_subset ) ( K'.C_subset.trans ( Finset.sdiff_subset ) );
      exact hK.2 hCD_eq;
    · obtain ⟨l, hl⟩ : ∃ l ∈ Set.Ioo (0 : ℝ) 1, G.condPrior (K.C ∪ K'.C) = fun θ => l * G.condPrior K.C θ + (1 - l) * G.condPrior K'.C θ := by
        apply condPrior_union_convexCombo K.C_nonempty hK'.left (by
        exact Finset.Subset.trans K.C_subset hΘsub) (by
        exact Finset.Subset.trans K'.C_subset ( Finset.sdiff_subset.trans hΘsub )) (by
        exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( K'.C_subset hx' ) |>.2 hx);
      have := hQC ( G.condPrior K.C ) ?_ ( G.condPrior K'.C ) ?_ l hl.1;
      · grind;
      · exact G.condPrior_mem_simplex K.C_nonempty ( Finset.Subset.trans K.C_subset hΘsub ) |> fun h => simplexOn_mono ( Finset.Subset.trans K.C_subset hΘsub ) h;
      · exact G.condPrior_mem_simplex hK'.1 ( Finset.Subset.trans K'.C_subset ( Finset.sdiff_subset.trans hΘsub ) ) |> fun h => simplexOn_mono ( Finset.Subset.trans K'.C_subset ( Finset.sdiff_subset.trans hΘsub ) ) h;
  obtain ⟨Kt, hKt⟩ : ∃ Kt : Coalition (G.restrict Θt hΘne hΘsub), Kt.C = (G.restrict Θt hΘne hΘsub).canSend m'' ∧ Kt.w = (G.restrict Θt hΘne hΘsub).vbar ((G.restrict Θt hΘne hΘsub).condPrior ((G.restrict Θt hΘne hΘsub).canSend m'')) := by
    apply pooling_coalition;
    exact hm''.1;
  refine' ⟨ Kt, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
  · exact Exists.elim hK'.1 fun x hx => ⟨ x, Or.inr hx, by have := K'.C_subset hx; aesop ⟩;
  · convert hCD_eq using 1;
    rw [ DisclosureGame.restrict_condPrior ];
    · rfl;
    · exact ⟨ _, Finset.mem_union_left _ ( K.C_nonempty.choose_spec ) ⟩;
    · exact Finset.union_subset ( K.C_subset ) ( K'.C_subset.trans ( Finset.sdiff_subset ) )

end DisclosureGame

end CPD
