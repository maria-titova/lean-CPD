import CPD.BetweennessCore

/-!
# Evidence games and truth-leaning equilibrium (Hart–Kremer–Perry) (§8.1)

Formalizes the comparison with Hart–Kremer–Perry (2017): **Definition 27**
(evidence game: a disclosure game whose message mapping has *evidence
structure* — messages are identified with types, `𝓜 = Θ`, every type can send
its own message (reflexivity), and the message mapping is transitive) →
`EvidenceStructure`; **Definition 28** (truth-leaning equilibrium: a PBE
satisfying (A0) — a type sends its own message with probability one whenever
that message is optimal — and (P0) — off-path beliefs are point masses on the
sender) → `TruthLeaningSupports`; the HKP truth-telling dichotomy lemma →
`hkp_dichotomy`; **Proposition 10** (every truth-leaning equilibrium strategy is
a coalition-proof PBE strategy, so the receiver-optimal commitment outcome of
Hart–Kremer–Perry is a coalition-proof PBE outcome) → `hkp_cppbe`.

HKP's own results (their equivalence theorem) are taken as external inputs;
only the dichotomy is re-proved here, so the module is self-contained given
the definitions.

Standing hypotheses: `V` single-valued and `v̄` satisfying betweenness (B).
Messages are identified with types (`Msg = T`); `δ_m` is `G.condPrior {m}` and
the equilibrium payoff is `u θ = max_{m ∈ M θ} r m`.
-/

open Set Topology
open scoped Classical

namespace CPD

variable {T : Type*} [Fintype T]

namespace DisclosureGame

variable {G : DisclosureGame T T}

variable (G) in
/-- **Definition 27** (evidence game). The message mapping has *evidence
structure*: messages are the types, every type can send its own message (L1,
reflexivity), and accessibility is transitive (L2). An *evidence game*
additionally has `V` single-valued and `v̄` satisfying B (carried as
hypotheses below). -/
def EvidenceStructure : Prop :=
  G.𝓜 = G.Θ ∧
  (∀ θ ∈ G.Θ, θ ∈ G.M θ) ∧
  (∀ θ ∈ G.Θ, ∀ θ' ∈ G.M θ, ∀ θ'' ∈ G.M θ', θ'' ∈ G.M θ)

/-- **Definition 28** (truth-leaning equilibrium). A PBE `(σ, μ, r)` (the
house `Supports` triple) is *truth-leaning* if (A0) whenever type `θ`'s own
message is optimal it is sent with probability one, and (P0) off-path beliefs
are the point masses `δ_m`. -/
structure TruthLeaningSupports (s : Strategy G) (μ : T → T → ℝ) (r : T → ℝ) :
    Prop extends Supports s μ r where
  /-- (A0): if `r(θ) = u(θ)` then `σ(θ|θ) = 1` (`eqPayoff` is
  `max_{m ∈ M θ} r m`, PBEChar.lean). -/
  a0 : ∀ θ ∈ G.Θ, r θ = G.eqPayoff r θ → s.σ θ θ = 1
  /-- (P0): off-path beliefs are `δ_m`. -/
  p0 : ∀ m ∈ G.𝓜, m ∉ s.evidence → μ m = G.condPrior {m}

/-! ## Finite betweenness (upper half), fresh copies of the private core lemmas -/

/-- Sub-level sets of `v̄` are convex under betweenness (upper half of B). -/
private lemma evg_sublevel_convex (hB : G.Betweenness) (c : ℝ) :
    Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} := by
  intro μ hμ ν hν a b ha hb hab
  by_cases ha0 : a = 0
  · simp_all +decide [ show b = 1 by linarith ]
  · by_cases hb0 : b = 0
    · simp_all +decide [ show a = 1 by linarith ]
    · have := hB μ hμ.1 ν hν.1 ( a ) ⟨ lt_of_le_of_ne ha ( Ne.symm ha0 ), by linarith [ show 0 < b by positivity ] ⟩
      simp_all +decide [ ← eq_sub_iff_add_eq' ]
      exact ⟨ ⟨ fun x => add_nonneg ( mul_nonneg ha ( hμ.1.1 x ) ) ( mul_nonneg ( sub_nonneg.2 hb ) ( hν.1.1 x ) ), by simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, hμ.1.2.1, hν.1.2.1 ] ⟩, by cases this.2 <;> linarith! ⟩

/-- Finite betweenness (upper): `v̄` of a convex combination is bounded above by
the max of the values. -/
private lemma evg_convexCombo_le (hB : G.Betweenness) {E : Finset T}
    (x : T → (T → ℝ)) (a : T → ℝ)
    (hx : ∀ m ∈ E, x m ∈ simplexOn G.Θ)
    (ha : ∀ m ∈ E, 0 ≤ a m) (hsum : ∑ m ∈ E, a m = 1)
    {c : ℝ} (hc : ∀ m ∈ E, G.vbar (x m) ≤ c) :
    G.vbar (fun θ => ∑ m ∈ E, a m * x m θ) ≤ c := by
  have h_convex : Convex ℝ {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ G.vbar μ ≤ c} :=
    evg_sublevel_convex hB c
  convert h_convex.sum_mem ( fun m _ => ha m ‹_› ) hsum ( fun m _ => ⟨ hx m ‹_›, hc m ‹_› ⟩ ) |> fun h => h.2 using 1 ; simp +decide [ Finset.sum_mul _ _ _, mul_comm, Finset.mul_sum ] ; ring
  exact congr_arg _ ( funext fun θ => by simp +decide [ mul_comm, Finset.mul_sum _ _ _ ] )

/-! ## The truth-telling dichotomy: components -/

/-
**Dichotomy, part (1).** If message `θ` is used (`θ ∈ X(σ)`), then
`r θ = u θ` and `σ(θ|θ) = 1`.
-/
private lemma dich_used (hev : G.EvidenceStructure)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) {θ : T} (hθ : θ ∈ G.Θ)
    (hused : (θ : T) ∈ s.evidence) :
    r θ = G.eqPayoff r θ ∧ s.σ θ θ = 1 := by
  obtain ⟨θ', hθ', hθ'_mem⟩ : ∃ θ' ∈ G.Θ, θ ∈ s.msgSupport θ' := by
    unfold Strategy.evidence at hused; aesop;
  have hθ'_mem_M : θ ∈ G.M θ' := by
    contrapose! hθ'_mem;
    simp +decide [ Strategy.msgSupport, hθ'_mem ];
    exact le_of_eq ( s.mem θ' hθ' |>.2.2 θ hθ'_mem );
  have hα_le_rθ : G.eqPayoff r θ ≤ r θ := by
    rw [ DisclosureGame.eqPayoff_eq_of_support h.toSupports hθ' ( show 0 < s.σ θ' θ from by
                                                                    exact lt_of_le_of_ne ( by have := s.mem θ' hθ'; exact this.1 θ ) ( Ne.symm <| by have := hθ'_mem; exact fun h => by simp_all +decide [ Strategy.msgSupport, simplexSupport ] ) ) ];
    have h_eqPayoff : G.M θ ⊆ G.M θ' := by
      intro m hm; exact hev.2.2 θ' hθ' θ hθ'_mem_M m hm;
    unfold DisclosureGame.eqPayoff;
    split_ifs <;> simp_all +decide [ Finset.sup'_le_iff ];
    · have := Finset.exists_max_image ( G.M θ ) r ‹_›;
      exact ⟨ this.choose, h_eqPayoff this.choose_spec.1, this.choose_spec.2 ⟩;
    · exact absurd ‹G.M θ = ∅› ( Finset.Nonempty.ne_empty ( G.M_nonempty θ hθ ) );
  have hα_ge_rθ : r θ ≤ G.eqPayoff r θ := by
    apply DisclosureGame.le_eqPayoff;
    · exact hθ;
    · exact hev.2.1 θ hθ;
  exact ⟨ le_antisymm hα_ge_rθ hα_le_rθ, h.a0 θ hθ ( le_antisymm hα_ge_rθ hα_le_rθ ) ⟩

/-
The Bayesian value at a used message equals its payoff: `v̄(μ_σ(·|θ)) = r θ`.
-/
private lemma dich_belief_value (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) {θ : T} (hθ : θ ∈ G.Θ)
    (hused : (θ : T) ∈ s.evidence) :
    G.vbar (s.belief θ) = r θ := by
  have h_bayesian : μ θ = s.belief θ := by
    convert h.bayesian θ _;
    exact hused;
  have hr : r θ ∈ G.V (μ θ) := by
    exact h.payoff_compat θ ( hev.1 ▸ hθ );
  rw [ ← h_bayesian, hSV _ ( h.belief_system _ ( hev.1 ▸ hθ ) ) ] at * ; aesop

/-
**Dichotomy, case (ii).** If message `θ` is not used, then `θ` is in case
(ii): `v(δ_θ) < u θ`, `r θ = v(δ_θ)`, and `σ(θ|θ) = 0`.
-/
private lemma dich_notUsed (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) {θ : T} (hθ : θ ∈ G.Θ)
    (hnu : (θ : T) ∉ s.evidence) :
    G.vbar (G.condPrior {θ}) < G.eqPayoff r θ ∧
      r θ = G.vbar (G.condPrior {θ}) ∧ s.σ θ θ = 0 := by
  refine' ⟨ _, _, _ ⟩;
  · refine' lt_of_le_of_ne _ _;
    · have h_le : r θ ≤ G.eqPayoff r θ := by
        apply G.le_eqPayoff hθ;
        exact hev.2.1 θ hθ;
      convert h_le using 1;
      convert h.payoff_compat θ ( hev.1 ▸ hθ ) using 1;
      rw [ h.p0 θ ( hev.1 ▸ hθ ) hnu, hSV _ _ ];
      · grind;
      · exact simplexOn_mono ( Finset.singleton_subset_iff.mpr hθ ) ( condPrior_mem_simplex ( Finset.singleton_nonempty θ ) ( Finset.singleton_subset_iff.mpr hθ ) );
    · intro h_eq;
      have := h.a0 θ hθ ( by
        have := h.payoff_compat θ ( hev.1 ▸ hθ );
        have := h.p0 θ ( hev.1 ▸ hθ ) hnu;
        have := hSV ( G.condPrior { θ } ) ( condPrior_mem_simplex ( Finset.singleton_nonempty θ ) ( Finset.singleton_subset_iff.mpr hθ ) |> fun h => simplexOn_mono ( Finset.singleton_subset_iff.mpr hθ ) h ) ; aesop; );
      exact hnu ( by rw [ show s.evidence = ⋃ θ ∈ G.Θ, s.msgSupport θ from by rfl ] ; exact Set.mem_iUnion₂.mpr ⟨ θ, hθ, by rw [ show s.msgSupport θ = simplexSupport ( s.σ θ ) from rfl ] ; exact by rw [ show simplexSupport ( s.σ θ ) = { m | 0 < s.σ θ m } from rfl ] ; exact by simp +decide [ this ] ⟩ );
  · have h_r_eq : r θ ∈ G.V (μ θ) := by
      exact h.payoff_compat θ ( hev.1 ▸ hθ );
    have h_r_eq : μ θ = G.condPrior {θ} := by
      exact h.p0 θ ( hev.1 ▸ hθ ) hnu;
    have := hSV ( G.condPrior { θ } ) ( DisclosureGame.condPrior_mem_simplex ⟨ θ, Finset.mem_singleton_self θ ⟩ ( Finset.singleton_subset_iff.mpr hθ ) |> fun h => simplexOn_mono ( Finset.singleton_subset_iff.mpr hθ ) h ) ; aesop;
  · contrapose! hnu;
    simp +decide [ Strategy.evidence, Strategy.msgSupport, hnu ];
    exact ⟨ θ, hθ, lt_of_le_of_ne ( s.mem θ hθ |>.1 θ ) ( Ne.symm hnu ) ⟩

/-
Point mass form of a singleton conditional prior: `δ_ψ ζ = 1` iff `ζ = ψ`
(for `ψ ∈ Θ`).
-/
private lemma evg_condPrior_singleton (ζ : T) {ψ : T} (hψ : ψ ∈ G.Θ) :
    G.condPrior {ψ} ζ = if ζ = ψ then 1 else 0 := by
  unfold DisclosureGame.condPrior;
  split_ifs <;> simp_all +decide [ Finset.sum_singleton, DisclosureGame.priorMeasure ];
  exact ne_of_gt ( G.μ0_fullSupport ψ hψ )

/-
The Bayesian belief at a used message `θ` is the convex combination of the
point masses `δ_ψ` over the senders `E := {ψ ∈ Θ | σ(θ|ψ) > 0}`, weighted by the
belief itself.
-/
private lemma evg_belief_eq_combo {s : Strategy G} {m : T} (hm : (m : T) ∈ s.evidence) :
    s.belief m =
      fun ζ => ∑ ψ ∈ G.Θ.filter (fun ψ => 0 < s.σ ψ m),
        s.belief m ψ * G.condPrior {ψ} ζ := by
  funext ζ;
  by_cases hζ : ζ ∈ G.Θ <;> simp_all +decide [ Strategy.belief ];
  · rw [ Finset.sum_eq_single ζ ] <;> simp_all +decide [ evg_condPrior_singleton ];
    · lia;
    · exact fun h => Or.inl <| Or.inr <| le_antisymm h <| s.mem ζ hζ |>.1 m;
  · rw [ G.μ0_mem.2.2 ζ hζ ] ; simp +decide [ Finset.sum_ite ];
    rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ G.μ0_mem.2.2 ];
    exact Or.inr ( by rw [ evg_condPrior_singleton _ ( by tauto ) ] ; aesop )

/-
The belief weights over the senders `E := {ψ ∈ Θ | σ(θ|ψ) > 0}` sum to one.
-/
private lemma evg_belief_sum_one {s : Strategy G} {m : T} (hm : (m : T) ∈ s.evidence) :
    ∑ ψ ∈ G.Θ.filter (fun ψ => 0 < s.σ ψ m), s.belief m ψ = 1 := by
  have h_sum : ∑ ψ ∈ G.Θ, s.belief m ψ = 1 := by
    obtain ⟨ _, hsum ⟩ := s.belief_mem_simplex hm;
    rw [ ← hsum.1, Finset.sum_subset ( Finset.subset_univ _ ) ] ; aesop;
  rw [ ← h_sum, Finset.sum_filter_of_ne ];
  intro x hx h; contrapose! h; simp_all +decide [ Strategy.belief ] ;
  exact Or.inl <| Or.inr <| le_antisymm h <| s.mem x hx |>.1 m

/-
A sender `ψ ≠ θ` of a used message `θ` is a pooled (case (ii)) type, so
`v(δ_ψ) < u θ`.
-/
private lemma evg_other_sender_lt (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) {θ : T} (hθ : θ ∈ G.Θ)
    (hused : (θ : T) ∈ s.evidence) {ψ : T} (hψ : ψ ∈ G.Θ) (hψθ : ψ ≠ θ)
    (hpos : 0 < s.σ ψ θ) :
    G.vbar (G.condPrior {ψ}) < G.eqPayoff r θ := by
  obtain ⟨hψ_not_used, hψ_eq⟩ := dich_notUsed hev hSV h hψ (by
  intro hψ_in_evidence
  have hσψψ : s.σ ψ ψ = 1 := by
    exact ( dich_used hev h hψ hψ_in_evidence ).2;
  have := s.mem ψ hψ;
  obtain ⟨ h₁, h₂ ⟩ := this;
  rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ ψ ) ] at h₂;
  linarith [ h₁ θ, Finset.single_le_sum ( fun x _ => h₁ x ) ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ θ, by aesop ⟩ : θ ∈ Finset.univ \ { ψ } ) ]);
  obtain ⟨hψ_eq, hψ_eq'⟩ := dich_used hev h hθ hused;
  have := DisclosureGame.eqPayoff_eq_of_support h.toSupports hψ hpos; aesop;

/-
**Dichotomy, case (i) inequality.** If message `θ` is used, then
`u θ ≤ v(δ_θ)`.
-/
private lemma dich_used_ineq (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    (hB : G.Betweenness)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) {θ : T} (hθ : θ ∈ G.Θ)
    (hused : (θ : T) ∈ s.evidence) :
    G.eqPayoff r θ ≤ G.vbar (G.condPrior {θ}) := by
  contrapose! h;
  intro hTL
  obtain ⟨hrθ, hσ⟩ := dich_used hev hTL hθ hused;
  -- By `evg_other_sender_lt`, for every `ψ ∈ E`, `G.vbar (G.condPrior {ψ}) < G.eqPayoff r θ`.
  have hbound : ∀ ψ ∈ G.Θ.filter (fun ψ => 0 < s.σ ψ θ), G.vbar (G.condPrior {ψ}) < G.eqPayoff r θ := by
    intro ψ hψ
    by_cases hψθ : ψ = θ;
    · aesop;
    · exact evg_other_sender_lt hev hSV hTL hθ hused ( Finset.mem_filter.mp hψ |>.1 ) hψθ ( Finset.mem_filter.mp hψ |>.2 );
  -- Let `c := E.sup' hEne (fun ψ => G.vbar (G.condPrior {ψ}))`. Then `hc_lt : c < G.eqPayoff r θ`.
  set E := G.Θ.filter (fun ψ => 0 < s.σ ψ θ)
  have hEne : E.Nonempty := by
    exact ⟨ θ, Finset.mem_filter.mpr ⟨ hθ, by linarith ⟩ ⟩
  set c := E.sup' hEne (fun ψ => G.vbar (G.condPrior {ψ}))
  have hc_lt : c < G.eqPayoff r θ := by
    obtain ⟨ ψ, hψ ⟩ := Finset.exists_max_image E ( fun ψ => G.vbar ( G.condPrior { ψ } ) ) hEne ; aesop;
  -- Apply `evg_convexCombo_le` with `x := fun ψ => G.condPrior {ψ}`, `a := fun ψ => s.belief θ ψ`, and `E := E`.
  have hcombo : G.vbar (fun ζ => ∑ ψ ∈ E, s.belief θ ψ * G.condPrior {ψ} ζ) ≤ c := by
    apply evg_convexCombo_le hB;
    · exact fun ψ hψ => condPrior_mem_simplex ( Finset.singleton_nonempty ψ ) ( Finset.singleton_subset_iff.mpr ( Finset.mem_filter.mp hψ |>.1 ) ) |> fun h => simplexOn_mono ( Finset.singleton_subset_iff.mpr ( Finset.mem_filter.mp hψ |>.1 ) ) h;
    · exact fun m hm => ( s.belief_mem_simplex hused ).1 m;
    · exact evg_belief_sum_one hused;
    · exact fun ψ hψ => Finset.le_sup' ( fun ψ => G.vbar ( G.condPrior { ψ } ) ) hψ;
  rw [ ← evg_belief_eq_combo hused ] at hcombo;
  linarith [ dich_belief_value hev hSV hTL hθ hused ]

/-- **HKP truth-telling dichotomy** (Hart–Kremer–Perry). In a truth-leaning
equilibrium of an evidence game, every type `θ` falls in exactly one of:
(i) `v(δ_θ) ≥ u(θ)`, message `θ` is on path, and `σ(θ|θ) = 1`;
(ii) `u(θ) > v(δ_θ)`, `r(θ) = v(δ_θ)`, and `σ(θ|θ) = 0`.
(The two cases exclude each other through the opposite inequalities.) -/
lemma hkp_dichotomy (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    (hB : G.Betweenness) {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) {θ : T} (hθ : θ ∈ G.Θ) :
    (G.eqPayoff r θ ≤ G.vbar (G.condPrior {θ}) ∧
      (θ : T) ∈ s.evidence ∧ s.σ θ θ = 1) ∨
    (G.vbar (G.condPrior {θ}) < G.eqPayoff r θ ∧
      r θ = G.vbar (G.condPrior {θ}) ∧ s.σ θ θ = 0) := by
  by_cases hused : (θ : T) ∈ s.evidence
  · exact Or.inl ⟨dich_used_ineq hev hSV hB h hθ hused, hused,
      (dich_used hev h hθ hused).2⟩
  · exact Or.inr (dich_notUsed hev hSV h hθ hused)

/-- **Sequential rationality closure.** If `R` is down-closed under equilibrium
payoff `u = eqPayoff r`, then every equilibrium sender of any message available
to an `R`-type is again in `R`. -/
private lemma evg_senders_subset (hev : G.EvidenceStructure)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) (hnorm : ∀ θ ∉ G.Θ, s.σ θ = 0)
    {R : Finset T} (hRsub : R ⊆ G.Θ)
    (hdown : ∀ θ ∈ R, ∀ ψ ∈ G.Θ, G.eqPayoff r ψ ≤ G.eqPayoff r θ → ψ ∈ R)
    {θ : T} (hθ : θ ∈ R) {m : T} (hm : m ∈ G.M θ) {ψ : T} (hψpos : 0 < s.σ ψ m) :
    ψ ∈ R := by
  -- `ψ ∈ G.Θ`: else `hnorm` makes `s.σ ψ = 0`, contradicting `0 < s.σ ψ m`.
  have hψΘ : ψ ∈ G.Θ := by
    by_contra hψ
    have := congrFun (hnorm ψ hψ) m
    simp_all
  -- `r m = G.eqPayoff r ψ` (ψ sends m) and `r m ≤ G.eqPayoff r θ` (m ∈ M θ).
  have h1 : r m = G.eqPayoff r ψ := DisclosureGame.eqPayoff_eq_of_support h.toSupports hψΘ hψpos
  have h2 : r m ≤ G.eqPayoff r θ := DisclosureGame.le_eqPayoff (hRsub hθ) hm
  exact hdown θ hθ ψ hψΘ (by rw [← h1]; exact h2)

/-
**Transitivity closure.** If the *message-as-type* `m` lies in the pooling
preimage `D = M⁻¹_R(X)`, then every equilibrium sender of message `m` also lies
in `D`.  (Uses transitivity `L2`: a sender `ψ` of `m` has `M m ⊆ M ψ`, so `ψ`
inherits an `X`-message from `m`; and `evg_senders_subset` places `ψ` in `R`.)
-/
private lemma evg_msg_senders_in_D (hev : G.EvidenceStructure)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) (hnorm : ∀ θ ∉ G.Θ, s.σ θ = 0)
    {R : Finset T} (hRsub : R ⊆ G.Θ)
    (hdown : ∀ θ ∈ R, ∀ ψ ∈ G.Θ, G.eqPayoff r ψ ≤ G.eqPayoff r θ → ψ ∈ R)
    {X : Finset T} {m : T} (hmD : m ∈ preimage G.M R X) {ψ : T} (hψpos : 0 < s.σ ψ m) :
    ψ ∈ preimage G.M R X := by
  obtain ⟨hmR, hmX⟩ : m ∈ R ∧ (G.M m ∩ X).Nonempty := mem_preimage.mp hmD
  -- By evg_senders_subset, since ψ is an equilibrium sender of m and m ∈ R, we have ψ ∈ R.
  have hψR : ψ ∈ R := by
    apply evg_senders_subset hev h hnorm hRsub hdown hmR;
    exact hev.2.1 m ( hRsub hmR );
    exact hψpos;
  have hψM : m ∈ G.M ψ := by
    exact not_not.mp fun h => hψpos.ne' <| s.mem ψ ( hRsub hψR ) |>.2.2 m h;
  have hψX : (G.M ψ ∩ X).Nonempty := by
    exact hmX.imp fun x hx => by have := hev.2.2 ψ ( hRsub hψR ) m hψM x ( Finset.mem_of_mem_inter_left hx ) ; aesop;
  exact Finset.mem_filter.mpr ⟨ hψR, hψX ⟩

/-! ### Bayesian decomposition of a pooled prior over equilibrium messages -/

/-- Mass of `D`-types sending message `m` in equilibrium. -/
private noncomputable def poolW (s : Strategy G) (D : Finset T) (m : T) : ℝ :=
  ∑ θ ∈ D, G.μ0 θ * s.σ θ m

/-- The `D`-restricted Bayesian belief at message `m`. -/
private noncomputable def poolBel (s : Strategy G) (D : Finset T) (m : T) : T → ℝ :=
  fun ζ => (if ζ ∈ D then G.μ0 ζ * s.σ ζ m else 0) / poolW s D m

/-
`∑_m poolW = μ⁰(D)`.
-/
private lemma evg_poolW_sum {s : Strategy G} {D : Finset T} (hD : D ⊆ G.Θ) :
    ∑ m, poolW s D m = G.priorMeasure D := by
  have h_sum_comm : ∑ m ∈ Finset.univ, ∑ θ ∈ D, G.μ0 θ * s.σ θ m = ∑ θ ∈ D, ∑ m ∈ Finset.univ, G.μ0 θ * s.σ θ m := by
    exact Finset.sum_comm;
  convert h_sum_comm using 1;
  exact Finset.sum_congr rfl fun x hx => by rw [ ← Finset.mul_sum _ _ _, show ∑ m : T, s.σ x m = 1 from s.mem x ( hD hx ) |>.2.1 ] ; ring;

/-
Each `poolBel` (for a message actually used by `D`) is a belief in `ΔΘ`.
-/
private lemma evg_poolBel_simplex {s : Strategy G} {D : Finset T} (hD : D ⊆ G.Θ)
    {m : T} (hm : 0 < poolW s D m) : poolBel s D m ∈ simplexOn G.Θ := by
  refine' ⟨ fun ζ => _, _, _ ⟩;
  · refine' div_nonneg _ hm.le;
    split_ifs <;> [ exact mul_nonneg ( G.μ0_mem.1 _ ) ( s.mem _ ( hD ‹_› ) |>.1 _ ) ; exact le_rfl ];
  · unfold poolBel; simp +decide [ ← Finset.sum_div, hm.ne' ] ;
    exact div_self hm.ne';
  · intro ζ hζ; simp +decide [ poolBel, hζ ] ;
    exact Or.inl fun h => False.elim <| hζ <| hD h

/-
**Bayes decomposition.** `μ⁰_D` is the `poolW`-weighted average of the
`D`-restricted beliefs over the equilibrium messages.
-/
private lemma evg_condPrior_decomp {s : Strategy G} {D : Finset T}
    (hDne : D.Nonempty) (hD : D ⊆ G.Θ) :
    G.condPrior D =
      fun ζ => ∑ m ∈ Finset.univ.filter (fun m => 0 < poolW s D m),
        (poolW s D m / G.priorMeasure D) * poolBel s D m ζ := by
  ext ζ; simp +decide [ poolBel ] ;
  by_cases hζD : ζ ∈ D <;> simp +decide [ hζD, poolW ];
  · have h_sum_zero : ∑ m, (∑ θ ∈ D, G.μ0 θ * s.σ θ m) / G.priorMeasure D * (G.μ0 ζ * s.σ ζ m / ∑ θ ∈ D, G.μ0 θ * s.σ θ m) = G.condPrior D ζ := by
      convert congr_arg ( fun x : ℝ => x / G.priorMeasure D ) ( show ∑ m, G.μ0 ζ * s.σ ζ m = G.μ0 ζ from ?_ ) using 1;
      · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun m hm => _ ; by_cases h : ∑ θ ∈ D, G.μ0 θ * s.σ θ m = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
        rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h;
        · exact Or.inr <| Or.inl <| by simpa [ G.μ0_fullSupport ζ ( hD hζD ) |> ne_of_gt ] using h ζ hζD;
        · exact fun x hx => mul_nonneg ( s.mem x ( hD hx ) |>.1 m ) ( G.μ0_mem.1 x );
      · simp +decide [ condPrior, hζD ];
      · rw [ ← Finset.mul_sum _ _ _, s.mem ζ ( hD hζD ) |>.2.1, mul_one ];
    rw [ ← h_sum_zero, Finset.sum_filter_of_ne ];
    exact fun m _ hm => lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => mul_nonneg ( G.μ0_mem.1 _ ) ( s.mem _ ( hD ‹_› ) |>.1 _ ) ) ( Ne.symm <| by aesop );
  · unfold DisclosureGame.condPrior; aesop;

/-
**Case (m ∈ D): the `D`-restricted belief is the full Bayesian belief.**
Because every equilibrium sender of `m` is in `D` (transitivity closure).
-/
private lemma evg_poolBel_eq_belief (hev : G.EvidenceStructure)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) (hnorm : ∀ θ ∉ G.Θ, s.σ θ = 0)
    {R : Finset T} (hRsub : R ⊆ G.Θ)
    (hdown : ∀ θ ∈ R, ∀ ψ ∈ G.Θ, G.eqPayoff r ψ ≤ G.eqPayoff r θ → ψ ∈ R)
    {X : Finset T} {m : T} (hmD : m ∈ preimage G.M R X) (hm : 0 < poolW s (preimage G.M R X) m) :
    poolBel s (preimage G.M R X) m = s.belief m := by
  have h_pool_eq : ∀ ψ ∉ preimage G.M R X, s.σ ψ m = 0 := by
    intro ψ hψ;
    by_cases hψΘ : ψ ∈ G.Θ;
    · exact le_antisymm ( le_of_not_gt fun hψpos => hψ <| evg_msg_senders_in_D hev h hnorm hRsub hdown hmD hψpos ) ( ( s.mem ψ hψΘ ).1 m );
    · exact congr_fun ( hnorm ψ hψΘ ) m;
  -- By definition of `poolW`, we have `poolW s (preimage G.M R X) m = s.onPathProb m`.
  have h_poolW_eq : poolW s (preimage G.M R X) m = s.onPathProb m := by
    refine' Finset.sum_subset _ _ <;> simp_all +decide [ Finset.subset_iff ];
    exact fun x hx => hRsub ( mem_preimage.mp hx |>.1 );
  ext ζ; by_cases hζ : ζ ∈ preimage G.M R X <;> simp +decide [ *, poolBel, Strategy.belief ] ;

/-- `σ` is everywhere nonnegative (on `Θ` by `s.mem`, off `Θ` by `hnorm`). -/
private lemma evg_sigma_nonneg {s : Strategy G} (hnorm : ∀ θ ∉ G.Θ, s.σ θ = 0)
    (θ m : T) : 0 ≤ s.σ θ m := by
  by_cases hθ : θ ∈ G.Θ
  · exact (s.mem θ hθ).1 m
  · simp [hnorm θ hθ]

/-- A type sending a message other than its own does not send its own message
with probability one. -/
private lemma evg_sigma_ne_one {s : Strategy G} {θ m : T} (hθ : θ ∈ G.Θ)
    (hne : m ≠ θ) (hpos : 0 < s.σ θ m) : s.σ θ θ ≠ 1 := by
  intro hone
  have hnn : ∀ x, 0 ≤ s.σ θ x := (s.mem θ hθ).1
  have hsum : ∑ x, s.σ θ x = 1 := (s.mem θ hθ).2.1
  have : s.σ θ θ + s.σ θ m ≤ ∑ x, s.σ θ x := by
    rw [← Finset.sum_pair (Ne.symm hne)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hnn x)
  rw [hone, hsum] at this
  linarith

/-- If a belief `p ∈ ΔΘ` is supported on a finite set `S` on which every point
mass `δ_θ` has value `≤ U`, then `p` itself has value `≤ U` (upper betweenness). -/
private lemma evg_vbar_le_of_supp (hB : G.Betweenness) {p : T → ℝ}
    (hp : p ∈ simplexOn G.Θ) {S : Finset T} (hSΘ : S ⊆ G.Θ)
    (hsupp : ∀ θ ∉ S, p θ = 0) {U : ℝ}
    (hbound : ∀ θ ∈ S, G.vbar (G.condPrior {θ}) ≤ U) :
    G.vbar p ≤ U := by
  have hcombo : p = fun ζ => ∑ θ ∈ S, p θ * G.condPrior {θ} ζ := by
    funext ζ
    have : (∑ θ ∈ S, p θ * G.condPrior {θ} ζ)
        = ∑ θ ∈ S, p θ * (if ζ = θ then 1 else 0) := by
      refine Finset.sum_congr rfl fun θ hθ => ?_
      rw [evg_condPrior_singleton ζ (hSΘ hθ)]
    rw [this]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq' S ζ p]
    by_cases hζ : ζ ∈ S
    · simp [hζ]
    · simp [hζ, hsupp ζ hζ]
  have hsum : ∑ θ ∈ S, p θ = 1 := by
    rw [← hp.2.1, ← Finset.sum_subset (Finset.subset_univ S) (fun θ _ hθ => hsupp θ hθ)]
  rw [hcombo]
  exact evg_convexCombo_le hB (fun θ => G.condPrior {θ}) p
    (fun θ hθ => simplexOn_mono (Finset.singleton_subset_iff.mpr (hSΘ hθ))
      (condPrior_mem_simplex (Finset.singleton_nonempty θ) (Finset.singleton_subset_iff.mpr (hSΘ hθ))))
    (fun θ _ => hp.1 θ) hsum hbound

/-- **Per-message value bound.** Each `D`-restricted belief has value `≤ U`. -/
private lemma evg_poolBel_le (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) (hnorm : ∀ θ ∉ G.Θ, s.σ θ = 0)
    (hB : G.Betweenness)
    {R : Finset T} (hRsub : R ⊆ G.Θ)
    (hdown : ∀ θ ∈ R, ∀ ψ ∈ G.Θ, G.eqPayoff r ψ ≤ G.eqPayoff r θ → ψ ∈ R)
    {U : ℝ} (hU : ∀ θ ∈ R, G.eqPayoff r θ ≤ U)
    {X : Finset T} {m : T} (hm : 0 < poolW s (preimage G.M R X) m) :
    G.vbar (poolBel s (preimage G.M R X) m) ≤ U := by
  by_cases hmD : m ∈ preimage G.M R X
  · -- `m ∈ D`: the `D`-restricted belief is the full Bayesian belief, value `r m ≤ U`.
    obtain ⟨θ0, hθ0D, hθ0pos⟩ : ∃ θ0 ∈ preimage G.M R X, 0 < s.σ θ0 m := by
      contrapose! hm
      exact Finset.sum_nonpos fun θ hθ =>
        mul_nonpos_of_nonneg_of_nonpos (G.μ0_mem.1 θ) (hm θ hθ)
    have hθ0e : m ∈ s.evidence := by
      rw [Strategy.evidence, Set.mem_iUnion₂]
      exact ⟨θ0, hRsub (mem_preimage.mp hθ0D).1,
        by simp [Strategy.msgSupport, simplexSupport, hθ0pos]⟩
    have hmΘ : m ∈ G.Θ := hRsub (mem_preimage.mp hmD).1
    rw [evg_poolBel_eq_belief hev h hnorm hRsub hdown hmD hm,
        dich_belief_value hev hSV h hmΘ hθ0e]
    have hrm : r m = G.eqPayoff r θ0 :=
      DisclosureGame.eqPayoff_eq_of_support h.toSupports (hRsub (mem_preimage.mp hθ0D).1) hθ0pos
    rw [hrm]; exact hU θ0 (mem_preimage.mp hθ0D).1
  · -- `m ∉ D`: `poolBel` is supported on senders `≠ m`, all pooled (case (ii)).
    have hDsub : preimage G.M R X ⊆ G.Θ := fun θ hθ => hRsub (mem_preimage.mp hθ).1
    set E' := (preimage G.M R X).filter (fun θ => 0 < s.σ θ m) with hE'
    have h_bound : ∀ θ ∈ E', G.vbar (G.condPrior {θ}) ≤ U := by
      intro θ hθ
      have hθD : θ ∈ preimage G.M R X := (Finset.mem_filter.mp hθ).1
      have hθpos : 0 < s.σ θ m := (Finset.mem_filter.mp hθ).2
      have hθR : θ ∈ R := (mem_preimage.mp hθD).1
      have hθm : m ≠ θ := fun heq => hmD (heq ▸ hθD)
      have hθne1 : s.σ θ θ ≠ 1 := evg_sigma_ne_one (hRsub hθR) hθm hθpos
      have hθnu : θ ∉ s.evidence := fun hev' => hθne1 (dich_used hev h (hRsub hθR) hev').2
      exact le_of_lt (lt_of_lt_of_le (dich_notUsed hev hSV h (hRsub hθR) hθnu).1 (hU θ hθR))
    have hsupp : ∀ θ ∉ E', poolBel s (preimage G.M R X) m θ = 0 := by
      intro θ hθ
      simp only [poolBel]
      by_cases hθD : θ ∈ preimage G.M R X
      · have hz : s.σ θ m = 0 := by
          by_contra hpos
          exact hθ (Finset.mem_filter.mpr ⟨hθD,
            lt_of_le_of_ne (evg_sigma_nonneg hnorm θ m) (Ne.symm hpos)⟩)
        simp [hθD, hz]
      · simp [hθD]
    exact evg_vbar_le_of_supp hB (evg_poolBel_simplex hDsub hm)
      (fun θ hθ => hDsub (Finset.mem_filter.mp hθ).1) hsupp h_bound

/-- **Pooling-value bound (the core of Proposition 10).** In a truth-leaning
equilibrium, no pooling coalition over a residual set `R` (down-closed under the
equilibrium payoff) can beat the largest equilibrium payoff `U` available in `R`:
`v*(R) ≤ U`. Here `U` is any common upper bound on `u θ = eqPayoff r θ` over `R`. -/
private lemma evg_vstar_le (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    (hB : G.Betweenness) {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r)
    (hnorm : ∀ θ ∉ G.Θ, s.σ θ = 0)
    {R : Finset T} (hRne : R.Nonempty) (hRsub : R ⊆ G.Θ)
    (hdown : ∀ θ ∈ R, ∀ ψ ∈ G.Θ, G.eqPayoff r ψ ≤ G.eqPayoff r θ → ψ ∈ R)
    {U : ℝ} (hU : ∀ θ ∈ R, G.eqPayoff r θ ≤ U) :
    G.vstar R ≤ U := by
  obtain ⟨X, hXsub, hXne, hX⟩ := (G.vstar_isGreatest hRne hRsub).1
  rw [hX]
  set D := preimage G.M R X with hDdef
  have hDsub : D ⊆ G.Θ := fun θ hθ => hRsub (mem_preimage.mp hθ).1
  have hDne : D.Nonempty := by
    obtain ⟨m0, hm0⟩ := hXne
    have : m0 ∈ G.restrictMsgSpace R := hXsub hm0
    rw [DisclosureGame.restrictMsgSpace, Finset.mem_biUnion] at this
    obtain ⟨θ, hθR, hθm⟩ := this
    exact ⟨θ, mem_preimage.mpr ⟨hθR, ⟨m0, Finset.mem_inter.mpr ⟨hθm, hm0⟩⟩⟩⟩
  have hpm : 0 < G.priorMeasure D := priorMeasure_pos hDne hDsub
  rw [evg_condPrior_decomp hDne hDsub]
  apply evg_convexCombo_le hB (fun m => poolBel s D m)
    (fun m => poolW s D m / G.priorMeasure D)
  · exact fun m hm => evg_poolBel_simplex hDsub (Finset.mem_filter.mp hm).2
  · exact fun m hm => div_nonneg (le_of_lt (Finset.mem_filter.mp hm).2) hpm.le
  · rw [← Finset.sum_div]
    have hWnonneg : ∀ m, (0:ℝ) ≤ poolW s D m := by
      intro m
      exact Finset.sum_nonneg fun θ hθ => mul_nonneg (G.μ0_mem.1 θ) ((s.mem θ (hDsub hθ)).1 m)
    have hsum : ∑ m ∈ Finset.univ.filter (fun m => 0 < poolW s D m), poolW s D m
        = G.priorMeasure D := by
      rw [← evg_poolW_sum (s := s) hDsub]
      apply Finset.sum_filter_of_ne
      intro m _ hne
      exact lt_of_le_of_ne (hWnonneg m) (Ne.symm hne)
    rw [hsum, div_self (ne_of_gt hpm)]
  · exact fun m hm => evg_poolBel_le hev hSV h hnorm hB hRsub hdown hU
      (Finset.mem_filter.mp hm).2

/-
**Proposition 10.** The sender's strategy in every truth-leaning equilibrium
of an evidence game is a coalition-proof PBE strategy. (Consequently, by HKP's
equivalence theorem — an external input — the receiver's optimal-commitment
outcome is a coalition-proof PBE outcome.)

The statement carries the normalization hypothesis `hnorm : ∀ θ ∉ Θ, σ(·|θ) = 0`.
Without it the statement is *false* for the `Strategy` type of this
development, for the same reason documented for `pbe_characterization` in
`PBEChar.lean`: a `Strategy G` carries a total map `σ : T → T → ℝ`, but
`TruthLeaningSupports` (through `Supports`) never constrains `σ(·|θ)` for
`θ ∉ Θ`, whereas `IsCPPBEStrategy s` unfolds to `s = P.toSenderStrategy` and
every `toSenderStrategy` vanishes off `Θ`. A truth-leaning equilibrium that is
nonzero off `Θ` is therefore never associated with any partition. `hnorm` is
the natural normalization hypothesis satisfied by every equilibrium strategy
identified with a partition, and is exactly the one `pbe_characterization`
requires.
-/
theorem hkp_cppbe (hev : G.EvidenceStructure) (hSV : G.SingleValued)
    (hB : G.Betweenness) {s : Strategy G} {μ : T → T → ℝ} {r : T → ℝ}
    (h : G.TruthLeaningSupports s μ r) (hnorm : ∀ θ ∉ G.Θ, s.σ θ = 0) :
    G.IsCPPBEStrategy s := by
  refine' ⟨ DisclosureGame.forwardPartition h.toSupports hnorm, ⟨ _, _ ⟩, DisclosureGame.forwardPartition_associatedWith h.toSupports hnorm ⟩;
  · exact ⟨ DisclosureGame.forwardPartition_IsIR h.toSupports hnorm, DisclosureGame.fwdW_strictAnti.antitone ⟩;
  · constructor ; rintro ⟨ wtil, theta_ne, K, K_w ⟩;
    -- Obtain the least violating index: from `theta_ne : (P.thetaBelow wtil).Nonempty` and `P.thetaBelow wtil = (Finset.univ.filter (fun t => P.w t < wtil)).biUnion P.C`, the filter `Finset.univ.filter (fun t => P.w t < wtil)` is nonempty; let `τ := Finset.min' _ _`. Then `hτlt : P.w τ < wtil` (from `Finset.mem_filter`, `Finset.min'_mem`) and `hτmin : ∀ t, P.w t < wtil → τ ≤ t` (`Finset.min'_le`).
    obtain ⟨τ, hτ⟩ : ∃ τ : Fin (forwardPartition h.toSupports hnorm).card, (forwardPartition h.toSupports hnorm).w τ < wtil ∧ ∀ t : Fin (forwardPartition h.toSupports hnorm).card, (forwardPartition h.toSupports hnorm).w t < wtil → τ ≤ t := by
      obtain ⟨τ, hτ⟩ : ∃ τ : Fin (forwardPartition h.toSupports hnorm).card, (forwardPartition h.toSupports hnorm).w τ < wtil := by
        obtain ⟨ θ, hθ ⟩ := theta_ne;
        simp_all +decide [ Partition.thetaBelow ];
        exact Exists.elim ( Finset.mem_biUnion.mp hθ ) fun τ hτ => ⟨ τ, by aesop ⟩;
      exact ⟨ Finset.min' ( Finset.univ.filter fun t => ( forwardPartition h.toSupports hnorm ).w t < wtil ) ⟨ τ, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hτ ⟩ ⟩, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun t => ( forwardPartition h.toSupports hnorm ).w t < wtil ) ⟨ τ, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hτ ⟩ ⟩ ) |>.2, fun t ht => Finset.min'_le _ _ ( by aesop ) ⟩;
    -- Bound the equilibrium payoffs on the residual set: `hU : ∀ θ ∈ P.thetaBelow wtil, G.eqPayoff r θ ≤ P.w τ`.
    have hU : ∀ θ ∈ (forwardPartition h.toSupports hnorm).thetaBelow wtil, G.eqPayoff r θ ≤ (forwardPartition h.toSupports hnorm).w τ := by
      intro θ hθ
      have hθ_step : θ ∈ thetaStep (forwardPartition h.toSupports hnorm).C τ := by
        convert hθ using 1;
        apply Eq.symm; exact (by
          have := (forwardPartition h.toSupports hnorm).thetaBelow_eq_thetaStep (by
          exact ( DisclosureGame.fwdW_strictAnti ).antitone) hτ.1 hτ.2;
          exact this);
      obtain ⟨ t, ht₁, ht₂ ⟩ := Finset.mem_biUnion.mp hθ_step;
      simp_all +decide [ forwardPartition ];
      simp_all +decide [ DisclosureGame.fwdC ];
      exact G.fwdW_strictAnti.antitone ht₁;
    have hdown : ∀ θ ∈ (forwardPartition h.toSupports hnorm).thetaBelow wtil, ∀ ψ ∈ G.Θ,
        G.eqPayoff r ψ ≤ G.eqPayoff r θ →
        ψ ∈ (forwardPartition h.toSupports hnorm).thetaBelow wtil := by
      intro θ hθ ψ hψ hle
      -- `θ` lies in a cell with payoff `< wtil`, and `eqPayoff r θ` equals that payoff.
      simp only [Partition.thetaBelow, Finset.mem_biUnion, Finset.mem_filter] at hθ ⊢
      obtain ⟨i, ⟨_, hi⟩, hθi⟩ := hθ
      have hθeq : G.eqPayoff r θ = G.fwdW r i := by
        have := Finset.mem_filter.mp (show θ ∈ G.fwdC r i from hθi)
        exact this.2
      -- `ψ`'s cell `j` satisfies `fwdW r j = eqPayoff r ψ ≤ eqPayoff r θ = fwdW r i < wtil`.
      obtain ⟨j, _, hψj⟩ := Finset.mem_biUnion.mp (G.fwdC_cover hψ)
      have hψeq : G.eqPayoff r ψ = G.fwdW r j := (Finset.mem_filter.mp hψj).2
      exact ⟨j, ⟨Finset.mem_univ _, by
        have : G.fwdW r j ≤ G.fwdW r i := by rw [← hψeq, ← hθeq]; exact hle
        exact lt_of_le_of_lt this hi⟩, hψj⟩
    have hvstar := evg_vstar_le hev hSV hB h hnorm theta_ne
      ( DisclosureGame.Partition.thetaBelow_subset _ _ ) hdown hU;
    linarith [ btw_attained_le hSV hB theta_ne ( ( forwardPartition h.toSupports hnorm ).thetaBelow_subset wtil ) K ]

end DisclosureGame

end CPD
