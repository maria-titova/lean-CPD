import CPD.PBE
import CPD.Kakutani

/-!
# Existence of PBE (§4: Perfect Bayesian Equilibrium, Lemma K.4)

**Lemma K.4**: every disclosure game admits a PBE. This is the unique place
in the development where Kakutani's fixed-point theorem (`kakutani`) is
used: it is applied to the best-response correspondence `Φ` on the compact
convex domain `K = Σ × ∏_m 𝓕(m) × ∏_m I`, and a PBE is read off a fixed
point.
-/

open Set
open scoped Classical

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

/-
`simplexOn S` is nonempty whenever `S` is.
-/
lemma exPBE_simplexOn_nonempty {α : Type*} [Fintype α] {S : Finset α}
    (hS : S.Nonempty) : (simplexOn S).Nonempty := by
  refine' ⟨ fun a => if a ∈ S then 1 / S.card else 0, _, _, _ ⟩ <;> simp +decide [ hS.ne_empty ];
  exact fun a => by split_ifs <;> positivity;

/-
`simplexOn S` is convex.
-/
lemma exPBE_convex_simplexOn {α : Type*} [Fintype α] (S : Finset α) :
    Convex ℝ (simplexOn S) := by
  intro μ hμ ν hν a b ha hb hab;
  refine' ⟨ fun x => _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ];
  · nlinarith [ hμ.1 x, hν.1 x ];
  · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hμ.2.1, hν.2.1, hab ]

namespace DisclosureGame

section Existence

variable (G : DisclosureGame T Msg)

/-- Upper bound for receiver payoffs at message `m`: `max_{μ ∈ 𝓕(m)} v̄(μ)`. -/
noncomputable def exPBE_vbarMax (m : Msg) : ℝ := sSup (G.vbar '' G.feasibleBeliefs m)

/-- Lower bound for receiver payoffs at message `m`: `min_{μ ∈ 𝓕(m)} v̲(μ)`. -/
noncomputable def exPBE_vlowMin (m : Msg) : ℝ := sInf (G.vlow '' G.feasibleBeliefs m)

/-- Raw on-path probability of `m` under a raw strategy `σ`. -/
noncomputable def exPBE_onPath (σ : T → Msg → ℝ) (m : Msg) : ℝ :=
  ∑ θ ∈ G.Θ, G.μ0 θ * σ θ m

/-- Raw Bayesian belief at `m` under a raw strategy `σ`. -/
noncomputable def exPBE_belief (σ : T → Msg → ℝ) (m : Msg) : T → ℝ :=
  fun θ => G.μ0 θ * σ θ m / exPBE_onPath G σ m

/-- The best-response set for type `θ` given payoff vector `r`. -/
def exPBE_BR (r : Msg → ℝ) (θ : T) : Set (Msg → ℝ) :=
  {x | x ∈ simplexOn (G.M θ) ∧
        ∀ y ∈ simplexOn (G.M θ), (∑ m, y m * r m) ≤ ∑ m, x m * r m}

/-- The compact convex domain `K = Σ × ∏_m 𝓕(m) × ∏_m I`. -/
def exPBE_K : Set (FixedPointSpace T Msg) :=
  {p | (∀ θ ∈ G.Θ, p.1 θ ∈ simplexOn (G.M θ)) ∧ (∀ θ ∉ G.Θ, p.1 θ = 0)
     ∧ (∀ m ∈ G.𝓜, p.2.1 m ∈ G.feasibleBeliefs m) ∧ (∀ m ∉ G.𝓜, p.2.1 m = 0)
     ∧ (∀ m ∈ G.𝓜, p.2.2 m ∈ Icc (exPBE_vlowMin G m) (exPBE_vbarMax G m))
     ∧ (∀ m ∉ G.𝓜, p.2.2 m = 0)}

/-- The best-response correspondence `Φ`. -/
def exPBE_Phi (p : FixedPointSpace T Msg) : Set (FixedPointSpace T Msg) :=
  {q | (∀ θ ∈ G.Θ, q.1 θ ∈ exPBE_BR G p.2.2 θ) ∧ (∀ θ ∉ G.Θ, q.1 θ = 0)
     ∧ (∀ m ∈ G.𝓜, q.2.1 m ∈ G.feasibleBeliefs m
          ∧ ∀ θ ∈ G.Θ, exPBE_onPath G p.1 m * q.2.1 m θ = G.μ0 θ * p.1 θ m)
     ∧ (∀ m ∉ G.𝓜, q.2.1 m = 0)
     ∧ (∀ m ∈ G.𝓜, q.2.2 m ∈ G.V (p.2.1 m)) ∧ (∀ m ∉ G.𝓜, q.2.2 m = 0)}

/-
The receiver-payoff interval `[v̲ₘ, v̄ₘ]` is nonempty.
-/
lemma exPBE_vlowMin_le_vbarMax {m : Msg} (hm : m ∈ G.𝓜) :
    exPBE_vlowMin G m ≤ exPBE_vbarMax G m := by
  obtain ⟨μ, hμ⟩ : ∃ μ ∈ G.feasibleBeliefs m, G.vlow μ ∈ Set.image G.vlow (G.feasibleBeliefs m) ∧ G.vbar μ ∈ Set.image G.vbar (G.feasibleBeliefs m) := by
    exact Exists.elim ( G.feasibleBeliefs_nonempty hm ) fun μ hμ => ⟨ μ, hμ, Set.mem_image_of_mem _ hμ, Set.mem_image_of_mem _ hμ ⟩;
  refine' le_trans _ ( le_csSup _ hμ.2.2 );
  · refine' le_trans ( csInf_le _ hμ.2.1 ) _;
    · have h_lower_semicontinuous : LowerSemicontinuousOn G.vlow (G.feasibleBeliefs m) := by
        exact G.vlow_lowerSemicontinuousOn.mono ( DisclosureGame.feasibleBeliefs_subset_simplex m );
      grind +suggestions;
    · apply G.vlow_le;
      · exact G.feasibleBeliefs_subset_simplex m hμ.1;
      · exact G.vbar_mem ( G.feasibleBeliefs_subset_simplex m hμ.1 );
  · have h_compact : IsCompact (G.feasibleBeliefs m) := by
      exact ( DisclosureGame.isCompact_convex_feasibleBeliefs hm ).1;
    have h_upper_semicontinuous : UpperSemicontinuousOn G.vbar (G.feasibleBeliefs m) := by
      exact DisclosureGame.vbar_upperSemicontinuousOn.mono ( DisclosureGame.feasibleBeliefs_subset_simplex m );
    exact h_upper_semicontinuous.bddAbove_of_isCompact h_compact

/-
Every value `V(μ)` lies in the receiver-payoff interval, for `μ ∈ 𝓕(m)`.
-/
lemma exPBE_V_subset_box {m : Msg} (hm : m ∈ G.𝓜) {μ : T → ℝ}
    (hμ : μ ∈ G.feasibleBeliefs m) :
    G.V μ ⊆ Icc (exPBE_vlowMin G m) (exPBE_vbarMax G m) := by
  intro x hx
  have hvlow : G.vlow μ ≤ x := by
    exact G.vlow_le ( G.feasibleBeliefs_subset_simplex m hμ ) hx
  have hvbar : x ≤ G.vbar μ := by
    exact (G.le_vbar (DisclosureGame.feasibleBeliefs_subset_simplex m hμ) hx)
  have hvlowMin : G.exPBE_vlowMin m ≤ G.vlow μ := by
    apply_rules [ csInf_le, Set.mem_image_of_mem ];
    have h_compact : IsCompact (G.feasibleBeliefs m) := by
      exact ( DisclosureGame.isCompact_convex_feasibleBeliefs hm ).1;
    have h_lower_semicontinuous : LowerSemicontinuousOn G.vlow (G.feasibleBeliefs m) := by
      exact G.vlow_lowerSemicontinuousOn.mono ( DisclosureGame.feasibleBeliefs_subset_simplex m );
    have := h_lower_semicontinuous.bddBelow_of_isCompact h_compact;
    exact this
  have hvbarMax : G.vbar μ ≤ G.exPBE_vbarMax m := by
    apply le_csSup;
    · have hvbar_bddAbove : BddAbove (G.vbar '' G.feasibleBeliefs m) := by
        have h_compact : IsCompact (G.feasibleBeliefs m) := by
          exact ( DisclosureGame.isCompact_convex_feasibleBeliefs hm ).1
        have h_upper_semicontinuous : UpperSemicontinuousOn G.vbar (G.feasibleBeliefs m) := by
          exact G.vbar_upperSemicontinuousOn.mono ( DisclosureGame.feasibleBeliefs_subset_simplex m );
        exact h_upper_semicontinuous.bddAbove_of_isCompact h_compact;
      exact hvbar_bddAbove;
    · exact Set.mem_image_of_mem _ hμ
  exact ⟨by linarith, by linarith⟩

/-
The graph of `V` over the simplex is closed.
-/
lemma exPBE_V_isClosed_graph :
    IsClosed {pr : (T → ℝ) × ℝ | pr.1 ∈ simplexOn G.Θ ∧ pr.2 ∈ G.V pr.1} := by
  have h_closed : ∀ pr₀ : (T → ℝ) × ℝ, pr₀ ∉ {pr : (T → ℝ) × ℝ | pr.1 ∈ simplexOn G.Θ ∧ pr.2 ∈ G.V pr.1} → ∃ U : Set ((T → ℝ) × ℝ), IsOpen U ∧ pr₀ ∈ U ∧ U ⊆ {pr : (T → ℝ) × ℝ | pr.1 ∈ simplexOn G.Θ ∧ pr.2 ∈ G.V pr.1}ᶜ := by
    intro pr₀ hpr₀
    by_cases hμ₀ : pr₀.1 ∈ simplexOn G.Θ;
    · by_cases hV₀ : pr₀.2 ∈ G.V pr₀.1;
      · exact False.elim ( hpr₀ ⟨ hμ₀, hV₀ ⟩ );
      · obtain ⟨d, hd_pos, hd⟩ : ∃ d > 0, ∀ x ∈ G.V pr₀.1, dist pr₀.2 x ≥ d := by
          have := Metric.isOpen_iff.mp ( isOpen_compl_iff.mpr ( G.V_isCompact pr₀.1 hμ₀ |> IsCompact.isClosed ) ) pr₀.2 hV₀;
          exact ⟨ this.choose, this.choose_spec.1, fun x hx => le_of_not_gt fun h => this.choose_spec.2 ( Metric.mem_ball'.2 h ) hx ⟩;
        obtain ⟨W, hW⟩ : ∃ W ∈ nhdsWithin pr₀.1 (simplexOn G.Θ), ∀ μ' ∈ W, G.V μ' ⊆ {x : ℝ | d / 2 < dist x pr₀.2} := by
          have := G.V_uhc pr₀.1 hμ₀ { x : ℝ | d / 2 < dist x pr₀.2 } ?_ ?_;
          · exact this;
          · exact isOpen_lt continuous_const ( continuous_id.dist continuous_const );
          · exact fun x hx => by rw [ Set.mem_setOf_eq, dist_comm ] ; linarith [ hd x hx ] ;
        obtain ⟨U, hU⟩ : ∃ U : Set ((T → ℝ) × ℝ), IsOpen U ∧ pr₀ ∈ U ∧ ∀ pr ∈ U, pr.1 ∈ W ∨ pr.1 ∉ simplexOn G.Θ := by
          rcases mem_nhdsWithin.mp hW.1 with ⟨ U, hUo, hU ⟩;
          exact ⟨ U ×ˢ Set.univ, hUo.prod isOpen_univ, ⟨ hU.1, Set.mem_univ _ ⟩, fun pr hpr => Classical.or_iff_not_imp_right.2 fun h => hU.2 ⟨ hpr.1, by simpa using h ⟩ ⟩;
        refine' ⟨ U ∩ { pr : ( T → ℝ ) × ℝ | dist pr.2 pr₀.2 < d / 2 }, _, _, _ ⟩;
        · exact hU.1.inter ( isOpen_lt ( continuous_snd.dist continuous_const ) continuous_const );
        · exact ⟨ hU.2.1, by simpa using half_pos hd_pos ⟩;
        · grind +locals;
    · exact ⟨ { pr : ( T → ℝ ) × ℝ | pr.1 ∉ simplexOn G.Θ }, isOpen_compl_iff.mpr ( isClosed_simplexOn G.Θ |> IsClosed.preimage continuous_fst ), hμ₀, fun pr hpr => by aesop ⟩;
  rw [ isClosed_iff_nhds ];
  exact fun pr₀ hpr₀ => Classical.not_not.1 fun hpr₀' => by rcases h_closed pr₀ hpr₀' with ⟨ U, hUo, hpr₀U, hU ⟩ ; rcases hpr₀ U ( hUo.mem_nhds hpr₀U ) with ⟨ y, hyU, hy ⟩ ; exact hU hyU hy;

/-
The best-response set is convex.
-/
lemma exPBE_convex_BR (r : Msg → ℝ) (θ : T) : Convex ℝ (exPBE_BR G r θ) := by
  intro x hx y hy a b ha hb hab;
  refine' ⟨ _, _ ⟩;
  · exact exPBE_convex_simplexOn ( G.M θ ) hx.1 hy.1 ha hb hab;
  · intro z hz;
    convert add_le_add ( mul_le_mul_of_nonneg_left ( hx.2 z hz ) ha ) ( mul_le_mul_of_nonneg_left ( hy.2 z hz ) hb ) using 1 ; simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_left_comm, hab ] ; ring;
    · simp +decide only [mul_assoc, ← Finset.sum_add_distrib] ; congr ; ext ; rw [ ← add_mul, hab, one_mul ];
    · simp +decide only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, Finset.sum_add_distrib,
          Finset.mul_sum _ _ _]

/-
The support of a best response lies in the argmax of `r` over `M θ`.
-/
lemma exPBE_BR_support {r : Msg → ℝ} {θ : T} {x : Msg → ℝ}
    (hx : x ∈ exPBE_BR G r θ) :
    simplexSupport x ⊆ argmaxOn r (G.M θ) := by
  intro m hm;
  obtain ⟨c, hc⟩ : ∃ c, (∀ m' ∈ G.M θ, r m' ≤ c) ∧ (∑ m, x m * r m) = c := by
    refine' ⟨ _, fun m' hm' => _, rfl ⟩;
    have := hx.2 ( fun m => if m = m' then 1 else 0 ) ?_ <;> simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
    exact ⟨ fun _ => by split_ifs <;> norm_num, fun _ h => by rintro rfl; exact h hm' ⟩;
  have h_sum_zero : ∑ m, x m * (c - r m) = 0 := by
    simp +decide [ mul_sub, ← Finset.sum_mul _ _ _, hx.1.2.1, hc.2 ];
  rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_sum_zero;
  · simp_all +decide [ sub_eq_iff_eq_add ];
    cases h_sum_zero m <;> simp_all +decide [ ne_of_gt ];
    exact Classical.not_not.1 fun h => hm.ne' <| hx.1.2.2 m h;
  · intro m' _;
    by_cases hm' : m' ∈ G.M θ;
    · exact mul_nonneg ( hx.1.1 m' ) ( sub_nonneg.2 ( hc.1 m' hm' ) );
    · have := hx.1.2.2 m' hm'; aesop;

/-
`K` is nonempty.
-/
lemma exPBE_K_nonempty : (exPBE_K G).Nonempty := by
  refine' ⟨ ⟨ fun θ => if h : θ ∈ G.Θ then Classical.choose ( exPBE_simplexOn_nonempty ( G.M_nonempty θ h ) ) else 0, fun m => if h : m ∈ G.𝓜 then Classical.choose ( G.feasibleBeliefs_nonempty h ) else 0, fun m => if m ∈ G.𝓜 then exPBE_vlowMin G m else 0 ⟩, _, _, _, _, _ ⟩ <;> simp +decide [ funext_iff ];
  · intro θ hθ; have := Classical.choose_spec ( exPBE_simplexOn_nonempty ( G.M_nonempty θ hθ ) ) ; aesop;
  · tauto;
  · grind +suggestions;
  · tauto;
  · exact ⟨ fun m hm => ⟨ by rw [ if_pos hm ], by rw [ if_pos hm ] ; exact exPBE_vlowMin_le_vbarMax G hm ⟩, fun m hm hm' => False.elim ( hm hm' ) ⟩

/-
`K` is convex.
-/
lemma exPBE_K_convex : Convex ℝ (exPBE_K G) := by
  intro p hp q hq a b ha hb hab;
  constructor;
  · intro θ hθ
    have h_convex : Convex ℝ (simplexOn (G.M θ)) := by
      exact exPBE_convex_simplexOn (G.M θ)
    exact h_convex (hp.1 θ hθ) (hq.1 θ hθ) ha hb hab;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · intro θ hθ; have := hp.2.1 θ hθ; have := hq.2.1 θ hθ; aesop;
    · intro m hm
      have h_convex : Convex ℝ (G.feasibleBeliefs m) := by
        exact DisclosureGame.convex_feasibleBeliefs hm
      exact h_convex (hp.2.2.1 m hm) (hq.2.2.1 m hm) ha hb hab;
    · intro m hm; have := hp.2.2.2.1 m hm; have := hq.2.2.2.1 m hm; aesop;
    · intro m hm
      have h_convex : Convex ℝ (Icc (G.exPBE_vlowMin m) (G.exPBE_vbarMax m)) := by
        exact convex_Icc _ _;
      exact h_convex ( hp.2.2.2.2.1 m hm ) ( hq.2.2.2.2.1 m hm ) ha hb hab;
    · intro m hm; have := hp.2.2.2.2.2 m hm; have := hq.2.2.2.2.2 m hm; aesop;

/-
`K` is compact.
-/
lemma exPBE_K_isCompact : IsCompact (exPBE_K G) := by
  convert ( isCompact_pi_infinite fun θ => ?_ ) |> IsCompact.prod <| ( isCompact_pi_infinite fun m => ?_ ) |> IsCompact.prod <| ( isCompact_univ_pi fun m => ?_ ) using 1;
  rotate_left;
  use fun θ => if hθ : θ ∈ G.Θ then simplexOn ( G.M θ ) else { 0 };
  split_ifs <;> [ exact isCompact_simplexOn _; exact isCompact_singleton ];
  use fun m => if hm : m ∈ G.𝓜 then G.feasibleBeliefs m else { 0 };
  rotate_left;
  use fun m => if hm : m ∈ G.𝓜 then Set.Icc ( exPBE_vlowMin G m ) ( exPBE_vbarMax G m ) else { 0 };
  · split_ifs <;> [ exact CompactIccSpace.isCompact_Icc; exact isCompact_singleton ];
  · ext ⟨σ, μ, r⟩; simp [exPBE_K];
    constructor <;> intro h <;> simp_all +decide [ simplexOn ]; all_goals grind;
  · split_ifs with hm;
    · exact ( DisclosureGame.isCompact_convex_feasibleBeliefs hm ).1;
    · exact isCompact_singleton

/-
`Φ` has nonempty values on `K`.
-/
lemma exPBE_Phi_nonempty {p : FixedPointSpace T Msg} (hp : p ∈ exPBE_K G) :
    (exPBE_Phi G p).Nonempty := by
  obtain ⟨q1, hq1⟩ : ∃ q1 : T → Msg → ℝ, (∀ θ ∈ G.Θ, q1 θ ∈ exPBE_BR G p.2.2 θ) ∧ (∀ θ ∉ G.Θ, q1 θ = 0) := by
    have hq1 : ∀ θ ∈ G.Θ, ∃ q1 : Msg → ℝ, q1 ∈ exPBE_BR G p.2.2 θ := by
      intro θ hθ
      have h_compact : IsCompact (simplexOn (G.M θ)) := by
        exact isCompact_simplexOn _
      have h_nonempty : (simplexOn (G.M θ)).Nonempty := by
        exact exPBE_simplexOn_nonempty ( G.M_nonempty θ hθ )
      have h_continuous : Continuous (fun x : Msg → ℝ => ∑ m, x m * p.2.2 m) := by
        fun_prop (disch := solve_by_elim)
      have h_max : ∃ q1 ∈ simplexOn (G.M θ), ∀ y ∈ simplexOn (G.M θ), (∑ m, y m * p.2.2 m) ≤ (∑ m, q1 m * p.2.2 m) := by
        exact h_compact.exists_isMaxOn h_nonempty h_continuous.continuousOn
      exact ⟨h_max.choose, h_max.choose_spec.left, fun y hy => h_max.choose_spec.right y hy⟩;
    choose! q1 hq1 using hq1;
    exact ⟨ fun θ => if h : θ ∈ G.Θ then q1 θ else 0, fun θ hθ => by simpa [ hθ ] using hq1 θ hθ, fun θ hθ => by simp +decide [ hθ ] ⟩;
  obtain ⟨q2, hq2⟩ : ∃ q2 : Msg → T → ℝ, (∀ m ∈ G.𝓜, q2 m ∈ G.feasibleBeliefs m ∧ ∀ θ ∈ G.Θ, exPBE_onPath G p.1 m * q2 m θ = G.μ0 θ * p.1 θ m) ∧ (∀ m ∉ G.𝓜, q2 m = 0) := by
    refine' ⟨ fun m => if hm : m ∈ G.𝓜 then if h : 0 < exPBE_onPath G p.1 m then exPBE_belief G p.1 m else ( G.feasibleBeliefs_nonempty hm ).choose else 0, _, _ ⟩ <;> simp +decide;
    · intro m hm
      by_cases h : 0 < exPBE_onPath G p.1 m;
      · simp +decide [ hm, h ];
        refine' ⟨ _, _ ⟩;
        · convert Strategy.belief_mem_feasibleBeliefs ( ⟨ p.1, hp.1 ⟩ : Strategy G ) _;
          exact Set.mem_iUnion₂.2 ⟨ Classical.choose ( show ∃ θ, θ ∈ G.Θ ∧ 0 < p.1 θ m from by
                                                        contrapose! h;
                                                        exact Finset.sum_nonpos fun θ hθ => mul_nonpos_of_nonneg_of_nonpos ( G.μ0_mem.1 θ ) ( h θ hθ ) ), Classical.choose_spec ( show ∃ θ, θ ∈ G.Θ ∧ 0 < p.1 θ m from by
                                                                                                                                  contrapose! h;
                                                                                                                                  exact Finset.sum_nonpos fun θ hθ => mul_nonpos_of_nonneg_of_nonpos ( G.μ0_mem.1 θ ) ( h θ hθ ) ) |>.1, by
                                                                                                                                  all_goals generalize_proofs at *;
                                                                                                                                  exact Classical.choose_spec ‹∃ x ∈ G.Θ, 0 < p.1 x m› |>.2 ⟩;
        · intro θ hθ
          simp [exPBE_belief, h];
          rw [ mul_div_cancel₀ _ h.ne' ];
      · have h_zero : ∀ θ ∈ G.Θ, G.μ0 θ * p.1 θ m = 0 := by
          intro θ hθ
          have h_zero : G.μ0 θ * p.1 θ m ≤ 0 := by
            exact le_trans ( Finset.single_le_sum ( fun a _ => mul_nonneg ( G.μ0_mem.1 a ) ( hp.1 a ( by aesop ) |>.1 m ) ) ( by aesop ) ) ( le_of_not_gt h );
          exact le_antisymm h_zero ( mul_nonneg ( G.μ0_mem.1 θ ) ( hp.1 θ hθ |>.1 m ) );
        split_ifs ; simp_all +decide [ exPBE_onPath ];
        exact ⟨ Exists.choose_spec ( G.feasibleBeliefs_nonempty hm ), fun θ hθ => by rw [ Finset.sum_eq_zero fun θ' hθ' => by cases h_zero θ' hθ' <;> simp +decide [ * ] ] ; simp +decide [ h_zero θ hθ ] ⟩;
    · tauto;
  obtain ⟨q3, hq3⟩ : ∃ q3 : Msg → ℝ, (∀ m ∈ G.𝓜, q3 m ∈ G.V (p.2.1 m)) ∧ (∀ m ∉ G.𝓜, q3 m = 0) := by
    have hq3 : ∀ m ∈ G.𝓜, ∃ r : ℝ, r ∈ G.V (p.2.1 m) := by
      exact fun m hm => G.V_nonempty _ ( hp.2.2.1 m hm |> fun h => by simpa using feasibleBeliefs_subset_simplex _ h );
    choose! r hr using hq3;
    exact ⟨ fun m => if hm : m ∈ G.𝓜 then r m else 0, fun m hm => by simpa [ hm ] using hr m hm, fun m hm => by simp +decide [ hm ] ⟩;
  exact ⟨ ⟨ q1, q2, q3 ⟩, hq1.1, hq1.2, hq2.1, hq2.2, hq3.1, hq3.2 ⟩

/-
`Φ` has convex values on `K`.
-/
lemma exPBE_Phi_convex {p : FixedPointSpace T Msg} (hp : p ∈ exPBE_K G) :
    Convex ℝ (exPBE_Phi G p) := by
  intro q1 hq1 q2 hq2 a b ha hb hab;
  refine' ⟨ _, _, _, _, _ ⟩;
  · intro θ hθ;
    have := G.exPBE_convex_BR p.2.2 θ ( hq1.1 θ hθ ) ( hq2.1 θ hθ ) ha hb hab;
    convert this using 1;
  · intro θ hθ; have := hq1.2.1 θ hθ; have := hq2.2.1 θ hθ; simp_all +decide [ Prod.smul_fst ] ;
  · intro m hm
    have h_feasible : (a • q1.2.1 m + b • q2.2.1 m) ∈ G.feasibleBeliefs m := by
      apply convex_feasibleBeliefs hm;
      · exact hq1.2.2.1 m hm |>.1;
      · exact hq2.2.2.1 m hm |>.1;
      · exact ha;
      · exact hb;
      · exact hab;
    have := hq1.2.2.1 m hm; have := hq2.2.2.1 m hm; simp_all +decide [ exPBE_onPath ] ;
    grind;
  · intro m hm; have := hq1.2.2.2.1 m hm; have := hq2.2.2.2.1 m hm; aesop;
  · refine' ⟨ _, _ ⟩;
    · intro m hm
      have h_convex : Convex ℝ (G.V (p.2.1 m)) := by
        convert G.V_ordConnected ( p.2.1 m ) _ |> OrdConnected.convex;
        · infer_instance;
        · exact hp.2.2.1 m hm |> fun h => by simpa using G.feasibleBeliefs_subset_simplex m h;
      exact h_convex ( hq1.2.2.2.2.1 m hm ) ( hq2.2.2.2.2.1 m hm ) ha hb hab;
    · intro m hm; have := hq1.2.2.2.2.2 m hm; have := hq2.2.2.2.2.2 m hm; aesop;

/-
`Φ` maps `K` into `K`.
-/
lemma exPBE_Phi_subset {p : FixedPointSpace T Msg} (hp : p ∈ exPBE_K G) :
    exPBE_Phi G p ⊆ exPBE_K G := by
  intro q hq
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ := hq
  exact ⟨by
  exact fun θ hθ => ( hq1 θ hθ ).1, by
    exact hq2, by
    exact fun m hm => hq3 m hm |>.1, by
    exact hq4, by
    exact fun m hm => exPBE_V_subset_box G hm ( hp.2.2.1 m hm ) ( hq5 m hm ), by
    exact hq6⟩

/-
`Φ` has closed graph.
-/
lemma exPBE_Phi_isClosed_graph :
    IsClosed {pr : FixedPointSpace T Msg × FixedPointSpace T Msg |
      pr.1 ∈ exPBE_K G ∧ pr.2 ∈ exPBE_Phi G pr.1} := by
  refine' isClosed_of_closure_subset _;
  intro pr hpr
  obtain ⟨hpr1, hpr2⟩ : pr.1 ∈ G.exPBE_K ∧ pr.2 ∈ G.exPBE_Phi pr.1 := by
    rw [ mem_closure_iff_seq_limit ] at hpr;
    obtain ⟨ x, hx, hx' ⟩ := hpr;
    refine' ⟨ _, _ ⟩;
    · exact IsClosed.mem_of_tendsto ( G.exPBE_K_isCompact.isClosed ) ( continuousAt_fst.tendsto.comp hx' ) ( Filter.Eventually.of_forall fun n => hx n |>.1 );
    · refine' ⟨ _, _, _, _, _ ⟩;
      · intro θ hθ
        have h_lim : Filter.Tendsto (fun n => (x n).2.1 θ) Filter.atTop (nhds (pr.2.1 θ)) := by
          exact tendsto_pi_nhds.mp ( continuousAt_snd.fst.tendsto.comp hx' ) θ
        have h_lim_r : Filter.Tendsto (fun n => (x n).1.2.2) Filter.atTop (nhds (pr.1.2.2)) := by
          exact continuousAt_snd.snd.tendsto.comp ( continuousAt_fst.tendsto.comp hx' )
        have h_lim_BR : ∀ y ∈ simplexOn (G.M θ), (∑ m, y m * (pr.1.2.2 m)) ≤ (∑ m, (pr.2.1 θ m) * (pr.1.2.2 m)) := by
          intro y hy
          have h_lim_BR : ∀ n, (∑ m, y m * (x n).1.2.2 m) ≤ (∑ m, (x n).2.1 θ m * (x n).1.2.2 m) := by
            intro n
            specialize hx n
            generalize_proofs at *;
            exact hx.2.1 θ hθ |>.2 y hy;
          exact le_of_tendsto_of_tendsto' ( tendsto_finset_sum _ fun _ _ => tendsto_const_nhds.mul ( tendsto_pi_nhds.mp h_lim_r _ ) ) ( tendsto_finset_sum _ fun _ _ => Filter.Tendsto.mul ( tendsto_pi_nhds.mp h_lim _ ) ( tendsto_pi_nhds.mp h_lim_r _ ) ) h_lim_BR
        exact ⟨by
        have h_lim_simplex : ∀ n, (x n).2.1 θ ∈ simplexOn (G.M θ) := by
          intro n
          have := hx n
          simp [exPBE_Phi] at this
          generalize_proofs at *;
          exact this.2.1 θ hθ |>.1;
        exact IsClosed.mem_of_tendsto ( isClosed_simplexOn _ ) h_lim ( Filter.Eventually.of_forall h_lim_simplex ), by
          exact h_lim_BR⟩;
      · intro θ hθ;
        have h_lim : Filter.Tendsto (fun n => (x n).2.1 θ) Filter.atTop (nhds (pr.2.1 θ)) := by
          exact tendsto_pi_nhds.mp ( continuousAt_snd.fst.tendsto.comp hx' ) θ;
        exact tendsto_nhds_unique h_lim ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; have := hx n; have := this.2.2.1; aesop ) );
      · intro m hm
        have h_lim : Filter.Tendsto (fun n => (x n).2.2.1 m) Filter.atTop (nhds (pr.2.2.1 m)) := by
          exact tendsto_pi_nhds.mp ( continuousAt_snd.snd.fst.tendsto.comp hx' ) m;
        refine' ⟨ _, _ ⟩;
        · have h_closed : IsClosed (G.feasibleBeliefs m) := by
            grind +suggestions;
          exact h_closed.mem_of_tendsto h_lim ( Filter.Eventually.of_forall fun n => hx n |>.2.2.2.1 m hm |>.1 );
        · intro θ hθ
          have h_lim_eq : Filter.Tendsto (fun n => exPBE_onPath G (x n).1.1 m * (x n).2.2.1 m θ) Filter.atTop (nhds (exPBE_onPath G pr.1.1 m * pr.2.2.1 m θ)) := by
            refine' Filter.Tendsto.mul _ _;
            · refine' tendsto_finset_sum _ fun θ _ => _;
              exact tendsto_const_nhds.mul ( tendsto_pi_nhds.mp ( tendsto_pi_nhds.mp ( continuousAt_fst.fst.tendsto.comp hx' ) θ ) m );
            · exact tendsto_pi_nhds.mp h_lim θ;
          have h_lim_eq : Filter.Tendsto (fun n => G.μ0 θ * (x n).1.1 θ m) Filter.atTop (nhds (G.μ0 θ * pr.1.1 θ m)) := by
            exact tendsto_const_nhds.mul ( tendsto_pi_nhds.mp ( tendsto_pi_nhds.mp ( continuousAt_fst.fst.tendsto.comp hx' ) θ ) m );
          exact tendsto_nhds_unique ‹_› ( h_lim_eq.congr fun n => by have := hx n; have := this.2.2.2.1 m hm; aesop );
      · intro m hm;
        have h_zero : ∀ n, (x n).2.2.1 m = 0 := by
          intro n; specialize hx n; unfold exPBE_Phi at hx; aesop;
        exact tendsto_nhds_unique ( continuousAt_apply _ _ |> ContinuousAt.tendsto |> Filter.Tendsto.comp <| continuousAt_snd.snd.fst.tendsto.comp hx' ) ( tendsto_const_nhds.congr fun n => h_zero n ▸ rfl );
      · have h_closed : IsClosed {pr : (T → ℝ) × ℝ | pr.1 ∈ simplexOn G.Θ ∧ pr.2 ∈ G.V pr.1} := by
          convert exPBE_V_isClosed_graph G using 1;
        have h_closed : ∀ m ∈ G.𝓜, Filter.Tendsto (fun n => (x n).1.2.1 m) Filter.atTop (nhds (pr.1.2.1 m)) ∧ Filter.Tendsto (fun n => (x n).2.2.2 m) Filter.atTop (nhds (pr.2.2.2 m)) := by
          intro m hm;
          exact ⟨ tendsto_pi_nhds.mp ( continuousAt_fst.snd.fst.tendsto.comp hx' ) m, tendsto_pi_nhds.mp ( continuousAt_snd.snd.snd.tendsto.comp hx' ) m ⟩;
        have h_closed : ∀ m ∈ G.𝓜, (pr.1.2.1 m, pr.2.2.2 m) ∈ {pr : (T → ℝ) × ℝ | pr.1 ∈ simplexOn G.Θ ∧ pr.2 ∈ G.V pr.1} := by
          intro m hm
          have h_seq : ∀ n, (x n).1.2.1 m ∈ simplexOn G.Θ ∧ (x n).2.2.2 m ∈ G.V ((x n).1.2.1 m) := by
            intro n
            have := hx n
            simp [exPBE_K, exPBE_Phi] at this;
            exact ⟨ this.1.2.2.1 m hm |> fun h => by simpa using feasibleBeliefs_subset_simplex m h, this.2.2.2.2.2.1 m hm ⟩;
          exact ‹IsClosed { pr : ( T → ℝ ) × ℝ | pr.1 ∈ simplexOn G.Θ ∧ pr.2 ∈ G.V pr.1 } ›.mem_of_tendsto ( Filter.Tendsto.prodMk_nhds ( h_closed m hm |>.1 ) ( h_closed m hm |>.2 ) ) ( Filter.Eventually.of_forall h_seq );
        have h_closed : ∀ m ∉ G.𝓜, Filter.Tendsto (fun n => (x n).2.2.2 m) Filter.atTop (nhds (pr.2.2.2 m)) := by
          exact fun m hm => tendsto_pi_nhds.mp ( continuousAt_snd.snd.snd.tendsto.comp hx' ) m;
        have h_closed : ∀ m ∉ G.𝓜, pr.2.2.2 m = 0 := by
          intro m hm
          have h_zero : ∀ n, (x n).2.2.2 m = 0 := by
            intro n; specialize hx n; have := hx.2; simp_all +decide [ exPBE_Phi ] ;
          exact tendsto_nhds_unique ( h_closed m hm ) ( tendsto_const_nhds.congr fun n => h_zero n ▸ rfl );
        aesop
  exact ⟨hpr1, hpr2⟩

/-
From a fixed point of `Φ` we read off a PBE.
-/
lemma exPBE_readoff {p : FixedPointSpace T Msg} (hpK : p ∈ exPBE_K G)
    (hpfix : p ∈ exPBE_Phi G p) : ∃ s : Strategy G, G.IsPBE s := by
  use ⟨p.1, hpK.1⟩;
  obtain ⟨hBR, _, hbel, _, hpay, _⟩ := hpfix;
  refine' ⟨ p.2.1, p.2.2, _, _, _, _, _ ⟩;
  · exact fun m hm => feasibleBeliefs_subset_simplex _ ( hbel m hm |>.1 );
  · exact fun m hm => hbel m hm |>.1;
  · intro m hm
    have hm_mem : m ∈ G.𝓜 := by
      obtain ⟨ θ, hθ, hm ⟩ := Set.mem_iUnion₂.mp hm;
      exact G.M_subset θ hθ ( CPD.simplexSupport_subset ( hpK.1 θ hθ ) hm )
    have hO_pos : 0 < exPBE_onPath G p.1 m := by
      obtain ⟨θ, hθ⟩ : ∃ θ ∈ G.Θ, m ∈ simplexSupport (p.1 θ) := by
        unfold Strategy.evidence at hm; aesop;
      have hO_pos : 0 < G.μ0 θ * p.1 θ m := by
        exact mul_pos ( G.μ0_fullSupport θ hθ.1 ) hθ.2;
      exact lt_of_lt_of_le hO_pos ( Finset.single_le_sum ( fun x _ => mul_nonneg ( show 0 ≤ G.μ0 x from by
                                                                                    exact G.μ0_mem.1 x ) ( show 0 ≤ p.1 x m from by
                                                                                                                      exact hpK.1 x ‹_› |>.1 m ) ) ( Finset.mem_coe.mpr hθ.1 ) )
    have h_eq : ∀ θ, p.2.1 m θ = G.μ0 θ * p.1 θ m / exPBE_onPath G p.1 m := by
      intro θ
      by_cases hθ : θ ∈ G.Θ;
      · rw [ ← hbel m hm_mem |>.2 θ hθ, mul_div_cancel_left₀ _ hO_pos.ne' ];
      · have h_zero : p.2.1 m θ = 0 := by
          have := hbel m hm_mem |>.1;
          obtain ⟨ s, hs ⟩ := this;
          rw [ ← hs.2, Strategy.belief ];
          rw [ G.μ0_mem.2.2 θ hθ, MulZeroClass.zero_mul, zero_div ];
        have := G.μ0_mem; simp_all +decide [ simplexOn ] ;
    exact (by
    exact funext h_eq);
  · exact hpay;
  · exact fun θ hθ => exPBE_BR_support _ ( hBR θ hθ )

end Existence

/-- **Lemma K.4**: every disclosure game admits a PBE. Proved via
Kakutani's fixed-point theorem (`kakutani`), the sole external axiom of
this development. -/
theorem exists_PBE (G : DisclosureGame T Msg) : ∃ s : Strategy G, G.IsPBE s := by
  obtain ⟨p, hpK, hpfix⟩ :=
    kakutani (FixedPointSpace T Msg) (exPBE_K G) (exPBE_Phi G)
      (exPBE_K_nonempty G) (exPBE_K_isCompact G) (exPBE_K_convex G)
      (fun x hx => exPBE_Phi_nonempty G hx) (fun x hx => exPBE_Phi_convex G hx)
      (fun x hx => exPBE_Phi_subset G hx) (exPBE_Phi_isClosed_graph G)
  exact exPBE_readoff G hpK hpfix

end DisclosureGame

end CPD
