import Mathlib

/-!
# Best-response payoff correspondence (Lemma K.1)

This file proves **Lemma K.1**, the best-response microfoundation for Assumption
1(A4). Let `Θ` be finite and let `A` be a nonempty compact Hausdorff action
space. Suppose the sender payoff `u_S : A → ℝ` is continuous and each receiver
payoff `u_R(·, θ)` is continuous. For a belief `μ`, define the receiver's
best-response set `a*(μ)` and let the sender payoff correspondence be the
convex hull of `u_S '' a*(μ)`.

## Setup

- `Θ` is a finite type space
- `A` is a nonempty compact Hausdorff action space
- `u_S : A → ℝ` is a continuous sender payoff function
- `u_R : A → Θ → ℝ` gives continuous receiver payoff functions

## Main definitions

- `receiverExpPayoff u_R μ a` — the receiver's expected payoff from action `a` under belief `μ`
- `bestResponse u_R μ` — the set of optimal actions (best responses) under belief `μ`
- `upperEnvelope u_R u_S μ` — the upper envelope `v̄(μ) = max_{a ∈ a*(μ)} u_S(a)`
- `lowerEnvelope u_R u_S μ` — the lower envelope `v̲(μ) = min_{a ∈ a*(μ)} u_S(a)`
- `senderPayoffCorr u_R u_S μ` — the sender payoff correspondence `v(μ) = [v̲(μ), v̄(μ)]`

## Lemma K.1

* `bestResponse_nonempty`, `bestResponse_isCompact`, and
  `bestResponse_upperHemicontinuous` prove the corresponding properties of
  `a*`.
* `senderPayoffCorr_eq_convexHull` identifies the interval
  `[v̲(μ), v̄(μ)]` with `conv (u_S '' a*(μ))`.
* `senderPayoffCorr_nonempty`, `senderPayoffCorr_isCompact`,
  `senderPayoffCorr_convex`, and `senderPayoffCorr_upperHemicontinuous` prove
  that this payoff correspondence is nonempty-, compact-, convex-valued, and
  upper hemicontinuous.
* `upperEnvelope_upperSemicontinuous` and
  `lowerEnvelope_lowerSemicontinuous` prove the asserted semicontinuity of its
  envelopes.
* `bestResponse_payoff_correspondence` packages the statement of Lemma K.1.
-/

open Finset Set Filter BigOperators Topology

namespace CPD

variable {Θ : Type*} [Fintype Θ]
variable {A : Type*} [TopologicalSpace A] [CompactSpace A] [Nonempty A] [T2Space A]

/-! ## Definitions -/

/-- The receiver's expected payoff from action `a` under belief `μ`:
  `U_R(a, μ) = ∑_i μ_i · u_R(a, θ_i)`. -/
def receiverExpPayoff (u_R : A → Θ → ℝ) (μ : Θ → ℝ) (a : A) : ℝ :=
  ∑ i : Θ, μ i * u_R a i

/-- The best-response set: the set of actions maximizing the receiver's expected payoff.
  `a*(μ) = argmax_{a ∈ A} U_R(a, μ)`. -/
def bestResponse (u_R : A → Θ → ℝ) (μ : Θ → ℝ) : Set A :=
  {a : A | ∀ a' : A, receiverExpPayoff u_R μ a' ≤ receiverExpPayoff u_R μ a}

variable (u_R : A → Θ → ℝ) (u_S : A → ℝ)

/-- The upper envelope: `v̄(μ) = max_{a ∈ a*(μ)} u_S(a)`. -/
noncomputable def upperEnvelope (μ : Θ → ℝ) : ℝ :=
  sSup (u_S '' bestResponse u_R μ)

/-- The lower envelope: `v̲(μ) = min_{a ∈ a*(μ)} u_S(a)`. -/
noncomputable def lowerEnvelope (μ : Θ → ℝ) : ℝ :=
  sInf (u_S '' bestResponse u_R μ)

/-- The sender payoff correspondence: `v(μ) = [v̲(μ), v̄(μ)]`. -/
def senderPayoffCorr (μ : Θ → ℝ) : Set ℝ :=
  Set.Icc (lowerEnvelope u_R u_S μ) (upperEnvelope u_R u_S μ)

/-! ## Continuity of receiver expected payoff -/

variable {u_R}

/--
The receiver's expected payoff is jointly continuous in `(μ, a)`.
-/
lemma continuous_receiverExpPayoff (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ) :
    Continuous fun p : (Θ → ℝ) × A => receiverExpPayoff u_R p.1 p.2 := by
  exact continuous_finset_sum _ fun i _ => Continuous.mul ( continuous_apply i |> Continuous.comp <| continuous_fst ) ( hu_R i |> Continuous.comp <| continuous_snd )

/--
The receiver's expected payoff is continuous in `a` for fixed `μ`.
-/
lemma continuous_receiverExpPayoff_right (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (μ : Θ → ℝ) : Continuous (receiverExpPayoff u_R μ) := by
  exact continuous_finset_sum Finset.univ fun _ _ => Continuous.mul ( continuous_const ) ( hu_R _ )

/-! ## Nonemptiness and compactness of best-response sets -/

/--
The best-response set is nonempty: a continuous function on a nonempty compact space
  attains its maximum.
-/
theorem bestResponse_nonempty (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (μ : Θ → ℝ) : (bestResponse u_R μ).Nonempty := by
  -- By definition of bestResponse, we need to show that there exists an a in A such that for all a' in A, receiverExpPayoff u_R μ a' ≤ receiverExpPayoff u_R μ a.
  suffices h_suff : ∃ a : A, ∀ a' : A, receiverExpPayoff u_R μ a' ≤ receiverExpPayoff u_R μ a by
    exact ⟨ h_suff.choose, h_suff.choose_spec ⟩;
  convert ( IsCompact.exists_isMaxOn ( isCompact_univ ) ( Set.univ_nonempty ) ( show ContinuousOn ( fun a => receiverExpPayoff u_R μ a ) Set.univ from Continuous.continuousOn ( continuous_receiverExpPayoff_right hu_R μ ) ) ) using 1;
  -- The two functions are equal because the IsMaxOn condition is exactly the same as the first function's condition.
  simp [IsMaxOn];
  simp +decide [ IsMaxFilter ]

/--
The best-response set is closed.
-/
lemma bestResponse_isClosed (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (μ : Θ → ℝ) : IsClosed (bestResponse u_R μ) := by
  refine' isClosed_iff_clusterPt.mpr fun x hx => _;
  intro y;
  have h_seq : ∀ U ∈ nhds x, ∃ a ∈ U, receiverExpPayoff u_R μ y ≤ receiverExpPayoff u_R μ a := by
    intro U hU;
    rw [ clusterPt_principal_iff ] at hx;
    exact Exists.elim ( hx U hU ) fun a ha => ⟨ a, ha.1, ha.2 y ⟩;
  contrapose! h_seq;
  exact ⟨ { a | receiverExpPayoff u_R μ a < receiverExpPayoff u_R μ y }, IsOpen.mem_nhds ( isOpen_lt ( continuous_receiverExpPayoff_right hu_R μ ) continuous_const ) h_seq, fun a ha => ha ⟩

/--
The best-response set is compact.
-/
theorem bestResponse_isCompact (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (μ : Θ → ℝ) : IsCompact (bestResponse u_R μ) := by
  exact IsClosed.isCompact ( bestResponse_isClosed hu_R μ )

/-! ## Upper hemicontinuity of the best-response correspondence -/

/--
The value function `V(μ) = max_a U_R(a, μ)` is continuous.
-/
lemma continuous_valueFn (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ) :
    Continuous fun μ : Θ → ℝ => sSup ((fun a => receiverExpPayoff u_R μ a) '' Set.univ) := by
  apply_rules [ IsCompact.continuous_sSup ];
  · exact isCompact_univ;
  · convert continuous_receiverExpPayoff hu_R using 1

/--
The maximum of `U_R(·, μ)` over any compact set is continuous in `μ`.
-/
lemma continuous_sSup_over_compact (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    {K : Set A} (hK : IsCompact K) :
    Continuous fun μ : Θ → ℝ => sSup ((fun a => receiverExpPayoff u_R μ a) '' K) := by
  have hreceiverExpPayoff :
      Continuous (fun (p : (Θ → ℝ) × A) => receiverExpPayoff u_R p.1 p.2) := by
    exact continuous_receiverExpPayoff hu_R
  have := @IsCompact.continuous_sSup;
  exact this hK hreceiverExpPayoff

/--
The best-response correspondence is upper hemicontinuous.
-/
theorem bestResponse_upperHemicontinuous (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ) :
    UpperHemicontinuous (bestResponse u_R) := by
  -- Fix μ₀ and open U with bestResponse u_R μ₀ ⊆ U.
  have h_upper_hemicontinuous (μ₀ : Θ → ℝ) (U : Set A) (hU : IsOpen U) (h_subset : bestResponse u_R μ₀ ⊆ U) : ∀ᶠ μ in nhds μ₀, bestResponse u_R μ ⊆ U := by
    by_cases hU_compl_empty : Uᶜ = ∅;
    · simp_all +decide [ Set.ext_iff ];
      exact Filter.Eventually.of_forall fun μ => fun x hx => hU_compl_empty x;
    · -- Let K = Uᶜ. K is closed (complement of open) and compact (closed in compact space, use IsClosed.isCompact).
      set K : Set A := Uᶜ
      have hK_closed : IsClosed K := by
        exact hU.isClosed_compl
      have hK_compact : IsCompact K := by
        exact hK_closed.isCompact;
      -- Define m_K(μ) = sSup ((fun a => receiverExpPayoff u_R μ a) '' K) and m_all(μ) = sSup ((fun a => receiverExpPayoff u_R μ a) '' Set.univ).
      set m_K : (Θ → ℝ) → ℝ := fun μ => sSup ((fun a => receiverExpPayoff u_R μ a) '' K)
      set m_all : (Θ → ℝ) → ℝ := fun μ => sSup ((fun a => receiverExpPayoff u_R μ a) '' Set.univ);
      -- Since $m_K$ and $m_{all}$ are continuous and $m_K(\mu_0) < m_{all}(\mu_0)$, eventually $m_K(\mu) < m_{all}(\mu)$.
      have h_cont : Continuous m_K ∧ Continuous m_all := by
        exact ⟨ continuous_sSup_over_compact hu_R hK_compact, continuous_valueFn hu_R ⟩
      have h_lt : m_K μ₀ < m_all μ₀ := by
        -- Since $K$ is nonempty, there exists some $a₀ \in K$ such that $receiverExpPayoff u_R μ₀ a₀ = m_K(μ₀)$.
        obtain ⟨a₀, ha₀⟩ : ∃ a₀ ∈ K, receiverExpPayoff u_R μ₀ a₀ = m_K μ₀ := by
          exact ( IsCompact.sSup_mem ( hK_compact.image ( continuous_receiverExpPayoff_right hu_R μ₀ ) ) ( Set.Nonempty.image _ ( Set.nonempty_iff_ne_empty.2 hU_compl_empty ) ) );
        -- Since $a₀ \in K$, we have $a₀ \notin bestResponse u_R μ₀$, so there exists some $a' \in A$ such that $receiverExpPayoff u_R μ₀ a' > receiverExpPayoff u_R μ₀ a₀$.
        obtain ⟨a', ha'⟩ : ∃ a' : A, receiverExpPayoff u_R μ₀ a' > receiverExpPayoff u_R μ₀ a₀ := by
          contrapose! h_subset;
          exact Set.not_subset.2 ⟨ a₀, fun a' => h_subset a', ha₀.1 ⟩;
        exact ha₀.2 ▸ lt_of_lt_of_le ha' ( le_csSup ( by exact ( IsCompact.bddAbove ( isCompact_univ.image ( continuous_receiverExpPayoff_right hu_R μ₀ ) ) ) ) ( Set.mem_image_of_mem _ ( Set.mem_univ _ ) ) )
      have h_eventually_lt : ∀ᶠ μ in nhds μ₀, m_K μ < m_all μ := by
        exact IsOpen.mem_nhds ( isOpen_lt h_cont.1 h_cont.2 ) h_lt;
      filter_upwards [ h_eventually_lt ] with μ hμ a ha;
      contrapose! hμ;
      refine' csSup_le _ _ <;> simp_all +decide [ bestResponse ];
      · exact ⟨ _, ⟨ a, rfl ⟩ ⟩;
      · exact fun x => le_csSup ( by exact ( IsCompact.bddAbove ( hK_compact.image ( continuous_receiverExpPayoff_right hu_R μ ) ) ) ) ( Set.mem_image_of_mem _ hμ ) |> le_trans ( ha x );
  exact upperHemicontinuous_iff_forall_isOpen.mpr h_upper_hemicontinuous

/-! ## Semicontinuity of the envelopes -/

variable {u_S}

/--
The upper envelope `v̄` is upper semicontinuous.
-/
theorem upperEnvelope_upperSemicontinuous (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (hu_S : Continuous u_S) :
    UpperSemicontinuous (upperEnvelope u_R u_S) := by
  intro μ₀ r;
  intro hr;
  -- Given that the best response correspondence is upper hemicontinuous, there exists a neighborhood $V$ of $\mu_0$ such that for all $\mu \in V$, $bestResponse u_R μ \subseteq U$.
  obtain ⟨U, hU_open, hU⟩ : ∃ U : Set A, IsOpen U ∧ bestResponse u_R μ₀ ⊆ U ∧ ∀ a ∈ U, u_S a < r := by
    refine' ⟨ { a | u_S a < r }, isOpen_lt hu_S continuous_const, _, _ ⟩;
    · intro a ha;
      exact lt_of_le_of_lt ( le_csSup ( show BddAbove ( u_S '' bestResponse u_R μ₀ ) from IsCompact.bddAbove ( bestResponse_isCompact hu_R μ₀ |> IsCompact.image <| hu_S ) ) <| Set.mem_image_of_mem _ ha ) hr;
    · exact fun a ha => ha;
  have h_upper_hemicontinuous : ∀ᶠ x' in 𝓝 μ₀, bestResponse u_R x' ⊆ U := by
    have := bestResponse_upperHemicontinuous hu_R μ₀;
    have := this U;
    simp_all +decide [ Set.subset_def, nhdsSet ];
    exact this ( fun a ha => IsOpen.mem_nhds hU_open ( hU.1 a ha ) ) |> fun h => h.mono fun x hx a ha => mem_of_mem_nhds ( hx a ha );
  filter_upwards [ h_upper_hemicontinuous ] with x' hx';
  obtain ⟨a', ha'⟩ : ∃ a' ∈ bestResponse u_R x', u_S a' = upperEnvelope u_R u_S x' := by
    have h_compact : IsCompact (u_S '' bestResponse u_R x') := by
      exact IsCompact.image ( bestResponse_isCompact hu_R x' ) hu_S;
    have := h_compact.sSup_mem;
    exact this ( Set.Nonempty.image _ ( bestResponse_nonempty hu_R x' ) );
  linarith [ hU.2 a' ( hx' ha'.1 ) ]

/--
The lower envelope `v̲` is lower semicontinuous.
-/
theorem lowerEnvelope_lowerSemicontinuous (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (hu_S : Continuous u_S) :
    LowerSemicontinuous (lowerEnvelope u_R u_S) := by
  intro μ₀ r hr
  set U : Set A := {a | r < u_S a} with hU_def
  have hU_open : IsOpen U := by
    exact isOpen_lt continuous_const hu_S
  have hU_bestResponse : bestResponse u_R μ₀ ⊆ U := by
    intro a ha
    have h_lowerEnvelope : lowerEnvelope u_R u_S μ₀ ≤ u_S a := by
      exact csInf_le ( by exact IsCompact.bddBelow ( bestResponse_isCompact hu_R μ₀ |> IsCompact.image <| hu_S ) ) <| Set.mem_image_of_mem _ ha
    have h_r_lt_uS_a : r < u_S a := by
      linarith
    exact h_r_lt_uS_a
  have hU_bestResponse_eventually : ∀ᶠ μ in nhds μ₀, bestResponse u_R μ ⊆ U := by
    have := bestResponse_upperHemicontinuous hu_R;
    exact UpperHemicontinuous.forall_isOpen this μ₀ U hU_open hU_bestResponse
  have h_lowerEnvelope_eventually : ∀ᶠ μ in nhds μ₀, lowerEnvelope u_R u_S μ > r := by
    filter_upwards [ hU_bestResponse_eventually ] with μ hμ
    have h_lowerEnvelope_eventually : lowerEnvelope u_R u_S μ = sInf (u_S '' bestResponse u_R μ) := by
      rfl
    rw [h_lowerEnvelope_eventually];
    have h_lowerEnvelope_eventually : ∃ a ∈ bestResponse u_R μ, ∀ b ∈ bestResponse u_R μ, u_S a ≤ u_S b := by
      have h_lowerEnvelope_eventually : IsCompact (bestResponse u_R μ) := by
        exact bestResponse_isCompact hu_R μ
      have := h_lowerEnvelope_eventually.exists_isMinOn ( bestResponse_nonempty hu_R μ ) hu_S.continuousOn;
      exact ⟨ this.choose, this.choose_spec.1, fun b hb => this.choose_spec.2 hb ⟩;
    obtain ⟨ a, ha₁, ha₂ ⟩ := h_lowerEnvelope_eventually; exact lt_of_lt_of_le ( hμ ha₁ ) ( le_csInf ( Set.Nonempty.image _ ⟨ a, ha₁ ⟩ ) ( Set.forall_mem_image.2 ha₂ ) ) ;
  exact h_lowerEnvelope_eventually.mono fun μ hμ => hμ

/-! ## Properties of the sender payoff correspondence -/

/--
The sender payoff correspondence is nonempty-valued.
-/
theorem senderPayoffCorr_nonempty (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (hu_S : Continuous u_S) (μ : Θ → ℝ) :
    (senderPayoffCorr u_R u_S μ).Nonempty := by
  refine' Set.nonempty_Icc.mpr _;
  apply_rules [ Real.sInf_le_sSup ];
  · exact IsCompact.bddBelow ( bestResponse_isCompact hu_R μ |> IsCompact.image <| hu_S );
  · exact IsCompact.bddAbove ( bestResponse_isCompact hu_R μ |> IsCompact.image <| hu_S )

/--
The sender payoff correspondence is compact-valued.
-/
theorem senderPayoffCorr_isCompact (μ : Θ → ℝ) :
    IsCompact (senderPayoffCorr u_R u_S μ) := by
  exact CompactIccSpace.isCompact_Icc

/--
The sender payoff correspondence is convex-valued.
-/
theorem senderPayoffCorr_convex (μ : Θ → ℝ) :
    Convex ℝ (senderPayoffCorr u_R u_S μ) := by
  exact convex_Icc _ _

/-- **Lemma K.1.** The interval-valued sender payoff correspondence is the
convex hull of the sender payoffs at receiver best responses. -/
theorem senderPayoffCorr_eq_convexHull
    (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (hu_S : Continuous u_S) (μ : Θ → ℝ) :
    senderPayoffCorr u_R u_S μ = convexHull ℝ (u_S '' bestResponse u_R μ) := by
  let S := u_S '' bestResponse u_R μ
  have hcompact : IsCompact S := (bestResponse_isCompact hu_R μ).image hu_S
  have hnonempty : S.Nonempty := (bestResponse_nonempty hu_R μ).image u_S
  have hle : sInf S ≤ sSup S :=
    Real.sInf_le_sSup S hcompact.bddBelow hcompact.bddAbove
  change Set.Icc (sInf S) (sSup S) = convexHull ℝ S
  apply Set.Subset.antisymm
  · rw [← Set.uIcc_of_le hle, ← segment_eq_uIcc]
    exact (convex_convexHull ℝ S).segment_subset
      (subset_convexHull ℝ S (hcompact.sInf_mem hnonempty))
      (subset_convexHull ℝ S (hcompact.sSup_mem hnonempty))
  · exact convexHull_min
      (fun _ hx => ⟨csInf_le hcompact.bddBelow hx, le_csSup hcompact.bddAbove hx⟩)
      (convex_Icc _ _)

/--
The sender payoff correspondence is upper hemicontinuous.
-/
theorem senderPayoffCorr_upperHemicontinuous (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (hu_S : Continuous u_S) :
    UpperHemicontinuous (senderPayoffCorr u_R u_S) := by
  -- Given Icc (lE μ₀) (uE μ₀) ⊆ U with U open:
  have h_upper_hemi : ∀ μ₀ : Θ → ℝ, ∀ U : Set ℝ, IsOpen U → senderPayoffCorr u_R u_S μ₀ ⊆ U → ∀ᶠ μ in nhds μ₀, senderPayoffCorr u_R u_S μ ⊆ U := by
    intro μ₀ U hU hU';
    -- Since $U$ is open and contains the sender payoff correspondence at $\mu_0$, there exists an $\epsilon > 0$ such that $(lowerEnvelope u_R u_S \mu_0 - \epsilon, upperEnvelope u_R u_S \mu_0 + \epsilon) \subseteq U$.
    obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ x, lowerEnvelope u_R u_S μ₀ - ε < x ∧ x < upperEnvelope u_R u_S μ₀ + ε → x ∈ U := by
      rcases Metric.isOpen_iff.1 hU ( lowerEnvelope u_R u_S μ₀ ) ( hU' ( Set.left_mem_Icc.2 <| by
        apply_rules [ Real.sInf_le_sSup ];
        · exact IsCompact.bddBelow ( bestResponse_isCompact hu_R μ₀ |> IsCompact.image <| hu_S );
        · exact IsCompact.bddAbove ( bestResponse_isCompact hu_R μ₀ |> IsCompact.image <| hu_S ) ) ) with ⟨ ε₁, ε₁pos, hε₁ ⟩
      rcases Metric.isOpen_iff.1 hU ( upperEnvelope u_R u_S μ₀ ) ( hU' ( Set.right_mem_Icc.2 <| by
        apply_rules [ csInf_le_csSup ];
        · exact IsCompact.bddBelow ( bestResponse_isCompact hu_R μ₀ |> IsCompact.image <| hu_S );
        · exact IsCompact.bddAbove ( bestResponse_isCompact hu_R μ₀ |> IsCompact.image <| hu_S );
        · exact Set.Nonempty.image _ ( bestResponse_nonempty hu_R μ₀ ) ) ) with ⟨ ε₂, ε₂pos, hε₂ ⟩
      use min ε₁ ε₂
      simp [ε₁pos, ε₂pos];
      intro x hx₁ hx₂
      by_cases hx : x ≤ lowerEnvelope u_R u_S μ₀;
      · exact hε₁ (Metric.mem_ball.mpr (abs_lt.mpr
          ⟨by linarith [min_le_left ε₁ ε₂], by linarith [min_le_left ε₁ ε₂]⟩));
      · by_cases hx' : x ≥ upperEnvelope u_R u_S μ₀;
        · exact hε₂ (Metric.mem_ball.mpr (abs_lt.mpr
            ⟨by linarith [min_le_left ε₁ ε₂, min_le_right ε₁ ε₂],
             by linarith [min_le_left ε₁ ε₂, min_le_right ε₁ ε₂]⟩));
        · exact hU' ⟨ by linarith, by linarith ⟩;
    obtain ⟨V, hV⟩ : ∃ V ∈ nhds μ₀,
        ∀ μ ∈ V, lowerEnvelope u_R u_S μ > lowerEnvelope u_R u_S μ₀ - ε ∧
          upperEnvelope u_R u_S μ < upperEnvelope u_R u_S μ₀ + ε := by
      have h_lower : ∀ᶠ μ in nhds μ₀, lowerEnvelope u_R u_S μ > lowerEnvelope u_R u_S μ₀ - ε := by
        have := lowerEnvelope_lowerSemicontinuous hu_R hu_S;
        exact this μ₀ ( lowerEnvelope u_R u_S μ₀ - ε ) ( by linarith )
      have h_upper : ∀ᶠ μ in nhds μ₀, upperEnvelope u_R u_S μ < upperEnvelope u_R u_S μ₀ + ε := by
        have := upperEnvelope_upperSemicontinuous hu_R hu_S μ₀ ( upperEnvelope u_R u_S μ₀ + ε ) ( lt_add_of_pos_right _ hε.1 );
        exact this
      exact ⟨_, Filter.inter_mem h_lower h_upper, fun μ hμ => ⟨hμ.1, hμ.2⟩⟩;
    filter_upwards [ hV.1 ] with μ hμ;
    exact fun x hx => hε.2 x
      ⟨by linarith [hV.2 μ hμ, hx.1], by linarith [hV.2 μ hμ, hx.2]⟩;
  intro μ₀ U hU;
  rcases mem_nhdsSet_iff_exists.mp hU with ⟨ V, hV₁, hV₂ ⟩;
  filter_upwards [h_upper_hemi μ₀ V hV₁ hV₂.1] with μ hμ using
    mem_nhdsSet_iff_exists.mpr ⟨V, hV₁, hμ, hV₂.2⟩

/-- **Lemma K.1 (best-response payoff correspondence).** Under continuity of
the sender's and receiver's payoffs on a nonempty compact Hausdorff action
space, the convex hull of sender payoffs at receiver best responses is
nonempty-, compact-, and convex-valued and upper hemicontinuous. Its upper and
lower envelopes are upper and lower semicontinuous, respectively. -/
theorem bestResponse_payoff_correspondence
    (hu_R : ∀ θ : Θ, Continuous fun a => u_R a θ)
    (hu_S : Continuous u_S) :
    (∀ μ : Θ → ℝ,
      senderPayoffCorr u_R u_S μ = convexHull ℝ (u_S '' bestResponse u_R μ) ∧
      (senderPayoffCorr u_R u_S μ).Nonempty ∧
      IsCompact (senderPayoffCorr u_R u_S μ) ∧
      Convex ℝ (senderPayoffCorr u_R u_S μ)) ∧
    UpperHemicontinuous (senderPayoffCorr u_R u_S) ∧
    UpperSemicontinuous (upperEnvelope u_R u_S) ∧
    LowerSemicontinuous (lowerEnvelope u_R u_S) := by
  refine ⟨?_, senderPayoffCorr_upperHemicontinuous hu_R hu_S,
    upperEnvelope_upperSemicontinuous hu_R hu_S,
    lowerEnvelope_lowerSemicontinuous hu_R hu_S⟩
  intro μ
  exact ⟨senderPayoffCorr_eq_convexHull hu_R hu_S μ,
    senderPayoffCorr_nonempty hu_R hu_S μ,
    senderPayoffCorr_isCompact μ,
    senderPayoffCorr_convex μ⟩

end CPD
