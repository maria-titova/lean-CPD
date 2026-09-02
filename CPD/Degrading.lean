import CPD.Theorem4
import CPD.CoalitionProof
import CPD.COE

/-!
# Payoff Degradation

Formalizes Section 6.4 of the paper. These are sufficient conditions for
existence that constrain only the lower envelope `v̲` of the payoff
correspondence `V`. The common mechanism is **payoff degradation (PD)**
(Definition 18): the ability to re-price a coalition's payoff `w` down to any
`w' ∈ [v_min, w]` while keeping its type set `C` fixed, in every restricted
game `G|_R`. We record this abstract property and show it forces every
greedy run to halt only once it covers `Θ`, so a coalition-proof PBE exists
(Theorem 5, `degrade_halts`). We then give a sufficient condition for PD:
cheap-talk copies (M-CT) together with **decomposability** (Definition 20,
`degrade_general`). The remaining sufficient conditions, **free disposal**
(Definition 19) and **revelation aversion** (Definition 21), and their
existence corollaries, live in `ExistenceDegrading`.

* `DegradationProperty` — payoff degradation (Definition 18, PD).
* `degrade_halts` — PD implies existence of a coalition-proof PBE
  (Theorem 5).
* `Degradable` — decomposability of `V` (Definition 20).
* `FreeDisposal` — free disposal (Definition 19).
* `RevelationAverse` — revelation aversion (Definition 21).
* `degrade_general` — cheap-talk copies + decomposable ⇒ PD (Proposition 4).
-/

open Set
open scoped Classical

set_option maxHeartbeats 1000000

namespace CPD

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable (G : DisclosureGame T Msg)

/-- The point mass `δ_θ` on `θ`. -/
noncomputable def pointMass (θ : T) : T → ℝ := fun θ' => if θ' = θ then 1 else 0

/-- **Definition 20** (decomposable): `V` is decomposable if every belief `q`
with `v̄(q) ≥ w' ≥ v_min` is a convex combination of beliefs, each supported
inside `supp q` and paying `w'`. -/
def Degradable : Prop :=
  ∀ q ∈ simplexOn G.Θ, ∀ w' ∈ Set.Icc G.vMin (G.vbar q),
    q ∈ convexHull ℝ
      {μ | μ ∈ simplexOn G.Θ ∧ simplexSupport μ ⊆ simplexSupport q ∧ w' ∈ G.V μ}

/-- **Definition 19** (free disposal): the lower envelope is constant at the
floor, `v̲(μ) = v_min` for every `μ`. -/
def FreeDisposal : Prop := ∀ μ ∈ simplexOn G.Θ, G.vlow μ = G.vMin

/-- **Definition 21** (revelation averse): `v̲(δ_θ) = v_min` for every
`θ ∈ Θ`. -/
def RevelationAverse : Prop := ∀ θ ∈ G.Θ, G.vlow (pointMass θ) = G.vMin

/-- **Definition 18** (payoff degradation, PD): in every restricted game
`G|_R`, every coalition `(C,σ,w)` can be re-priced down to any
`w' ∈ [v_min, w]` while keeping its type set `C`. This is the hypothesis of
`degrade_halts` (Theorem 5). -/
def DegradationProperty : Prop :=
  ∀ {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (K : Coalition (G.restrict R hne hsub)) (w' : ℝ),
    w' ∈ Set.Icc G.vMin K.w →
    ∃ K' : Coalition (G.restrict R hne hsub), K'.C = K.C ∧ K'.w = w'

variable {G}

/-! ## Infrastructure for `degrade_halts`

We build a *clamped greedy* partition by recursion, mirroring the COE
construction of `Theorem1` but realizing each cell payoff via degradation rather
than always taking the residual maximum.  Throughout we carry a fixed floor `vf`
(instantiated to `G.vMin`). -/

/-- The degradation property of a game `H`, with an explicit floor `vf`. -/
private def DegFloor (H : DisclosureGame T Msg) (vf : ℝ) : Prop :=
  ∀ {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ H.Θ)
    (K : Coalition (H.restrict R hne hsub)) (w' : ℝ),
    w' ∈ Set.Icc vf K.w →
    ∃ K' : Coalition (H.restrict R hne hsub), K'.C = K.C ∧ K'.w = w'

/-- A partition is **clamped** at ceiling `c` if each payoff `w_t` is the greatest
attainable payoff in the residual game subject to staying below the previous
payoff and (at `t = 0`) below `c`. -/
private def Clamped {g : DisclosureGame T Msg} (P : Partition g) (c : ℝ) : Prop :=
  ∀ t : Fin P.card,
    IsGreatest
      {w : ℝ | w ∈ P.stepPayoffs t ∧
        (∀ t' : Fin P.card, (t' : ℕ) + 1 = (t : ℕ) → w ≤ P.w t') ∧
        ((t : ℕ) = 0 → w ≤ c)} (P.w t)

/-
Every partition has at least one cell.
-/
private lemma deg_card_pos {g : DisclosureGame T Msg} (P : Partition g) : 0 < P.card := by
  by_contra! h;
  convert P.C_cover;
  simp +decide [ Finset.subset_iff ];
  exact ⟨ g.Θ_nonempty.choose, g.Θ_nonempty.choose_spec, fun i => by linarith [ Fin.pos i ] ⟩

/-! ### Transport helpers (along equalities of games) -/

/-- Transport a strategy along an equality of games, preserving evidence and beliefs. -/
private lemma deg_strategy_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂)
    (s : Strategy g₁) :
    ∃ s' : Strategy g₂, s'.evidence = s.evidence ∧
      ∀ m, s'.coalitionBelief m = s.coalitionBelief m := by
  subst h; exact ⟨s, rfl, fun _ => rfl⟩

/-- Transport a coalition along an equality of games, preserving cell and payoff. -/
private lemma deg_coalition_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂)
    (K : g₁.Coalition) :
    ∃ K' : g₂.Coalition, K'.C = K.C ∧ K'.w = K.w := by
  subst h; exact ⟨K, rfl, rfl⟩

/-- Coalition-payoff sets agree for equal games. -/
private lemma deg_coalitionPayoffs_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂) :
    g₁.coalitionPayoffs = g₂.coalitionPayoffs := by
  subst h; rfl

/-! ### Floor lemmas -/

/-
The global floor `v_min` lower-bounds the lower envelope on `ΔΘ`.
-/
private lemma deg_vMin_le_vlow {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.vMin ≤ G.vlow μ := by
  -- Since `vMin` is the infimum of `vlow` over the simplex, and `μ` is in the simplex, we have `vMin ≤ vlow μ`.
  have h_inf : G.vMin ≤ G.vlow μ := by
    have h_inf : ∀ x ∈ G.vlow '' simplexOn G.Θ, G.vMin ≤ x := by
      intros x hx
      obtain ⟨μ, hμ, rfl⟩ := hx;
      have := G.vlow_lowerSemicontinuousOn;
      obtain ⟨ν, hν⟩ : ∃ ν ∈ simplexOn G.Θ, IsMinOn G.vlow (simplexOn G.Θ) ν := by
        apply_rules [ LowerSemicontinuousOn.exists_isMinOn ];
        · exact ⟨ _, hμ ⟩;
        · exact isCompact_simplexOn G.Θ;
      exact le_trans ( csInf_le ⟨ G.vlow ν, Set.forall_mem_image.2 fun x hx => hν.2 hx ⟩ ⟨ ν, hν.1, rfl ⟩ ) ( hν.2 hμ )
    exact h_inf _ ( Set.mem_image_of_mem _ hμ );
  exact h_inf

/-
Every coalition payoff is at least the floor.
-/
private lemma coalition_w_ge {H : DisclosureGame T Msg} {vf : ℝ}
    (hvf : ∀ μ ∈ simplexOn H.Θ, vf ≤ H.vlow μ) (K : Coalition H) : vf ≤ K.w := by
  have h_coalition_nonempty : (H.preimageSetFull K.σ.evidence).Nonempty := by
    exact K.preimage_eq.symm ▸ K.C_nonempty;
  obtain ⟨θ, hθ⟩ : ∃ θ ∈ H.preimageSetFull K.σ.evidence, ∃ m ∈ K.σ.evidence, m ∈ H.M θ := by
    exact Exists.elim h_coalition_nonempty fun x hx => ⟨ x, by aesop, by obtain ⟨ m, hm ⟩ := Finset.mem_filter.mp hx |>.2; exact ⟨ m, by aesop ⟩ ⟩;
  obtain ⟨m, hm₁, hm₂⟩ := hθ.right
  have h_coalitionBelief : K.σ.coalitionBelief m ∈ simplexOn H.Θ := by
    convert zeroExt_mem_simplex ( K.C_subset ) ( K.σ.belief_mem_simplex hm₁ ) using 1
  have h_vlow : H.vlow (K.σ.coalitionBelief m) ≤ K.w := by
    have := K.payoff m hm₁; simp_all +decide [ DisclosureGame.vlow ] ;
    exact csInf_le ( H.V_isCompact _ ( by exact ⟨ h_coalitionBelief.1, h_coalitionBelief.2.1, h_coalitionBelief.2.2 ⟩ ) |> IsCompact.bddBelow ) this
  exact le_trans (hvf (K.σ.coalitionBelief m) h_coalitionBelief) h_vlow

/-
The floor property passes to restricted games.
-/
private lemma hvf_restrict {H : DisclosureGame T Msg} {vf : ℝ}
    (hvf : ∀ μ ∈ simplexOn H.Θ, vf ≤ H.vlow μ) {S : Finset T}
    (hSne : S.Nonempty) (hSsub : S ⊆ H.Θ) :
    ∀ μ ∈ simplexOn (H.restrict S hSne hSsub).Θ, vf ≤ (H.restrict S hSne hSsub).vlow μ := by
  -- Let's unfold the definition of `vlow` to use the hypothesis `hvf`.
  unfold DisclosureGame.vlow at hvf ⊢;
  intro μ hμ;
  convert hvf μ _ using 1;
  convert simplexOn_mono hSsub hμ using 1

/-
The degradation property passes to restricted games (same floor).
-/
private lemma DegFloor_restrict {H : DisclosureGame T Msg} {vf : ℝ}
    (hdeg : DegFloor H vf) {S : Finset T} (hSne : S.Nonempty) (hSsub : S ⊆ H.Θ) :
    DegFloor (H.restrict S hSne hSsub) vf := by
  intro R hRne hRsub K w' hw';
  obtain ⟨ K0, hK0C, hK0w ⟩ := deg_coalition_of_eq ( DisclosureGame.restrict_restrict hSne hSsub hRne hRsub ) K;
  obtain ⟨ K1, hK1C, hK1w ⟩ := hdeg hRne ( by
    grind +splitImp ) K0 w' ⟨ hw'.1, by
    linarith [ hw'.2 ] ⟩;
  obtain ⟨ K2, hK2C, hK2w ⟩ := deg_coalition_of_eq ( DisclosureGame.restrict_restrict hSne hSsub hRne hRsub |> Eq.symm ) K1; use K2; aesop;

/-
**Realizability.** Any value in `[vf, max 𝒲_H]` is an attainable coalition
payoff of `H`.
-/
private lemma exists_coalition_w {H : DisclosureGame T Msg} {vf : ℝ}
    (hdeg : DegFloor H vf) (hvf : ∀ μ ∈ simplexOn H.Θ, vf ≤ H.vlow μ)
    {w : ℝ} (hwlo : vf ≤ w) (hwhi : w ≤ sSup H.coalitionPayoffs) :
    ∃ K : Coalition H, K.w = w := by
  obtain ⟨Kmax, hKmax⟩ : ∃ Kmax : Coalition H, Kmax.w = sSup H.coalitionPayoffs := by
    convert ( IsCompact.sSup_mem ( H.isCompact_coalitionPayoffs ) ( H.coalitionPayoffs_nonempty ) ) using 1;
  have := hdeg H.Θ_nonempty ( subset_rfl );
  obtain ⟨K0, hK0⟩ : ∃ K0 : Coalition (H.restrict H.Θ H.Θ_nonempty subset_rfl), K0.w = Kmax.w := by
    grind +suggestions;
  obtain ⟨K1, hK1⟩ : ∃ K1 : Coalition (H.restrict H.Θ H.Θ_nonempty subset_rfl), K1.w = w := by
    exact this K0 w ⟨ hwlo, by linarith ⟩ |> fun ⟨ K1, hK1 ⟩ => ⟨ K1, hK1.2 ⟩;
  have := deg_coalition_of_eq ( DisclosureGame.restrict_self ) K1; aesop;

/-- **Realizability in the residual game.** -/
private lemma mem_cp_of_Icc {H : DisclosureGame T Msg} {vf : ℝ}
    (hdeg : DegFloor H vf) (hvf : ∀ μ ∈ simplexOn H.Θ, vf ≤ H.vlow μ)
    {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ H.Θ) {w : ℝ}
    (hwlo : vf ≤ w) (hwhi : w ≤ sSup (H.restrict R hne hsub).coalitionPayoffs) :
    w ∈ (H.restrict R hne hsub).coalitionPayoffs := by
  obtain ⟨K, hK⟩ :=
    exists_coalition_w (DegFloor_restrict hdeg hne hsub) (hvf_restrict hvf hne hsub)
      (w := w) hwlo (by simpa using hwhi)
  exact ⟨K, hK⟩

/-! ### Structural prepend (cf. `Theorem1.exists_prependP`) -/

/-- Construct the prepended partition (structure only), matching cells/payoffs and
residuals index-by-index to `K` (level 0) and `P'` (later levels). -/
private lemma deg_exists_prependP (H : DisclosureGame T Msg) (K : H.Coalition)
    (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ)
    (P' : Partition (H.restrict (H.Θ \ K.C) hne hsub)) :
    ∃ P : Partition H, P.card = P'.card + 1 ∧
      (∀ t : Fin P.card, (t : ℕ) = 0 → thetaStep P.C t = H.Θ ∧ P.w t = K.w) ∧
      (∀ (t : Fin P.card) (j : Fin P'.card), (t : ℕ) = (j : ℕ) + 1 →
        thetaStep P.C t = thetaStep P'.C j ∧ P.w t = P'.w j) := by
  refine' ⟨ _, _, _, _ ⟩;
  use P'.card + 1;
  exact fun t => Fin.cases K.C ( fun j => P'.C j ) t;
  all_goals norm_num [ Fin.forall_fin_succ, Fin.exists_fin_succ, thetaStep ];
  exact ⟨ K.C_nonempty, fun i => P'.C_nonempty i ⟩;
  exact ⟨ fun i hi => Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( P'.C_subset i hx' ) |>.2 hx, fun i => ⟨ Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( P'.C_subset i hx ) |>.2 hx', fun j hj => P'.C_disjoint i j hj ⟩ ⟩;
  exact ⟨ K.C_subset, fun i => P'.C_subset i |> Finset.Subset.trans <| Finset.sdiff_subset ⟩;
  rotate_left;
  exact fun t => Fin.cases K.σ ( fun j => ( deg_strategy_of_eq ( restrict_restrict hne hsub ( P'.C_nonempty j ) ( P'.C_subset j ) ) ( P'.σ j ) ).choose ) t;
  exact fun t => Fin.cases K.w ( fun j => P'.w j ) t;
  all_goals norm_num [ Fin.forall_fin_succ, Fin.exists_fin_succ, Finset.ext_iff, Set.ext_iff ] at *;
  · constructor;
    · convert K.exclusive using 1;
      simp +decide [ Finset.ext_iff, Set.ext_iff, DisclosureGame.preimageSet, DisclosureGame.preimageSetFull ];
      intro a ha; constructor <;> intro h <;> contrapose! ha <;> simp_all +decide [ Fin.exists_fin_succ, Finset.ext_iff, Set.ext_iff ] ;
      · exact False.elim ( ha ( K.C_subset ( h.elim ( fun h => h ) fun ⟨ i, hi ⟩ => P'.C_subset i hi |> fun h => by aesop ) ) );
      · intro m hm; specialize ha 0; simp_all +decide [ Fin.cases ] ;
        intro hm';
        have := K.exclusive; simp_all +decide [ Finset.ext_iff, Set.ext_iff, DisclosureGame.preimageSet, DisclosureGame.preimageSetFull ] ;
        exact ha ( this ( Finset.mem_filter.mpr ⟨ h, ⟨ m, by aesop ⟩ ⟩ ) );
    · intro i;
      have := P'.exclusive i;
      convert this using 1;
      ext; simp [preimageSet];
      constructor <;> intro h;
      · obtain ⟨ ⟨ j, hj₁, hj₂ ⟩, hj₃ ⟩ := h;
        rcases j with ⟨ _ | j, hj ⟩ <;> simp_all +decide [ Fin.ext_iff, thetaStep ];
        refine' ⟨ ⟨ ⟨ j, by linarith ⟩, _, _ ⟩, _ ⟩;
        · exact Nat.le_of_succ_le_succ hj₁;
        · exact hj₂;
        · convert hj₃ using 1;
          grind +suggestions;
      · refine' ⟨ ⟨ Fin.succ i, _, _ ⟩, _ ⟩ <;> simp_all +decide [ thetaStep ];
        · obtain ⟨ ⟨ j, hj₁, hj₂ ⟩, hj₃ ⟩ := h;
          exact this ( by
            exact Finset.mem_filter.mpr ⟨ Finset.mem_biUnion.mpr ⟨ j, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj₁ ⟩, hj₂ ⟩, hj₃ ⟩ );
        · convert h.2 using 1;
          grind;
  · refine' ⟨ K.payoff, _ ⟩;
    intro i m hm
    have := P'.payoff i m
    simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    grind;
  · intro a;
    constructor;
    · rintro ( ha | ⟨ i, ha ⟩ ) <;> [ exact K.C_subset ha; exact P'.C_subset i ha |> fun h => hsub h ];
    · intro ha
      by_cases haK : a ∈ K.C;
      · exact Or.inl haK;
      · have := P'.cover_eq;
        replace this := Finset.ext_iff.mp this a; aesop;
  · intro i j hij; simp +decide [ Fin.ext hij ] ;
  · intro θ hθ;
    by_cases hθK : θ ∈ K.C;
    · exact Finset.mem_biUnion.mpr ⟨ ⟨ 0, Nat.succ_pos _ ⟩, Finset.mem_univ _, by simpa using hθK ⟩;
    · have := P'.cover_eq;
      replace this := Finset.ext_iff.mp this θ; simp_all +decide [ Finset.mem_biUnion ] ;
      exact ⟨ Fin.succ this.choose, this.choose_spec ⟩

/-! ### The clamped partition exists -/

/-
The single-cell clamped partition when the chosen cell exhausts `H.Θ`.
-/
private lemma deg_single_cell (H : DisclosureGame T Msg) (K : H.Coalition)
    (hempty : H.Θ \ K.C = ∅) (c : ℝ)
    (hmem : K.w ∈ H.coalitionPayoffs) (hle : K.w ≤ c)
    (hgreatest : ∀ w ∈ H.coalitionPayoffs, w ≤ c → w ≤ K.w) :
    ∃ P : Partition H, Clamped P c := by
  refine' ⟨ _, _ ⟩;
  refine' ⟨ 1, fun _ => K.C, _, _, _, _, fun _ => K.σ, fun _ => K.w, _, _ ⟩ <;> norm_num;
  all_goals norm_num [ Fin.forall_fin_succ, thetaStep ] at *;
  lia;
  exact fun θ hθ => by simp_all +decide [ DisclosureGame.preimageSet ] ;
  grind +suggestions;
  intro t; fin_cases t; simp +decide [ Clamped ] ;
  refine' ⟨ _, fun w hw => _ ⟩ <;> simp_all +decide [ Partition.stepPayoffs ];
  · convert hmem using 1;
    convert deg_coalitionPayoffs_of_eq _;
    convert DisclosureGame.restrict_self;
    simp +decide [ thetaStep ];
    exact Finset.Subset.antisymm K.C_subset ( by rw [ Finset.sdiff_eq_empty_iff_subset ] at hempty; exact hempty );
  · convert hgreatest w _ hw.2;
    convert hw.1 using 1;
    convert deg_coalitionPayoffs_of_eq _;
    convert DisclosureGame.restrict_self;
    convert DisclosureGame.Partition.restrict_eq_of_eq _ _ _ _ _ using 1;
    rotate_left;
    exact H.Θ;
    all_goals norm_num [ thetaStep ];
    grind +suggestions;
    exact H.Θ_nonempty;
    exact fun x hx => by_contra fun hx' => Finset.notMem_empty x ( hempty ▸ Finset.mem_sdiff.mpr ⟨ hx, hx' ⟩ );
    grind +suggestions

/-
The prepended partition is clamped at ceiling `c`.
-/
private lemma prepend_isClamped (H : DisclosureGame T Msg) (K : H.Coalition)
    (c : ℝ)
    (hmem : K.w ∈ H.coalitionPayoffs) (hle : K.w ≤ c)
    (hgreatest : ∀ w ∈ H.coalitionPayoffs, w ≤ c → w ≤ K.w)
    (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ)
    (P' : Partition (H.restrict (H.Θ \ K.C) hne hsub)) (hP' : Clamped P' K.w)
    (P : Partition H) (hcard : P.card = P'.card + 1)
    (h0 : ∀ t : Fin P.card, (t : ℕ) = 0 → thetaStep P.C t = H.Θ ∧ P.w t = K.w)
    (hsucc : ∀ (t : Fin P.card) (j : Fin P'.card), (t : ℕ) = (j : ℕ) + 1 →
        thetaStep P.C t = thetaStep P'.C j ∧ P.w t = P'.w j) :
    Clamped P c := by
  intro t
  by_cases ht : t.val = 0;
  · have h_stepPayoffs : P.stepPayoffs t = H.coalitionPayoffs := by
      have h_stepPayoffs : P.stepPayoffs t = (H.restrict (H.Θ) (by
      exact ⟨ _, H.Θ_nonempty.choose_spec ⟩) (by
      exact Set.Subset.rfl)).coalitionPayoffs := by
        unfold Partition.stepPayoffs; aesop;
      generalize_proofs at *;
      rw [ h_stepPayoffs, deg_coalitionPayoffs_of_eq ( DisclosureGame.restrict_self ) ];
    simp_all +decide [ IsGreatest, mem_upperBounds ];
  · obtain ⟨j, hj⟩ : ∃ j : Fin P'.card, t.val = j.val + 1 := by
      exact ⟨ ⟨ t - 1, by omega ⟩, by simp +decide [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ht ) ] ⟩;
    have h_stepPayoffs : P.stepPayoffs t = P'.stepPayoffs j := by
      unfold Partition.stepPayoffs; simp +decide [ hsucc t j hj ] ;
      rw [ DisclosureGame.restrict_restrict ];
    convert hP' j using 1;
    · ext w;
      constructor <;> intro h <;> simp_all +decide [ Fin.ext_iff ];
      · constructor;
        · intro t' ht';
          convert h.2 ⟨ t'.val + 1, by linarith [ Fin.is_lt t', Fin.is_lt j ] ⟩ ( by simp +decide [ ht' ] ) using 1;
          exact hsucc ⟨ t'.val + 1, by linarith [ Fin.is_lt t', Fin.is_lt j ] ⟩ t' ( by simp +decide [ ht' ] ) |>.2.symm;
        · intro hj0
          have h_t' : ∃ t' : Fin P.card, t'.val = 0 := by
            exact ⟨ ⟨ 0, by linarith [ Fin.is_lt t ] ⟩, rfl ⟩;
          grind;
      · intro t' ht';
        by_cases hj0 : j.val = 0;
        · grind +qlia;
        · obtain ⟨j', hj'⟩ : ∃ j' : Fin P'.card, j'.val + 1 = j.val := by
            exact ⟨ ⟨ j - 1, by omega ⟩, by simp +decide [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hj0 ) ] ⟩;
          grind +qlia;
    · exact hsucc t j hj |>.2

/-
**Existence of a clamped partition** for any game with the degradation
property and a valid floor.
-/
private lemma exists_clamped (H : DisclosureGame T Msg) (vf : ℝ)
    (hdeg : DegFloor H vf) (hvf : ∀ μ ∈ simplexOn H.Θ, vf ≤ H.vlow μ)
    (c : ℝ) (hc : vf ≤ c) :
    ∃ P : Partition H, Clamped P c := by
  induction' n : H.Θ.card using Nat.strong_induction_on with n ih generalizing H c;
  obtain ⟨K, hK⟩ : ∃ K : Coalition H, K.w = min (sSup H.coalitionPayoffs) c := by
    apply exists_coalition_w hdeg hvf;
    · obtain ⟨Kmax, hKmax⟩ : ∃ Kmax : Coalition H, Kmax.w = sSup H.coalitionPayoffs := by
        exact ( isCompact_coalitionPayoffs H ).sSup_mem (DisclosureGame.coalitionPayoffs_nonempty H);
      exact le_min ( hKmax ▸ coalition_w_ge hvf Kmax ) hc;
    · exact min_le_left _ _;
  by_cases hempty : H.Θ \ K.C = ∅;
  · apply deg_single_cell;
    any_goals tauto;
    · exact hK.symm ▸ min_le_right _ _;
    · exact fun w hw hw' => hK.symm ▸ le_min ( le_csSup ( H.isCompact_coalitionPayoffs.bddAbove ) hw ) hw';
  · have hcard : (H.Θ \ K.C).card < H.Θ.card := by
      rw [ Finset.card_sdiff ];
      exact Nat.sub_lt ( Finset.card_pos.mpr ⟨ _, H.Θ_nonempty.choose_spec ⟩ ) ( Finset.card_pos.mpr ⟨ _, Finset.mem_inter.mpr ⟨ K.C_nonempty.choose_spec, K.C_nonempty.choose_spec |> fun h => K.C_subset h ⟩ ⟩ );
    obtain ⟨P', hP'⟩ : ∃ P' : Partition (H.restrict (H.Θ \ K.C) (Finset.nonempty_of_ne_empty hempty) (Finset.sdiff_subset)), Clamped P' K.w := by
      apply ih (H.Θ \ K.C).card (by
      linarith) (H.restrict (H.Θ \ K.C) (Finset.nonempty_of_ne_empty hempty) (Finset.sdiff_subset)) (DegFloor_restrict hdeg (Finset.nonempty_of_ne_empty hempty) (Finset.sdiff_subset)) (hvf_restrict hvf (Finset.nonempty_of_ne_empty hempty) (Finset.sdiff_subset)) K.w (by
      exact coalition_w_ge hvf K) (by
      rfl);
    obtain ⟨P, hP⟩ : ∃ P : Partition H, P.card = P'.card + 1 ∧ (∀ t : Fin P.card, (t : ℕ) = 0 → thetaStep P.C t = H.Θ ∧ P.w t = K.w) ∧ (∀ (t : Fin P.card) (j : Fin P'.card), (t : ℕ) = (j : ℕ) + 1 → thetaStep P.C t = thetaStep P'.C j ∧ P.w t = P'.w j) := by
      apply deg_exists_prependP H K (Finset.nonempty_of_ne_empty hempty) (Finset.sdiff_subset) P';
    refine' ⟨ P, prepend_isClamped H K c _ _ _ _ _ P' hP' P hP.1 hP.2.1 hP.2.2 ⟩;
    · exact ⟨ K, rfl ⟩;
    · exact hK.symm ▸ min_le_right _ _;
    · intro w hw hw'; rw [ hK ] ; exact le_min ( le_csSup ( by exact H.isCompact_coalitionPayoffs.bddAbove ) hw ) hw';

/-! ### Clamped ⇒ greedy -/

/-
A clamped partition has antitone payoffs.
-/
private lemma clamped_antitone {g : DisclosureGame T Msg} {P : Partition g} {c : ℝ}
    (h : Clamped P c) : Antitone P.w := by
  intro i j hij;
  induction' j with j hj generalizing i;
  induction' j with j ih generalizing i;
  · rw [ le_antisymm hij ( Nat.zero_le _ ) ];
  · cases hij.eq_or_lt <;> simp_all +decide [ Fin.le_iff_val_le_val ];
    exact le_trans ( h ⟨ j + 1, hj ⟩ |>.1.2.1 ⟨ j, by linarith ⟩ rfl ) ( ih ( by linarith ) ( Nat.le_of_lt_succ ‹_› ) )

/-
Residual greedy lower bounds are antitone along the partition.
-/
private lemma greedyLower_anti {g : DisclosureGame T Msg} (P : Partition g)
    {s t : Fin P.card} (hst : (s : ℕ) ≤ (t : ℕ)) :
    P.greedyLower t ≤ P.greedyLower s := by
  refine' Finset.sup'_le _ _ _;
  intro b hb
  have h_subset : thetaStep P.C t ⊆ thetaStep P.C s := by
    simp +decide [ thetaStep ];
    exact fun x hx => Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_trans hst hx ⟩ );
  exact Finset.le_sup' ( fun x => g.skeptical x ) ( h_subset hb )

/-
A clamped partition with a non-binding ceiling is greedy.
-/
private lemma clamped_isGreedy (hdeg : G.DegradationProperty) (P : Partition G)
    {c : ℝ} (hceil : ∀ w ∈ P.stepPayoffs ⟨0, deg_card_pos P⟩, w ≤ c)
    (hcl : Clamped P c) : P.IsGreedy := by
  intro t
  unfold Clamped at hcl
  refine ⟨?_, ?_⟩;
  · exact ⟨ hcl t |>.1.1, by
      induction' t with t ih;
      induction' t with t ih;
      · refine' le_trans _ ( hcl ⟨ 0, ih ⟩ |>.2 ⟨ _, fun t' ht' => _, _ ⟩ );
        exact P.greedyLower_le_stepMax ⟨ 0, ih ⟩;
        · exact P.isGreatest_stepMax _ |>.1;
        · cases ht';
        · exact fun _ => hceil _ ( P.isGreatest_stepMax ⟨ 0, ih ⟩ |>.1 );
      · by_cases h : P.stepMax ⟨t + 1, ih⟩ ≤ P.w ⟨t, by linarith⟩;
        · have := hcl ⟨ t + 1, ih ⟩;
          exact le_trans ( P.greedyLower_le_stepMax _ ) ( this.2 ⟨ P.isGreatest_stepMax _ |>.1, fun t' ht' => by
            grind, by
            simp +decide ⟩ );
        · have h_mem : P.w ⟨t, by linarith⟩ ∈ P.stepPayoffs ⟨t + 1, ih⟩ := by
            apply mem_cp_of_Icc hdeg (fun μ hμ => deg_vMin_le_vlow hμ);
            · have := hcl ⟨ t, by linarith ⟩;
              obtain ⟨ K, hK ⟩ := this.1.1;
              exact hK ▸ coalition_w_ge ( hvf_restrict ( fun μ hμ => deg_vMin_le_vlow hμ ) _ _ ) K;
            · exact le_trans ( le_of_not_ge h ) ( le_rfl );
          have := hcl ⟨ t + 1, ih ⟩ |>.2 ⟨ h_mem, ?_, ?_ ⟩ <;> simp_all +decide [ Fin.ext_iff ];
          · exact le_trans ( greedyLower_anti P ( Nat.le_succ _ ) ) ( ih ( Nat.lt_of_succ_lt ‹_› ) ) |> le_trans <| this;
          · exact fun t' ht' => by rw [ show t' = ⟨ t, by linarith ⟩ from Fin.ext ht' ] ;, hcl t |>.1.2.1 ⟩;
  · intro w hw; have := hcl t; exact this.2 ⟨ hw.1, hw.2.2, fun ht => hceil _ ( by
      convert hw.1;
      exact ht.symm ) ⟩ ;

/-- **Theorem 5** (payoff degradation ⇒ existence): under the payoff
degradation property (PD), no run of the greedy algorithm halts short of
covering `Θ`, so `G` admits a greedy partition and a coalition-proof PBE
exists. -/
theorem degrade_halts (hdeg : G.DegradationProperty) :
    ∃ P : Partition G, P.IsCPPBEPartition := by
  obtain ⟨P, hcl⟩ : ∃ P : Partition G, Clamped P (sSup G.coalitionPayoffs) := by
    apply exists_clamped G G.vMin hdeg (fun μ hμ => deg_vMin_le_vlow hμ) (sSup G.coalitionPayoffs) (by
    obtain ⟨K, hK⟩ : ∃ K : G.Coalition, K.w = sSup G.coalitionPayoffs := by
      exact ( isCompact_coalitionPayoffs G ).sSup_mem ( coalitionPayoffs_nonempty G );
    exact hK ▸ coalition_w_ge ( fun μ hμ => G.deg_vMin_le_vlow hμ ) K);
  refine' ⟨ P, ( DisclosureGame.Partition.cppbe_characterization P ).mpr ( clamped_isGreedy hdeg P _ hcl ) ⟩;
  intro w hw
  have h_stepPayoffs : P.stepPayoffs ⟨0, deg_card_pos P⟩ = G.coalitionPayoffs := by
    rw [ DisclosureGame.Partition.stepPayoffs ];
    rw [ DisclosureGame.Partition.restrict_eq_of_eq ];
    convert deg_coalitionPayoffs_of_eq _;
    exact DisclosureGame.restrict_self;
    ext θ; simp [thetaStep];
    exact ⟨ fun ⟨ a, _, ha ⟩ => P.C_subset a ha, fun hθ => by rcases Finset.mem_biUnion.mp ( P.cover_eq.symm ▸ hθ ) with ⟨ a, _, ha ⟩ ; exact ⟨ a, Nat.zero_le _, ha ⟩ ⟩
  rw [h_stepPayoffs] at hw
  exact le_csSup (isCompact_coalitionPayoffs G).bddAbove hw

/-! ### Infrastructure for `degrade_general` -/

/-
**Realization.** Given a finite decomposition of the conditional prior on `C`
into beliefs `ν i` (supported in `C`, paying `w'`), each carried by a distinct
message `msg i` available to its support and exclusive to `C`, there is a
coalition of `H` with cell `C` and payoff `w'`.
-/
private lemma exists_coalition_realize (H : DisclosureGame T Msg)
    {C : Finset T} (hCne : C.Nonempty) (hCsub : C ⊆ H.Θ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (msg : ι → Msg)
    (hmsg_inj : Function.Injective msg)
    (lam : ι → ℝ) (ν : ι → (T → ℝ))
    (hlam : ∀ i, 0 < lam i)
    (hν : ∀ i, ν i ∈ simplexOn C)
    (hcons : ∀ θ, H.condPrior C θ = ∑ i, lam i * ν i θ)
    (havail : ∀ (i : ι) (θ : T), θ ∈ C → 0 < ν i θ → msg i ∈ H.M θ)
    (hpre : ∀ (i : ι) (θ : T), θ ∈ H.Θ → msg i ∈ H.M θ → θ ∈ C)
    (w' : ℝ) (hpay : ∀ i, w' ∈ H.V (ν i)) :
    ∃ K' : Coalition H, K'.C = C ∧ K'.w = w' := by
  obtain ⟨K', hK'⟩ : ∃ K' : Strategy (H.restrict C hCne hCsub), K'.evidence = Finset.univ.image (fun i => msg i) ∧ ∀ i, K'.coalitionBelief (msg i) = ν i := by
    refine' ⟨ ⟨ fun θ m => ( ∑ i, if msg i = m then lam i * ν i θ else 0 ) / H.condPrior C θ, _ ⟩, _, _ ⟩ <;> simp +decide [ Finset.sum_ite, hmsg_inj.eq_iff ];
    all_goals norm_num [ funext_iff, Finset.sum_ite, hmsg_inj.eq_iff ];
    all_goals norm_num [ Strategy.evidence, Strategy.coalitionBelief ];
    all_goals norm_num [ Set.ext_iff, Strategy.msgSupport, Strategy.belief, zeroExt ];
    all_goals norm_num [ Strategy.onPathProb, Finset.sum_div _ _ _ ];
    · intro θ hθ
      constructor;
      · intro m
        apply Finset.sum_nonneg
        intro i hi
        apply div_nonneg (mul_nonneg (le_of_lt (hlam i)) (by
        grind +suggestions)) (by
        exact hcons θ ▸ Finset.sum_nonneg fun _ _ => mul_nonneg ( le_of_lt ( hlam _ ) ) ( hν _ |>.1 _ ));
      · constructor;
        · rw [ ← Finset.sum_biUnion ];
          · rw [ ← Finset.sum_div _ _ _, div_eq_iff ];
            · rw [ one_mul, hcons ];
              rw [ show ( Finset.univ.biUnion fun x => { x_1 | msg x_1 = x } ) = Finset.univ from Finset.eq_univ_of_forall fun i => Finset.mem_biUnion.mpr ⟨ msg i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, rfl ⟩ ⟩ ];
            · exact ne_of_gt ( H.condPrior_pos hCne hCsub hθ );
          · exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
        · intro m hm;
          refine' Or.inl ( Finset.sum_eq_zero fun i hi => _ );
          contrapose! hm;
          exact havail i θ hθ ( lt_of_le_of_ne ( hν i |>.1 θ ) ( Ne.symm ( by aesop ) ) ) |> fun h => by aesop;
    · intro m; constructor <;> intro h <;> contrapose! h <;> simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, div_nonneg, mul_nonneg, le_of_lt ] ;
      intro i hi; specialize h; contrapose! h; simp_all +decide [ Finset.sum_ite, hmsg_inj.eq_iff ] ;
      -- Since $C$ is nonempty, there exists some $\theta \in C$.
      obtain ⟨θ, hθ⟩ : ∃ θ ∈ C, 0 < ν i θ := by
        have := hν i;
        exact Exists.elim ( show ∃ θ, ν i θ ≠ 0 from not_forall.mp fun h => by simp +decide [ h ] at this ) fun x hx => ⟨ x, by_contradiction fun hx' => hx <| this.2.2 x hx', lt_of_le_of_ne ( this.1 x ) ( Ne.symm hx ) ⟩;
      refine' ⟨ θ, hθ.1, _ ⟩;
      refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => div_nonneg ( mul_nonneg ( le_of_lt ( hlam x ) ) ( hν x |>.1 θ ) ) ( Finset.sum_nonneg fun i _ => mul_nonneg ( le_of_lt ( hlam i ) ) ( hν i |>.1 θ ) ) ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ i, hi ⟩ ) ) ; simp +decide [ *, ne_of_gt ];
      exact lt_of_lt_of_le ( mul_pos ( hlam i ) hθ.2 ) ( Finset.single_le_sum ( fun i _ => mul_nonneg ( le_of_lt ( hlam i ) ) ( hν i |>.1 θ ) ) ( Finset.mem_univ i ) );
    · intro i x; split_ifs <;> simp_all +decide [ Finset.sum_div _ _ _, mul_div_cancel₀, ne_of_gt ] ;
      simp +decide [ Finset.sum_filter, hmsg_inj.eq_iff, Finset.sum_div _ _ _, mul_div_cancel₀, ne_of_gt ( hlam _ ) ];
      rw [ mul_div_cancel₀ ];
      · rw [ Finset.sum_congr rfl fun x hx => by rw [ ← hcons x, mul_div_cancel₀ _ ( ne_of_gt ( show 0 < H.condPrior C x from by
                                                                                                  grind +suggestions ) ) ] ];
        rw [ ← Finset.mul_sum _ _ _, show ∑ x ∈ C, ν i x = 1 from by rw [ ← hν i |>.2.1, Finset.sum_subset ( Finset.subset_univ C ) fun x hx₁ hx₂ => hν i |>.2.2 x hx₂ ] ] ; simp +decide [ ne_of_gt ( hlam i ) ];
      · have h_pos : 0 < H.condPrior C x := by
          expose_names; exact condPrior_pos hCne hCsub h;
        exact ne_of_gt ( hcons x ▸ h_pos );
  refine' ⟨ ⟨ C, hCne, hCsub, K', _, w', _ ⟩, rfl, rfl ⟩;
  · intro θ hθ;
    simp_all +decide [ DisclosureGame.preimageSetFull ];
    simp_all +decide [ DisclosureGame.preimageSet ];
    obtain ⟨ m, hm ⟩ := hθ.2; aesop;
  · simp_all +decide [ Finset.ext_iff ]

/-
Affinely independent points of the probability simplex number at most `|T|`.
-/
private lemma affineIndep_simplex_card_le {s : Finset (T → ℝ)}
    (h : AffineIndependent ℝ ((↑) : s → (T → ℝ)))
    (hsum : ∀ x ∈ s, ∑ a, x a = 1) : s.card ≤ Fintype.card T := by
  -- If `s` were empty, the statement would hold trivially.
  by_cases hs_empty : s = ∅;
  · aesop;
  · have h_dim_le : Module.finrank ℝ (vectorSpan ℝ (Set.range (fun x : s => x.val))) ≤ Fintype.card T - 1 := by
      -- The vector span of the range of `x ↦ x.val` is contained in the hyperplane `W := LinearMap.ker (∑-functional)`.
      have h_span_subset_ker : vectorSpan ℝ (Set.range (fun x : s => x.val)) ≤ LinearMap.ker (∑ a : T, LinearMap.proj a) := by
        refine' Submodule.span_le.mpr _;
        rintro x ⟨ y, z, hy, hz, rfl ⟩;
        aesop;
      refine' le_trans ( Submodule.finrank_mono h_span_subset_ker ) _;
      have h_ker_dim : LinearMap.range (∑ a : T, LinearMap.proj a : (T → ℝ) →ₗ[ℝ] ℝ) = ⊤ := by
        ext x
        simp [LinearMap.mem_range];
        by_cases hT : Nonempty T;
        · exact ⟨ fun _ => x / Fintype.card T, by simp +decide [ mul_div_cancel₀, Fintype.card_pos_iff ] ⟩;
        · simp_all +decide [ Finset.eq_empty_of_isEmpty ];
          exact False.elim ( hs_empty ( Finset.eq_empty_of_forall_notMem fun x hx => hsum x hx ) );
      have := LinearMap.finrank_range_add_finrank_ker ( ∑ a : T, LinearMap.proj a : ( T → ℝ ) →ₗ[ℝ] ℝ ) ; simp_all +decide ;
      rw [ h_ker_dim, finrank_top ] at this ; norm_num at this ; omega;
    have := @AffineIndependent.card_le_finrank_succ;
    convert this h |> le_trans <| Nat.add_le_add_right h_dim_le 1 using 1;
    · rw [ Fintype.card_coe ];
    · exact Eq.symm ( Nat.succ_pred_eq_of_pos ( Fintype.card_pos_iff.mpr ( by contrapose! hs_empty; aesop ) ) )

/-
Affinely independent points supported on `Sset` and summing to one number at
most `|Sset|`.
-/
private lemma affineIndep_simplexOn_card_le {Sset : Finset T} {s : Finset (T → ℝ)}
    (h : AffineIndependent ℝ ((↑) : s → (T → ℝ)))
    (hmem : ∀ x ∈ s, x ∈ simplexOn Sset) : s.card ≤ Sset.card := by
  by_cases hs : s.Nonempty <;> simp_all +decide [ Finset.card_univ ];
  -- Let $W$ be the subspace of functions supported on $Sset$ and summing to zero.
  set W : Submodule ℝ (T → ℝ) := Submodule.span ℝ {f : T → ℝ | (∀ a, a∉Sset → f a = 0) ∧ ∑ a, f a = 0};
  -- By `AffineIndependent.card_le_finrank_succ`, `s.card = Fintype.card ↥s ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑):s→(T→ℝ)))) + 1`.
  have h_card_le : s.card ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → (T → ℝ)))) + 1 := by
    convert AffineIndependent.card_le_finrank_succ h using 1;
    rw [ Fintype.card_of_subtype ] ; aesop;
  -- It suffices to show `Module.finrank ℝ (vectorSpan ...) ≤ Sset.card - 1`, which follows from `vectorSpan ... ≤ W` for a subspace `W` with `Module.finrank ℝ W ≤ Sset.card - 1`.
  have h_finrank_le : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → (T → ℝ)))) ≤ Module.finrank ℝ W := by
    refine' Submodule.finrank_mono _;
    refine' Submodule.span_le.mpr _;
    rintro _ ⟨ x, y, hx, hy, rfl ⟩;
    refine' Submodule.subset_span ⟨ _, _ ⟩ <;> simp_all +decide [ sub_eq_zero ];
  -- Since $W$ is a subspace of $U$, we have $\text{finrank}(W) \leq \text{finrank}(U) - 1$.
  have h_finrank_W_le : Module.finrank ℝ W ≤ Module.finrank ℝ (Submodule.span ℝ {f : T → ℝ | ∀ a, a∉Sset → f a = 0}) - 1 := by
    have h_finrank_W_le : W < Submodule.span ℝ {f : T → ℝ | ∀ a, a∉Sset → f a = 0} := by
      refine' lt_of_le_of_ne _ _;
      · exact Submodule.span_mono fun f hf => hf.1;
      · intro h_eq
        have h_sum_zero : ∀ f ∈ Submodule.span ℝ {f : T → ℝ | ∀ a, a∉Sset → f a = 0}, ∑ a, f a = 0 := by
          intro f hf
          rw [← h_eq] at hf
          exact (by
          rw [ Submodule.mem_span ] at hf;
          specialize hf ( LinearMap.ker ( ∑ a : T, LinearMap.proj a ) ) ; simp_all +decide [ Set.subset_def, LinearMap.mem_ker ] ;);
        obtain ⟨ x, hx ⟩ := hs;
        exact absurd ( h_sum_zero x ( Submodule.subset_span ( hmem x hx |>.2.2 ) ) ) ( by linarith [ hmem x hx |>.2.1 ] );
    exact Nat.le_sub_one_of_lt ( Submodule.finrank_lt_finrank_of_lt h_finrank_W_le );
  -- Since $U$ is isomorphic to $Sset → ℝ$, we have $\text{finrank}(U) = Sset.card$.
  have h_finrank_U_eq : Module.finrank ℝ (Submodule.span ℝ {f : T → ℝ | ∀ a, a∉Sset → f a = 0}) = Sset.card := by
    have h_finrank_U_eq : Submodule.span ℝ {f : T → ℝ | ∀ a, a∉Sset → f a = 0} = Submodule.span ℝ (Set.range (fun a : Sset => fun b : T => if b = a then 1 else 0)) := by
      refine' le_antisymm _ _;
      · rw [ Submodule.span_le ];
        intro f hf
        have h_decomp : f = ∑ a ∈ Sset, f a • (fun b => if b = a then 1 else 0 : T → ℝ) := by
          ext b; by_cases hb : b ∈ Sset <;> simp_all +decide [ Finset.sum_ite, Finset.filter_eq' ] ;
        exact h_decomp.symm ▸ Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ ⟨ a, ha ⟩, rfl ⟩ );
      · exact Submodule.span_mono ( Set.range_subset_iff.mpr fun a => fun b hb => by aesop );
    rw [ h_finrank_U_eq, finrank_span_eq_card ] <;> norm_num [ Function.Injective ];
    refine' Fintype.linearIndependent_iff.2 _;
    intro g hg i; replace hg := congr_fun hg i; simp_all +decide [ Finset.sum_ite, Finset.filter_eq' ] ;
  exact h_card_le.trans ( Nat.succ_le_succ ( h_finrank_le.trans ( h_finrank_W_le.trans ( by rw [ h_finrank_U_eq ] ) ) ) ) |> le_trans <| by simp +decide [ Nat.sub_add_cancel ( show 1 ≤ Sset.card from Finset.card_pos.mpr <| by
                                                                                                                                                                                  contrapose! hs; simp_all +decide [ Finset.nonempty_iff_ne_empty ] ;
                                                                                                                                                                                  exact Finset.eq_empty_of_forall_notMem fun x hx => by simpa [ hmem x hx ] using hmem x hx |>.2.1; ) ] ;

/-
**Cheap-talk selection.** Under `MCT`, if `ι` has at most `|Θ|` elements and
`cls i ∈ 𝓜`, we may injectively assign to each `i` a message with the same
preimage as `cls i`.
-/
private lemma exists_inj_msg {ι : Type*} [Fintype ι]
    (hMCT : G.MCT) (hcard : Fintype.card ι ≤ G.Θ.card)
    (cls : ι → Msg) (hcls : ∀ i, cls i ∈ G.𝓜) :
    ∃ msg : ι → Msg, Function.Injective msg ∧
      ∀ i, G.canSend (msg i) = G.canSend (cls i) := by
  -- Apply the hypothesis `hMCT` to each `cls i` to find a message with the same preimage as `cls i`.
  have hmsg : ∀ i, ∃ msg_i ∈ G.𝓜, G.canSend msg_i = G.canSend (cls i) ∧ (Fintype.card {j : ι | G.canSend (cls j) = G.canSend (cls i)}) ≤ (Finset.filter (fun m' => G.canSend m' = G.canSend (cls i)) G.𝓜).card := by
    refine' fun i => ⟨ cls i, hcls i, rfl, _ ⟩;
    have := hMCT ( cls i ) ( hcls i );
    exact le_trans ( Fintype.card_subtype_le _ ) ( by simpa using hcard.trans this );
  choose msg hmsg₁ hmsg₂ hmsg₃ using hmsg;
  have hmsg₄ : ∀ (v : Finset T), ∃ (msg' : {i : ι | G.canSend (cls i) = v} → Msg), Function.Injective msg' ∧ ∀ i, G.canSend (msg' i) = v := by
    intro v
    by_cases hv : ∃ i, G.canSend (cls i) = v;
    · obtain ⟨ i, rfl ⟩ := hv;
      have := Finset.exists_subset_card_eq ( hmsg₃ i );
      obtain ⟨ t, ht₁, ht₂ ⟩ := this;
      have hmsg₄ : Nonempty ({j : ι | G.canSend (cls j) = G.canSend (cls i)} ↪ t) := by
        exact ⟨ ( Fintype.equivOfCardEq ( by aesop ) ) |> Equiv.toEmbedding ⟩;
      exact ⟨ fun x => hmsg₄.some x |>.1, fun x y hxy => by simpa using hmsg₄.some.injective ( Subtype.ext hxy ), fun x => by simpa using Finset.mem_filter.mp ( ht₁ ( hmsg₄.some x |>.2 ) ) |>.2 ⟩;
    · simp_all +decide [ Function.Injective ];
      exact Or.inl ⟨ fun x => x.2 ⟩;
  choose msg' hmsg'₁ hmsg'₂ using hmsg₄;
  refine' ⟨ fun i => msg' ( G.canSend ( cls i ) ) ⟨ i, rfl ⟩, _, _ ⟩ <;> simp_all +decide [ Function.Injective ];
  grind

/-- Bayes plausibility (cf. the private `Existence.bayes_plausibility`). -/
private lemma deg_bayes_plausibility (H : DisclosureGame T Msg) (s : Strategy H) :
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
Per-message facts about a coalition's induced beliefs.
-/
private lemma deg_belief_facts {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (K : Coalition (G.restrict R hne hsub)) {m : Msg} (hm : m ∈ K.σ.evidence) :
    K.σ.belief m ∈ simplexOn K.C ∧ K.w ∈ G.V (K.σ.belief m) ∧ m ∈ G.𝓜 ∧
      simplexSupport (K.σ.belief m) ⊆ (G.canSend m : Set T) ∧
      (∀ θ ∈ R, θ ∈ G.canSend m → θ ∈ K.C) := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · convert K.σ.belief_mem_simplex hm using 1;
  · convert K.payoff m hm using 1;
    rw [ Strategy.coalitionBelief, DisclosureGame.zeroExt_eq_self ];
    · grind;
    · exact Strategy.belief_mem_simplex _ hm;
  · simp_all +decide [ Strategy.evidence, simplexSupport ];
    obtain ⟨ θ, hθ, hθ' ⟩ := hm; have := K.σ.mem θ; simp_all +decide [ Strategy.msgSupport, mem_simplexSupport ] ;
    contrapose! hθ';
    exact this.2.2 m ( by rintro hm; exact hθ' ( G.M_subset θ ( hsub ( K.C_subset hθ ) ) hm ) ) ▸ le_rfl;
  · intro θ hθ
    simp [simplexSupport, Strategy.belief] at hθ;
    contrapose! hθ; simp_all +decide [ DisclosureGame.canSend ] ;
    simp_all +decide [ DisclosureGame.condPrior, DisclosureGame.preimageFull ];
    split_ifs <;> simp_all +decide [ preimage ];
    have := K.σ.mem θ; simp_all +decide [ Finset.ext_iff ] ;
    rw [ this.2.2 m ( hθ ( hsub ‹_› ) ) ] ; norm_num;
  · have := K.exclusive;
    intro θ hθ hθm; specialize this; simp_all +decide [ Set.subset_def, DisclosureGame.preimageSetFull ] ;
    refine' this _;
    unfold DisclosureGame.preimageSet; simp_all +decide [ DisclosureGame.canSend ] ;
    unfold DisclosureGame.preimageFull at hθm; simp_all +decide [ Set.Nonempty ] ;
    unfold preimage at hθm; simp_all +decide [ Set.Nonempty ] ;
    exact ⟨ m, by obtain ⟨ x, hx ⟩ := hθm.2; aesop ⟩

/-
**Bayes + degradability.** The conditional prior on the cell `C := K.C`
is a convex combination of beliefs each supported in `C`, paying `w'`, and hosted
by a message whose preimage meets `R` only inside `C`.
-/
private lemma deg_condPrior_mem_hull (hdeg : G.Degradable)
    {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    (K : Coalition (G.restrict R hne hsub)) {w' : ℝ}
    (hw'lo : G.vMin ≤ w') (hw'hi : w' ≤ K.w) :
    G.condPrior K.C ∈ convexHull ℝ
      {μ : T → ℝ | μ ∈ simplexOn G.Θ ∧ w' ∈ G.V μ ∧
        simplexSupport μ ⊆ (K.C : Set T) ∧
        ∃ m ∈ G.𝓜, simplexSupport μ ⊆ (G.canSend m : Set T) ∧
          (∀ θ ∈ R, θ ∈ G.canSend m → θ ∈ K.C)} := by
  convert mem_convexHull_iff.mpr _;
  intro t ht ht_convex
  obtain ⟨E, hE⟩ : ∃ E : Finset Msg, E.Nonempty ∧ K.σ.evidence = E ∧ ∀ m ∈ E, K.σ.onPathProb m > 0 := by
    refine' ⟨ Finset.univ.filter fun m => m ∈ K.σ.evidence, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
    · have := K.σ.mem; simp_all +decide [ Finset.Nonempty ] ;
      obtain ⟨ θ, hθ ⟩ := K.C_nonempty; specialize this θ hθ; simp_all +decide [ Strategy.evidence ] ;
      contrapose! this; simp_all +decide [ Strategy.msgSupport ] ;
      exact fun _ _ => absurd ‹∑ a, K.σ.σ θ a = 1› ( by rw [ Finset.sum_eq_zero fun x hx => le_antisymm ( this x θ hθ ) ( by aesop ) ] ; norm_num );
    · grind +suggestions;
  have h_sum : ∀ θ, G.condPrior K.C θ = ∑ m ∈ E, (K.σ.onPathProb m) * (K.σ.belief m) θ := by
    intro θ
    have h_sum : G.condPrior K.C θ = ∑ m ∈ Finset.univ.filter (fun m => m ∈ K.σ.evidence), K.σ.onPathProb m * K.σ.belief m θ := by
      convert deg_bayes_plausibility _ _ |>.1 θ using 1;
      convert rfl;
      grind +suggestions;
    aesop;
  have h_sum_mem : ∀ m ∈ E, K.σ.belief m ∈ convexHull ℝ {μ | μ ∈ simplexOn G.Θ ∧ w' ∈ G.V μ ∧ simplexSupport μ ⊆ K.C ∧ ∃ m ∈ G.𝓜, simplexSupport μ ⊆ G.canSend m ∧ ∀ θ ∈ R, θ ∈ G.canSend m → θ ∈ K.C} := by
    intro m hm
    have h_belief : K.σ.belief m ∈ simplexOn K.C ∧ K.w ∈ G.V (K.σ.belief m) ∧ m ∈ G.𝓜 ∧ simplexSupport (K.σ.belief m) ⊆ G.canSend m ∧ ∀ θ ∈ R, θ ∈ G.canSend m → θ ∈ K.C := by
      apply deg_belief_facts hne hsub K (by
      exact hE.2.1.symm ▸ Finset.mem_coe.2 hm);
    have h_belief_mem : K.σ.belief m ∈ convexHull ℝ {μ | μ ∈ simplexOn G.Θ ∧ simplexSupport μ ⊆ simplexSupport (K.σ.belief m) ∧ w' ∈ G.V μ} := by
      apply hdeg (K.σ.belief m) (by
      exact simplexOn_mono ( K.C_subset.trans hsub ) h_belief.1) w' ⟨hw'lo, by
        exact le_trans hw'hi ( le_csSup ( G.V_isCompact _ ( by
          exact simplexOn_mono ( K.C_subset.trans hsub ) h_belief.1 ) |> IsCompact.bddAbove ) h_belief.2.1 )⟩;
    refine' convexHull_mono _ h_belief_mem;
    grind +suggestions;
  have h_sum_mem : ∑ m ∈ E, (K.σ.onPathProb m) • (K.σ.belief m) ∈ convexHull ℝ {μ | μ ∈ simplexOn G.Θ ∧ w' ∈ G.V μ ∧ simplexSupport μ ⊆ K.C ∧ ∃ m ∈ G.𝓜, simplexSupport μ ⊆ G.canSend m ∧ ∀ θ ∈ R, θ ∈ G.canSend m → θ ∈ K.C} := by
    convert convex_convexHull ℝ _ |> fun h => h.sum_mem _ _ _;
    · exact fun m hm => le_of_lt ( hE.2.2 m hm );
    · convert deg_bayes_plausibility _ _ |>.2 using 1;
      convert Finset.sum_subset _ _ <;> simp +decide [ hE.2.1 ];
      tauto;
    · exact h_sum_mem;
  convert convexHull_min ht ht_convex h_sum_mem using 1;
  exact funext fun θ => by simpa [ Finset.sum_apply, Pi.smul_apply ] using h_sum θ;

/-
Membership in `canSend`.
-/
private lemma deg_mem_canSend {m : Msg} {θ : T} :
    θ ∈ G.canSend m ↔ θ ∈ G.Θ ∧ m ∈ G.M θ := by
  convert Finset.mem_filter;
  simp +decide [ Finset.Nonempty ]

/-
A nonnegative distribution summing to one with support in `Sset` lies in `simplexOn Sset`.
-/
private lemma deg_mem_simplexOn_of_support {Sset : Finset T} {μ : T → ℝ}
    (h : μ ∈ simplexOn G.Θ) (hsupp : simplexSupport μ ⊆ (Sset : Set T)) :
    μ ∈ simplexOn Sset := by
  refine' ⟨ h.1, h.2.1, _ ⟩;
  exact fun a ha => le_antisymm ( le_of_not_gt fun ha' => ha <| hsupp ha' ) ( h.1 a )

/-
A point of the convex hull of a finset is a strictly-positive convex
combination of a subset.
-/
private lemma deg_convexHull_pos_decomp {x : T → ℝ} {t : Finset (T → ℝ)}
    (h : x ∈ convexHull ℝ (t : Set (T → ℝ))) :
    ∃ (u : Finset (T → ℝ)) (wt : (T → ℝ) → ℝ), u ⊆ t ∧ (∀ y ∈ u, 0 < wt y) ∧
      (∑ y ∈ u, wt y = 1) ∧ (∑ y ∈ u, wt y • y = x) := by
  obtain ⟨w, hw⟩ : ∃ w : (T → ℝ) → ℝ, (∀ y ∈ t, 0 ≤ w y) ∧ (∑ y ∈ t, w y = 1) ∧ (∑ y ∈ t, w y • y = x) := by
    rw [ mem_convexHull_iff_exists_fintype ] at h;
    obtain ⟨ ι, _, w, z, hw, hw', hz, hx ⟩ := h;
    refine' ⟨ fun y => ∑ i ∈ Finset.univ.filter ( fun i => z i = y ), w i, _, _, _ ⟩;
    · exact fun y hy => Finset.sum_nonneg fun i hi => hw i;
    · rw [ ← hw', Finset.sum_fiberwise_of_maps_to ] ; aesop;
    · simp +decide [ ← hx, Finset.sum_filter, Finset.sum_smul ];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  refine' ⟨ t.filter fun y => w y ≠ 0, w, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_filter_of_ne ];
  exact fun y hy hy' => lt_of_le_of_ne ( hw.1 y hy ) ( Ne.symm hy' )

/-- **Proposition 4** (part): cheap-talk copies (M-CT) together with
decomposability of `V` (Definition 20) yield the payoff-degradation property
(PD). -/
theorem degrade_general (hMCT : G.MCT) (hdeg : G.Degradable) :
    G.DegradationProperty := by
  intro R hne hsub K w' hw'
  haveI : Nonempty Msg := ⟨G.𝓜_nonempty.choose⟩
  -- Bayes + degradability: the conditional prior is a convex hull of "good" beliefs.
  have hH := deg_condPrior_mem_hull hdeg hne hsub K hw'.1 hw'.2
  rw [convexHull_eq_union] at hH
  simp only [Set.mem_iUnion, exists_prop] at hH
  obtain ⟨t, htS, htAI, htmem⟩ := hH
  -- Carathéodory with strictly positive weights.
  obtain ⟨u, wt, hut, hwtpos, hwtsum, hwtcm⟩ := deg_convexHull_pos_decomp htmem
  have hSi := fun y (hy : y ∈ u) => htS (Finset.mem_coe.mpr (hut hy))
  -- choose a hosting message for each point.
  choose! cls' hcls1 hcls2 hcls3 using fun y hy => (hSi y hy).2.2.2
  -- `u` is nonempty.
  have hune : u.Nonempty := by
    rcases Finset.eq_empty_or_nonempty u with h | h
    · rw [h] at hwtsum; simp at hwtsum
    · exact h
  haveI : Nonempty {y // y ∈ u} := ⟨⟨hune.choose, hune.choose_spec⟩⟩
  -- cardinality bound from affine independence inside the simplex.
  have hAIu : AffineIndependent ℝ ((↑) : {y // y ∈ u} → (T → ℝ)) :=
    htAI.comp_embedding
      ⟨fun y => ⟨y.1, hut y.2⟩, fun a b hab => Subtype.ext (by simpa using hab)⟩
  have hcard : Fintype.card {y // y ∈ u} ≤ G.Θ.card := by
    rw [Fintype.card_coe]
    exact affineIndep_simplexOn_card_le hAIu (fun y hy => (hSi y hy).1)
  -- cheap-talk selection of distinct hosting messages.
  obtain ⟨msg, hmsg_inj, hmsg_eq⟩ :=
    exists_inj_msg (ι := {y // y ∈ u}) hMCT hcard (fun i => cls' i.val)
      (fun i => hcls1 i.val i.2)
  -- consistency identity.
  have hcons : ∀ θ, (G.restrict R hne hsub).condPrior K.C θ
      = ∑ i : {y // y ∈ u}, wt i.val * i.val θ := by
    intro θ
    have hsum : ∑ y ∈ u, wt y * y θ = G.condPrior K.C θ := by
      have hcm := congr_arg (fun f => f θ) hwtcm
      simpa [Finset.sum_apply, Pi.smul_apply] using hcm
    rw [Partition.restrict_condPrior_eq hne hsub K.C_nonempty K.C_subset,
      Finset.sum_coe_sort u (fun y => wt y * y θ)]
    exact hsum.symm
  -- assemble the coalition.
  obtain ⟨K', hK'C, hK'w⟩ :=
    exists_coalition_realize (G.restrict R hne hsub) K.C_nonempty K.C_subset msg hmsg_inj
      (fun i => wt i.val) (fun i => i.val)
      (fun i => hwtpos i.val i.2)
      (fun i => deg_mem_simplexOn_of_support (hSi i.val i.2).1 (hSi i.val i.2).2.2.1)
      hcons
      (fun i θ _ hpos => by
        have hfin : θ ∈ G.canSend (cls' i.val) :=
          Finset.mem_coe.mp (hcls2 i.val i.2 (mem_simplexSupport.mpr hpos))
        have hmem : θ ∈ G.canSend (msg i) := by rw [hmsg_eq i]; exact hfin
        rw [restrict_M]
        exact (deg_mem_canSend.mp hmem).2)
      (fun i θ hθΘ hθM => by
        have hmem : θ ∈ G.canSend (msg i) := deg_mem_canSend.mpr ⟨hsub hθΘ, hθM⟩
        rw [hmsg_eq i] at hmem
        exact hcls3 i.val i.2 θ hθΘ hmem)
      w'
      (fun i => (hSi i.val i.2).2.1)
  exact ⟨K', hK'C, hK'w⟩

end DisclosureGame

end CPD
