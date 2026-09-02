import CPD.RichGame

/-!
# Tent path-independence (Lemma I.2, Proposition 8)

Standing hypothesis of the tent development (§7): `Γ.UniqueMaximizers` — `v̄`
has a unique maximizer over `Δ_ν` for every nonzero sub-measure `ν`; a
`FaceMax` selects the maximizer `μ*_C` of every face `Δ_C`.

* `faceMax_peak_consistency` (**Lemma I.2**, peak consistency): if
  `∅ ≠ D ⊆ C ⊆ Θ` and `supp μ*_C ⊆ D`, then `μ*_D = μ*_C`.
* `tent_path_independence` (**Proposition 8**, tent path independence): any
  two simplex decompositions of the same belief yield the same value. (The
  identification of the common value with the greedy value is carried by the
  greedy decomposition constructed in `simplexDecomp_exists`, which is a
  `SimplexDecomp` of `μ` like any other.)
-/

namespace CPD

namespace RichGame

variable {T : Type*} [Fintype T] {Γ : RichGame T}

/-- **Lemma I.2** (peak consistency). Let `∅ ≠ D ⊆ C ⊆ Θ`. If `supp μ*_C ⊆ D`,
then `μ*_D = μ*_C`: the belief `μ*_C` lies in `Δ_D ⊆ Δ_C`, hence maximizes
`v̄` over `Δ_D`, and the maximizer over `Δ_D` is unique. -/
lemma faceMax_peak_consistency (huniq : Γ.UniqueMaximizers) (F : Γ.FaceMax)
    {D C : Finset T} (hDne : D.Nonempty) (hCne : C.Nonempty)
    (hDC : D ⊆ C) (hCsub : C ⊆ Γ.Θ)
    (hsupp : simplexSupport (F.μstar C hCne hCsub) ⊆ (D : Set T)) :
    F.μstar D hDne (hDC.trans hCsub) = F.μstar C hCne hCsub := by
  apply ExistsUnique.unique;
  convert huniq ( fun θ => if θ ∈ D then 1 else 0 ) _ _ _;
  all_goals norm_num [ IsMaxOn, IsMaxFilter ];
  exact fun _ => Classical.dec _;
  · exact fun _ => by split_ifs <;> norm_num;
  · exact fun h => by obtain ⟨ x, hx ⟩ := hDne; simpa [ hx ] using congr_fun h x;
  · intro θ hθ; aesop;
  · refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    · exact F.mem D hDne ( hDC.trans hCsub ) |>.1;
    · have := F.mem D hDne ( hDC.trans hCsub ); simp_all +decide [ Set.subset_def ];
    · intro μ hμ;
      convert F.isMax D hDne ( hDC.trans hCsub ) μ _ _;
      · exact hμ.1;
      · exact fun x hx => by have := hμ.2 hx; aesop;
  · refine' ⟨ _, _ ⟩;
    · refine' ⟨ _, _ ⟩;
      · exact F.mem C hCne hCsub |>.1;
      · intro θ hθ; specialize hsupp hθ; aesop;
    · intro μ hμ;
      apply F.isMax C hCne hCsub μ;
      · exact hμ.1;
      · exact hμ.2.trans ( by aesop_cat )

open scoped Classical

/-! ## A weighted nested family representing a sub-measure

The proof of Proposition 8 (tent path independence) proceeds by strong induction on the size of the
support, peeling off the greedy peak `μ*_S`.  To carry the induction we use a
lightweight "family representation" of a sub-measure `ν`: a finite set of
(positive-weight) indices `s`, nested sets `E k ⊆ Θ` (nested by the `ℕ`-order
on indices), and beliefs `b k = μ*_{E k}`, with `ν = ∑_{k∈s} α k • b k`.  A
`SimplexDecomp` gives such a family (dropping the zero-weight entries), and its
`value` is exactly the family value `∑_{k∈s} α k • v̄(b k)`. -/

variable (Γ) in
/-- A weighted nested family (with positive weights) representing the
sub-measure `ν`.  Indices are natural numbers, and the sets are nested along
the `ℕ`-order. -/
structure FamRep (F : Γ.FaceMax) (ν : T → ℝ) where
  /-- The (active) index set; all weights on it are positive. -/
  s : Finset ℕ
  /-- The nested sets. -/
  E : ℕ → Finset T
  /-- The beliefs `b k = μ*_{E k}`. -/
  b : ℕ → (T → ℝ)
  /-- The weights. -/
  α : ℕ → ℝ
  /-- Weights on `s` are positive. -/
  pos : ∀ k ∈ s, 0 < α k
  /-- Sets on `s` are non-empty. -/
  Ene : ∀ k ∈ s, (E k).Nonempty
  /-- Sets on `s` are inside `Θ`. -/
  Esub : ∀ k ∈ s, E k ⊆ Γ.Θ
  /-- Sets are nested along the index order. -/
  mono : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → E j ⊆ E i
  /-- `b k` is the face maximizer of `E k`. -/
  b_eq : ∀ k ∈ s, ∀ (h1 : (E k).Nonempty) (h2 : E k ⊆ Γ.Θ), b k = F.μstar (E k) h1 h2
  /-- The representation identity. -/
  rep : ν = fun θ => ∑ k ∈ s, α k * b k θ

/-- The value `∑_{k∈s} α k • v̄(b k)` of a family representation. -/
noncomputable def FamRep.value {F : Γ.FaceMax} {ν : T → ℝ} (f : Γ.FamRep F ν) : ℝ :=
  ∑ k ∈ f.s, f.α k * Γ.vbar (f.b k)

/-
The measure represented by a family is non-negative.
-/
private lemma FamRep.nonneg {F : Γ.FaceMax} {ν : T → ℝ} (f : Γ.FamRep F ν) :
    ∀ θ, 0 ≤ ν θ := by
  obtain ⟨ s, E, b, α, pos, Ene, Esub, mono, b_eq, rep ⟩ := f;
  intro θ
  simp [rep];
  refine' Finset.sum_nonneg fun k hk => mul_nonneg ( le_of_lt ( pos k hk ) ) _;
  exact b_eq k hk ( Ene k hk ) ( Esub k hk ) ▸ ( F.mem ( E k ) ( Ene k hk ) ( Esub k hk ) ) |>.1 |>.1 θ

/-
The measure represented by a family is supported inside `Θ`.
-/
private lemma FamRep.supp_subset {F : Γ.FaceMax} {ν : T → ℝ} (f : Γ.FamRep F ν) :
    simplexSupport ν ⊆ (Γ.Θ : Set T) := by
  intro θ hθ
  have h_support : ∃ k ∈ f.s, 0 < f.b k θ := by
    contrapose! hθ; simp_all +decide [ simplexSupport ];
    rw [ f.rep ]; exact Finset.sum_nonpos fun k hk => mul_nonpos_of_nonneg_of_nonpos ( le_of_lt ( f.pos k hk ) ) ( hθ k hk );
  obtain ⟨k, hk_s, hk_pos⟩ := h_support
  have h_support_k : simplexSupport (f.b k) ⊆ (Γ.Θ : Set T) := by
    have h_support_k : f.b k = F.μstar (f.E k) (f.Ene k hk_s) (f.Esub k hk_s) := by
      exact f.b_eq k hk_s _ _;
    exact h_support_k.symm ▸ F.mem _ _ _ |>.1 |> fun h => CPD.simplexSupport_subset h
  exact (h_support_k hk_pos)

/-
A `SimplexDecomp` induces a family representation with the same value.
-/
private lemma FamRep.of_simplexDecomp (F : Γ.FaceMax) {μ : T → ℝ}
    (d : Γ.SimplexDecomp F μ) :
    ∃ f : Γ.FamRep F μ, f.value = d.value := by
  unfold FamRep.value SimplexDecomp.value;
  refine' ⟨ _, _ ⟩;
  refine' { s := ( Finset.univ.filter fun j => 0 < d.ω j ).image ( fun j => j.val ), E := fun k => if h : k < Γ.Θ.card then d.chain.C ⟨ k, h ⟩ else ∅, b := fun k => if h : k < Γ.Θ.card then F.μstar ( d.chain.C ⟨ k, h ⟩ ) ( d.chain.C_nonempty ⟨ k, h ⟩ ) ( d.chain.C_subset ⟨ k, h ⟩ ) else 0, α := fun k => if h : k < Γ.Θ.card then d.ω ⟨ k, h ⟩ else 0, pos := _, Ene := _, Esub := _, mono := _, b_eq := _, rep := _ };
  all_goals simp +decide [ Finset.sum_image, Fin.val_injective.eq_iff ];
  any_goals intro a ha; simp +decide [ ha, d.chain.C_nonempty, d.chain.C_subset ];
  · exact fun i hi j hj hij => d.chain.C_mono i j hij;
  · grind;
  · convert d.eq using 1;
    ext θ;
    rw [ Finset.sum_filter_of_ne ]; aesop;
    exact fun x _ hx => lt_of_le_of_ne ( d.ω_nonneg x ) ( Ne.symm <| by aesop );
  · rw [ Finset.sum_filter_of_ne ];
    exact fun x _ hx => lt_of_le_of_ne ( d.ω_nonneg x ) ( Ne.symm <| by aesop )

/-
Two weights that both satisfy the greedy peel characterization (largest `A`
with `A • p ≤ ν`, attained at some point of `supp p`) coincide.
-/
private lemma eq_of_peak_char {ν p : T → ℝ} {A A' : ℝ}
    (hA : ∀ θ, 0 < p θ → A * p θ ≤ ν θ) (hAe : ∃ θ, 0 < p θ ∧ A * p θ = ν θ)
    (hA' : ∀ θ, 0 < p θ → A' * p θ ≤ ν θ) (hA'e : ∃ θ, 0 < p θ ∧ A' * p θ = ν θ) :
    A = A' := by
  cases' hAe with θ hθ;
  -- By combining the inequalities from hA and hA', we can conclude that A' ≤ A and A ≤ A', hence A = A'.
  have h_le : A' ≤ A := by
    nlinarith [ hA θ hθ.1, hA' θ hθ.1 ]
  have h_ge : A ≤ A' := by
    obtain ⟨ θ', hθ' ⟩ := hA'e; nlinarith [ hA θ' hθ'.1, hA' θ' hθ'.1 ];
  exact le_antisymm h_ge h_le

/-
Normalize a family representation of `ν`: intersect every set with the
support `S` of `ν`, without changing the beliefs (peak-consistency), the value,
or the represented measure.
-/
private lemma FamRep.exists_normalized (huniq : Γ.UniqueMaximizers) (F : Γ.FaceMax)
    {ν : T → ℝ} (S : Finset T) (hS : ∀ θ, θ ∈ S ↔ 0 < ν θ)
    (f : Γ.FamRep F ν) :
    ∃ g : Γ.FamRep F ν, g.value = f.value ∧ ∀ k ∈ g.s, g.E k ⊆ S := by
  refine' ⟨ _, _, _ ⟩;
  use f.s, fun k => f.E k ∩ S, f.b, f.α;
  exact fun k a ↦ f.pos k a;
  all_goals norm_num [ FamRep.value ];
  · intro k hk
    have h_support : simplexSupport (f.b k) ⊆ S := by
      intro θ hθ
      have h_le : f.α k * f.b k θ ≤ ν θ := by
        convert Finset.single_le_sum ( fun x _ => ?_ ) hk using 1;
        any_goals exact fun k => f.α k * f.b k θ;
        all_goals try infer_instance;
        · rfl;
        · convert congr_fun f.rep θ using 1;
        · exact mul_nonneg ( le_of_lt ( f.pos x ‹_› ) ) ( f.b_eq x ‹_› ( f.Ene x ‹_› ) ( f.Esub x ‹_› ) ▸ ( F.mem _ ( f.Ene x ‹_› ) ( f.Esub x ‹_› ) |>.1 |>.1 θ ) );
      exact hS θ |>.2 ( lt_of_lt_of_le ( mul_pos ( f.pos k hk ) hθ ) h_le );
    have h_support : simplexSupport (f.b k) ⊆ (f.E k : Set T) := by
      have := F.mem ( f.E k ) ( f.Ene k hk ) ( f.Esub k hk );
      grind +suggestions;
    have h_support : ∃ θ, 0 < f.b k θ := by
      have h_support : ∑ θ, f.b k θ = 1 := by
        have := f.b_eq k hk ( f.Ene k hk ) ( f.Esub k hk );
        exact this.symm ▸ F.mem _ _ _ |>.1 |> fun h => h.2.1;
      contrapose! h_support;
      exact ne_of_lt ( lt_of_le_of_lt ( Finset.sum_nonpos fun _ _ => h_support _ ) ( by norm_num ) );
    exact ⟨ h_support.choose, Finset.mem_inter.mpr ⟨ ‹simplexSupport ( f.b k ) ⊆ ( f.E k : Set T ) › h_support.choose_spec, ‹simplexSupport ( f.b k ) ⊆ ( S : Set T ) › h_support.choose_spec ⟩ ⟩;
  · exact fun k hk => Finset.inter_subset_left.trans ( f.Esub k hk );
  · exact fun i hi j hj hij => Finset.inter_subset_inter ( f.mono i hi j hj hij ) ( Finset.Subset.refl _ );
  · intro k hk h1 h2
    have h_support : simplexSupport (f.b k) ⊆ (f.E k ∩ S : Set T) := by
      intro θ hθ
      have hθ_support : θ ∈ f.E k := by
        have := F.mem ( f.E k ) ( f.Ene k hk ) ( f.Esub k hk );
        exact this.2 ( by simpa [ f.b_eq k hk ( f.Ene k hk ) ( f.Esub k hk ) ] using hθ )
      have hθ_S : θ ∈ S := by
        have hθ_S : f.α k * f.b k θ ≤ ν θ := by
          have hθ_S : f.α k * f.b k θ ≤ ∑ k' ∈ f.s, f.α k' * f.b k' θ := by
            apply Finset.single_le_sum (fun k' _ => mul_nonneg (le_of_lt (f.pos k' ‹_›)) (by
            have := f.b_eq k' ‹_› ( f.Ene k' ‹_› ) ( f.Esub k' ‹_› );
            exact this.symm ▸ F.mem _ _ _ |>.1 |>.1 _)) hk;
          convert hθ_S using 1;
          convert congr_fun f.rep θ using 1;
        exact hS θ |>.2 ( lt_of_lt_of_le ( mul_pos ( f.pos k hk ) hθ ) hθ_S )
      exact ⟨hθ_support, hθ_S⟩;
    have h_peak_consistency : F.μstar (f.E k) (f.Ene k hk) (f.Esub k hk) = F.μstar (f.E k ∩ S) h1 h2 := by
      apply Eq.symm;
      grind +suggestions;
    rw [ ← h_peak_consistency, f.b_eq k hk ( f.Ene k hk ) ( f.Esub k hk ) ];
  · exact f.rep

/-
Greedy peel step on a normalized family: subtract the maximal multiple
`A • μ*_S` of the greedy peak, obtaining a family of strictly smaller support
whose value drops by exactly `A • v̄(μ*_S)`.
-/
set_option maxHeartbeats 1000000 in
private lemma FamRep.reduce_norm (huniq : Γ.UniqueMaximizers) (F : Γ.FaceMax)
    {ν : T → ℝ} (S : Finset T) (hS : ∀ θ, θ ∈ S ↔ 0 < ν θ)
    (hSne : S.Nonempty) (hSsub : S ⊆ Γ.Θ)
    (f : Γ.FamRep F ν) (hnorm : ∀ k ∈ f.s, f.E k ⊆ S) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∃ g : Γ.FamRep F (fun θ => ν θ - A * F.μstar S hSne hSsub θ),
        f.value = A * Γ.vbar (F.μstar S hSne hSsub) + g.value ∧
        (∀ θ, 0 < F.μstar S hSne hSsub θ → A * F.μstar S hSne hSsub θ ≤ ν θ) ∧
        (∃ θ, 0 < F.μstar S hSne hSsub θ ∧ A * F.μstar S hSne hSsub θ = ν θ) ∧
        (Finset.univ.filter
            (fun θ => 0 < (ν θ - A * F.μstar S hSne hSsub θ))).card <
          (Finset.univ.filter (fun θ => 0 < ν θ)).card := by
  by_contra! h_contra;
  obtain ⟨k0, hk0⟩ : ∃ k0 ∈ f.s, ∀ k ∈ f.s, k0 ≤ k := by
    by_cases h_empty : f.s = ∅;
    · have := f.rep; simp_all +decide [ Finset.ext_iff ];
      exact hSne.ne_empty ( Finset.eq_empty_of_forall_notMem hS );
    · exact ⟨ Finset.min' f.s ( Finset.nonempty_of_ne_empty h_empty ), Finset.min'_mem _ _, fun k hk => Finset.min'_le _ _ hk ⟩;
  have h_b_k0 : f.b k0 = F.μstar S hSne hSsub := by
    have h_E_k0 : f.E k0 = S := by
      refine' Finset.Subset.antisymm ( hnorm k0 hk0.1 ) _;
      intro θ hθ
      have hθ_pos : 0 < ν θ := by
        exact hS θ |>.1 hθ
      have hθ_sum : ∃ k ∈ f.s, 0 < f.α k * f.b k θ := by
        have hθ_sum : ν θ = ∑ k ∈ f.s, f.α k * f.b k θ := by
          exact congr_fun f.rep θ;
        contrapose! hθ_pos;
        exact hθ_sum.symm ▸ Finset.sum_nonpos hθ_pos
      obtain ⟨k, hk₁, hk₂⟩ := hθ_sum
      have hk₃ : k0 ≤ k := by
        exact hk0.2 k hk₁
      have hk₄ : f.E k ⊆ f.E k0 := by
        exact f.mono k0 hk0.1 k hk₁ hk₃
      have hk₅ : θ ∈ f.E k := by
        have := F.mem ( f.E k ) ( f.Ene k hk₁ ) ( f.Esub k hk₁ );
        exact this.2 ( show 0 < F.μstar ( f.E k ) ( f.Ene k hk₁ ) ( f.Esub k hk₁ ) θ from by rw [ f.b_eq k hk₁ ( f.Ene k hk₁ ) ( f.Esub k hk₁ ) ] at hk₂; exact lt_of_le_of_ne ( by nlinarith [ f.pos k hk₁ ] ) ( Ne.symm <| by aesop ) )
      exact hk₄ hk₅;
    convert f.b_eq k0 hk0.1 _ _;
    · exact h_E_k0.symm;
    · exact h_E_k0.symm ▸ hSne;
    · exact h_E_k0.symm ▸ hSsub;
  obtain ⟨θ, hθ⟩ : ∃ θ, 0 < F.μstar S hSne hSsub θ ∧ (∀ k ∈ f.s \ (f.s.filter (fun k => f.b k = F.μstar S hSne hSsub)), F.μstar S hSne hSsub θ ≠ 0 → f.b k θ = 0) := by
    by_cases h_empty : f.s \ (f.s.filter (fun k => f.b k = F.μstar S hSne hSsub)) = ∅;
    · simp_all +decide [ Finset.ext_iff ];
      have := F.mem S hSne hSsub;
      have := this.1.2.1;
      exact not_forall_not.mp fun h => by rw [ Finset.sum_eq_zero fun x hx => le_antisymm ( le_of_not_gt fun hx' => h x hx' ) ( F.mem S hSne hSsub |>.1.1 x ) ] at this; norm_num at this;
    · obtain ⟨r, hr⟩ : ∃ r ∈ f.s \ (f.s.filter (fun k => f.b k = F.μstar S hSne hSsub)), ∀ k ∈ f.s \ (f.s.filter (fun k => f.b k = F.μstar S hSne hSsub)), r ≤ k := by
        exact ⟨ Finset.min' _ ( Finset.nonempty_of_ne_empty h_empty ), Finset.min'_mem _ _, fun k hk => Finset.min'_le _ _ hk ⟩;
      have h_not_subset : ¬(simplexSupport (F.μstar S hSne hSsub) ⊆ (f.E r : Set T)) := by
        intro h_subset
        have h_eq : f.b r = F.μstar S hSne hSsub := by
          convert faceMax_peak_consistency huniq F _ _ _ _ _ using 1;
          exact f.b_eq r ( Finset.mem_sdiff.mp hr.1 |>.1 ) ( f.Ene r ( Finset.mem_sdiff.mp hr.1 |>.1 ) ) ( f.Esub r ( Finset.mem_sdiff.mp hr.1 |>.1 ) );
          · exact hnorm r ( Finset.mem_sdiff.mp hr.1 |>.1 );
          · exact h_subset;
        grind;
      simp_all +decide [ Set.not_subset ];
      obtain ⟨ θ, hθ₁, hθ₂ ⟩ := h_not_subset;
      refine' ⟨ θ, hθ₁, fun k hk hk' hk'' => _ ⟩;
      have h_subset : f.E k ⊆ f.E r := by
        exact f.mono r hr.1.1 k hk ( hr.2 k hk hk' );
      have := F.mem ( f.E k ) ( f.Ene k hk ) ( f.Esub k hk );
      exact f.b_eq k hk ( f.Ene k hk ) ( f.Esub k hk ) ▸ le_antisymm ( le_of_not_gt fun h => hθ₂ <| h_subset <| this.2 h ) ( this.1.1 θ );
  -- Let's define the residual measure ν' and its family representation g.
  set A := ∑ k ∈ f.s.filter (fun k => f.b k = F.μstar S hSne hSsub), f.α k
  set ν' := fun θ => ν θ - A * F.μstar S hSne hSsub θ
  set g : Γ.FamRep F ν' := ⟨f.s \ (f.s.filter (fun k => f.b k = F.μstar S hSne hSsub)), f.E, f.b, f.α, by
    exact fun k hk => f.pos k ( Finset.mem_sdiff.mp hk |>.1 ), by
    exact fun k hk => f.Ene k ( Finset.mem_sdiff.mp hk |>.1 ), by
    exact fun k hk => f.Esub k ( Finset.mem_sdiff.mp hk |>.1 ), by
    exact fun i hi j hj hij => f.mono i ( Finset.mem_sdiff.mp hi |>.1 ) j ( Finset.mem_sdiff.mp hj |>.1 ) hij, by
    exact fun k hk h1 h2 => f.b_eq k ( Finset.mem_sdiff.mp hk |>.1 ) h1 h2, by
    ext θ; simp [ν', A]; (
    rw [ Finset.sum_filter, Finset.sum_mul _ _ _ ];
    rw [ Finset.sum_filter ];
    rw [ show ν θ = ∑ k ∈ f.s, f.α k * f.b k θ from ?_ ];
    · grind;
    · exact congr_fun f.rep θ)⟩
  generalize_proofs at *;
  refine' h_contra A _ g _ _ _ |> not_le_of_gt ( Finset.card_lt_card _ );
  · simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
    refine' ⟨ fun x hx => _, θ, _, _ ⟩;
    · exact lt_of_le_of_lt ( mul_nonneg ( Finset.sum_nonneg fun _ _ => le_of_lt ( f.pos _ ( Finset.mem_filter.mp ‹_› |>.1 ) ) ) ( F.mem _ hSne hSsub |>.1 |>.1 _ ) ) hx;
    · have := f.rep;
      rw [ this ];
      refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun k _ => mul_nonneg ( le_of_lt ( f.pos k ‹_› ) ) ( show 0 ≤ f.b k θ from _ ) ) hk0.1 );
      · exact mul_pos ( f.pos k0 hk0.1 ) ( by simpa [ h_b_k0 ] using hθ.1 );
      · grind;
    · have h_sum : ν θ = ∑ k ∈ f.s, f.α k * f.b k θ := by
        exact congr_fun f.rep θ;
      rw [ h_sum, Finset.sum_mul _ _ _ ];
      rw [ ← Finset.sum_sdiff ( Finset.filter_subset ( fun k => f.b k = F.μstar S hSne hSsub ) f.s ) ];
      rw [ Finset.sum_congr rfl fun x hx => by rw [ hθ.2 x hx hθ.1.ne' ] ]; simp +decide [ Finset.sum_filter ];
      exact Finset.sum_le_sum fun x hx => by split_ifs <;> simp +decide [ * ];
  · exact Finset.sum_nonneg fun _ _ => le_of_lt ( f.pos _ ( Finset.mem_filter.mp ‹_› |>.1 ) );
  · simp +decide [ FamRep.value, Finset.sum_filter_add_sum_filter_not ];
    rw [ ← Finset.sum_sdiff ( Finset.filter_subset ( fun k => f.b k = F.μstar S hSne hSsub ) f.s ) ];
    rw [ add_comm, Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_filter.mp hx |>.2 ] ]; ring!;
    rw [ mul_comm, Finset.sum_mul ];
  · intro θ hθ_pos
    have h_sum : ν θ = ∑ k ∈ f.s, f.α k * f.b k θ := by
      exact congr_fun f.rep θ;
    rw [ h_sum, Finset.sum_mul _ _ _ ];
    rw [ ← Finset.sum_filter_add_sum_filter_not f.s ( fun k => f.b k = F.μstar S hSne hSsub ) ];
    refine' le_add_of_le_of_nonneg _ _;
    · refine' Finset.sum_le_sum fun k hk => _;
      rw [ Finset.mem_filter.mp hk |>.2 ];
    · refine' Finset.sum_nonneg fun k hk => mul_nonneg _ _;
      · exact le_of_lt ( f.pos k ( Finset.mem_filter.mp hk |>.1 ) );
      · have := F.mem ( f.E k ) ( f.Ene k ( Finset.mem_filter.mp hk |>.1 ) ) ( f.Esub k ( Finset.mem_filter.mp hk |>.1 ) );
        rw [ f.b_eq k ( Finset.mem_filter.mp hk |>.1 ) ( f.Ene k ( Finset.mem_filter.mp hk |>.1 ) ) ( f.Esub k ( Finset.mem_filter.mp hk |>.1 ) ) ];
        exact this.1.1 θ;
  · use θ;
    simp_all +decide [ Finset.sum_ite ];
    have h_sum : ν θ = ∑ k ∈ f.s, f.α k * f.b k θ := by
      exact congr_fun f.rep θ;
    rw [ h_sum, Finset.sum_mul _ _ _ ];
    rw [ Finset.sum_filter ];
    refine' Finset.sum_congr rfl fun k hk => _;
    grind

/-
Strong induction: any two family representations of the same sub-measure
have the same value.
-/
private lemma FamRep.value_eq_aux (huniq : Γ.UniqueMaximizers) (F : Γ.FaceMax) :
    ∀ (m : ℕ) (ν : T → ℝ), (∀ θ, 0 ≤ ν θ) →
      simplexSupport ν ⊆ (Γ.Θ : Set T) →
      (Finset.univ.filter (fun θ => 0 < ν θ)).card ≤ m →
      ∀ f g : Γ.FamRep F ν, f.value = g.value := by
  intro m;
  induction' m with m ih generalizing F;
  · intro ν hν hsub hcard f g
    have hν_zero : ν = 0 := by
      ext θ; contrapose! hcard; simp_all +decide [ Finset.ext_iff ];
      exact ⟨ θ, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, lt_of_le_of_ne ( hν θ ) ( Ne.symm hcard ) ⟩ ⟩;
    have h_sum_zero : ∀ (h : Γ.FamRep F 0), h.value = 0 := by
      intro h
      have h_sum_zero : ∑ k ∈ h.s, h.α k * (∑ θ, h.b k θ) = 0 := by
        convert congr_arg ( fun x : T → ℝ => ∑ θ, x θ ) h.rep.symm using 1;
        · rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ];
        · norm_num;
      have h_sum_zero : ∀ k ∈ h.s, ∑ θ, h.b k θ = 1 := by
        intro k hk
        have h_b_k : h.b k ∈ simplexOn Γ.Θ := by
          have := h.b_eq k hk ( h.Ene k hk ) ( h.Esub k hk );
          exact this.symm ▸ F.mem _ _ _ |>.1;
        exact h_b_k.2.1;
      simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_nonneg, h.pos ];
      exact Finset.sum_eq_zero fun k hk => mul_eq_zero_of_left ( by linarith [ h.pos k hk, Finset.single_le_sum ( fun x _ => le_of_lt ( h.pos x ‹_› ) ) hk ] ) _;
    subst hν_zero; exact h_sum_zero f ▸ h_sum_zero g ▸ rfl;
  · intro ν hν_nonneg hν_sub hν_card f g
    by_cases hν_zero : (Finset.univ.filter (fun θ => 0 < ν θ)).card = 0;
    · grind;
    · obtain ⟨f1, hf1v, hf1n⟩ := FamRep.exists_normalized huniq F (Finset.univ.filter (fun θ => 0 < ν θ)) (by
      simp +decide) f
      obtain ⟨g1, hg1v, hg1n⟩ := FamRep.exists_normalized huniq F (Finset.univ.filter (fun θ => 0 < ν θ)) (by
      simp +decide) g;
      obtain ⟨Af, hAf0, gf, hvf, hbf, hef, hcf⟩ := FamRep.reduce_norm huniq F (Finset.univ.filter (fun θ => 0 < ν θ)) (by
      simp +decide [ Finset.ext_iff ]) (by
      exact Finset.card_pos.mp ( Nat.pos_of_ne_zero hν_zero )) (by
      exact fun x hx => hν_sub <| by simpa using hx;) f1 hf1n
      obtain ⟨Ag, hAg0, gg, hvg, hbg, heg, hcg⟩ := FamRep.reduce_norm huniq F (Finset.univ.filter (fun θ => 0 < ν θ)) (by
      simp +decide) (by
      exact Finset.card_pos.mp ( Nat.pos_of_ne_zero hν_zero )) (by
      exact fun x hx => hν_sub <| by simpa using hx;) g1 hg1n
      have hAf_eq_Ag : Af = Ag := by
        apply eq_of_peak_char hbf hef hbg heg
      subst hAf_eq_Ag;
      linarith [ ih F ( fun θ => ν θ - Af * F.μstar { θ | 0 < ν θ } ( Finset.card_pos.mp ( Nat.pos_of_ne_zero hν_zero ) ) ( fun θ hθ => hν_sub ( by simpa using hθ ) ) θ ) ( fun θ => FamRep.nonneg gf θ ) ( FamRep.supp_subset gf ) ( by linarith ) gf gg ]

/-- Any two family representations of the same sub-measure have the same value. -/
private lemma FamRep.value_eq (huniq : Γ.UniqueMaximizers) (F : Γ.FaceMax)
    {ν : T → ℝ} (f g : Γ.FamRep F ν) : f.value = g.value := by
  exact FamRep.value_eq_aux huniq F
    (Finset.univ.filter (fun θ => 0 < ν θ)).card ν f.nonneg f.supp_subset le_rfl f g

/-- **Proposition 8** (tent path independence). Any two simplex
decompositions of the same belief yield the same value:
`∑_j ω_j v̄(μ*_{C_j}) = ∑_j ω'_j v̄(μ*_{C'_j})`. -/
theorem tent_path_independence (huniq : Γ.UniqueMaximizers) (F : Γ.FaceMax)
    {μ : T → ℝ} (d d' : Γ.SimplexDecomp F μ) :
    d.value = d'.value := by
  obtain ⟨f, hf⟩ := FamRep.of_simplexDecomp F d
  obtain ⟨f', hf'⟩ := FamRep.of_simplexDecomp F d'
  rw [← hf, ← hf', FamRep.value_eq huniq F f f']

end RichGame

end CPD
