import Mathlib

/-!
# The standard simplex on a `Finset`  (§2 notation)

For a finite type space and a finite subset `S`, `Δ S` (`simplexOn S`) is the
set of probability distributions on `S`: functions `α → ℝ` that are
nonnegative, sum to one, and vanish outside `S` (the zero-extension encoding
used throughout the paper for beliefs and mixed strategies).
`simplexSupport μ := {a | μ a > 0}` is the support of a distribution.
-/

open Set

namespace CPD

variable {α : Type*} [Fintype α]

/-- `Δ S`, the probability distributions supported on `S ⊆ α`. -/
def simplexOn (S : Finset α) : Set (α → ℝ) :=
  {μ | (∀ a, 0 ≤ μ a) ∧ (∑ a, μ a = 1) ∧ (∀ a ∉ S, μ a = 0)}

variable {S : Finset α}

@[simp] lemma mem_simplexOn {μ : α → ℝ} :
    μ ∈ simplexOn S ↔ (∀ a, 0 ≤ μ a) ∧ (∑ a, μ a = 1) ∧ (∀ a ∉ S, μ a = 0) :=
  Iff.rfl

lemma simplexOn.nonneg {μ : α → ℝ} (h : μ ∈ simplexOn S) (a : α) : 0 ≤ μ a := h.1 a

lemma simplexOn.sum_eq_one {μ : α → ℝ} (h : μ ∈ simplexOn S) : ∑ a, μ a = 1 := h.2.1

lemma simplexOn.eq_zero_of_not_mem {μ : α → ℝ} (h : μ ∈ simplexOn S) {a : α}
    (ha : a ∉ S) : μ a = 0 := h.2.2 a ha

/-- The `support` of a distribution `μ`, i.e. `{a | μ a > 0}`. -/
def simplexSupport (μ : α → ℝ) : Set α := {a | 0 < μ a}

omit [Fintype α] in
@[simp] lemma mem_simplexSupport {μ : α → ℝ} {a : α} :
    a ∈ simplexSupport μ ↔ 0 < μ a := Iff.rfl

/-
A distribution in `Δ S` has support inside `S`.
-/
lemma simplexSupport_subset {μ : α → ℝ} (h : μ ∈ simplexOn S) :
    simplexSupport μ ⊆ (S : Set α) := by
  exact fun x hx => Classical.not_not.1 fun hx' => hx.out.ne' ( h.2.2 x hx' )

/-
Monotonicity of the simplex in its support set.
-/
lemma simplexOn_mono {S S' : Finset α} (h : S ⊆ S') :
    simplexOn S ⊆ simplexOn S' := by
  intro μ hμ;
  exact ⟨ hμ.1, hμ.2.1, fun a ha => hμ.2.2 a <| fun ha' => ha <| h ha' ⟩

/-
`Δ S` is contained in the Mathlib standard simplex `stdSimplex ℝ α`.
-/
lemma simplexOn_subset_stdSimplex : simplexOn S ⊆ stdSimplex ℝ α := by
  intro μ hμ;
  constructor <;> aesop

/-
`Δ S` is closed in `α → ℝ`.
-/
lemma isClosed_simplexOn (S : Finset α) : IsClosed (simplexOn S) := by
  simp +decide only [simplexOn];
  simp +decide only [setOf_and, setOf_forall];
  exact IsClosed.inter ( isClosed_iInter fun _ => isClosed_le continuous_const <| continuous_apply _ ) ( IsClosed.inter ( isClosed_eq ( continuous_finset_sum _ fun _ _ => continuous_apply _ ) continuous_const ) <| isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq ( continuous_apply _ ) continuous_const )

/-
`Δ S`, regarded as a compact subset of `ℝ^S`.
-/
lemma isCompact_simplexOn (S : Finset α) : IsCompact (simplexOn S) := by
  refine' IsCompact.of_isClosed_subset ( _ ) ( isClosed_simplexOn _ ) _;
  exact Set.pi Set.univ fun a => Set.Icc 0 1;
  · exact isCompact_univ_pi fun _ => CompactIccSpace.isCompact_Icc;
  · exact fun μ hμ => fun a _ => ⟨ hμ.1 a, hμ.2.1 ▸ Finset.single_le_sum ( fun a _ => hμ.1 a ) ( Finset.mem_univ a ) ⟩

end CPD