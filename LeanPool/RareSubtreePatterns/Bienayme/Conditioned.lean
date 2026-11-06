/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bienayme.Normalization


/-!
# Size-conditioned Bienaymé trees and admissible sizes

Source lines 699–700: `𝒯^n` is a `μ`-Bienaymé tree conditioned to have `n` vertices, for the
admissible sizes `n`, i.e. those with `𝐏(|𝒯| = n) > 0`. We prove:

* `conditioned_isProbabilityMeasure`: at an admissible size the conditioned law is a
  probability measure (for every offspring law), and it is the zero measure otherwise;
* `conditioned_apply_singleton`: `𝐏(𝒯^n = T) = 𝐏_μ(T) / 𝐏_μ(|𝒯| = n)` if `|T| = n`, else `0`;
* `infinite_setOf_admissible`, `nonempty_setOf_admissible`: for critical `μ` with `μ_1 ≠ 1`,
  the admissible sizes form an infinite set containing `1` (sizes `m j + 1` are admissible
  for any `j ≥ 2` with `μ_j > 0`);
* the filter `admissibleAtTop μ` of large admissible sizes, which is proper for critical
  `μ` with `μ_1 ≠ 1` (`admissibleAtTop_neBot`), and along which the conditioned laws are
  eventually probability measures.

No aperiodicity is assumed: periodic offspring laws have admissible sizes in a lattice.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PoissonDeclumping.PlaneTree

variable {μ : PMF ℕ} {n : ℕ}

/-- The law of the size: `𝐏_μ(|T| = n) = ∑_{|T| = n} ∏_{u∈T} μ_{k_u(T)}`. -/
theorem bienayme_vertexCount_eq (μ : PMF ℕ) (n : ℕ) :
    bienayme μ {T | T.vertexCount = n} =
      ∑' T, if T.vertexCount = n then weight μ T else 0 := by
  rw [bienayme_apply]
  congr 1
  ext T
  by_cases h : T.vertexCount = n <;> simp [h]

/-- A size is admissible iff some tree of that size has positive weight. -/
theorem admissible_iff : Admissible μ n ↔ ∃ T, T.vertexCount = n ∧ weight μ T ≠ 0 := by
  rw [Admissible, pos_iff_ne_zero, Ne, bienayme_apply, ENNReal.tsum_eq_zero]
  push Not
  constructor
  · rintro ⟨T, hT⟩
    by_cases h : T.vertexCount = n
    · exact ⟨T, h, by rwa [Set.indicator_of_mem (show T ∈ {T | T.vertexCount = n} from h)] at hT⟩
    · exact absurd (Set.indicator_of_notMem (show T ∉ {T | T.vertexCount = n} from h) _) hT
  · rintro ⟨T, h, hT⟩
    exact ⟨T, by rwa [Set.indicator_of_mem (show T ∈ {T | T.vertexCount = n} from h)]⟩

theorem admissible_vertexCount {T : PlaneTree} (h : weight μ T ≠ 0) :
    Admissible μ T.vertexCount :=
  admissible_iff.2 ⟨T, rfl, h⟩

/-! ### The conditioned laws -/

/-- At an admissible size, the conditioned law is a probability measure (for every offspring
law; criticality is not needed since `bienayme μ` is finite). -/
theorem conditioned_isProbabilityMeasure (h : Admissible μ n) :
    IsProbabilityMeasure (conditioned μ n) :=
  cond_isProbabilityMeasure h.ne'

/-- At an inadmissible size, the conditioned "law" is the zero measure. -/
theorem conditioned_eq_zero_of_not_admissible (h : ¬Admissible μ n) : conditioned μ n = 0 :=
  cond_eq_zero_of_meas_eq_zero (not_lt.1 h |>.antisymm zero_le)

theorem conditioned_apply (μ : PMF ℕ) (n : ℕ) (s : Set PlaneTree) :
    conditioned μ n s =
      (bienayme μ {T | T.vertexCount = n})⁻¹ * bienayme μ ({T | T.vertexCount = n} ∩ s) :=
  cond_apply (DiscreteMeasurableSpace.forall_measurableSet _) _ _

/-- `𝐏(𝒯^n = T) = 𝐏_μ(T) / 𝐏_μ(|𝒯| = n)` for a tree `T` with `n` vertices. -/
theorem conditioned_apply_singleton_of_vertexCount_eq {T : PlaneTree} (hT : T.vertexCount = n) :
    conditioned μ n {T} = weight μ T / bienayme μ {T | T.vertexCount = n} := by
  rw [conditioned_apply, Set.inter_eq_right.2
    (show {T} ⊆ {T : PlaneTree | T.vertexCount = n} from Set.singleton_subset_iff.2 hT),
    bienayme_apply_singleton, div_eq_mul_inv, mul_comm]

/-- `𝐏(𝒯^n = T) = 0` for a tree `T` whose size is not `n`. -/
theorem conditioned_apply_singleton_of_vertexCount_ne {T : PlaneTree} (hT : T.vertexCount ≠ n) :
    conditioned μ n {T} = 0 := by
  rw [conditioned_apply,
    Set.inter_singleton_eq_empty.2 (show T ∉ {T : PlaneTree | T.vertexCount = n} from hT),
    measure_empty, mul_zero]

theorem conditioned_apply_singleton (μ : PMF ℕ) (n : ℕ) (T : PlaneTree) :
    conditioned μ n {T} =
      if T.vertexCount = n then weight μ T / bienayme μ {T | T.vertexCount = n} else 0 := by
  split_ifs with hT
  · exact conditioned_apply_singleton_of_vertexCount_eq hT
  · exact conditioned_apply_singleton_of_vertexCount_ne hT

/-- The conditioned tree has `n` vertices almost surely. -/
theorem conditioned_vertexCount (h : Admissible μ n) :
    conditioned μ n {T | T.vertexCount = n} = 1 :=
  cond_apply_self h.ne' (measure_ne_top _ _)

/-! ### Admissible sizes -/

/-- Auxiliary trees: a spine of length `m` where each spine vertex has `j - 1` extra leaf
children. They have `m j + 1` vertices. -/
private def spine (j : ℕ) : ℕ → PlaneTree
  | 0 => node []
  | m + 1 => node (spine j m :: List.replicate (j - 1) (node []))

private theorem vertexCount_spine {j : ℕ} (hj : 1 ≤ j) :
    ∀ m, (spine j m).vertexCount = m * j + 1
  | 0 => by simp [spine, vertexCount_node]
  | m + 1 => by
    rw [spine, vertexCount_node, List.map_cons, List.sum_cons, vertexCount_spine hj m,
      List.map_replicate, List.sum_replicate, vertexCount_node]
    simp only [List.map_nil, List.sum_nil, zero_add, smul_eq_mul, mul_one]
    rw [add_mul, one_mul]
    omega

private theorem weight_spine_ne_zero {j : ℕ} (hj : 1 ≤ j) (h0 : μ 0 ≠ 0) (hμj : μ j ≠ 0) :
    ∀ m, weight μ (spine j m) ≠ 0
  | 0 => by simp [spine, weight_node, h0]
  | m + 1 => by
    rw [spine, weight_node, List.length_cons, List.length_replicate, Nat.sub_add_cancel hj,
      List.map_cons, List.prod_cons, List.map_replicate, List.prod_replicate]
    refine mul_ne_zero hμj (mul_ne_zero (weight_spine_ne_zero hj h0 hμj m) (pow_ne_zero _ ?_))
    simpa [weight_node] using h0

/-- Size `1` (the single-vertex tree) is admissible when `μ_0 ≠ 0`. -/
theorem admissible_one (h0 : μ 0 ≠ 0) : Admissible μ 1 := by
  have := admissible_vertexCount (μ := μ) (T := node []) (by simpa [weight_node] using h0)
  simpa [vertexCount_node] using this

/-- If `μ_0 ≠ 0` and `μ_j ≠ 0` with `j ≥ 1`, every size `m j + 1` is admissible. -/
theorem admissible_mul_add_one (h0 : μ 0 ≠ 0) {j : ℕ} (hj : 1 ≤ j) (hμj : μ j ≠ 0) (m : ℕ) :
    Admissible μ (m * j + 1) := by
  rw [← vertexCount_spine hj m]
  exact admissible_vertexCount (weight_spine_ne_zero hj h0 hμj m)

/-- For a critical `μ` with `μ_1 ≠ 1`, there are infinitely many admissible sizes. -/
theorem infinite_setOf_admissible (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    {n | Admissible μ n}.Infinite := by
  obtain ⟨j, hj, hμj⟩ := hc.exists_two_le_ne_zero hne
  refine Set.infinite_of_injective_forall_mem (f := fun m => m * j + 1) ?_
    (admissible_mul_add_one (hc.apply_zero_ne_zero hne) (by omega) hμj)
  intro a b hab
  simp only [add_left_inj] at hab
  exact Nat.eq_of_mul_eq_mul_right (by omega) hab

/-- The set of admissible sizes is nonempty (it contains `1`). -/
theorem nonempty_setOf_admissible (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    {n | Admissible μ n}.Nonempty :=
  ⟨1, admissible_one (hc.apply_zero_ne_zero hne)⟩

/-- The filter "`n → ∞` along admissible sizes". -/
def admissibleAtTop (μ : PMF ℕ) : Filter ℕ := atTop ⊓ 𝓟 {n | Admissible μ n}

theorem eventually_admissible (μ : PMF ℕ) : ∀ᶠ n in admissibleAtTop μ, Admissible μ n :=
  mem_inf_of_right (mem_principal_self _)

theorem admissibleAtTop_le_atTop (μ : PMF ℕ) : admissibleAtTop μ ≤ atTop := inf_le_left

theorem eventually_isProbabilityMeasure_conditioned (μ : PMF ℕ) :
    ∀ᶠ n in admissibleAtTop μ, IsProbabilityMeasure (conditioned μ n) :=
  (eventually_admissible μ).mono fun _ h => conditioned_isProbabilityMeasure h

/-- For a critical `μ` with `μ_1 ≠ 1`, the filter of admissible sizes is proper, so limits
along it are meaningful. -/
theorem admissibleAtTop_neBot (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    (admissibleAtTop μ).NeBot :=
  frequently_iff_neBot.1 (Nat.frequently_atTop_iff_infinite.2 (infinite_setOf_admissible hc hne))

/-- Subtype-indexed form: the conditioned law at an admissible size is a probability measure. -/
instance isProbabilityMeasure_conditioned_subtype (n : {n // Admissible μ n}) :
    IsProbabilityMeasure (conditioned μ n) :=
  conditioned_isProbabilityMeasure n.2

end PoissonDeclumping.PlaneTree
