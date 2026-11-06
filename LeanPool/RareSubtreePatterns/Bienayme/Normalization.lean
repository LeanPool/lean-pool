/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bienayme.Basic

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Normalization of the critical Bienaymé law

Source lines 694–699 (and B13 of the inventory): for a critical offspring law `μ` with
`μ_1 ≠ 1` (the paper's standing nondegeneracy assumption), the weights
`∏_{u∈T} μ_{k_u(T)}` of the finite plane trees sum to one, so `bienayme μ` is a probability
measure (`PlaneTree.bienayme_isProbabilityMeasure`). Equivalently, the critical nondegenerate
Bienaymé tree is almost surely finite (extinction).

Route: the total weight `q = 𝐏_μ(univ)` satisfies `q ≤ 1` for every `μ`
(`PlaneTree.bienayme_univ_le_one`, by truncation in height) and, by the branching property,
`q = f_μ(q)` for the generating function `f_μ(s) = ∑ μ_k s^k`. For critical `μ` with
`μ_1 ≠ 1`, Bernoulli's inequality `s^k ≥ 1 + k (s - 1)`, strict for `k ≥ 2` and `s < 1`, and
`∑ k μ_k = 1` show that `1` is the only fixed point of `f_μ` in `[0, 1]`. Along the way:
`μ_0 ≠ 0` and `μ_j ≠ 0` for some `j ≥ 2`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PoissonDeclumping

/-- The generating function `f_μ(s) = ∑_k μ_k s^k` of an offspring law, on `[0, ∞]`. -/
noncomputable def offspringGF (μ : PMF ℕ) (s : ℝ≥0∞) : ℝ≥0∞ := ∑' k, μ k * s ^ k

variable {μ : PMF ℕ}

theorem offspringGF_zero (μ : PMF ℕ) : offspringGF μ 0 = μ 0 := by
  rw [offspringGF, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

theorem offspringGF_one (μ : PMF ℕ) : offspringGF μ 1 = 1 := by
  simp [offspringGF, μ.tsum_coe]

theorem offspringGF_le_one (μ : PMF ℕ) {s : ℝ≥0∞} (hs : s ≤ 1) : offspringGF μ s ≤ 1 :=
  (ENNReal.tsum_le_tsum fun _ => mul_le_of_le_one_right' (pow_le_one₀ zero_le hs)).trans
    μ.tsum_coe.le

/-- A critical law with `μ_1 ≠ 1` puts mass on some `j ≥ 2`. -/
theorem IsCritical.exists_two_le_ne_zero (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ j, 2 ≤ j ∧ μ j ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  have hc' := hc
  rw [IsCritical, tsum_eq_single 1] at hc'
  · simpa using hc'
  · intro j hj
    rcases j with _ | _ | j
    · simp
    · exact absurd rfl hj
    · simp [h (j + 2) (by omega)]

/-- Strict Bernoulli inequality: `1 + j (x - 1) < x ^ j` for `0 ≤ x < 1` and `j ≥ 2`. -/
private theorem one_add_mul_sub_lt_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∀ m : ℕ, 1 + ((m + 2 : ℕ) : ℝ) * (x - 1) < x ^ (m + 2)
  | 0 => by
    push_cast
    nlinarith [sq_pos_of_pos (sub_pos.2 hx1)]
  | m + 1 => by
    have ih := one_add_mul_sub_lt_pow hx0 hx1 m
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    push_cast at ih ⊢
    rw [pow_succ]
    nlinarith [sq_pos_of_pos (sub_pos.2 hx1), mul_le_mul_of_nonneg_right ih.le hx0]

/-- For critical `μ` with `μ_1 ≠ 1`, the only fixed point of `f_μ` in `[0, 1]` is `1`
(convexity of the generating function, `f_μ(1) = 1`, `f_μ'(1) = 1`). -/
theorem IsCritical.eq_one_of_offspringGF_eq (hc : IsCritical μ) (hne : μ 1 ≠ 1) {s : ℝ≥0∞}
    (hs : s ≤ 1) (hfix : offspringGF μ s = s) : s = 1 := by
  by_contra hs1
  obtain ⟨j, hj, hμj⟩ := hc.exists_two_le_ne_zero hne
  have hst : s ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hs
  set x := s.toReal with hxdef
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  have hx1 : x < 1 := by
    have : s < 1 := lt_of_le_of_ne hs hs1
    rw [hxdef]
    exact ENNReal.toReal_lt_of_lt_ofReal (by simpa using this)
  have hsx : s = ENNReal.ofReal x := (ENNReal.ofReal_toReal hst).symm
  -- `s^k + k (1 - s)` as a real number
  have hkey : ∀ k : ℕ, s ^ k + (k : ℝ≥0∞) * (1 - s) =
      ENNReal.ofReal (x ^ k + (k : ℝ) * (1 - x)) := by
    intro k
    rw [hsx, ENNReal.ofReal_add (pow_nonneg hx0 k)
      (mul_nonneg k.cast_nonneg (by linarith)), ENNReal.ofReal_pow hx0,
      ENNReal.ofReal_mul k.cast_nonneg, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sub _ hx0, ENNReal.ofReal_one]
  have hle : ∀ k : ℕ, 1 ≤ s ^ k + (k : ℝ≥0∞) * (1 - s) := by
    intro k
    rw [hkey, ENNReal.one_le_ofReal]
    have := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ x by linarith) k
    linarith
  have hlt : 1 < s ^ j + (j : ℝ≥0∞) * (1 - s) := by
    rw [hkey, ENNReal.one_lt_ofReal]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hj
    have := one_add_mul_sub_lt_pow hx0 hx1 m
    linarith
  have hsum : ∑' k, μ k * (s ^ k + (k : ℝ≥0∞) * (1 - s)) = 1 := by
    simp only [mul_add, ENNReal.tsum_add]
    have : ∀ k : ℕ, μ k * ((k : ℝ≥0∞) * (1 - s)) = (1 - s) * ((k : ℝ≥0∞) * μ k) := by
      intro k; ring
    simp only [this, ENNReal.tsum_mul_left]
    rw [show ∑' k, μ k * s ^ k = offspringGF μ s from rfl, hfix]
    rw [show ∑' k : ℕ, (k : ℝ≥0∞) * μ k = 1 from hc, mul_one, add_tsub_cancel_of_le hs]
  have hlt' : ∑' k, μ k * 1 < ∑' k, μ k * (s ^ k + (k : ℝ≥0∞) * (1 - s)) := by
    refine ENNReal.tsum_lt_tsum (i := j) ?_ (fun k => by gcongr; exact hle k) ?_
    · simp [μ.tsum_coe]
    · exact (ENNReal.mul_lt_mul_iff_right hμj (μ.apply_ne_top j)).2 hlt
  simp [μ.tsum_coe, hsum] at hlt'

/-- A critical law with `μ_1 ≠ 1` gives positive mass to `0`. -/
theorem IsCritical.apply_zero_ne_zero (hc : IsCritical μ) (hne : μ 1 ≠ 1) : μ 0 ≠ 0 := by
  intro h0
  have := hc.eq_one_of_offspringGF_eq hne zero_le (by rw [offspringGF_zero, h0])
  exact zero_ne_one this

namespace PlaneTree

/-- The total weight `q = 𝐏_μ(T finite)` is a fixed point of the generating function. -/
theorem offspringGF_bienayme_univ (μ : PMF ℕ) :
    offspringGF μ (bienayme μ Set.univ) = bienayme μ Set.univ := by
  rw [offspringGF, ← bienayme_forall_children_mem]
  simp

/-- **Normalization** (source lines 694–699, "implicitly `μ_1 ≠ 1`"): for a critical offspring
law with `μ_1 ≠ 1`, the Bienaymé weights of the finite plane trees sum to one, i.e. the
critical Bienaymé tree is almost surely finite. -/
theorem bienayme_univ (hc : IsCritical μ) (hne : μ 1 ≠ 1) : bienayme μ Set.univ = 1 :=
  hc.eq_one_of_offspringGF_eq hne (bienayme_univ_le_one μ) (offspringGF_bienayme_univ μ)

theorem bienayme_isProbabilityMeasure (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    IsProbabilityMeasure (bienayme μ) :=
  ⟨bienayme_univ hc hne⟩

/-- Instance form of `bienayme_isProbabilityMeasure`, for use with `Fact` hypotheses. -/
instance isProbabilityMeasure_bienayme [hc : Fact (IsCritical μ)] [hne : Fact (μ 1 ≠ 1)] :
    IsProbabilityMeasure (bienayme μ) :=
  bienayme_isProbabilityMeasure hc.out hne.out

/-- The weights `∏_{u∈T} μ_{k_u(T)}` of all finite plane trees sum to one. -/
theorem tsum_weight (hc : IsCritical μ) (hne : μ 1 ≠ 1) : ∑' T, weight μ T = 1 := by
  rw [← bienayme_univ hc hne, bienayme_apply]
  simp

/-! ### The root degree and the conditional branching property -/

/-- `𝐏_μ(k_∅ = k) = μ_k 𝐏_μ(univ)^k` for every offspring law. -/
theorem bienayme_rootDegree_eq_mul_pow (μ : PMF ℕ) (k : ℕ) :
    bienayme μ {T | T.rootDegree = k} = μ k * bienayme μ Set.univ ^ k := by
  have h := bienayme_rootDegree_eq_children_mem μ k fun _ => Set.univ
  simp only [Set.mem_univ, implies_true, and_true, Finset.prod_const, Finset.card_range] at h
  exact h

/-- For critical `μ` with `μ_1 ≠ 1`, the root degree of a `μ`-Bienaymé tree has law `μ`. -/
theorem bienayme_rootDegree_eq (hc : IsCritical μ) (hne : μ 1 ≠ 1) (k : ℕ) :
    bienayme μ {T | T.rootDegree = k} = μ k := by
  rw [bienayme_rootDegree_eq_mul_pow, bienayme_univ hc hne, one_pow, mul_one]

theorem map_rootDegree_bienayme (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    (bienayme μ).map rootDegree = μ.toMeasure := by
  refine Measure.ext_iff_singleton.2 fun k => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton k),
    PMF.toMeasure_apply_singleton μ k (measurableSet_singleton k)]
  exact bienayme_rootDegree_eq hc hne k

/-- **Branching property, conditional form** (source lines 696–698): for critical `μ` with
`μ_1 ≠ 1` and `μ_k ≠ 0`, conditionally on the root having `k` children, the child subtrees
`T_0, …, T_{k-1}` are independent `μ`-Bienaymé trees:
`𝐏_μ(T_i ∈ A_i for all i < k | k_∅ = k) = ∏_{i<k} 𝐏_μ(A_i)`. -/
theorem cond_rootDegree_children_mem (hc : IsCritical μ) (hne : μ 1 ≠ 1) {k : ℕ} (hk : μ k ≠ 0)
    (A : ℕ → Set PlaneTree) :
    ProbabilityTheory.cond (bienayme μ) {T | T.rootDegree = k}
        {T | ∀ (i : ℕ) (hi : i < T.children.length), T.children[i] ∈ A i} =
      ∏ i ∈ Finset.range k, bienayme μ (A i) := by
  rw [ProbabilityTheory.cond_apply MeasurableSet.of_discrete, bienayme_rootDegree_eq hc hne]
  have : {T : PlaneTree | T.rootDegree = k} ∩
      {T | ∀ (i : ℕ) (hi : i < T.children.length), T.children[i] ∈ A i} =
      {T | T.rootDegree = k ∧ ∀ (i : ℕ) (hi : i < T.children.length), T.children[i] ∈ A i} :=
    rfl
  rw [this, bienayme_rootDegree_eq_children_mem, ENNReal.inv_mul_cancel_left hk (μ.apply_ne_top k)]

end PlaneTree
end PoissonDeclumping
