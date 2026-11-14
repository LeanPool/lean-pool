/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Average.Influence
public import LeanPool.AaronsonAmbainis.Row.Degree

/-!
# The theorems for functions of bounded degree, from the links

A function `f` on the cube with `|f| ≤ 1` and degree at most `d` has a row of cost at most
`π² d²` at every point (`RowBoundPM`, Theorem 6.8 of the paper), and
`∑_j |f(x) - f(x^j)| ≤ 4 d²` at every point `x` (`SensitivityBound`, Corollary 6.10). With these
two inputs:

* `mainTheorem_of_influence : InfluenceBound → SensitivityBound → RowBoundPM → MainTheorem` —
  the main theorem (Theorem 1.1 of the paper). The bound for the influences (Theorem 8.3) with
  `K = π² d²` and `L(f) ≤ 4 d²` reads
  `3 Var(f)^5 ≤ 3125 (4 d²)² (π² d²)^4 Inf_j(f)² = 50000 π^8 d^12 Inf_j(f)²`.
* `meanIncrementDegree_of_meanIncrement :
  MeanIncrementBound → RowBoundPM → MeanIncrementDegreeBound` —
  the bound for the mean absolute increments (Theorem 7.10) with `K = π² d²`, which is
  Corollary 7.11 of the paper: `Var(f)^3 ≤ 36 (π² d²)^4 L_j(f)² = 36 π^8 d^8 L_j(f)²`.
* `mainTheoremImproved_of_influence :
  InfluenceBound → SensitivityBound → RowBound → MainTheoremImproved` —
  the main theorem with the constant `3125 π^8` in place of `50000 π^8` (Remark 8.4 of the
  paper). Its hypothesis `RowBound` is the row bound of Agarwal and Ben-David (Theorem 1.7 of
  arXiv:2410.19062), which is not proved in this project; it gives rows of cost at most
  `π² d² / 2` (`rows_of_rowBound`), and `3125 (4 d²)² (π² d² / 2)^4 = 3125 π^8 d^12`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

/-- The main theorem (Theorem 1.1 of the paper) from the bound for the influences (Theorem 8.3),
the sensitivity bound (Corollary 6.10) and the row bound (Theorem 6.8). -/
theorem mainTheorem_of_influence :
    InfluenceBound → SensitivityBound → RowBoundPM → MainTheorem := by
  intro hI hS hR ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := hR ι d f hf hdeg
  obtain ⟨j, hj⟩ := Average.influence_of_incr hI f a ha0 haK hacov (hS ι d f hf hdeg) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring

/-- The bound for the mean absolute increments of a bounded function of degree at most `d`
(Corollary 7.11 of the paper), from the bound for functions with rows of cost at most `K`
(Theorem 7.10) and the row bound (Theorem 6.8). -/
theorem meanIncrementDegree_of_meanIncrement :
    MeanIncrementBound → RowBoundPM → MeanIncrementDegreeBound := by
  intro hM hR ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := hR ι d f hf hdeg
  obtain ⟨j, hj⟩ := hM ι f (Real.pi ^ 2 * (d : ℝ) ^ 2) a ha0 haK hacov hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring

/-- The row bound of Agarwal and Ben-David (the hypothesis `RowBound`) for a function `f` with
values in `[-1,1]`: applied to `(1 + f)/2`, with the weights doubled, it gives rows of `f` of
cost at most `π² d² / 2`. -/
theorem rows_of_rowBound (hRB : RowBound) {ι : Type} [Fintype ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d) :
    ∃ a : Cube ι → ι → ℝ, (∀ x i, 0 ≤ a x i) ∧
      (∀ x, ∑ i, a x i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 / 2) ∧
      ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i := by
  classical
  -- `(1 + f)/2` has degree at most `d` and takes values in `[0,1]`
  have hdeg' : HasDegreeLE (fun x => 1 / 2 + 1 / 2 * f x) d :=
    Row.hasDegreeLE_add (Row.hasDegreeLE_const (1 / 2) d)
      (Row.hasDegreeLE_const_mul (1 / 2) hdeg)
  have hr : ∀ x, 0 ≤ 1 / 2 + 1 / 2 * f x ∧ 1 / 2 + 1 / 2 * f x ≤ 1 := by
    intro x
    have h1 := abs_le.mp (hf x)
    constructor <;> linarith [h1.1, h1.2]
  obtain ⟨c, hc1, hc2⟩ := hRB ι d (fun x => 1 / 2 + 1 / 2 * f x) hr hdeg'
  -- the weights are nonnegative: take `y = x^i`
  have hnn : ∀ x i, 0 ≤ c x i := fun x i =>
    le_trans (abs_nonneg _) (Level.abs_incr_le_of_rows hc1 x i)
  refine ⟨fun x i => 2 * c x i, fun x i => mul_nonneg (by norm_num) (hnn x i),
    fun x => ?_, fun x y => ?_⟩
  · have h2 := hc2 x
    rw [← Finset.mul_sum]
    linarith
  · have h1 : |(1 / 2 + 1 / 2 * f x) - (1 / 2 + 1 / 2 * f y)| ≤ ∑ i ∈ diffSet x y, c x i :=
      hc1 x y
    have e : (1 / 2 + 1 / 2 * f x) - (1 / 2 + 1 / 2 * f y) = (f x - f y) / 2 := by ring
    rw [e, abs_div, abs_two] at h1
    rw [← Finset.mul_sum]
    linarith

/-- The main theorem with the constant that the row bound of Agarwal and Ben-David gives
(Remark 8.4 of the paper), from the bound for the influences, the sensitivity bound and the
hypothesis `RowBound`. -/
theorem mainTheoremImproved_of_influence :
    InfluenceBound → SensitivityBound → RowBound → MainTheoremImproved := by
  intro hI hS hRB ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := rows_of_rowBound hRB d f hf hdeg
  obtain ⟨j, hj⟩ := Average.influence_of_incr hI f a ha0 haK hacov (hS ι d f hf hdeg) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring

end AaronsonAmbainis
