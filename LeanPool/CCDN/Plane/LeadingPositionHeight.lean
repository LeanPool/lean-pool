/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.Algebra.HomogeneousTranslation
public import LeanPool.CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import LeanPool.CCDN.Algebra.HomogeneousEvaluation
import LeanPool.CCDN.Algebra.HomogeneousRankDichotomy
import LeanPool.CCDN.ForMathlib.Log
import LeanPool.CCDN.Plane.GridHeight
import LeanPool.CCDN.Plane.HomogeneousLeadingCoefficient

/-!
The bounded leading-coefficient translation has a controlled height cost.
Its logarithmic coefficient-position loss is at most 14d².

Coefficient height controls homogeneous evaluations, uniformly on the
integer point box, with the exact number of monomials.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem homogeneous_integer_evaluation_bound {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d)
    {H R : ℝ} (hH : 0 ≤ H) (hR : 1 ≤ R) (hcoeff : CoefficientHeightLE f H)
    (x : Fin (n + 1) → ℤ) (hx : InBox x R) :
    |(eval x f : ℝ)| ≤ ((n + d).choose d : ℝ) * H * R ^ d := by
  classical
  conv_lhs => rw [homogeneous_eq_sum_coeff f hf]
  simp only [map_sum, eval_monomial, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ j, |(f.coeff (homogeneousMonomials n d j) : ℝ) *
      (((homogeneousMonomials n d j).prod (fun i k => x i ^ k) : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin ((n + d).choose d), H * R ^ d := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hcoeff _) (abs_monomial_value_le _ x hR hx
        (homogeneousMonomials_degree n d j).le) (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

private lemma ternary_homogeneous_dimension_le_square (d : ℕ) :
    ((2 + d).choose d : ℝ) ≤ ((d : ℝ) + 2) ^ 2 := by
  have h : 2 * ((2 + d).choose d : ℝ) = ((d : ℝ) + 2) * (d + 1) := by
    exact_mod_cast ternary_homogeneous_dimension d
  nlinarith [show (0 : ℝ) ≤ d by positivity]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Real

/-- The height-loss factor `(d + 1) ^ (4 (d + 1)) (d + 2) ^ 2 (2 d + 1) ^ d` by which the
coefficients of the affine chart of a ternary form of degree `d`, after a translation with
parameters in `[0, d]`, may exceed a coefficient height `L` of the form (measured as
`(d + 1) ^ (2 (d + 1)) * L`); see `homogeneousTranslation_chart_coefficient_bound`. -/
def leadingPositionHeightFactor (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) ^ (4 * (d + 1)) * ((d : ℝ) + 2) ^ 2 * (2 * (d : ℝ) + 1) ^ d

/-- The factor `leadingPositionHeightFactor d` is at least `1`. -/
lemma leadingPositionHeightFactor_one_le (d : ℕ) : 1 ≤ leadingPositionHeightFactor d := by
  unfold leadingPositionHeightFactor
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    · exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  · exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)

/-- For `d ≥ 1`, the logarithm of `leadingPositionHeightFactor d` is at most `14 d²`. -/
lemma leadingPositionHeightFactor_log_le {d : ℕ} (hd : 0 < d) :
    Real.log (leadingPositionHeightFactor d) ≤ 14 * (d : ℝ) ^ 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h₁ : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  have h₂ : Real.log ((d : ℝ) + 2) ≤ d + 1 := by
    rw [show (d : ℝ) + 2 = (d + 1) + 1 by ring]
    exact Real.log_add_one_le_self (by positivity)
  have h₃ : Real.log (2 * (d : ℝ) + 1) ≤ 2 * d := Real.log_add_one_le_self (by positivity)
  unfold leadingPositionHeightFactor
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  calc
    _ ≤ 4 * ((d : ℝ) + 1) * d + 2 * ((d : ℝ) + 1) + d * (2 * d) := by gcongr
    _ ≤ _ := by nlinarith

/-- Control the transformed coefficients through interpolation of translated
grid values. -/
theorem homogeneousTranslation_chart_coefficient_bound {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (a : Fin 2 → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    {L : ℝ} (hL : 0 ≤ L)
    (hcoeff : CoefficientHeightLE f (((d : ℝ) + 1) ^ (2 * (d + 1)) * L))
    (m : Fin 2 →₀ ℕ) :
    |((affineChart 2 (homogeneousTranslation ℤ a f)).coeff m : ℝ)| ≤
      leadingPositionHeightFactor d * L := by
  let K := ((d : ℝ) + 1) ^ (2 * (d + 1))
  let V := ((d : ℝ) + 2) ^ 2 * (K * L) * (2 * (d : ℝ) + 1) ^ d
  have heval (x y : ℕ) (hx : x ≤ d) (hy : y ≤ d) :
      |(eval ![(x : ℤ), (y : ℤ)] (affineChart 2 (homogeneousTranslation ℤ a f)) : ℝ)| ≤ V := by
    let z : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
    have hz : ∀ j, 0 ≤ z j ∧ z j ≤ d := by
      intro j
      fin_cases j
      · change 0 ≤ (x : ℤ) ∧ (x : ℤ) ≤ d
        exact ⟨by positivity, by exact_mod_cast hx⟩
      · change 0 ≤ (y : ℤ) ∧ (y : ℤ) ≤ d
        exact ⟨by positivity, by exact_mod_cast hy⟩
    have hbox : ∀ j, |((Fin.cons 1 (z + a) : Fin 3 → ℤ) j : ℝ)| ≤ 2 * d + 1 := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cons_zero, Int.cast_one, abs_one]
        have := Nat.cast_nonneg (α := ℝ) d
        linarith
      · simp only [Fin.cons_succ, Pi.add_apply, Int.cast_add]
        have hz0 : (0 : ℝ) ≤ z k := by exact_mod_cast (hz k).1
        have ha0 : (0 : ℝ) ≤ a k := by exact_mod_cast (ha k).1
        have hzd : (z k : ℝ) ≤ d := by exact_mod_cast (hz k).2
        have had : (a k : ℝ) ≤ d := by exact_mod_cast (ha k).2
        rw [abs_of_nonneg (by linarith)]
        linarith
    rw [affineChart_eval, homogeneousTranslation_eval_chart]
    have h := homogeneous_integer_evaluation_bound f hf (show 0 ≤ K * L by dsimp [K]; positivity)
      (show (1 : ℝ) ≤ 2 * d + 1 by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      hcoeff (Fin.cons 1 (z + a)) hbox
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ternary_homogeneous_dimension_le_square d) (by positivity))
      (by positivity)
  have h := integer_plane_coefficient_bound_of_grid (affineChart 2 (homogeneousTranslation ℤ a f))
    ((affineChart_totalDegree_le _).trans (homogeneousTranslation_homogeneous a hf).totalDegree_le)
    (show 0 ≤ V by dsimp [V, K]; positivity) heval m
  convert h using 1
  dsimp only [leadingPositionHeightFactor, V, K]
  rw [show 4 * (d + 1) = 2 * (d + 1) + 2 * (d + 1) by omega, pow_add]
  ring

/-- A bounded integer translation supplies the leading-position
hypothesis with absolute constant 14, and a coefficient height at least one. -/
theorem exists_translated_coefficient_position {d : ℕ} (hd : 0 < d)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      CoefficientHeightLE (affineChart 2 (homogeneousTranslation ℤ a f)) H ∧
      Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| ≤
        Real.log H ∧
      Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
          14 * (d : ℝ) ^ 2 := by
  obtain ⟨a, ha, hne, hcoeff⟩ := exists_bounded_leading_coefficient_translation f hf hf0
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Int.one_le_abs hne
  have hP := leadingPositionHeightFactor_one_le d
  have hpos : 0 < leadingPositionHeightFactor d := by linarith
  have hLpos : 0 < L := by linarith
  refine ⟨a, leadingPositionHeightFactor d * L, ha, one_le_mul_of_one_le_of_one_le hP hL,
    homogeneousTranslation_chart_coefficient_bound f hf a ha hLpos.le hcoeff, ?_, ?_⟩
  · apply Real.log_le_log hLpos
    nlinarith
  · rw [Real.log_mul hpos.ne' hLpos.ne']
    have h := leadingPositionHeightFactor_log_le hd
    linarith

end
end CCDN
