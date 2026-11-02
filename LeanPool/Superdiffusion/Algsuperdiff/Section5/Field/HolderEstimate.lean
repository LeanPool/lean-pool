/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.Holder

/-!
# HolderEstimate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stream-field Hölder estimate

This module joins the crossover estimate at distances below one to the linear
growth estimate at larger distances.  The resulting exponent is `gamma / 2`
and the radius-dependent modulus has polynomial growth of degree one.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open HCPolySupport
open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

private theorem norm_le_sqrt_vecNormSq_estimate (x : Vec d) :
    ‖x‖ ≤ Real.sqrt (vecNormSq x) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (HCPolySupport.sq_apply_le_vecNormSq x i)

/-- **The quantitative stream-field modulus.**  On the Euclidean ball of
radius `R ≥ 1`, the field is Hölder continuous with exponent `M.gamma / 2` and
constant `streamFieldHolderConst M omega * (1 + R)`. -/
theorem matrixOperatorNorm_streamField_sub_le (M : ABKModel d)
    (omega : FullSample d M.gamma) {R : ℝ} (hR : 1 ≤ R)
    {x y : Vec d} (hx : Real.sqrt (vecNormSq x) ≤ R)
    (hy : Real.sqrt (vecNormSq y) ≤ R) :
    matrixOperatorNorm (streamField omega x - streamField omega y) ≤
      streamFieldHolderModulus M omega R *
        Real.rpow ‖x - y‖ (streamHolderExponent M) := by
  by_cases hxy : x = y
  · subst y
    rw [sub_self, matrixOperatorNorm_zero]
    exact mul_nonneg
      (mul_nonneg (streamFieldHolderConst_nonneg M omega)
        (by linarith only [hR]))
      (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hsmall : ‖x - y‖ < 1
  · exact matrixOperatorNorm_streamField_sub_le_small M omega hR hx hy hxy hsmall
  · have hdist : 1 ≤ ‖x - y‖ := not_lt.1 hsmall
    have hpow : 1 ≤ Real.rpow ‖x - y‖ (streamHolderExponent M) :=
      Real.one_le_rpow hdist (streamHolderExponent_pos M).le
    have hxGrowth := matrixOperatorNorm_streamField_le_of_euclidean M omega hR hx
    have hyGrowth := matrixOperatorNorm_streamField_le_of_euclidean M omega hR hy
    have hentry : ∀ i k : Fin d,
        |(streamField omega x - streamField omega y) i k| ≤
          2 * streamFieldGrowthConst M omega * (1 + R) := by
      intro i k
      simp only [Matrix.sub_apply]
      calc
        |streamField omega x i k - streamField omega y i k| ≤
            |streamField omega x i k| + |streamField omega y i k| := abs_sub _ _
        _ ≤ matrixOperatorNorm (streamField omega x) +
            matrixOperatorNorm (streamField omega y) :=
          add_le_add (abs_entry_le_matrixOperatorNorm _ i k)
            (abs_entry_le_matrixOperatorNorm _ i k)
        _ ≤ 2 * streamFieldGrowthConst M omega * (1 + R) := by
          linarith only [hxGrowth, hyGrowth]
    have hmatrix : matrixOperatorNorm (streamField omega x - streamField omega y) ≤
        (d : ℝ) ^ 2 * (2 * streamFieldGrowthConst M omega * (1 + R)) := by
      calc
        matrixOperatorNorm (streamField omega x - streamField omega y) ≤
            ∑ i, ∑ k, |(streamField omega x - streamField omega y) i k| := by
          have h := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
            (streamField omega x - streamField omega y) (0 : Mat d)
          simpa only [matrixOperatorNorm_zero, Matrix.zero_apply, sub_zero, zero_add] using h
        _ ≤ ∑ _i : Fin d, ∑ _k : Fin d,
            2 * streamFieldGrowthConst M omega * (1 + R) := by
          gcongr with i _ k _
          exact hentry i k
        _ = (d : ℝ) ^ 2 * (2 * streamFieldGrowthConst M omega * (1 + R)) := by
          simp [pow_two]
          ring
    have hcoeff : 2 * (d : ℝ) ^ 2 * streamFieldGrowthConst M omega ≤
        streamFieldHolderConst M omega :=
      two_mul_dim_sq_mul_growthConst_le_holderConst M omega
    have hR0 : 0 ≤ 1 + R := by linarith only [hR]
    have hbase : (d : ℝ) ^ 2 * (2 * streamFieldGrowthConst M omega * (1 + R)) ≤
        streamFieldHolderConst M omega * (1 + R) := by
      have := mul_le_mul_of_nonneg_right hcoeff hR0
      convert this using 1
      all_goals first | rfl | ring
    have hmod0 : 0 ≤ streamFieldHolderModulus M omega R :=
      mul_nonneg (streamFieldHolderConst_nonneg M omega) hR0
    exact hmatrix.trans (hbase.trans (by
      have hmul := mul_le_mul_of_nonneg_left hpow hmod0
      simpa only [streamFieldHolderModulus, mul_one] using hmul))

/-- Euclidean-distance form of the quantitative modulus. -/
theorem matrixOperatorNorm_streamField_sub_le_of_euclidean (M : ABKModel d)
    (omega : FullSample d M.gamma) {R : ℝ} (hR : 1 ≤ R)
    {x y : Vec d} (hx : Real.sqrt (vecNormSq x) ≤ R)
    (hy : Real.sqrt (vecNormSq y) ≤ R) :
    matrixOperatorNorm (streamField omega x - streamField omega y) ≤
      streamFieldHolderModulus M omega R *
        Real.rpow (Real.sqrt (vecNormSq (x - y))) (streamHolderExponent M) := by
  have hfield := matrixOperatorNorm_streamField_sub_le M omega hR hx hy
  have hdist := norm_le_sqrt_vecNormSq_estimate (x - y)
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hdist (streamHolderExponent_pos M).le
  exact hfield.trans (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (streamFieldHolderConst_nonneg M omega) (by linarith only [hR])))

end

end Algsuperdiff.Section5.Field
