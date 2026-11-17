/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import LeanPool.CCDN.AuxiliaryPolynomial.AffineHeightCutoff
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledAffineMinimum
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import LeanPool.CCDN.Height.ScaledHypersurfaceHeight

/-! All box and coefficient cases for the affine auxiliary theorem when
the constant coefficient is nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The affine auxiliary degree bound `affineMinimumAuxiliaryBound` is monotone in the
comparison constant `A`, for `1 ≤ B`, `1 ≤ L` and `0 ≤ b`. -/
lemma affineMinimumAuxiliaryBound_mono_A (n d : ℕ) {A A' B L b : ℝ}
    (hA : A ≤ A') (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineMinimumAuxiliaryBound n d A B L b ≤ affineMinimumAuxiliaryBound n d A' B L b := by
  have hT : 0 ≤ Real.log L + d * Real.log B + (d : ℝ) ^ 2 := by
    exact add_nonneg (add_nonneg (Real.log_nonneg hL)
      (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB))) (sq_nonneg _)
  have hmin := le_min hT (mul_nonneg (sq_nonneg (d : ℝ)) hb)
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) :=
    (Real.exp_pos 1).le.trans (le_max_right _ _)
  have hC := (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  unfold affineMinimumAuxiliaryBound
  gcongr

/-- The affine auxiliary degree bound `affineMinimumAuxiliaryBound` is monotone in the
bad-prime factor `b`, for `0 ≤ A`, `1 ≤ B` and `1 ≤ L`. -/
lemma affineMinimumAuxiliaryBound_mono_b (n d : ℕ) {A B L b b' : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : b ≤ b') :
    affineMinimumAuxiliaryBound n d A B L b ≤ affineMinimumAuxiliaryBound n d A B L b' := by
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) :=
    (Real.exp_pos 1).le.trans (le_max_right _ _)
  have hC := (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  unfold affineMinimumAuxiliaryBound
  gcongr

/-- The affine auxiliary degree bound is at least the degree `d` whenever `0 < d`, so the
equation itself always meets it. -/
lemma degree_le_affineMinimumAuxiliaryBound (n : ℕ) {d : ℕ} (hd : 0 < d)
    {A B L b : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    (d : ℝ) ≤ affineMinimumAuxiliaryBound n d A B L b := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hdD : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
  have hT : 0 ≤ Real.log L + d * Real.log B + (d : ℝ) ^ 2 :=
    add_nonneg (add_nonneg (Real.log_nonneg hL)
      (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB))) (sq_nonneg _)
  have hmin := le_min hT (mul_nonneg (sq_nonneg (d : ℝ)) hb)
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) :=
    (Real.exp_pos 1).le.trans (le_max_right _ _)
  have hlog := Real.log_nonneg hB
  have hC := hypersurfaceAbsoluteAuxiliaryConstant_one_le n
  let E := max (affineHeightTransferConstant n) (Real.exp 1) * A *
      (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
      min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
      B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
        L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
      (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  unfold affineMinimumAuxiliaryBound
  exact (hdD.trans (le_add_of_nonneg_left hE)).trans
    (le_mul_of_one_le_left (by positivity) hC)

/-- The scale $4 R^2$, with `R = scalingPrimeRatio`, of the small-box threshold
`affineAuxiliaryBoxScale * (d + 1) ^ affineAuxiliaryBoxExponent n` separating the unscaled
case of the affine auxiliary theorem from the prime-scaled cases. -/
def affineAuxiliaryBoxScale : ℝ := 4 * scalingPrimeRatio ^ 2

/-- The exponent $4(n + 2) + 2$ of `d + 1` in the small-box threshold of the affine
auxiliary theorem for equations in `n + 2` variables. -/
def affineAuxiliaryBoxExponent (n : ℕ) : ℕ := 4 * (n + 2) + 2

/-- The comparison constant used uniformly over all box radii in the affine auxiliary
theorem: the larger of `scalingPrimeRatio` and the small-box scale times
$e^{(4(n + 2) + 2)(n + 2)}$. -/
def affineAuxiliaryComparisonConstant (n : ℕ) : ℝ :=
  max scalingPrimeRatio
    (Real.exp (Real.log affineAuxiliaryBoxScale + (affineAuxiliaryBoxExponent n : ℝ) * (n + 2 : ℝ)))

/-- The small-box scale `affineAuxiliaryBoxScale` is at least `1`. -/
lemma affineAuxiliaryBoxScale_one_le : 1 ≤ affineAuxiliaryBoxScale := by
  have h := scalingPrimeRatio_one_le
  unfold affineAuxiliaryBoxScale
  nlinarith

/-- The comparison constant `affineAuxiliaryComparisonConstant n` is at least `1`. -/
lemma affineAuxiliaryComparisonConstant_one_le (n : ℕ) :
    1 ≤ affineAuxiliaryComparisonConstant n :=
  scalingPrimeRatio_one_le.trans (le_max_left _ _)

/-- Every primitive irreducible equation with nonzero constant coefficient
has the affine auxiliary, uniformly over all box radii. -/
theorem affine_auxiliary_minimum_nonzero_constant {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) (hc : f.coeff 0 ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree
        (affineAuxiliaryComparisonConstant n) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor f) := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
  have hL : 1 ≤ L := leading_height_one_le f hir.ne_zero
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
  have hb' : b ≤ hypersurfaceBadPrimeFactor f :=
    hypersurfaceBadPrimeFactor_unscaledHomogenize_le f hir.ne_zero
  have hA : 1 ≤ affineAuxiliaryComparisonConstant n := affineAuxiliaryComparisonConstant_one_le n
  by_cases hsmall : B ≤ affineAuxiliaryBoxScale * ((d : ℝ) + 1) ^ affineAuxiliaryBoxExponent n
  · obtain ⟨g, hg, hgdeg⟩ := unscaled_affine_auxiliary_minimum f hprim hir hd
      affineAuxiliaryBoxScale_one_le hB hsmall
    refine ⟨g, hg, hgdeg.trans ?_⟩
    exact (affineMinimumAuxiliaryBound_mono_A n d (le_max_right _ _) hB hL hb).trans
      (affineMinimumAuxiliaryBound_mono_b n d (zero_le_one.trans hA) hB hL hb')
  · have hBA : scalingPrimeRatio ≤ B := by
      have hS : scalingPrimeRatio ≤ affineAuxiliaryBoxScale := by
        have h := scalingPrimeRatio_one_le
        unfold affineAuxiliaryBoxScale
        nlinarith
      have hpow : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ affineAuxiliaryBoxExponent n :=
        one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      have hS0 := zero_le_one.trans affineAuxiliaryBoxScale_one_le
      exact (hS.trans (le_mul_of_one_le_right hS0 hpow)).trans (le_of_not_ge hsmall)
    by_cases hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio
    · obtain ⟨g, hg, hgdeg⟩ := affine_auxiliary_minimum_of_small_constant_coefficient
        f hprim hir hd hc hBA hheight
      refine ⟨g, hg, hgdeg.trans ?_⟩
      exact (affineMinimumAuxiliaryBound_mono_A n d (le_max_left _ _) hB hL hb).trans
        (affineMinimumAuxiliaryBound_mono_b n d (zero_le_one.trans hA) hB hL hb')
    · rcases affine_coefficient_height_dichotomy f hir.ne_zero hprim hB with hh | hg
      · have hcoef : Real.log |(f.coeff 0 : ℝ)| ≤ Real.log (integerCoefficientHeight f : ℝ) :=
          Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc))
            (coefficient_abs_le_integerCoefficientHeight f 0)
        have hcut := affine_coefficient_height_cutoff (n + 2) d scalingPrimeRatio_one_le hB
          ((le_of_not_gt hheight).trans (hcoef.trans hh))
        exact (hsmall hcut).elim
      · obtain ⟨g, hg, hgdeg⟩ := hg
        refine ⟨g, hg, ?_⟩
        have hgR : (g.totalDegree : ℝ) ≤ d := by exact_mod_cast hgdeg
        exact hgR.trans (degree_le_affineMinimumAuxiliaryBound n hd (zero_le_one.trans hA) hB hL
          (hypersurfaceBadPrimeFactor_nonneg f))

end
end CCDN
