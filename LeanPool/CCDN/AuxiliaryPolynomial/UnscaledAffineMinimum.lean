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
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import LeanPool.CCDN.Height.ScaledHypersurfaceHeight

/-! The ordinary homogenization attains the affine box exponent on every
polynomial range in the degree, with both terms of the minimum retained. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient height of the leading homogeneous component of an integer polynomial is at most
the coefficient height of the polynomial itself. -/
lemma leading_height_le_coefficient_height {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) :
    (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ≤
      (integerCoefficientHeight f : ℝ) := by
  simpa only [Int.cast_one, one_pow, one_mul,
    integerCoefficientHeight_scaledHomogenize_one] using
      scaledHomogenize_leading_height_lower f (h := 1) le_rfl

/-- Both coefficient-sensitive branches hold for the unscaled model itself.
This estimate preserves their minimum before applying the box estimate. -/
private theorem unscaled_hypersurface_minimum_height_bound {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {B : ℝ} (hB : 1 ≤ B) :
    (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) *
        hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f) /
          (integerCoefficientHeight f : ℝ) ^
            (1 / ((n + 1 : ℝ) * f.totalDegree * (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ)))) ≤
      max (affineHeightTransferConstant n) (Real.exp 1) *
        (f.totalDegree : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
        min (Real.log (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) +
          f.totalDegree * Real.log B + (f.totalDegree : ℝ) ^ 2)
          ((f.totalDegree : ℝ) ^ 2 *
            hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) /
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ^
          (1 / ((n + 1 : ℝ) * f.totalDegree * (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ)))) := by
  let d := f.totalDegree
  let F := scaledHomogenize d 1 f
  let H := (integerCoefficientHeight f : ℝ)
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor F
  let K := max (affineHeightTransferConstant n) (Real.exp 1)
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  have hd0 : (0 : ℝ) < d := by dsimp only [d]; exact_mod_cast hd
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hLH : L ≤ H := leading_height_le_coefficient_height f
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg F
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero d one_ne_zero hf
  have hFdegree : F.totalDegree = d :=
    (scaledHomogenize_homogeneous (1 : ℤ) f le_rfl).totalDegree hF0
  have hKheight : affineHeightTransferConstant n ≤ K := le_max_left _ _
  have hK1 : 1 ≤ K := by
    have hh : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    exact hh.trans (le_max_right _ _)
  have hT : 0 ≤ T := by
    dsimp only [T]
    exact add_nonneg (add_nonneg (Real.log_nonneg hL)
      (mul_nonneg hd0.le (Real.log_nonneg hB))) (sq_nonneg _)
  have hlog : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * T / L ^ q := by
    have htransfer := hypersurface_badPrime_height_transfer F hF0 hFdegree hd hL
      (by simpa only [F, integerCoefficientHeight_scaledHomogenize_one] using hLH)
    have ht : Real.log L + (d : ℝ) ^ 2 ≤ T := by
      dsimp only [T]
      have hh := mul_nonneg hd0.le (Real.log_nonneg hB)
      linarith
    have hheight0 : 0 ≤ affineHeightTransferConstant n := by
      unfold affineHeightTransferConstant
      exact mul_nonneg (by positivity) (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
    change (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤ _
    calc
      _ ≤ affineHeightTransferConstant n *
          (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log L + (d : ℝ) ^ 2) / L ^ q := by
        simpa only [F, b, H, q, affineHeightTransferConstant,
          integerCoefficientHeight_scaledHomogenize_one] using htransfer
      _ ≤ K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * T / L ^ q := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_right hKheight (by positivity))
          ht (by positivity) (by positivity)
  have hfactor : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) / L ^ q := by
    have hpow : L ^ q ≤ H ^ q :=
      Real.rpow_le_rpow hL0.le hLH (by dsimp [q]; positivity)
    have he : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) =
        (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ 2 :=
      rpow_four_sub_eq_mul_sq hd0 n
    calc
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) / L ^ q := by
        rw [he]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hK1
          (show 0 ≤ (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) / L ^ q by positivity)
        simpa only [one_mul, mul_assoc, mul_div_assoc] using hh
  change _ ≤ K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * min T ((d : ℝ) ^ 2 * b) / L ^ q
  rcases le_total T ((d : ℝ) ^ 2 * b) with h | h
  · rw [min_eq_left h]
    exact hlog
  · rw [min_eq_right h]
    exact hfactor

/-- The full auxiliary degree bound retains both branches of the minimum
on every box bounded polynomially in the degree. -/
private theorem unscaled_hypersurface_auxiliary_minimum_bound {n k : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {S B : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * ((f.totalDegree : ℝ) + 1) ^ k) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f))
        (integerCoefficientHeight f : ℝ) ≤
      affineMinimumAuxiliaryBound n f.totalDegree
        (Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  let d := f.totalDegree
  let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
  let H := (integerCoefficientHeight f : ℝ)
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let K := max (affineHeightTransferConstant n) (Real.exp 1)
  let E := Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))
  let T := min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b)
  let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let β := 1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  have hcoef : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * T / L ^ q :=
    unscaled_hypersurface_minimum_height_bound f hf hd hB
  have hpower : B ^ α ≤ E * B ^ β := by
    have hh := polynomial_box_projective_power_bound (r := n + 1) (by omega) hd hS hB hbound
    simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using hh
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
  have hcoefficient : 0 ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) hb)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hmain : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b * B ^ α / H ^ q ≤
      K * E * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * T * B ^ β / L ^ q := by
    convert mul_le_mul hcoef hpower (Real.rpow_nonneg (by linarith : 0 ≤ B) α)
      (hcoefficient.trans hcoef) using 1 <;> ring
  unfold hypersurfaceAuxiliaryDegreeBound affineMinimumAuxiliaryBound
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain le_rfl) le_rfl)
    (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le

/-- An affine auxiliary with the minimum degree bound in the
polynomial box range. The constant coefficient is arbitrary. -/
theorem unscaled_affine_auxiliary_minimum {n k : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {S B : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * ((f.totalDegree : ℝ) + 1) ^ k) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree
        (Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨g, hg, hgdeg⟩ := unscaled_affine_auxiliary f hprim hir hd hB
  exact ⟨g, hg, hgdeg.trans
    (unscaled_hypersurface_auxiliary_minimum_bound f hir.ne_zero hd hS hB hbound)⟩

end
end CCDN
