/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineNegSobolevNorm
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusNegOneScale

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.OrderComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The finite-scale negative-order conversion and its cancellation

The first theorem is the exact duality conversion once the positive test-norm
embedding is supplied.  The remaining theorems certify the scale algebra that
the inverse-radius statement consumes.
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

/-- A positive test-norm embedding gives the corresponding dual negative-order
comparison without narrowing either test class. -/
theorem negOneNorm_le_of_hsNormSq_le_h1NormSq
    {d : ℕ} {V : Set (Vec d)} {s K : ℝ} (hK : 0 < K)
    (hTest : ∀ psi : Vec d → Vec d, IsLocalVecTest V psi →
      hsNormSq V s psi ≤ ENNReal.ofReal K * h1NormSq V psi)
    (F : Vec d → Vec d) :
    negOneNorm V F ≤
      ENNReal.ofReal (Real.sqrt K) * negSobolevNorm V s F := by
  unfold negOneNorm
  apply iSup_le
  intro test
  apply dualPairing_le_negSobolevNorm_of_hsNormSq_le F test.1 hK test.2.1
  calc
    hsNormSq V s test.1 ≤
        ENNReal.ofReal K * h1NormSq V test.1 := hTest test.1 test.2.1
    _ ≤ ENNReal.ofReal K * 1 :=
      by
        simpa only [mul_comm] using
          (mul_le_mul_left test.2.2 (ENNReal.ofReal K))
    _ = ENNReal.ofReal K := mul_one _

/-- The dual conversion applies jointly to the gradient and flux rows with one
common positive embedding constant. -/
theorem negOneNorm_pair_le_of_hsNormSq_le_h1NormSq
    {d : ℕ} {V : Set (Vec d)} {s K : ℝ} (hK : 0 < K)
    (hTest : ∀ psi : Vec d → Vec d, IsLocalVecTest V psi →
      hsNormSq V s psi ≤ ENNReal.ofReal K * h1NormSq V psi)
    (F G : Vec d → Vec d) :
    negOneNorm V F + negOneNorm V G ≤
      ENNReal.ofReal (Real.sqrt K) *
        (negSobolevNorm V s F + negSobolevNorm V s G) := by
  calc
    negOneNorm V F + negOneNorm V G ≤
        ENNReal.ofReal (Real.sqrt K) * negSobolevNorm V s F +
          ENNReal.ofReal (Real.sqrt K) * negSobolevNorm V s G :=
      add_le_add
        (negOneNorm_le_of_hsNormSq_le_h1NormSq hK hTest F)
        (negOneNorm_le_of_hsNormSq_le_h1NormSq hK hTest G)
    _ = ENNReal.ofReal (Real.sqrt K) *
        (negSobolevNorm V s F + negSobolevNorm V s G) :=
      (mul_add _ _ _).symm

/-- Exact real exponent arithmetic behind the inverse-radius normalization. -/
theorem inverse_scale_mul_order_loss
    (n : ℤ) (s : ℝ) :
    (((3 : ℝ) ^ n)⁻¹) *
        (3 : ℝ) ^ ((1 - s) * (n : ℝ)) =
      (3 : ℝ) ^ (-s * (n : ℝ)) := by
  rw [← Real.rpow_intCast]
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The same cancellation in the extended nonnegative carrier used by the
frozen clause. -/
theorem ofReal_inverse_scale_mul_order_loss
    (n : ℤ) (s : ℝ) :
    ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
        ENNReal.ofReal ((3 : ℝ) ^ ((1 - s) * (n : ℝ))) =
      ENNReal.ofReal ((3 : ℝ) ^ (-s * (n : ℝ))) := by
  rw [← ENNReal.ofReal_mul
    (inv_nonneg.mpr (zpow_pos (by norm_num : (0 : ℝ) < 3) n).le)]
  exact congrArg ENNReal.ofReal (inverse_scale_mul_order_loss n s)

/-- Consumer-side composition of the two-row fractional estimate, the
finite-scale order comparison, and the inverse-radius normalization.  The
two analytic estimates remain explicit inputs; all scale accounting is proved
here. -/
theorem printOrder_twoRow_feeds_v2_scale
    {d : ℕ} (n : ℤ) (s : ℝ) (A B : ℝ≥0∞)
    (F G : Vec d → Vec d)
    (hOrder :
      negOneNorm (openCubeSet (originCube d n)) F +
          negOneNorm (openCubeSet (originCube d n)) G ≤
        A * ENNReal.ofReal
            ((3 : ℝ) ^ ((1 - s) * (n : ℝ))) *
          (negSobolevNorm (openCubeSet (originCube d n)) s F +
            negSobolevNorm (openCubeSet (originCube d n)) s G))
    (hFractional :
      negSobolevNorm (openCubeSet (originCube d n)) s F +
          negSobolevNorm (openCubeSet (originCube d n)) s G ≤ B) :
    ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          negOneNorm (openCubeSet (originCube d n)) F +
        ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          negOneNorm (openCubeSet (originCube d n)) G ≤
      A * ENNReal.ofReal ((3 : ℝ) ^ (-s * (n : ℝ))) * B := by
  rw [← mul_add]
  calc
    ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          (negOneNorm (openCubeSet (originCube d n)) F +
            negOneNorm (openCubeSet (originCube d n)) G) ≤
        ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          (A * ENNReal.ofReal
              ((3 : ℝ) ^ ((1 - s) * (n : ℝ))) *
            (negSobolevNorm (openCubeSet (originCube d n)) s F +
              negSobolevNorm (openCubeSet (originCube d n)) s G)) :=
      by
        simpa only [mul_comm] using
          (mul_le_mul_left hOrder
            (ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹)))
    _ ≤ ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          (A * ENNReal.ofReal
              ((3 : ℝ) ^ ((1 - s) * (n : ℝ))) * B) := by
      gcongr
    _ = A * ENNReal.ofReal ((3 : ℝ) ^ (-s * (n : ℝ))) * B := by
      calc
        ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
              (A * ENNReal.ofReal
                ((3 : ℝ) ^ ((1 - s) * (n : ℝ))) * B) =
            A *
              (ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
                ENNReal.ofReal
                  ((3 : ℝ) ^ ((1 - s) * (n : ℝ)))) * B := by
          ac_rfl
        _ = A * ENNReal.ofReal ((3 : ℝ) ^ (-s * (n : ℝ))) * B := by
          rw [ofReal_inverse_scale_mul_order_loss]

end

end HighContrast
end HCPolySupport
