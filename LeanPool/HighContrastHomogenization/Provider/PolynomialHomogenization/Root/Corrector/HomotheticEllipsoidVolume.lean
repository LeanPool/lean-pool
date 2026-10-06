/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedEllipsoidWeightedNormBridge
public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.HomotheticEllipsoidVolume

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Homothetic ellipsoid volume comparisons

Positive scalar dilation preserves the ellipsoid shape and scales its volume
by the dimension power.  Consequently normalized weighted energies compare
uniformly across a bounded ratio of radii, independently of the matrix.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem matVecMul_smul_one (q : ℝ) (x : Vec d) :
    matVecMul (q • (1 : Mat d)) x = q • x := by
  rw [smul_matVecMul, matVecMul_one]

private theorem vecDot_smul_self (q : ℝ) (x : Vec d) (M : Mat d) :
    vecDot (q • x) (matVecMul M (q • x)) =
      q ^ 2 * vecDot x (matVecMul M x) := by
  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

/-- An ellipsoid at a positively dilated radius is the image of the original
ellipsoid by the same scalar dilation. -/
theorem matImage_smul_one_ellipsoid
    (abar : Mat d) {q : ℝ} (hq : 0 < q) (r : ℝ) :
    matImage (q • (1 : Mat d)) (ellipsoid abar r) =
      ellipsoid abar (q * r) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [matVecMul_smul_one, ellipsoid, Set.mem_ofPred_eq,
      vecDot_smul_self]
    calc
      q ^ 2 * vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤
          q ^ 2 * (specBound (symmPart abar)⁻¹ * r ^ 2) :=
        mul_le_mul_of_nonneg_left hx (sq_nonneg q)
      _ = specBound (symmPart abar)⁻¹ * (q * r) ^ 2 := by ring
  · intro hy
    let x : Vec d := q⁻¹ • y
    refine ⟨x, ?_, ?_⟩
    · rw [ellipsoid, Set.mem_ofPred_eq]
      have hscale :
          vecDot x (matVecMul (symmPart abar)⁻¹ x) =
            q⁻¹ ^ 2 * vecDot y (matVecMul (symmPart abar)⁻¹ y) := by
        dsimp only [x]
        exact vecDot_smul_self q⁻¹ y (symmPart abar)⁻¹
      rw [hscale]
      calc
        q⁻¹ ^ 2 * vecDot y (matVecMul (symmPart abar)⁻¹ y) ≤
            q⁻¹ ^ 2 *
              (specBound (symmPart abar)⁻¹ * (q * r) ^ 2) :=
          mul_le_mul_of_nonneg_left hy (sq_nonneg q⁻¹)
        _ = specBound (symmPart abar)⁻¹ * r ^ 2 := by
          field_simp [hq.ne']
    · rw [matVecMul_smul_one]
      funext i
      simp [x, hq.ne']

/-- Positive scalar dilation multiplies ellipsoid volume by `q^d`. -/
theorem volume_ellipsoid_mul
    (abar : Mat d) {q : ℝ} (hq : 0 < q) (r : ℝ) :
    volume (ellipsoid abar (q * r)) =
      ENNReal.ofReal (q ^ d) * volume (ellipsoid abar r) := by
  let L : Mat d := q • (1 : Mat d)
  have hdet : L.det = q ^ d := by
    dsimp only [L]
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hL : IsUnit L.det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero d hq.ne')
  rw [← matImage_smul_one_ellipsoid abar hq r,
    volume_matImage L (ellipsoid abar r), hdet,
    abs_of_pos (pow_pos hq d)]

/-- Ellipsoids are monotone in a nonnegative radius. -/
theorem ellipsoid_mono_of_nonneg
    (abar : Mat d) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    ellipsoid abar r ⊆ ellipsoid abar R := by
  intro x hx
  exact hx.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ hr (hr.trans hrR)).2 hrR) (specBound_nonneg _))

/-- The volume ratio of two positive-radius ellipsoids is bounded only by a
prescribed dilation factor, not by the defining matrix. -/
theorem volume_ellipsoid_div_le_of_le_mul
    [NeZero d] (abar : Mat d) {r R q : ℝ}
    (hS : (symmPart abar).PosDef)
    (hr : 0 < r) (hrR : r ≤ R) (hq : 1 ≤ q) (hRq : R ≤ q * r) :
    volume (ellipsoid abar R) / volume (ellipsoid abar r) ≤
      ENNReal.ofReal (q ^ d) := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hRsub : ellipsoid abar R ⊆ ellipsoid abar (q * r) := by
    exact ellipsoid_mono_of_nonneg abar
      (hr.le.trans hrR) hRq
  have hvol : volume (ellipsoid abar R) ≤
      volume (ellipsoid abar (q * r)) := measure_mono hRsub
  rw [volume_ellipsoid_mul abar hqpos r] at hvol
  rw [ENNReal.div_le_iff (volume_ellipsoid_pos abar hr).ne'
    (volume_ellipsoid_lt_top hS r).ne]
  exact hvol

end

end Root
end HighContrast
end HCPolySupport
