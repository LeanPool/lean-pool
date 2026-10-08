/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicNormalized

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicCaccioppoliNorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace CubeCalderonZygmund

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The normalized direct Caccioppoli estimate with all cutoff arithmetic
absorbed into one dimension-only constant. -/
theorem exists_harmonic_centralChild_euclideanGradient_cubeLpNorm_le
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          cubeLpNorm (centralChild Q) (2 : ℝ≥0∞)
              (fun x => euclideanNorm (u.grad x)) ≤
            C * (cubeScaleFactor Q)⁻¹ *
              cubeLpNorm Q (2 : ℝ≥0∞) u.toFun := by
  let B : ℝ := ((3 ^ d : ℕ) : ℝ) *
    (256 * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2)
  let A : ℝ := Real.sqrt B
  refine ⟨1 + A, by positivity, ?_⟩
  intro Q u hu
  let X : ℝ := cubeLpNorm (centralChild Q) (2 : ℝ≥0∞)
    (fun x => euclideanNorm (u.grad x))
  let Y : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.toFun
  let L : ℝ := cubeScaleFactor Q
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hA_sq : A ^ 2 = B := by
    simpa [A] using Real.sq_sqrt hB
  have hX : 0 ≤ X := cubeLpNorm_nonneg _ _ _
  have hY : 0 ≤ Y := cubeLpNorm_nonneg _ _ _
  have hL : 0 < L := by
    simpa [L, cubeScaleFactor] using
      zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale
  have hcoeff :
      (((3 ^ d : ℕ) : ℝ) *
          (4 * ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              (((3 / 4 : ℝ) - 1 / 2) * cubeRadius Q)) ^ 2))) =
        B * L⁻¹ ^ 2 := by
    dsimp [B, L]
    rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
    field_simp [(cubeRadius_pos Q).ne']
    ring
  have hsq : X ^ 2 ≤ B * L⁻¹ ^ 2 * Y ^ 2 := by
    have hraw := harmonic_centralChild_euclideanGradient_cubeLpNorm_sq_le Q u hu
    simpa only [X, Y, hcoeff] using hraw
  have htarget_sq : X ^ 2 ≤ (A * L⁻¹ * Y) ^ 2 := by
    calc
      X ^ 2 ≤ B * L⁻¹ ^ 2 * Y ^ 2 := hsq
      _ = (A * L⁻¹ * Y) ^ 2 := by rw [← hA_sq]; ring
  have hbase : X ≤ A * L⁻¹ * Y := by
    exact (sq_le_sq₀ hX (mul_nonneg (mul_nonneg hA (inv_nonneg.mpr hL.le)) hY)).mp
      htarget_sq
  have hfactor : 0 ≤ L⁻¹ * Y := mul_nonneg (inv_nonneg.mpr hL.le) hY
  calc
    X ≤ A * L⁻¹ * Y := hbase
    _ ≤ (1 + A) * L⁻¹ * Y := by
      calc
        A * L⁻¹ * Y = A * (L⁻¹ * Y) := by ring
        _ ≤ (1 + A) * (L⁻¹ * Y) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hfactor
        _ = (1 + A) * L⁻¹ * Y := by ring

end

end CubeCalderonZygmund
end HCPolySupport
