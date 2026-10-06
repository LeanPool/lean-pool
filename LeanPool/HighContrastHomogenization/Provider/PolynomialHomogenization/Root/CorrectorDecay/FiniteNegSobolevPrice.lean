/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.RoundedAffineReplacement
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationFiniteEllipticity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.HomogenizationAssemblyRHS
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedAnalyticGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalDualToBesovBridge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.FiniteNegSobolevPrice

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

@[expose]
public def cubeEuclideanLpFieldOfMemVectorL2
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemVectorL2 (cubeSet Q) F) :
    CubeEuclideanLpField Q FiniteLpExponent.two :=
  { toField := F
    euclideanMemLp := by
      have hnormalized : MemLp F (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) :=
        memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF
      simpa only [Function.comp_apply, HilbertVec.ofVecL_apply] using!
        (HilbertVec.ofVecL d).comp_memLp' hnormalized }

/-- The physical compact-test fractional dual is the inverse cube weight
times the response theorem's scale-normalized full dual, up to the available
finite dimension constant. -/
theorem negSobolevNorm_le_inverseWeight_normalizedDual
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : Vec d → Vec d) (hF : MemVectorL2 (cubeSet Q) F) :
    negSobolevNorm (openCubeSet Q) s F ≤
      fractionalDualToBesovConstant d *
        ENNReal.ofReal
          ((cubeBesovScaleWeight s Q)⁻¹ *
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F) := by
  let FF : CubeEuclideanLpField Q FiniteLpExponent.two :=
    cubeEuclideanLpFieldOfMemVectorL2 Q F hF
  have hmain :=
    negSobolevNorm_le_fractionalDualToBesovConstant_mul_fullDualSum
      Q hs hsHalf FF
  let S : ℝ := ∑ i : Fin d,
    cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
      (fun x ↦ F x i)
  let W : ℝ := cubeBesovScaleWeight s Q
  have hW : 0 < W := by
    dsimp only [W, cubeBesovScaleWeight, cubeScaleFactor]
    positivity
  have hnormalize :
      W⁻¹ * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F = S := by
    unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
    change W⁻¹ * (W * S) = S
    calc
      W⁻¹ * (W * S) = (W⁻¹ * W) * S := by ring
      _ = S := by rw [inv_mul_cancel₀ hW.ne']; simp
  rw [show (cubeBesovScaleWeight s Q)⁻¹ *
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F = S by
        simpa only [W] using hnormalize]
  simpa only [FF, S] using! hmain

/-- On an origin cube, removing the normalizing Besov weight costs exactly
the physical factor `3^(s*m)`. -/
theorem inverse_originCubeBesovWeight
    {d : ℕ} (s : ℝ) (m : ℤ) :
    (cubeBesovScaleWeight s (originCube d m))⁻¹ =
      Real.rpow 3 (s * (m : ℝ)) := by
  rw [cubeBesovScaleWeight, cubeScaleFactor_originCube]
  rw [Real.rpow_neg (by positivity : 0 ≤ (3 : ℝ) ^ m), inv_inv]
  rw [← Real.rpow_intCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

end

end HighContrast
end HCPolySupport
