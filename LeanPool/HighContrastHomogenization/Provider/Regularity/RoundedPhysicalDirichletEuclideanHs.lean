/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCubeDirichletEuclideanHsRegularity
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedPhysicalDirichletAffineResponse

/-!
# High-contrast homogenization: Provider.Regularity.RoundedPhysicalDirichletEuclideanHs

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Uniform rounded physical Dirichlet Euclidean Hs provider

The all-scale rounded-reference regularity theorem is composed with the
quotient-first affine response.  One fractional order and one finite constant
are selected before every scale, effective matrix, and datum.  The normalized
full-norm estimate and the physical weak, quotient, and affine-loss conclusions
are exported together.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

/-- One selected order and finite constant simultaneously supply the
rounded-reference centered-cube response and its quotient-first physical
affine representative. -/
theorem exists_roundedPhysicalDirichletEuclideanHsConstant
    (d : ℕ) [NeZero d] :
    ∃ s : FractionalOrder, s.1 < (1 : ℝ) / 12 ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧
        ∀ (m : ℤ) (abar : Mat d) (hS : (symmPart abar).PosDef)
          (h : CenteredCubeEuclideanL2Field d m),
          MemCenteredCubeEuclideanHs s h →
            ∃ w : H10Function (openCubeSet (originCube d m)),
              IsZeroTraceDirichletRhsWeakSolution
                (constantCoeffField (roundedReferenceMatrix abar hS))
                (openCubeSet (originCube d m)) w (fun y ↦ -h y) ∧
              MemCenteredCubeEuclideanHs s
                (centeredCubeGradientEuclideanL2Field w) ∧
              centeredCubeEuclideanHsFullENorm s
                  (centeredCubeGradientEuclideanL2Field w) ≤
                C * centeredCubeEuclideanHsFullENorm s h ∧
              ∃ wPhysical : H10Function (roundedPhysicalCube abar m),
                wPhysical.toH1Function.toFun =
                  (fun x ↦ w.toH1Function.toFun
                    (matVecMul
                      (baseRoundedGrid (symmPart abar))⁻¹ x)) ∧
                wPhysical.toH1Function.grad =
                  (fun x ↦ matVecMul
                    (baseRoundedGrid (symmPart abar))⁻¹
                    (w.toH1Function.grad
                      (matVecMul
                        (baseRoundedGrid (symmPart abar))⁻¹ x))) ∧
                IsZeroTraceDirichletRhsWeakSolution
                  (constantCoeffField
                    (roundedPhysicalReferenceMatrix abar))
                  (roundedPhysicalCube abar m) wPhysical
                  (fun x ↦ -roundedPhysicalDirichletDatum abar h x) ∧
                wPhysical.toH1Function.gradToHilbertVectorL2 =
                  affineGradientQuotientPushforward
                    (isUnit_det_baseRoundedGrid hS)
                    (measurableSet_matImage
                      (isUnit_det_baseRoundedGrid hS)
                      (measurableSet_openCubeSet (originCube d m)))
                    (matImage_inv_matImage
                      (isUnit_det_baseRoundedGrid hS)
                      (openCubeSet (originCube d m))).symm
                    (baseRoundedGrid (symmPart abar))⁻¹
                    w.toH1Function.gradToHilbertVectorL2 ∧
                hsNormSq (roundedPhysicalCube abar m) s.1
                    wPhysical.toH1Function.grad ≤
                  roundedPhysicalGradientHsLoss abar s.1 *
                    hsNormSq (openCubeSet (originCube d m)) s.1
                      w.toH1Function.grad := by
  rcases exists_roundedCenteredCubeDirichletEuclideanHsRegularity d with
    ⟨s, hs, C, hC, hregular⟩
  refine ⟨s, hs, C, hC, ?_⟩
  intro m abar hS h hh
  rcases hregular m abar hS h hh with
    ⟨w, hwWeak, hwMem, hwEstimate⟩
  rcases exists_roundedPhysicalDirichletAffineResponse
      abar hS h w hwWeak with
    ⟨wPhysical, hwPhysicalFun, hwPhysicalGrad, hwPhysicalWeak,
      hwPhysicalQuotient, hwPhysicalHs⟩
  exact ⟨w, hwWeak, hwMem, hwEstimate, wPhysical,
    hwPhysicalFun, hwPhysicalGrad, hwPhysicalWeak,
    hwPhysicalQuotient, hwPhysicalHs s⟩

end

end HighContrast
end HCPolySupport
