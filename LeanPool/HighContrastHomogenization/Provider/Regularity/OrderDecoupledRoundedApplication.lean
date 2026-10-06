/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedPhysicalDirichletEuclideanHs
public import LeanPool.HighContrastHomogenization.Provider.Regularity.QuantitativeCorrectorThreshold
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedResponseRows

/-!
# High-contrast homogenization: Provider.Regularity.OrderDecoupledRoundedApplication

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Order-decoupled rounded coefficient application

The deterministic Dirichlet response selects its fractional order before any
coefficient sample is introduced.  The stochastic certificate selects its
printed order after `g`.  Their common output consists only of the rounded
coefficient family, the corrected effective scale, and response rows at the
printed order.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

/-- The deterministic rounded Dirichlet response with its internally selected
small order. -/
structure PrivateRoundedPhysicalDirichletSpine (d : ℕ) [NeZero d] where
  order : FractionalOrder
  order_lt_one_twelfth : order.1 < (1 : ℝ) / 12
  responseConstant : ℝ≥0∞
  responseConstant_lt_top : responseConstant < ∞
  respond :
    ∀ (m : ℤ) (abar : Mat d) (hS : (symmPart abar).PosDef)
      (h : CenteredCubeEuclideanL2Field d m),
      MemCenteredCubeEuclideanHs order h →
        ∃ w : H10Function (openCubeSet (originCube d m)),
          IsZeroTraceDirichletRhsWeakSolution
            (constantCoeffField (roundedReferenceMatrix abar hS))
            (openCubeSet (originCube d m)) w (fun y ↦ -h y) ∧
          MemCenteredCubeEuclideanHs order
            (centeredCubeGradientEuclideanL2Field w) ∧
          centeredCubeEuclideanHsFullENorm order
              (centeredCubeGradientEuclideanL2Field w) ≤
            responseConstant * centeredCubeEuclideanHsFullENorm order h ∧
          ∃ wPhysical : H10Function (roundedPhysicalCube abar m),
            wPhysical.toH1Function.toFun =
              (fun x ↦ w.toH1Function.toFun
                (matVecMul (baseRoundedGrid (symmPart abar))⁻¹ x)) ∧
            wPhysical.toH1Function.grad =
              (fun x ↦ matVecMul
                (baseRoundedGrid (symmPart abar))⁻¹
                (w.toH1Function.grad
                  (matVecMul
                    (baseRoundedGrid (symmPart abar))⁻¹ x))) ∧
            IsZeroTraceDirichletRhsWeakSolution
              (constantCoeffField (roundedPhysicalReferenceMatrix abar))
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
            hsNormSq (roundedPhysicalCube abar m) order.1
                wPhysical.toH1Function.grad ≤
              roundedPhysicalGradientHsLoss abar order.1 *
                hsNormSq (openCubeSet (originCube d m)) order.1
                  w.toH1Function.grad

/-- The continuity-at-zero construction inhabits the private response spine. -/
theorem nonempty_privateRoundedPhysicalDirichletSpine
    (d : ℕ) [NeZero d] :
    Nonempty (PrivateRoundedPhysicalDirichletSpine d) := by
  obtain ⟨s, hs, C, hC, hresponse⟩ :=
    exists_roundedPhysicalDirichletEuclideanHsConstant d
  exact ⟨⟨s, hs, C, hC, hresponse⟩⟩

/-- A fixed choice of the deterministic response spine, made before any
stochastic exponent or sample is introduced. -/
@[expose]
noncomputable def privateRoundedPhysicalDirichletSpine
    (d : ℕ) [NeZero d] : PrivateRoundedPhysicalDirichletSpine d :=
  Classical.choice (nonempty_privateRoundedPhysicalDirichletSpine d)

end

end HighContrast
end HCPolySupport
