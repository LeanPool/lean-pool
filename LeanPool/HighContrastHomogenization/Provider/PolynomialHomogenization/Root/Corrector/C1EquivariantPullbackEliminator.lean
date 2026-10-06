/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.EquivariantPhysicalCorrectorFamilyWrapper
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalProjectionAbsoluteDecay
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1BaseSlopeEnergyControl
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.LiouvillePrivateThresholdRestart
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootGoodScaleProvider
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineRegularityJointAssembly

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1EquivariantPullbackEliminator

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Canonical pullback data for an equivariant corrector family

The physical family records the normalized joint corrector from which its
gradient is obtained.  This is the identification needed to transport a
simultaneous-slope estimate from normalized cubes to physical coordinates.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A physical corrector family retains, at every certified sample, one
small-order normalized reference family and the exact normalized-root pullback
identity for the canonical joint corrector. -/
structure CanonicalPullbackCorrectorFamily
    [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop)
    (abar : Mat d)
    (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
    (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d) : Prop where
  weakGradient : ∀ (a : CoeffSpace d) (x : ℝ), GoodScale abar a x →
    ∀ e : Vec d,
      HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a)
  normalizedJoint : ∀ (a : CoeffSpace d) (x : ℝ), GoodScale abar a x →
    ∃ (hS : (symmPart abar).PosDef) (s tolerance : ℝ)
      (aRef : Book.Ch03.CoeffFamily d) (L : ℕ)
      (hCauchy : FiniteAffineCorrectionLocalCauchy aRef),
        0 < s ∧ s < 1 / 2 ∧
        (∀ Q : TriadicCube d,
          (aRef.coeffOn Q).toCoeffField =
            affineCoefficient (Selection.normalizedRoot (symmPart abar))
              ((Matrix.isUnit_iff_isUnit_det _).mp
                (normalizedRoot_posDef_of_posDef hS).isUnit)
              ⇑(normalizedCenteredCoeff a abar hS).1) ∧
        ScalarIdentityGoodTail aRef s tolerance
          (((Quenched.triadicCeilingIndex x + L : ℕ) : ℤ)) ∧
        IsFiniteAffineCorrectionJointLocalEquation aRef
          (finiteAffineCorrectionJointLocalLimit aRef hCauchy) ∧
        ∀ e : Vec d,
          (∃ c₀ : ℝ,
            (fun y ↦ Phi e a
              (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) =ᵐ[volume]
              fun y ↦
                (finiteAffineCorrectionJointLocalLimit aRef hCauchy
                  (matVecMul (Selection.normalizedRoot (symmPart abar)) e)).globalValueRepresentative y + c₀) ∧
          (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
            (e + gradPhi e a
              (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
            fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar)) e +
              (finiteAffineCorrectionJointLocalLimit aRef hCauchy
                (matVecMul (Selection.normalizedRoot (symmPart abar)) e)).globalGradientRepresentative y

end

end Root
end HighContrast
end HCPolySupport
