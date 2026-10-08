/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.CubeHodgeByDuality
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.GaugeCubeTranslationReduction
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.AdaptedCellGaugeGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.DomainDualityFromHodge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Duality.CdualGaugeWitnessTerminal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `Cdual` at the gauge witness, from the cube projection stability

The consumer instantiates the printed duality at the **gauge image**
`Uhat = matImage (matSqrt (symmPart abar))⁻¹ Uphys` with the gauge-transformed
coefficient, whose constant reference is the identity.  Under the frozen
adapted-cell premise the gauge image is a triadic cube translated by an
arbitrary real vector, so the whole clause reduces — by translation invariance
and duality — to the positive `H^s` stability of the zero-trace gradient
projection on that cube, at

  `Cdual = 2 * Cproj + 1`,

law-free in the sample and in the comparison matrix.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The identity-reference Hodge hypothesis moves off an arbitrary
translation. -/
theorem hodgeHypothesis_translateSet_identity (z : Vec d) (S : Set (Vec d))
    {s C : ℝ}
    (hbase : ∀ w F : Vec d → Vec d, MemVectorL2 S F →
      IsPotentialZeroTraceOn S w →
      IsSolenoidalOn S (fun y => w y + F y) →
      negSobolevNorm S s w ≤ ENNReal.ofReal C * negSobolevNorm S s F) :
    ∀ w F : Vec d → Vec d, MemVectorL2 (translateSet z S) F →
      IsPotentialZeroTraceOn (translateSet z S) w →
      IsSolenoidalOn (translateSet z S) (fun y => w y + F y) →
      negSobolevNorm (translateSet z S) s w ≤
        ENNReal.ofReal C * negSobolevNorm (translateSet z S) s F := by
  have hone : ∀ w F : Vec d → Vec d,
      (fun y => matVecMul (1 : Mat d) (w y) + F y) = fun y => w y + F y := by
    intro w F
    funext y
    rw [matVecMul_one]
  have hbase' : ∀ w F : Vec d → Vec d, MemVectorL2 S F →
      IsPotentialZeroTraceOn S w →
      IsSolenoidalOn S (fun y => matVecMul (1 : Mat d) (w y) + F y) →
      negSobolevNorm S s w ≤ ENNReal.ofReal C * negSobolevNorm S s F := by
    intro w F hF hw hsolw
    rw [hone w F] at hsolw
    exact hbase w F hF hw hsolw
  intro w F hF hw hsolw
  refine gaugeHodgeHypothesis_translateSet z S 1 hbase' w F hF hw ?_
  rw [hone w F]
  exact hsolw

/-- **The printed two-row duality at the gauge witness**, conditional only on
the positive `H^s` stability of the zero-trace gradient projection on the cube.
The reference matrix in the gauge coordinates is the identity, so no
constant-matrix estimate is involved. -/
theorem printFaithfulDomainFluxDefectDuality_of_cubeProjection_of_potential
    [NeZero d]
    {L : Mat d} (hL : IsUnit L.det) (zc : Vec d) (Q : TriadicCube d)
    {Uphys Uhat : Set (Vec d)}
    (hUphys : Uphys = (fun x => zc + matVecMul L x) '' openCubeSet Q)
    (hUhat : Uhat = matImage L⁻¹ Uphys)
    {s Cproj : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hproj : CubeGradientProjectionHsStability d Q s Cproj)
    (aHat : CoeffField d) (u h : H1Function Uhat)
    (hFdefect : MemVectorL2 Uhat
      (fun x => matVecMul (aHat x - 1) (u.grad x)))
    (hpot : IsPotentialZeroTraceOn Uhat (fun x => u.grad x - h.grad x))
    (hsol : IsSolenoidalOn Uhat
      (fun x => matVecMul (aHat x) (u.grad x) - h.grad x)) :
    PrintFaithfulDomainFluxDefectDuality Uhat s aHat u h (2 * Cproj + 1) := by
  have hgauge : Uhat = translateSet (matVecMul L⁻¹ zc) (openCubeSet Q) := by
    rw [hUhat, hUphys]
    exact matImage_inv_affineImage hL zc (openCubeSet Q)
  subst hgauge
  exact printFaithfulDomainFluxDefectDuality_of_hodgeBound_of_potential hproj.1
    aHat u h hFdefect hpot hsol
    (hodgeHypothesis_translateSet_identity (matVecMul L⁻¹ zc) (openCubeSet Q)
      (fun w F hFw hw hsolw =>
        negSobolevNorm_le_of_cubeGradientProjectionHsStability Q hs hsHalf
          hproj hFw hw hsolw))

end

end RowSupply
end HighContrast
end HCPolySupport
