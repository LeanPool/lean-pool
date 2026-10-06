/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.FullBlockSharpHarmonic
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.MeanOrder
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockOrder
public import Mathlib.Tactic.NoncommRing

/-!
# High-contrast homogenization: Provider.Quenched.AlignedSubdivisionQuadraticGap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quadratic gap over an aligned subdivision

The response on a parent adapted cell is below the arithmetic mean of the
responses on its aligned children.  The sharp involution turns the harmonic
gap of those children into a quadratic fluctuation.  This module combines the
two facts while retaining the pathwise, matrix-valued form of the estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

/-- The fluctuation expression obtained after combining the sharp quadratic
gap with the primal-minus-sharp remainder. -/
@[expose]
def fullBlockSharpFluctuation {d : ℕ} (A G : FullBlockMat d) : FullBlockMat d :=
  (A - G) + G * ((fullBlockSharp A)⁻¹ - G⁻¹) * G

/-- The sharp quadratic term and the primal-minus-sharp remainder combine into
the fluctuation expression used by the variance estimate. -/
theorem fullBlockSharp_quadratic_add_primal_sub_eq_fluctuation {d : ℕ}
    {A G : FullBlockMat d} (hA : A.PosDef) (hG : G.PosDef) :
    (fullBlockSharp A - G) * (fullBlockSharp A)⁻¹ *
          (fullBlockSharp A - G) + (A - fullBlockSharp A) =
      fullBlockSharpFluctuation A G := by
  have hS : (fullBlockSharp A).PosDef := posDef_fullBlockSharp hA
  have hSdet : IsUnit (fullBlockSharp A).det :=
    (Matrix.isUnit_iff_isUnit_det (A := fullBlockSharp A)).mp hS.isUnit
  have hSright : fullBlockSharp A * (fullBlockSharp A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (fullBlockSharp A) hSdet
  have hSleft : (fullBlockSharp A)⁻¹ * fullBlockSharp A = 1 :=
    Matrix.nonsing_inv_mul (fullBlockSharp A) hSdet
  have hGdet : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det (A := G)).mp hG.isUnit
  have hGright : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGdet
  simp only [fullBlockSharpFluctuation]
  noncomm_ring [hSright, hSleft, hGright]

end

end Quenched
end HighContrast
end HCPolySupport
