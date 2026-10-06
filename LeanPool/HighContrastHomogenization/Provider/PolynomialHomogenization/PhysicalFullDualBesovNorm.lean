/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.Full
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The physical full-dual Besov vector norm on a triadic cube

The unnormalized componentwise dual Besov norm of a vector field on a cube,
its parent-scale weight, and the identity relating it to the scale-normalized
public norm of `HCPolySupport.Book.Ch03`.
-/

namespace HCPolySupport
namespace HighContrast

open Book Book.Ch03 MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The physical vector full-dual Besov norm on a cube, before the public
parent-scale normalization is applied. -/
@[expose]
def physicalFullDualBesovVectorNorm
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  ∑ i : Fin d,
    cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
      (fun x => F x i)

/-- The inverse of the public dual-Besov parent-scale weight. -/
@[expose]
def physicalDualBesovScaleFactor (Q : TriadicCube d) (s : ℝ) : ℝ :=
  (Real.rpow (3 : ℝ) (-s * (((Q.scale : ℤ) : ℝ))))⁻¹

theorem physicalDualBesovScaleFactor_nonneg
    (Q : TriadicCube d) (s : ℝ) :
    0 ≤ physicalDualBesovScaleFactor Q s := by
  unfold physicalDualBesovScaleFactor
  exact inv_nonneg.mpr (Real.rpow_nonneg (by norm_num) _)

theorem physicalFullDualBesovVectorNorm_eq_scaleFactor_mul_normalized
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    physicalFullDualBesovVectorNorm Q s F =
      physicalDualBesovScaleFactor Q s *
        scaleNormalizedDualNegativeBesovVectorNormTwo Q s F := by
  let w : ℝ := Real.rpow (3 : ℝ) (-s * (((Q.scale : ℤ) : ℝ)))
  have hw : 0 < w := by
    dsimp only [w]
    exact Real.rpow_pos_of_pos (by norm_num) _
  unfold physicalFullDualBesovVectorNorm physicalDualBesovScaleFactor
    scaleNormalizedDualNegativeBesovVectorNormTwo
  change (∑ i : Fin d, _) = w⁻¹ * (w * ∑ i : Fin d, _)
  field_simp [hw.ne']

end

end HighContrast
end HCPolySupport
