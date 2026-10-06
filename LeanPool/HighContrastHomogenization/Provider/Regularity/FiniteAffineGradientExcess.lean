/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeFamilyExistence

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineGradientExcess

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite affine gradient excess

This module defines the source-normalized gradient excess of a finite cube
solution relative to the family of finite affine-boundary solutions on the
same outer cube.
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

/-- The best weighted-gradient error on `Q_n` between a finite solution on
`Q_m` and a finite affine-boundary solution on that same outer cube. -/
@[expose]
noncomputable def finiteAffineGradientExcess
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (n m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) : ℝ≥0∞ :=
  ⨅ e : Vec d,
    weightedGradNorm
      (a.coeffOn (originCube d n)).toCoeffField
      (openCubeSet (originCube d n))
      (fun x ↦ u.toH1.grad x -
        (finiteAffineSolution a m e).toH1.grad x)

/-- Every affine boundary slope gives an upper bound on the canonical
finite affine gradient excess. -/
theorem finiteAffineGradientExcess_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (n m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (e : Vec d) :
    finiteAffineGradientExcess a n m u ≤
      weightedGradNorm
        (a.coeffOn (originCube d n)).toCoeffField
        (openCubeSet (originCube d n))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a m e).toH1.grad x) := by
  exact iInf_le _ e

end

end HighContrast
end HCPolySupport
