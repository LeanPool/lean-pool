/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1AdjacentExactMinimizer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientExcessRateSelection

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1FiniteRateComposition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Real-rate control of adjacent exact affine minimizers

The finite affine excess decay and the dimension-only adjacent-minimizer
estimate combine with one common smallness threshold.  The scale gap is
written from the outer cube inward, which is the geometric orientation used
by the finite slope telescope.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open scoped ENNReal

noncomputable section

/-- A proof-irrelevant choice of an exact finite affine excess minimizer. -/
@[expose]
noncomputable def finiteAffineExactMinimizer
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) : Vec d :=
  Classical.choose (exists_finiteAffineGradientExcess_candidate_eq a hnm u)

/-- The selected finite affine minimizer realizes the excess exactly. -/
theorem finiteAffineExactMinimizer_spec
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    weightedGradNorm
        (a.coeffOn (originCube d n)).toCoeffField
        (openCubeSet (originCube d n))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a m
            (finiteAffineExactMinimizer a hnm u)).toH1.grad x) =
      finiteAffineGradientExcess a n m u :=
  Classical.choose_spec (exists_finiteAffineGradientExcess_candidate_eq a hnm u)

end

end Root
end HighContrast
end HCPolySupport
