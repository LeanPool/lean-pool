/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.Integrability

/-!
# High-contrast homogenization: Annealed.Positivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positivity of the annealed block under the coarse ellipticity assumption

The annealed block at a centered cube is the expectation of a family of positive
definite coarse responses, and is therefore itself positive definite: the
well-formedness that `e.Theta.m` presupposes for `Θ_m`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The positivity of the annealed block** under `e.coarse.ellipticity`:
the annealed block at every scale is the honest expectation of a positive
definite family, and is itself positive definite. -/
theorem blockPosDef_annealedBlock_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    Book.Ch02.BlockPosDef (annealedBlock P (centeredCube d m)) :=
  blockPosDef_annealedBlock_centeredCube m
    (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag m)

end

end HighContrast
end HCPolySupport
