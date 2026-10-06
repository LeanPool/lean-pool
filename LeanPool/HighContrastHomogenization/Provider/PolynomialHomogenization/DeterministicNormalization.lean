/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DirichletDomain
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.DeterministicNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Deterministic identity normalization

The inverse square root of a positive definite symmetric part normalizes that
matrix to the positive scalar identity required by the deterministic
coarse-graining comparison.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The identity comparison coefficient in the Chapter 3 carrier. -/
@[expose]
def identityConstantCoeffMatrix (d : ℕ) : Book.Ch03.ConstantCoeffMatrix d where
  matrix := 1
  isSymm := Matrix.isSymm_one
  lam := 1
  Lam := 1
  lam_pos := by norm_num
  lam_le_Lam := le_rfl
  elliptic := by
    simpa only [one_smul] using
      (isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) (by norm_num))

/-- The matrix carried by the identity comparison coefficient is the identity. -/
@[simp] theorem identityConstantCoeffMatrix_matrix (d : ℕ) :
    (identityConstantCoeffMatrix d).matrix = (1 : Mat d) :=
  rfl

/-- The identity comparison coefficient satisfies the upstream positivity
contract. -/
theorem identityConstantCoeffMatrix_isPositiveScalarMatrix (d : ℕ) :
    IsPositiveScalarMatrix (identityConstantCoeffMatrix d).matrix := by
  refine ⟨1, by norm_num, ?_⟩
  simp only [identityConstantCoeffMatrix_matrix, one_smul]

end

end HighContrast
end HCPolySupport
