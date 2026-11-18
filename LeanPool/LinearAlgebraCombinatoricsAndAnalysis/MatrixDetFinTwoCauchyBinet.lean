/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Order.Hom.PowersetCard
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Cauchy–Binet formula

For `A : Matrix (Fin n) ι R` and `B : Matrix ι (Fin n) R` over a commutative ring, with `ι` a
finite linear order, `det (A * B)` is the sum over the `n`-element subsets `s` of `ι` of the
products of the maximal minors of `A` and `B` indexed by `s`. The proof pairs the `n`-th exterior
power of `ι → R` with its dual, in the basis induced by the standard basis. The second statement
is the same formula for arbitrary `n × n` minors of a product.

## Main statements

* `Matrix.det_mul_eq_sum_powersetCard`
* `Matrix.det_submatrix_mul`
-/

public section

variable {R : Type*} {n : ℕ} [CommRing R]

namespace Matrix

open Set exteriorPower

variable {l o ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The **Cauchy–Binet formula**: for `A : Matrix (Fin n) ι R` and `B : Matrix ι (Fin n) R`,
`det (A * B)` is the sum, over the `n`-element subsets `s` of `ι`, of the products of the
maximal minors of `A` and `B` indexed by `s`. -/
theorem det_mul_eq_sum_powersetCard (A : Matrix (Fin n) ι R) (B : Matrix ι (Fin n) R) :
    (A * B).det = ∑ s : powersetCard ι n,
      (A.submatrix id (powersetCard.ofFinEmbEquiv.symm s)).det *
        (B.submatrix (powersetCard.ofFinEmbEquiv.symm s) id).det := by
  have h := congr(pairingDual R (ι → R) n (ιMulti R n fun j ↦ ∑ k, B k j • LinearMap.proj k)
    $(((Pi.basisFun R ι).exteriorPower n).sum_repr (ιMulti R n fun i ↦ A i))).symm
  eta_expand at h
  simpa [ιMulti_family, basis_repr_apply, Pi.single_apply, mul_comm (B _ _)] using! h

/-- The **Cauchy–Binet formula** for minors: the minor of `A * B` on rows `I` and columns `K` is
the sum, over the `n`-element subsets `s` of `ι`, of the products of the minors of `A` on rows
`I` and columns `s` and of `B` on rows `s` and columns `K`. -/
theorem det_submatrix_mul (A : Matrix l ι R) (B : Matrix ι o R) (I : Fin n → l) (K : Fin n → o) :
    ((A * B).submatrix I K).det = ∑ s : powersetCard ι n,
      (A.submatrix I (powersetCard.ofFinEmbEquiv.symm s)).det *
        (B.submatrix (powersetCard.ofFinEmbEquiv.symm s) K).det := by
  simp [submatrix_mul A B I id K Function.bijective_id, det_mul_eq_sum_powersetCard]

end Matrix
