/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.CoeffC1


/-!
# `C²` coefficients

The differentiated-equation identity (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1, Theorem 2) needs one order of differentiability beyond the interior `H²` estimate:
the coefficient gradient `∂_ℓ aᵢⱼ` must itself be treated as a `C¹` weight. This file bundles
that hypothesis as `IsC2Coeff`, a mixin on top of `EllipticCoeff` one derivative order above
`IsC1Coeff` (a mechanical copy of `CoeffC1.lean`), leaving every existing consumer of
`EllipticCoeff` and `IsC1Coeff` untouched.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- A `C²` ellipticity bundle: every coefficient entry is twice continuously differentiable
with uniform bounds `A1` on the first and `A2` on the second derivatives. Layered on
`EllipticCoeff`, leaving every existing consumer untouched (as `IsC1Coeff` is). -/
structure IsC2Coeff (A : EllipticCoeff d) where
  /-- Every coefficient entry is twice continuously differentiable. -/
  contDiff : ∀ i j, ContDiff ℝ 2 (fun x => A.a x i j)
  /-- The uniform bound on the first derivatives of every entry. -/
  A1 : ℝ
  /-- `A1` is nonnegative. -/
  A1_nonneg : 0 ≤ A1
  /-- The Fréchet derivative of every coefficient entry is bounded by `A1` at every point. -/
  grad_bdd : ∀ i j, ∀ x, ‖fderiv ℝ (fun y => A.a y i j) x‖ ≤ A1
  /-- The uniform bound on the second derivatives of every entry. -/
  A2 : ℝ
  /-- `A2` is nonnegative. -/
  A2_nonneg : 0 ≤ A2
  /-- The nested Fréchet derivative (the second derivative, taken as `fderiv` of `fderiv`)
  of every coefficient entry is bounded by `A2` at every point. -/
  hess_bdd : ∀ i j, ∀ x,
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => A.a z i j) y) x‖ ≤ A2

/-- A `C²` bundle is in particular a `C¹` bundle (drops the second-order data). -/
def IsC2Coeff.toIsC1Coeff {A : EllipticCoeff d} (hA : IsC2Coeff A) : IsC1Coeff A :=
  { contDiff := fun i j => (hA.contDiff i j).of_le (by norm_num)
    A1 := hA.A1, A1_nonneg := hA.A1_nonneg, grad_bdd := hA.grad_bdd }

/-- The gradient entry `∂_ℓ a_{ij}` is `C¹` (needed to treat it as a differentiable weight in
the strong-datum move, Task 7). -/
theorem IsC2Coeff.contDiff_partialD_coeff {A : EllipticCoeff d} (hA : IsC2Coeff A)
    (i j ℓ : Fin d) : ContDiff ℝ 1 (partialD ℓ (fun y => A.a y i j)) := by
  have hf : ContDiff ℝ 1 (fderiv ℝ (fun y => A.a y i j)) :=
    (hA.contDiff i j).fderiv_right (by norm_num)
  change ContDiff ℝ 1 (fun x => (fderiv ℝ (fun y => A.a y i j) x) (EuclideanSpace.single ℓ 1))
  exact hf.clm_apply (contDiff_const (c := EuclideanSpace.single ℓ (1 : ℝ)))

end EllipticPdes.Regularity
