/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.IntegralOrder
public import LeanPool.HighContrastHomogenization.Geometry.Sharp

/-!
# High-contrast homogenization: Geometry.AnnealedSharpOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed sharp order

The annealed primal-adjoint order says that the expectation of the random block
matrix `A(U)` dominates its own sharp: `E(U)^♯ ≤ E(U)`.  The reference proof has
three moves: an algebraic identity, an external pathwise bound, and matrix
Jensen.

The primal-adjoint involution `F ↦ R F⁻¹ R` and the dual block, formed with the
swap matrix `R` of `s.scale.selection`, make the inverse of the sharp
conjugation by the reflection, so the random matrix `Z := R A R` has `Z⁻¹ = A^♯`;
that is `fullBlockSharp_inv` below.  The pathwise block order, which gives
`0 < A^♯ ≤ A` along every realization, is one of the properties of the coarse
block that `s.introduction` takes from HC: it is not proved here and appears as
the explicit hypothesis `hsharp`.  It is what makes
both `Z` and `Z⁻¹` integrable, so that no inverse moment is needed.  Matrix
Jensen then gives `(E Z)⁻¹ ≤ E (Z⁻¹)`, and the chain

`E(U)^♯ = (E Z)⁻¹ ≤ E (Z⁻¹) = E (A^♯) ≤ E (A) = E(U)`

closes the lemma, the last step being monotonicity of the average.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The dual identity**: the inverse of the sharp is conjugation by the
reflection. -/
theorem fullBlockSharp_inv {H : FullBlockMat d} (hH : H.PosDef) :
    (fullBlockSharp H)⁻¹ = fullBlockRefl d * H * fullBlockRefl d := by
  have hHu : IsUnit H.det := isUnit_det_of_posDef hH
  rw [fullBlockSharp, Matrix.mul_inv_rev, Matrix.mul_inv_rev, fullBlockRefl_inv,
    Matrix.nonsing_inv_nonsing_inv _ hHu]
  noncomm_ring

/-- Conjugation by the reflection recovers the sharp, in the direction the
averaging argument uses. -/
theorem refl_conj_inv {H : FullBlockMat d} (hH : H.PosDef) :
    (fullBlockRefl d * H * fullBlockRefl d)⁻¹ = fullBlockSharp H := by
  rw [← fullBlockSharp_inv hH,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef (posDef_fullBlockSharp hH))]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Conjugation by the reflection keeps an integrable function integrable. -/
theorem integrable_refl_conj {F : α → FullBlockMat d} (hF : Integrable F μ) :
    Integrable (fun a => fullBlockRefl d * F a * fullBlockRefl d) μ :=
  integrable_mul_left_mul_right _ _ hF

/-- **Conjugation by the reflection commutes with the average**, the reflection
being a fixed matrix. -/
theorem integral_refl_conj {F : α → FullBlockMat d} (hF : Integrable F μ) :
    ∫ a, fullBlockRefl d * F a * fullBlockRefl d ∂μ =
      fullBlockRefl d * (∫ a, F a ∂μ) * fullBlockRefl d :=
  integral_mul_left_mul_right _ _ hF

/-- **The annealed primal-adjoint order**: the average of a random positive
definite block matrix dominates its own sharp.  The pathwise block order enters
as the hypothesis `hsharp`; it is one of the properties of the coarse block
taken from HC and is not proved here. -/
theorem fullBlockSharp_integral_le_integral [IsProbabilityMeasure μ]
    {A : α → FullBlockMat d} (hpos : ∀ a, (A a).PosDef)
    (hsharp : ∀ a, fullBlockSharp (A a) ≤ A a) (hint : Integrable A μ)
    (hintSharp : Integrable (fun a => fullBlockSharp (A a)) μ)
    (hEpos : (∫ a, A a ∂μ).PosDef) :
    fullBlockSharp (∫ a, A a ∂μ) ≤ ∫ a, A a ∂μ := by
  -- The reflected matrix is the inverse of the sharp along every realization.
  set Z : α → FullBlockMat d := fun a => fullBlockRefl d * A a * fullBlockRefl d
  have hZpos : ∀ a, (Z a).PosDef := fun a => posDef_refl_conj (hpos a)
  have hZinv : ∀ a, (Z a)⁻¹ = fullBlockSharp (A a) := fun a => refl_conj_inv (hpos a)
  have hZint : Integrable Z μ := integrable_refl_conj hint
  have hZinvInt : Integrable (fun a => (Z a)⁻¹) μ := by
    simpa only [hZinv] using hintSharp
  have hZmean : ∫ a, Z a ∂μ = fullBlockRefl d * (∫ a, A a ∂μ) * fullBlockRefl d :=
    integral_refl_conj hint
  have hZmeanPos : (∫ a, Z a ∂μ).PosDef := by
    rw [hZmean]; exact posDef_refl_conj hEpos
  -- Matrix Jensen, then the pathwise block order.
  have hjensen : (∫ a, Z a ∂μ)⁻¹ ≤ ∫ a, (Z a)⁻¹ ∂μ :=
    inv_integral_le_integral_inv hZpos hZint hZinvInt hZmeanPos
  have hleft : (∫ a, Z a ∂μ)⁻¹ = fullBlockSharp (∫ a, A a ∂μ) := by
    rw [hZmean]; exact refl_conj_inv hEpos
  have hright : ∫ a, (Z a)⁻¹ ∂μ ≤ ∫ a, A a ∂μ := by
    refine integral_mono' hZinvInt hint (.of_forall fun a => ?_)
    change (Z a)⁻¹ ≤ A a
    rw [hZinv a]
    exact hsharp a
  rw [hleft] at hjensen
  exact hjensen.trans hright

end

end HighContrast
end HCPolySupport
