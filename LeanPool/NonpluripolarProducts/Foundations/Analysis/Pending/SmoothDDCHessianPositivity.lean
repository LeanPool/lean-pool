/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.StronglyPositiveForms

/-!
# Semipositivity of `ddᶜ` gives a semidefinite complex Hessian

`FirstPass.MongeAmpere.isSmoothPshOn_of_psh` turns plurisubharmonicity into
semidefiniteness of the coordinate complex Hessian. Local potentials for
semipositive closed forms instead supply `CoefficientSemipositive`.
`FirstPass.smoothDDC_complexDiagonal_eq_leviForm` identifies the complex
diagonal of `ddᶜφ` with the Levi form of `φ` up to the factor `π`.

This module records the direct route.  It assumes only `C²` regularity at the
point, which is what a `ContDiffOn ℝ ∞` local potential supplies on an open
parameter set.
-/

@[expose] public section

open Set Filter Complex
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.SmoothDDCHessianPositivity

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms

noncomputable section

variable {n : ℕ}

/-- The normalized `ddᶜ` is semipositive where the Levi form is nonnegative. -/
theorem isSemipositiveOneOne_smoothDDC_of_leviForm {g : ComplexModel n → ℝ} {x : ComplexModel n}
    (h2 : ContDiffAt ℝ 2 g x) (hl : ∀ v, 0 ≤ leviForm g x v) :
    IsSemipositiveOneOne (smoothDDC g x) := by
  refine ⟨fun u v => smoothDDC_isOneOne h2 u v, fun v => ?_⟩
  rw [smoothDDC_complexDiagonal_eq_leviForm h2 v]
  exact div_nonneg (hl v) Real.pi_pos.le

/-- A `C²` function with nonnegative Levi form in every direction has a
positive semidefinite coordinate complex Hessian. -/
theorem complexHessian_posSemidef_of_leviForm_nonneg {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z)
    (h : ∀ v : ComplexModel n, 0 ≤ leviForm u z v) :
    (complexHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact complexHessian_isHermitian hu
  · intro x
    rw [complexHessian_dotProduct_mulVec_eq_leviForm hu x]
    exact Complex.nonneg_iff.mpr ⟨h _, rfl⟩

/-- **The positivity bridge.**  If the normalized `ddᶜ` of a `C²` function is
semipositive at a point, its coordinate complex Hessian is positive
semidefinite there. -/
theorem complexHessian_posSemidef_of_coefficientSemipositive {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z)
    (h : CoefficientSemipositive (smoothDDC u z)) :
    (complexHessian u z).PosSemidef := by
  refine complexHessian_posSemidef_of_leviForm_nonneg hu fun v => ?_
  have hv : 0 ≤ leviForm u z v / Real.pi := by
    rw [← smoothDDC_complexDiagonal_eq_leviForm hu v]
    exact h v
  rcases div_nonneg_iff.mp hv with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · exact absurd h2 (not_le.mpr Real.pi_pos)

/-- The same statement for a function that is smooth on an open set and whose
`ddᶜ` is semipositive there. -/
theorem complexHessian_posSemidef_of_contDiffOn {U : Set (ComplexModel n)} (hU : IsOpen U)
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (h : ∀ z ∈ U, CoefficientSemipositive (smoothDDC u z)) :
    ∀ z ∈ U, (complexHessian u z).PosSemidef := by
  intro z hz
  have hu2 : ContDiffAt ℝ 2 u z :=
    ((hu z hz).contDiffAt (hU.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact complexHessian_posSemidef_of_coefficientSemipositive hu2 (h z hz)

end

end SGPT.Foundations.Analysis.Pending.SmoothDDCHessianPositivity
