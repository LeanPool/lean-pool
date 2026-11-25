/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorForms

/-!
# Association of smooth wedge factors

Associates the wedge of smooth differential forms acting on a local current.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorWedgeAssociation

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalCurrentLebesgue ConstantFormProducts ProductTestForms

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Associativity of the genuine smooth-form wedge on arbitrary currents. -/
theorem wedgeForm_wedge_two {r k m : ℕ} (h : r + 1 + k = m)
    (T : LocalProductCurrent n U m) {α : ComplexModel n → RealForm n (2 * k)}
    {β : ComplexModel n → RealForm n 2} (hα : ContDiffOn ℝ ∞ α U)
    (hβ : ContDiffOn ℝ ∞ β U) (hαS : ∀ x ∈ U, α x ∈ formSpan n k)
    (hβS : ∀ x ∈ U, β x ∈ formSpan n 1) :
    wedgeForm rfl (wedgeForm h T hα) hβ =
      wedgeForm (by omega : r + (k + 1) = m) T (contDiffOn_coordinateWedge hα hβ) := by
  classical
  have h' : r + (k + 1) = m := by omega
  have hηS : ∀ x ∈ U, coordinateWedge (α x) (β x) ∈ formSpan n (k + 1) :=
    fun x hx => wedgeTo_mem_formSpan (hαS x hx) (hβS x hx) rfl
  ext γ φ
  let X := fun p : Fin (Module.finrank ℝ (formSpan n 1)) ×
      Fin (Module.finrank ℝ (formSpan n k)) =>
    wedgeSpan n h (wedgeSpan n rfl γ (formBasis n 1 p.1)) (formBasis n k p.2)
  let ψ := fun p : Fin (Module.finrank ℝ (formSpan n 1)) ×
      Fin (Module.finrank ℝ (formSpan n k)) =>
    mulSmoothOnCLM (contDiffOn_formCoeff hα p.2)
      (mulSmoothOnCLM (contDiffOn_formCoeff hβ p.1) φ)
  let Y := fun i : Fin (Module.finrank ℝ (formSpan n (k + 1))) =>
    wedgeSpan n h' γ (formBasis n (k + 1) i)
  let χ := fun i : Fin (Module.finrank ℝ (formSpan n (k + 1))) => mulSmoothOnCLM
    (contDiffOn_formCoeff (k := k + 1) (contDiffOn_coordinateWedge hα hβ) i) φ
  have hpoint : ∀ x ∈ U, ∑ p, ψ p x • (X p : RealForm n (2 * m)) =
      ∑ i, χ i x • (Y i : RealForm n (2 * m)) := by
    intro x hx
    have e := sum_mulSmoothOnCLM_smul_wedgeSpan h'
      (contDiffOn_coordinateWedge hα hβ) hηS γ φ (by omega) hx
    change _ = ∑ i, mulSmoothOnCLM
      (contDiffOn_formCoeff (contDiffOn_coordinateWedge hα hβ) i) φ x •
        (wedgeSpan n h' γ (formBasis n (k + 1) i) : RealForm n (2 * m))
    rw [e, Fintype.sum_prod_type]
    have ei : ∀ j, ∑ i,
        mulSmoothOnCLM (contDiffOn_formCoeff hα i)
            (mulSmoothOnCLM (contDiffOn_formCoeff hβ j) φ) x •
          (wedgeSpan n h (wedgeSpan n rfl γ (formBasis n 1 j)) (formBasis n k i) :
            RealForm n (2 * m)) =
        mulSmoothOnCLM (contDiffOn_formCoeff hβ j) φ x •
          wedgeTo (by omega : 2 * (r + 1) + 2 * k = 2 * m)
            (wedgeSpan n rfl γ (formBasis n 1 j) : RealForm n (2 * (r + 1))) (α x) :=
      fun j => sum_mulSmoothOnCLM_smul_wedgeSpan h hα hαS
        (wedgeSpan n rfl γ (formBasis n 1 j))
        (mulSmoothOnCLM (contDiffOn_formCoeff hβ j) φ) (by omega) hx
    change (∑ j, ∑ i,
        mulSmoothOnCLM (contDiffOn_formCoeff hα i)
            (mulSmoothOnCLM (contDiffOn_formCoeff hβ j) φ) x •
          (wedgeSpan n h (wedgeSpan n rfl γ (formBasis n 1 j)) (formBasis n k i) :
            RealForm n (2 * m))) = _
    simp_rw [ei, ← wedgeTo_smul_left]
    rw [← wedgeTo_sum_left, sum_mulSmoothOnCLM_smul_wedgeSpan rfl hβ hβS γ φ (by omega) hx,
      wedgeTo_smul_left,
      wedgeTo_wedgeTo_comm (γ : RealForm n (2 * r)) (β x) (hαS x hx)
        (by omega : 2 * r + 2 = 2 * (r + 1))
        (by omega : 2 * (r + 1) + 2 * k = 2 * m)
        (by omega : 2 * r + 2 * k = 2 * (r + k))
        (by omega : 2 * (r + k) + 2 = 2 * m),
      wedgeTo_assoc (by omega : 2 * r + 2 * k = 2 * (r + k))
        (by omega : 2 * (r + k) + 2 = 2 * m)
        (by omega : 2 * k + 2 = 2 * (k + 1))
        (by omega : 2 * r + 2 * (k + 1) = 2 * m)]
    rw [wedgeTo_smul_left]
    rfl
  have he := sum_apply_eq_of_forall T X ψ Y χ hpoint
  simpa only [X, ψ, Y, χ, Fintype.sum_prod_type, wedgeForm_apply] using he

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorWedgeAssociation
