/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Upstream.KahlerClosed

/-!
# Hermitian and Kähler forms

For a real two-form, type `(1,1)` means `J`-invariance, and strict positivity
means `α(v, Jv) > 0` for every nonzero real tangent vector. These are explicit
conditions on the alternating forms, in every holomorphic chart.

A Hermitian form is smooth, real, positive and of type `(1,1)`. A Kähler form
is additionally closed. Admitting such a form is a separate existential
proposition: no existence on an arbitrary complex manifold is asserted.

The flat example uses the checked imaginary part of the Hermitian inner product
(conjugate-linear in its first argument). No global metric is made by setting
the coefficients constant in arbitrary charts.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ}

/-- Type `(1,1)` for a real alternating two-form: invariance under `J = i`. -/
def IsOneOne (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) : Prop :=
  ∀ u v, a ![Complex.I • u, Complex.I • v] = a ![u, v]

theorem isOneOne_add {a b : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsOneOne a) (hb : IsOneOne b) : IsOneOne (a + b) := by
  intro u v
  simp only [ContinuousAlternatingMap.add_apply, ha u v, hb u v]

theorem isOneOne_smul {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} (c : ℝ)
    (ha : IsOneOne a) : IsOneOne (c • a) := by
  intro u v
  simp only [ContinuousAlternatingMap.smul_apply, ha u v]

/-- Strict positivity of a real two-form in complex directions. -/
def IsStrictlyPositive (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) : Prop :=
  ∀ u : ComplexModel n, u ≠ 0 → 0 < a ![u, Complex.I • u]

namespace SmoothRealForm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A Hermitian fundamental form, specified by its genuine local two-forms. -/
def IsHermitian (form : SmoothRealForm n M 2) : Prop :=
  ∀ e z, z ∈ e.val.target →
    IsOneOne (form.coeff e z) ∧ IsStrictlyPositive (form.coeff e z)

/-- Being a Kähler form is a property of a given smooth form. -/
def IsKahler (form : SmoothRealForm n M 2) : Prop :=
  form.IsHermitian ∧ form.IsClosed

end SmoothRealForm

/-- The manifold admits a Kähler form. This is an existence proposition,
not an axiom, and it does not assert compactness. -/
def AdmitsKahlerForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] : Prop :=
  ∃ form : SmoothRealForm n M 2, form.IsKahler

/-- The metric associated to a real two-form is `g(u,v) = a(u,iv)`.
For a positive `(1,1)`-form this is the underlying real Hermitian metric. -/
def associatedMetric (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u v : ComplexModel n) : ℝ := a ![u, Complex.I • v]

/-- Positivity of the associated quadratic form follows directly from positivity. -/
theorem associatedMetric_self_pos {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) {u : ComplexModel n} (hu : u ≠ 0) :
    0 < associatedMetric a u u := ha u hu

/-- The standard flat fundamental form is `J`-invariant. -/
theorem flatFundamentalForm_isOneOne (n : ℕ) :
    IsOneOne (Kahler.fundamentalFormAlt : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) := by
  intro u v
  simpa only [Kahler.fundamentalFormAlt_apply, Kahler.complexStructure, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using Kahler.fundamentalForm_complexStructure u v

/-- The standard flat fundamental form is strictly positive. -/
theorem flatFundamentalForm_isStrictlyPositive (n : ℕ) :
    IsStrictlyPositive
      (Kahler.fundamentalFormAlt : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) := by
  intro u hu
  simpa only [Kahler.fundamentalFormAlt_apply, Kahler.complexStructure, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using
    Kahler.fundamentalForm_complexStructure_self_pos hu

/-- The constant standard form on the model space. Its atlas contains only
the identity chart, so its overlap equation is the identity pullback. -/
def flatKahlerForm (n : ℕ) : SmoothRealForm n (ComplexModel n) 2 where
  coeff := fun _ _ => Kahler.fundamentalFormAlt
  smooth := fun _ => contDiffOn_const
  compatible := by
    rintro ⟨e, he⟩ ⟨f, hf⟩ z hz v
    simp only [chartedSpaceSelf_atlas] at he hf
    subst e
    subst f
    change Kahler.fundamentalFormAlt v =
      Kahler.fundamentalFormAlt (fun i => (fderiv ℝ id z) (v i))
    simp

/-- The explicit flat form is Hermitian and closed. -/
theorem flatKahlerForm_isKahler (n : ℕ) : (flatKahlerForm n).IsKahler := by
  constructor
  · intro e z hz
    exact ⟨flatFundamentalForm_isOneOne n, flatFundamentalForm_isStrictlyPositive n⟩
  · intro e z hz
    exact Kahler.extDeriv_fundamentalFormAlt z

/-- A genuine existence theorem for the model space only. -/
theorem complexModel_admitsKahlerForm (n : ℕ) : AdmitsKahlerForm n (ComplexModel n) :=
  ⟨flatKahlerForm n, flatKahlerForm_isKahler n⟩

end

end SGPT.Foundations.Analysis.FirstPass
