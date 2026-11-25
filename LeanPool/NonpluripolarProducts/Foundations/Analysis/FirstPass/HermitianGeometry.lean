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

/-- Antisymmetry of a real two-form in its two slots. -/
theorem twoForm_swap {n : ℕ} (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u v : ComplexModel n) :
    A ![v, u] = -A ![u, v] := by
  simpa using A.map_swap ![u, v] (i := 0) (j := 1) (by decide)

/-- A real two-form is `ℝ`-homogeneous in its first slot. -/
theorem twoForm_smul_left {n : ℕ} (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (r : ℝ) (u v : ComplexModel n) :
    A ![r • u, v] = r * A ![u, v] :=
  A.toMultilinearMap.cons_smul ![v] r u

/-- A real two-form is additive in its first slot. -/
theorem twoForm_add_left {n : ℕ} (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u u' v : ComplexModel n) :
    A ![u + u', v] = A ![u, v] + A ![u', v] :=
  A.toMultilinearMap.cons_add ![v] u u'

/-- A real two-form is additive in its second slot. -/
theorem twoForm_add_right {n : ℕ} (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u v v' : ComplexModel n) :
    A ![u, v + v'] = A ![u, v] + A ![u, v'] := by
  rw [twoForm_swap A (v + v') u, twoForm_add_left,
    twoForm_swap A u v, twoForm_swap A u v']
  ring

/-- A real two-form is `ℝ`-homogeneous in its second slot. -/
theorem twoForm_smul_right {n : ℕ} (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (r : ℝ) (u v : ComplexModel n) :
    A ![u, r • v] = r * A ![u, v] := by
  rw [twoForm_swap A (r • v) u,
    twoForm_smul_left, twoForm_swap A u v]
  ring

/-- A real two-form negates when its second slot is negated. -/
theorem twoForm_neg_right {n : ℕ} (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u v : ComplexModel n) :
    A ![u, -v] = -A ![u, v] := by
  simpa using twoForm_smul_right A (-1) u v

/-- A real `(1,1)`-form moves multiplication by `i` between its slots with a sign. -/
theorem twoForm_I_smul_left_of_isOneOne {n : ℕ}
    {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} (hA : IsOneOne A) (u v : ComplexModel n) :
    A ![Complex.I • u, v] = -A ![u, Complex.I • v] := by
  rw [← hA u (Complex.I • v), smul_smul, Complex.I_mul_I, neg_one_smul,
    twoForm_neg_right]
  ring

/-- An alternating two-form vanishes on a repeated vector. -/
theorem twoForm_self (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (u : ComplexModel n) :
    A ![u, u] = 0 := by
  have := twoForm_swap A u u
  linarith

/-- A complex scalar acts through its real and imaginary parts. -/
theorem complex_smul_eq (c : ℂ) (w : ComplexModel n) :
    c • w = c.re • w + c.im • (Complex.I • w) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- The Hermitian form `h(v, w) = A(v, i w) + i A(v, w)` attached to a real `(1,1)`-form. -/
def hermitianOfTwoForm (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (v w : ComplexModel n) : ℂ :=
  (A ![v, Complex.I • w] : ℂ) + Complex.I * (A ![v, w] : ℂ)

theorem hermitianOfTwoForm_add_left (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (v v' w : ComplexModel n) :
    hermitianOfTwoForm A (v + v') w = hermitianOfTwoForm A v w + hermitianOfTwoForm A v' w := by
  simp only [hermitianOfTwoForm, twoForm_add_left]
  push_cast
  ring

theorem hermitianOfTwoForm_add_right (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (v w w' : ComplexModel n) :
    hermitianOfTwoForm A v (w + w') = hermitianOfTwoForm A v w + hermitianOfTwoForm A v w' := by
  simp only [hermitianOfTwoForm, smul_add, twoForm_add_right]
  push_cast
  ring

theorem hermitianOfTwoForm_smul_right {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (c : ℂ) (v w : ComplexModel n) :
    hermitianOfTwoForm A v (c • w) = c * hermitianOfTwoForm A v w := by
  rw [complex_smul_eq c w]
  simp only [hermitianOfTwoForm, smul_add, twoForm_add_right, smul_comm Complex.I (_ : ℝ),
    twoForm_smul_right, smul_smul, Complex.I_mul_I, neg_one_smul, twoForm_neg_right]
  conv_rhs => rw [← Complex.re_add_im c]
  push_cast
  linear_combination (-(c.im : ℂ) * ↑(A ![v, w])) * Complex.I_mul_I

theorem hermitianOfTwoForm_smul_left {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hA : IsOneOne A) (c : ℂ) (v w : ComplexModel n) :
    hermitianOfTwoForm A (c • v) w = starRingEnd ℂ c * hermitianOfTwoForm A v w := by
  rw [complex_smul_eq c v]
  simp only [hermitianOfTwoForm, twoForm_add_left, twoForm_smul_left,
    twoForm_I_smul_left_of_isOneOne hA,
    smul_smul, Complex.I_mul_I, neg_one_smul, twoForm_neg_right]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination ((c.im : ℂ) * ↑(A ![v, w])) * Complex.I_mul_I

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

/-- The standard Hermitian two-form `ω(v, w) = Im ⟪v, w⟫` on `ℂⁿ`. -/
def standardHermitianTwoForm (n : ℕ) : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ :=
  Kahler.fundamentalFormAlt

@[simp] theorem standardHermitianTwoForm_apply (v w : ComplexModel n) :
    standardHermitianTwoForm n ![v, w] = (inner ℂ v w).im := by
  simp [standardHermitianTwoForm, Kahler.fundamentalForm]

theorem standardHermitianTwoForm_eq_fundamentalFormAlt (n : ℕ) :
    standardHermitianTwoForm n = Kahler.fundamentalFormAlt := rfl

/-- On complex lines the standard form is the squared norm. -/
theorem standardHermitianTwoForm_apply_I_smul_self (u : ComplexModel n) :
    standardHermitianTwoForm n ![u, Complex.I • u] = ‖u‖ ^ 2 := by
  simp [inner_smul_right, ← Complex.ofReal_pow]

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
