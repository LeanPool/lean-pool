/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The homogeneous linear form `∑ i, a i * X i` with a given coefficient vector,
and its basic API: homogeneity, degree, evaluation, coefficient maps, renaming and
linearity in the coefficient vector. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {R S σ τ : Type*}

/-- The linear form `∑ i, a i * X i` with coefficient vector `a`. -/
def linearForm [CommSemiring R] [Fintype σ] (a : σ → R) : MvPolynomial σ R :=
  ∑ i, C (a i) * X i

section CommSemiring

variable [CommSemiring R] [Fintype σ]

/-- A linear form is homogeneous of degree one. -/
lemma linearForm_isHomogeneous (a : σ → R) : (linearForm a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ i)

/-- A linear form has total degree at most one. -/
lemma linearForm_totalDegree_le (a : σ → R) : (linearForm a).totalDegree ≤ 1 :=
  (linearForm_isHomogeneous a).totalDegree_le

/-- The linear form with coefficients `a` evaluates at `x` to `∑ i, a i * x i`. -/
@[simp] lemma eval_linearForm (a x : σ → R) : eval x (linearForm a) = ∑ i, a i * x i := by
  simp [linearForm]

/-- The linear form with coefficients `a` evaluates at a point `x` of an `R`-algebra `S` to
`∑ i, algebraMap R S (a i) * x i`. -/
@[simp] lemma aeval_linearForm [CommSemiring S] [Algebra R S] (a : σ → R) (x : σ → S) :
    aeval x (linearForm a) = ∑ i, algebraMap R S (a i) * x i := by
  simp [linearForm]

/-- Evaluating the linear form with coefficients `a` along `φ` at `x` gives
`∑ i, φ (a i) * x i`. -/
@[simp] lemma eval₂_linearForm [CommSemiring S] (φ : R →+* S) (a : σ → R) (x : σ → S) :
    eval₂ φ x (linearForm a) = ∑ i, φ (a i) * x i := by
  simp [linearForm]

/-- Renaming the variables of a linear form along a bijection `e` gives the linear form whose
coefficient vector is reindexed by `e.symm`. -/
lemma rename_linearForm [Fintype τ] (e : σ ≃ τ) (a : σ → R) :
    rename e (linearForm a) = linearForm (a ∘ e.symm) := by
  simp only [linearForm, map_sum, map_mul, rename_C, rename_X]
  simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
    e.sum_comp (fun j => C (a (e.symm j)) * X j)

/-- The linear form with zero coefficient vector is zero. -/
@[simp] lemma linearForm_zero : linearForm (0 : σ → R) = 0 := by
  simp [linearForm]

/-- The linear form is additive in its coefficient vector. -/
lemma linearForm_add (a b : σ → R) : linearForm (a + b) = linearForm a + linearForm b := by
  simp [linearForm, add_mul, Finset.sum_add_distrib]

/-- The linear form commutes with scalar multiplication of its coefficient vector. -/
lemma linearForm_smul (c : R) (a : σ → R) : linearForm (c • a) = c • linearForm a := by
  simp [linearForm, Finset.smul_sum, smul_eq_C_mul, mul_assoc]

variable (R σ) in
/-- `linearForm` as a linear map from coefficient vectors to polynomials. -/
def linearFormLinearMap : (σ → R) →ₗ[R] MvPolynomial σ R where
  toFun := linearForm
  map_add' := linearForm_add
  map_smul' := linearForm_smul

/-- The linear map `linearFormLinearMap R σ` sends a coefficient vector `a` to `linearForm a`. -/
@[simp] lemma linearFormLinearMap_apply (a : σ → R) :
    linearFormLinearMap R σ a = linearForm a :=
  rfl

end CommSemiring

section CommRing

variable [CommRing R] [Fintype σ]

end CommRing

end
end CCDN
