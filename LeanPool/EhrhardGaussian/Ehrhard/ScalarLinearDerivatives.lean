/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianLinearForm
public import LeanPool.EhrhardGaussian.Ehrhard.GaussianHeatRegularity
public import LeanPool.EhrhardGaussian.Ehrhard.OUGenerator
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Derivatives of scalar test functions pulled back along linear forms -/

@[expose] public noncomputable section

open EhrhardGaussian.Gaussian (coordinateDerivative)

namespace EhrhardGaussian.Ehrhard

/-- The derivative of a scalar function composed with a linear form is its scalar derivative times
that form. -/
theorem hasFDerivAt_scalar_comp {n : ℕ} {f : ℝ → ℝ} (c : Fin n → ℝ) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f (coordinateForm c x)) :
    HasFDerivAt (f ∘ coordinateForm c) (deriv f (coordinateForm c x) • coordinateForm c) x := by
  have h := hf.hasDerivAt.hasFDerivAt.comp x (coordinateForm c).hasFDerivAt
  convert h using 1
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  exact mul_comm _ _

/-- A coordinate derivative of a scaled scalar linear pullback equals the product of its scale,
coefficient and derivative. -/
theorem coordinateDerivative_const_mul_scalar_comp {n : ℕ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (a : ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    coordinateDerivative (fun y => a * f (coordinateForm c y)) i x =
      a * c i * deriv f (coordinateForm c x) := by
  rw [coordinateDerivative]
  change fderiv ℝ (fun y => a * (f ∘ coordinateForm c) y) x (Pi.single i 1) = _
  rw [((hasFDerivAt_scalar_comp c x (hf _)).const_mul a).fderiv]
  simp only [smul_apply, coordinateForm_single, smul_eq_mul]
  ring

/-- A coordinate derivative of a scalar linear pullback equals its coefficient times the scalar
derivative. -/
theorem coordinateDerivative_scalar_comp {n : ℕ} {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    coordinateDerivative (f ∘ coordinateForm c) i x = c i * deriv f (coordinateForm c x) := by
  simpa only [one_mul, Function.comp_def] using coordinateDerivative_const_mul_scalar_comp hf 1 c x
    i

/-- Second coordinate derivatives of a scalar linear pullback equal the coefficient product times
the scalar second derivative. -/
theorem secondCoordinateDerivative_scalar_comp {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    coordinateDerivative (coordinateDerivative (f ∘ coordinateForm c) i) j x =
      c i * c j * deriv (deriv f) (coordinateForm c x) := by
  have hf₀ := hf.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf₁ := hf.deriv'.differentiable_one
  have heq : coordinateDerivative (f ∘ coordinateForm c) i =
      fun y => c i * deriv f (coordinateForm c y) := funext fun y =>
        coordinateDerivative_scalar_comp hf₀ c y i
  rw [heq]
  exact coordinateDerivative_const_mul_scalar_comp hf₁ (c i) c x j

/-- Third coordinate derivatives of a scalar linear pullback equal the coefficient product times the
scalar third derivative. -/
theorem thirdCoordinateDerivative_scalar_comp {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (i j k : Fin n) :
    coordinateDerivative (coordinateDerivative (coordinateDerivative (f ∘ coordinateForm c) i) j) k
      x =
      c i * c j * c k * deriv (deriv (deriv f)) (coordinateForm c x) := by
  have hf₀ : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hf₂ : Differentiable ℝ (deriv (deriv f)) := hf.deriv'.deriv'.differentiable_one
  have heq : coordinateDerivative (coordinateDerivative (f ∘ coordinateForm c) i) j =
      fun y => (c i * c j) * deriv (deriv f) (coordinateForm c y) :=
    funext fun y => secondCoordinateDerivative_scalar_comp hf₀ c y i j
  rw [heq]
  exact coordinateDerivative_const_mul_scalar_comp hf₂ (c i * c j) c x k

/-- The generator of a scalar linear pullback is its variance times the second derivative minus its
argument times the first derivative. -/
theorem ouGenerator_scalar_comp {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (c : Fin n → ℝ) (x : Fin n → ℝ) :
    ouGenerator (f ∘ coordinateForm c) x =
      (∑ i, c i ^ 2) * deriv (deriv f) (coordinateForm c x) -
        coordinateForm c x * deriv f (coordinateForm c x) := by
  rw [ouGenerator]
  simp_rw [secondCoordinateDerivative_scalar_comp hf]
  rw [(hasFDerivAt_scalar_comp c x (hf.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    _)).fderiv]
  simp only [smul_apply, smul_eq_mul, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · exact mul_comm _ _

end EhrhardGaussian.Ehrhard

end
