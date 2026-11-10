/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUCommutation

/-!
# The second-order chain rule for the OU generator

The outer function needs regularity only at the range of the inner map. This
is essential for Gaussian quantiles, whose natural domain is the probability
box. The Hessian is always evaluated at the smoothed inputs.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- The derivative of a composition is the sum of its coordinate chain rule terms. -/
theorem fderiv_comp_apply_sum {n k : ℕ} {Ψ : (Fin k → ℝ) → ℝ}
    {g : (Fin n → ℝ) → (Fin k → ℝ)} {x : Fin n → ℝ}
    (hΨ : DifferentiableAt ℝ Ψ (g x)) (hg : DifferentiableAt ℝ g x) (v : Fin n → ℝ) :
    fderiv ℝ (Ψ ∘ g) x v =
      ∑ i, coordinateDerivative Ψ i (g x) * fderiv ℝ (fun y => g y i) x v := by
  rw [fderiv_comp _ hΨ hg, ContinuousLinearMap.comp_apply, concentration_fderiv_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_apply hg i, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    mul_comm]

/-- A coordinate derivative of a composition satisfies the coordinate chain rule. -/
theorem coordinateDerivative_comp {n k : ℕ} {Ψ : (Fin k → ℝ) → ℝ}
    {g : (Fin n → ℝ) → (Fin k → ℝ)} {x : Fin n → ℝ}
    (hΨ : DifferentiableAt ℝ Ψ (g x)) (hg : DifferentiableAt ℝ g x) (j : Fin n) :
    coordinateDerivative (Ψ ∘ g) j x =
      ∑ i, coordinateDerivative Ψ i (g x) * coordinateDerivative (fun y => g y i) j x := by
  rw [coordinateDerivative, fderiv_comp _ hΨ hg, ContinuousLinearMap.comp_apply,
    concentration_fderiv_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coordinateDerivative]
  rw [fderiv_apply hg i, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, mul_comm]

/-- Coordinate derivatives satisfy the product rule. -/
theorem coordinateDerivative_mul {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin n) :
    coordinateDerivative (fun y => f y * g y) j x =
      coordinateDerivative f j x * g x + f x * coordinateDerivative g j x := by
  have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j 1))
    (fderiv_fun_mul hf hg)
  simpa only [coordinateDerivative, add_apply, smul_apply, smul_eq_mul,
    mul_comm, add_comm] using h

/-- Coordinate differentiation commutes with finite sums of differentiable functions. -/
theorem coordinateDerivative_sum {n : ℕ} {α : Type*} (s : Finset α)
    {f : α → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (j : Fin n) :
    coordinateDerivative (fun y => ∑ i ∈ s, f i y) j x =
      ∑ i ∈ s, coordinateDerivative (f i) j x := by
  rw [coordinateDerivative, fderiv_fun_sum hf, sum_apply]
  rfl

/-- Coordinate derivatives of a twice continuously differentiable function are differentiable. -/
theorem differentiableAt_coordinateDerivative {k : ℕ} {Ψ : (Fin k → ℝ) → ℝ}
    {x : Fin k → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ x) (i : Fin k) :
    DifferentiableAt ℝ (coordinateDerivative Ψ i) x := by
  have h := (hΨ.fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : Fin k → ℝ => Pi.single i (1 : ℝ)) x)
  exact h.differentiableAt_one

/-- The second coordinate chain rule, including both the Hessian contraction
and the inner second derivatives. -/
theorem mixedSecondCoordinateDerivative_comp {n k : ℕ} {Ψ : (Fin k → ℝ) → ℝ}
    {g : (Fin n → ℝ) → (Fin k → ℝ)}
    (hΨ : ∀ y, ContDiffAt ℝ 2 Ψ (g y)) (hg : ContDiff ℝ 2 g)
    (x : Fin n → ℝ) (j m : Fin n) :
    coordinateDerivative (coordinateDerivative (Ψ ∘ g) j) m x =
      ∑ i, ((∑ l, coordinateDerivative (coordinateDerivative Ψ i) l (g x) *
          coordinateDerivative (fun y => g y l) m x) * coordinateDerivative (fun y => g y i) j x +
        coordinateDerivative Ψ i (g x) *
          coordinateDerivative (coordinateDerivative (fun y => g y i) j) m x) := by
  have hg' := hg.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hΨ' (y : Fin n → ℝ) := (hΨ y).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have heq : coordinateDerivative (Ψ ∘ g) j =
      fun y => ∑ i, coordinateDerivative Ψ i (g y) * coordinateDerivative (fun z => g z i) j y := by
    funext y
    exact coordinateDerivative_comp (hΨ' y) (hg' y) j
  rw [heq]
  have hgrad (i : Fin k) : DifferentiableAt ℝ
      (fun y => coordinateDerivative Ψ i (g y)) x :=
    (differentiableAt_coordinateDerivative (hΨ x) i).comp x (hg' x)
  have hinner (i : Fin k) : DifferentiableAt ℝ
      (coordinateDerivative (fun y => g y i) j) x :=
    differentiableAt_coordinateDerivative ((contDiff_pi.mp hg i).contDiffAt) j
  have hterm (i : Fin k) : DifferentiableAt ℝ
      (fun y => coordinateDerivative Ψ i (g y) * coordinateDerivative (fun z => g z i) j y) x := by
    simpa only [Pi.mul_def] using (hgrad i).mul (hinner i)
  rw [coordinateDerivative_sum Finset.univ (fun i _ => hterm i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateDerivative_mul (hgrad i) (hinner i)]
  have hchain := coordinateDerivative_comp
    (differentiableAt_coordinateDerivative (hΨ x) i) (hg' x) m
  simpa only [Function.comp_def] using congrArg
    (fun z : ℝ => z * coordinateDerivative (fun y => g y i) j x +
      coordinateDerivative Ψ i (g x) * coordinateDerivative (coordinateDerivative (fun y => g y i)
        j) m x) hchain

/-- Second coordinate derivatives of a composition satisfy the second order chain rule. -/
theorem secondCoordinateDerivative_comp {n k : ℕ} {Ψ : (Fin k → ℝ) → ℝ}
    {g : (Fin n → ℝ) → (Fin k → ℝ)}
    (hΨ : ∀ y, ContDiffAt ℝ 2 Ψ (g y)) (hg : ContDiff ℝ 2 g)
    (x : Fin n → ℝ) (j : Fin n) :
    coordinateDerivative (coordinateDerivative (Ψ ∘ g) j) j x =
      ∑ i, ((∑ l, coordinateDerivative (coordinateDerivative Ψ i) l (g x) *
          coordinateDerivative (fun y => g y l) j x) * coordinateDerivative (fun y => g y i) j x +
        coordinateDerivative Ψ i (g x) *
          coordinateDerivative (coordinateDerivative (fun y => g y i) j) j x) :=
  mixedSecondCoordinateDerivative_comp hΨ hg x j j

private theorem generator_sum_identity {n k : ℕ} (H : Fin k → Fin k → ℝ)
    (v W : Fin k → Fin n → ℝ) (a d : Fin k → ℝ) :
    (∑ j, ∑ i, ((∑ l, H i l * v l j) * v i j + a i * W i j)) - ∑ i, a i * d i =
      (∑ i, a i * ((∑ j, W i j) - d i)) +
        ∑ i, ∑ l, H i l * ∑ j, v i j * v l j := by
  have hH : (∑ j, ∑ i, (∑ l, H i l * v l j) * v i j) =
      ∑ i, ∑ l, H i l * ∑ j, v i j * v l j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hW : (∑ j, ∑ i, a i * W i j) = ∑ i, a i * ∑ j, W i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.mul_sum _ _ _).symm
  simp_rw [Finset.sum_add_distrib]
  rw [hH, hW]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- The OU generator of a composition consists of the first-order generator
term and the covariance-weighted Hessian contraction. -/
theorem ouGenerator_comp {n k : ℕ} {Ψ : (Fin k → ℝ) → ℝ}
    {g : (Fin n → ℝ) → (Fin k → ℝ)}
    (hΨ : ∀ y, ContDiffAt ℝ 2 Ψ (g y)) (hg : ContDiff ℝ 2 g) (x : Fin n → ℝ) :
    ouGenerator (Ψ ∘ g) x =
      (∑ i, coordinateDerivative Ψ i (g x) * ouGenerator (fun y => g y i) x) +
        ∑ i, ∑ l, coordinateDerivative (coordinateDerivative Ψ i) l (g x) *
          ∑ j, coordinateDerivative (fun y => g y i) j x *
            coordinateDerivative (fun y => g y l) j x := by
  have hg' := hg.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hΨ' := (hΨ x).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  rw [ouGenerator]
  simp_rw [secondCoordinateDerivative_comp hΨ hg]
  rw [fderiv_comp_apply_sum hΨ' (hg' x) x]
  exact generator_sum_identity
    (fun i l => coordinateDerivative (coordinateDerivative Ψ i) l (g x))
    (fun i j => coordinateDerivative (fun y => g y i) j x)
    (fun i j => coordinateDerivative (coordinateDerivative (fun y => g y i) j) j x)
    (fun i => coordinateDerivative Ψ i (g x))
    (fun i => fderiv ℝ (fun y => g y i) x x)

end EhrhardGaussian.Ehrhard

end
