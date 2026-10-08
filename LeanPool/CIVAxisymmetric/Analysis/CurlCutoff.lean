/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.DivCurl
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Curl Cutoff

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The gradient of a scalar `χ` on `Vec3`, as the vector of its partials. -/
@[expose] def gradVec (χ : Vec3 → ℝ) (x : Vec3) : Vec3 := fun i => fderiv ℝ χ x (basisVec i)

/-- The cross product on `Vec3`. -/
@[expose] def cross3 (a b : Vec3) : Vec3 :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

theorem curlVec_smul {χ : Vec3 → ℝ} {v : Vec3 → Vec3} {x : Vec3}
    (hχ : DifferentiableAt ℝ χ x) (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    curlVec (fun y => χ y • v y) x = χ x • curlVec v x + cross3 (gradVec χ x) (v x) := by
  ext i
  fin_cases i
  · -- component 0
    have h2 := fderiv_mul hχ (hv 2)
    have h1 := fderiv_mul hχ (hv 1)
    have h2_app := congrArg (fun (L : Vec3 →L[ℝ] ℝ) => L (basisVec 1)) h2
    have h1_app := congrArg (fun (L : Vec3 →L[ℝ] ℝ) => L (basisVec 2)) h1
    simp only [add_apply, smul_apply, smul_eq_mul] at h2_app h1_app
    have h2_app' : fderiv ℝ (fun y : Vec3 => χ y * v y 2) x (basisVec 1) =
        χ x * fderiv ℝ (fun y : Vec3 => v y 2) x (basisVec 1) + fderiv ℝ χ x (basisVec 1) * v x
          2 := by
      have eq_fn : (fun y : Vec3 => χ y * v y 2) = χ * (fun y : Vec3 => v y 2) := by
        ext y; simp
      simpa [eq_fn, mul_comm] using h2_app
    have h1_app' : fderiv ℝ (fun y : Vec3 => χ y * v y 1) x (basisVec 2) =
        χ x * fderiv ℝ (fun y : Vec3 => v y 1) x (basisVec 2) + fderiv ℝ χ x (basisVec 2) * v x
          1 := by
      have eq_fn : (fun y : Vec3 => χ y * v y 1) = χ * (fun y : Vec3 => v y 1) := by
        ext y; simp
      simpa [eq_fn, mul_comm] using h1_app
    simp [curlVec, cross3, gradVec, Pi.smul_apply, smul_eq_mul, h2_app', h1_app']
    ring_nf
  · -- component 1
    have h0 := fderiv_mul hχ (hv 0)
    have h2 := fderiv_mul hχ (hv 2)
    have h0_app := congrArg (fun (L : Vec3 →L[ℝ] ℝ) => L (basisVec 2)) h0
    have h2_app := congrArg (fun (L : Vec3 →L[ℝ] ℝ) => L (basisVec 0)) h2
    simp only [add_apply, smul_apply, smul_eq_mul] at h0_app h2_app
    have h0_app' : fderiv ℝ (fun y : Vec3 => χ y * v y 0) x (basisVec 2) =
        χ x * fderiv ℝ (fun y : Vec3 => v y 0) x (basisVec 2) + fderiv ℝ χ x (basisVec 2) * v x
          0 := by
      have eq_fn : (fun y : Vec3 => χ y * v y 0) = χ * (fun y : Vec3 => v y 0) := by
        ext y; simp
      simpa [eq_fn, mul_comm] using h0_app
    have h2_app' : fderiv ℝ (fun y : Vec3 => χ y * v y 2) x (basisVec 0) =
        χ x * fderiv ℝ (fun y : Vec3 => v y 2) x (basisVec 0) + fderiv ℝ χ x (basisVec 0) * v x
          2 := by
      have eq_fn : (fun y : Vec3 => χ y * v y 2) = χ * (fun y : Vec3 => v y 2) := by
        ext y; simp
      simpa [eq_fn, mul_comm] using h2_app
    simp [curlVec, cross3, gradVec, Pi.smul_apply, smul_eq_mul, h0_app', h2_app']
    ring_nf
  · -- component 2
    have h1 := fderiv_mul hχ (hv 1)
    have h0 := fderiv_mul hχ (hv 0)
    have h1_app := congrArg (fun (L : Vec3 →L[ℝ] ℝ) => L (basisVec 0)) h1
    have h0_app := congrArg (fun (L : Vec3 →L[ℝ] ℝ) => L (basisVec 1)) h0
    simp only [add_apply, smul_apply, smul_eq_mul] at h1_app h0_app
    have h1_app' : fderiv ℝ (fun y : Vec3 => χ y * v y 1) x (basisVec 0) =
        χ x * fderiv ℝ (fun y : Vec3 => v y 1) x (basisVec 0) + fderiv ℝ χ x (basisVec 0) * v x
          1 := by
      have eq_fn : (fun y : Vec3 => χ y * v y 1) = χ * (fun y : Vec3 => v y 1) := by
        ext y; simp
      simpa [eq_fn, mul_comm] using h1_app
    have h0_app' : fderiv ℝ (fun y : Vec3 => χ y * v y 0) x (basisVec 1) =
        χ x * fderiv ℝ (fun y : Vec3 => v y 0) x (basisVec 1) + fderiv ℝ χ x (basisVec 1) * v x
          0 := by
      have eq_fn : (fun y : Vec3 => χ y * v y 0) = χ * (fun y : Vec3 => v y 0) := by
        ext y; simp
      simpa [eq_fn, mul_comm] using h0_app
    simp [curlVec, cross3, gradVec, Pi.smul_apply, smul_eq_mul, h1_app', h0_app']
    ring_nf

theorem div_smul {χ : Vec3 → ℝ} {v : Vec3 → Vec3} {x : Vec3}
    (hχ : DifferentiableAt ℝ χ x) (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x (basisVec j) =
      χ x * ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j) +
        ∑ j : Fin 3, gradVec χ x j * v x j := by
  simp only [Pi.smul_apply, smul_eq_mul]
  have h_eq : ∀ j, fderiv ℝ (fun y : Vec3 => χ y * v y j) x (basisVec j)
      = fderiv ℝ (χ * (fun y : Vec3 => v y j)) x (basisVec j) := by
    intro j
    have eq_fn : (fun y : Vec3 => χ y * v y j) = χ * (fun y : Vec3 => v y j) := by
      ext y; simp
    rw [eq_fn]
  calc
    ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y * v y j) x (basisVec j)
        = ∑ j : Fin 3, fderiv ℝ (χ * (fun y : Vec3 => v y j)) x (basisVec j) := by
      simp [h_eq]
    _ = ∑ j : Fin 3, ((χ x • fderiv ℝ (fun y : Vec3 => v y j) x)
            + ((fun y : Vec3 => v y j) x) • fderiv ℝ χ x) (basisVec j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact congrArg (fun (L : Vec3 →L[ℝ] ℝ) => L (basisVec j)) (fderiv_mul hχ (hv j))
    _ = ∑ j : Fin 3, (χ x • fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j)
        + fderiv ℝ χ x (basisVec j) * v x j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [add_apply, smul_apply, smul_eq_mul, mul_comm]
    _ = (∑ j : Fin 3, χ x • fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j))
        + (∑ j : Fin 3, fderiv ℝ χ x (basisVec j) * v x j) := by
      rw [Finset.sum_add_distrib]
    _ = χ x * (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j))
        + (∑ j : Fin 3, fderiv ℝ χ x (basisVec j) * v x j) := by
      simp [Finset.mul_sum]
    _ = χ x * ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j)
        + ∑ j : Fin 3, gradVec χ x j * v x j := by
      simp [gradVec]

theorem sum_sq_cross3_le (a b : Vec3) :
    ∑ i : Fin 3, (cross3 a b i) ^ 2 ≤ (∑ i : Fin 3, a i ^ 2) * ∑ i : Fin 3, b i ^ 2 := by
  simp [cross3, Fin.sum_univ_three]
  nlinarith only [sq_nonneg (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)]

theorem sum_sq_add_le_two_mul (a b : Vec3) :
    ∑ i : Fin 3, (a i + b i) ^ 2 ≤ 2 * ∑ i : Fin 3, a i ^ 2 + 2 * ∑ i : Fin 3, b i ^ 2 := by
  simp [Fin.sum_univ_three]
  nlinarith only [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2 - b 2)]

theorem sum_sq_smul (c : ℝ) (a : Vec3) : ∑ i : Fin 3, (c • a) i ^ 2 = c ^ 2 * ∑ i : Fin 3, a i ^
    2 := by
  simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  ring_nf

end CIV
