/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedAxial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Boundary behavior of the modified-Bessel radial branches

This module records the boundary facts needed before turning the cross-normalized scalar
branches into a whole-plane mode.  At the origin it uses only the entire first-kind functions:
`I₂(0) = 0`, the exact factorizations of the regular transverse branches through the squared
radius (`minusInside_origin_factorization`, `plusInside_origin_factorization`) and their origin
values.  At infinity it proves explicit exponential bounds for `K₀`, `K₁`, and `K₂` along the
positive real radial variable (`modifiedBessel_K012_radial_exponential_bounds`), by comparing
their defining hyperbolic integrals with those at radius one.  No sectorial asymptotic
expansion is asserted.

The results here are scalar radial statements.  A regular Cartesian extension at the origin,
Sobolev membership, and decay of Cartesian derivatives are not treated here.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace ModifiedBesselBoundaryBehavior

open Complex Filter MeasureTheory Set Topology
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial

/-! ## First-kind behavior at the origin -/

/-- The order-two first-kind function vanishes at the origin. -/
@[simp] theorem I2_zero : ModifiedBessel.I2 0 = 0 := by
  simp [ModifiedBessel.I2]

/-! ## Exact branch factorizations through the squared radius -/

/-- The explicit coefficient `Phi_minus` for the regular signed order-zero branch. -/
def minusInsideSquaredRadiusCoefficient (kappa s : ℂ) : ℂ :=
  -ModifiedBessel.K0 kappa *
    regularizedHGFun 0 {(1 : ℂ)} (kappa ^ 2 * s / 4)

/-- The explicit coefficient `Phi_plus` after extracting the quadratic zero of the regular
order-two branch. -/
def plusInsideSquaredRadiusCoefficient (kappa s : ℂ) : ℂ :=
  ModifiedBessel.K2 kappa * (kappa ^ 2 / 4 *
    regularizedHGFun 0 {(3 : ℂ)} (kappa ^ 2 * s / 4))

/-- The signed order-zero branch is exactly a function of `r²`. -/
theorem minusInside_origin_factorization (kappa r : ℂ) :
    minusInside kappa r = minusInsideSquaredRadiusCoefficient kappa (r ^ 2) := by
  have harg : (kappa * r) ^ 2 / 4 = kappa ^ 2 * r ^ 2 / 4 := by ring
  simp only [minusInside, ModifiedBessel.I0, minusInsideSquaredRadiusCoefficient]
  rw [harg]

/-- The order-two branch is exactly `r²` times a function of `r²`. -/
theorem plusInside_origin_factorization (kappa r : ℂ) :
    plusInside kappa r =
      r ^ 2 * plusInsideSquaredRadiusCoefficient kappa (r ^ 2) := by
  have harg : (kappa * r) ^ 2 / 4 = kappa ^ 2 * r ^ 2 / 4 := by ring
  simp only [plusInside, ModifiedBessel.I2, plusInsideSquaredRadiusCoefficient]
  rw [harg]
  ring

/-! ## Second-kind decay on positive real rays -/

/-- Monotone-in-`r` domination for the second-kind hyperbolic integrals: for `Re κ > 0` and
`r ≥ 1`, the integral `∫_{t>0} e^{-κ r cosh t} a(t) dt` is bounded in norm by
`e^{-(Re κ)(r-1)}` times the corresponding integral at `r = 1`.  This is the exponential-decay
rate used for `K₀`, `K₁`, `K₂` on positive real rays. -/
private theorem norm_hyperbolicIntegral_radial_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re) (a : ℝ → ℝ) (ha : Continuous a)
    (hint : Integrable (fun t : ℝ ↦
      Complex.exp (-kappa * (Real.cosh t : ℂ)) * (a t : ℂ)))
    {r : ℝ} (hr : 1 ≤ r) :
    ‖∫ t in Ioi (0 : ℝ),
        Complex.exp (-(kappa * (r : ℂ)) * (Real.cosh t : ℂ)) * (a t : ℂ)‖ ≤
      Real.exp (-kappa.re * (r - 1)) *
        ∫ t in Ioi (0 : ℝ),
          ‖Complex.exp (-kappa * (Real.cosh t : ℂ)) * (a t : ℂ)‖ := by
  let F : ℝ → ℂ := fun t ↦
    Complex.exp (-(kappa * (r : ℂ)) * (Real.cosh t : ℂ)) * (a t : ℂ)
  let G : ℝ → ℂ := fun t ↦
    Complex.exp (-kappa * (Real.cosh t : ℂ)) * (a t : ℂ)
  have hdom : ∀ t : ℝ, ‖F t‖ ≤ ‖G t‖ := by
    intro t
    dsimp [F, G]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hre_r : (-(kappa * (r : ℂ)) * (Real.cosh t : ℂ)).re =
        -kappa.re * r * Real.cosh t := by
      norm_num [Complex.mul_re]
    have hre_one : (-kappa * (Real.cosh t : ℂ)).re =
        -kappa.re * Real.cosh t := by
      norm_num [Complex.mul_re]
    rw [hre_r, hre_one]
    have hkappaMul : kappa.re ≤ kappa.re * r :=
      le_mul_of_one_le_right hkappa.le hr
    have hmul : kappa.re * Real.cosh t ≤
        kappa.re * r * Real.cosh t :=
      mul_le_mul_of_nonneg_right hkappaMul (Real.cosh_pos t).le
    linarith
  have hF : IntegrableOn F (Ioi (0 : ℝ)) := by
    exact MeasureTheory.Integrable.mono hint.integrableOn
      (by exact (by dsimp [F]; fun_prop : Continuous F).aestronglyMeasurable.restrict)
      (ae_of_all _ hdom)
  have hrate : ∀ t : ℝ, ‖F t‖ ≤
      Real.exp (-kappa.re * (r - 1)) * ‖G t‖ := by
    intro t
    dsimp [F, G]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have hre_r : (-(kappa * (r : ℂ)) * (Real.cosh t : ℂ)).re =
        -kappa.re * r * Real.cosh t := by
      norm_num [Complex.mul_re]
    have hre_one : (-kappa * (Real.cosh t : ℂ)).re =
        -kappa.re * Real.cosh t := by
      norm_num [Complex.mul_re]
    have hexp : Real.exp
          (-(kappa * (r : ℂ)) * (Real.cosh t : ℂ)).re ≤
        Real.exp (-kappa.re * (r - 1)) *
          Real.exp (-kappa * (Real.cosh t : ℂ)).re := by
      rw [hre_r, hre_one, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hproduct : 0 ≤
          kappa.re * (r - 1) * (Real.cosh t - 1) :=
        mul_nonneg (mul_nonneg hkappa.le (sub_nonneg.mpr hr))
          (sub_nonneg.mpr (Real.one_le_cosh t))
      calc
        -kappa.re * r * Real.cosh t ≤
            -kappa.re * r * Real.cosh t +
              kappa.re * (r - 1) * (Real.cosh t - 1) :=
          le_add_of_nonneg_right hproduct
        _ = -kappa.re * (r - 1) + -kappa.re * Real.cosh t := by ring
    calc
      Real.exp (-(kappa * (r : ℂ)) * (Real.cosh t : ℂ)).re * ‖(a t : ℂ)‖ ≤
          (Real.exp (-kappa.re * (r - 1)) *
            Real.exp (-kappa * (Real.cosh t : ℂ)).re) * ‖(a t : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = Real.exp (-kappa.re * (r - 1)) *
          (Real.exp (-kappa * (Real.cosh t : ℂ)).re * ‖(a t : ℂ)‖) := by ring
  calc
    ‖∫ t in Ioi (0 : ℝ), F t‖ ≤ ∫ t in Ioi (0 : ℝ), ‖F t‖ :=
      norm_integral_le_integral_norm F
    _ ≤ ∫ t in Ioi (0 : ℝ),
        Real.exp (-kappa.re * (r - 1)) * ‖G t‖ := by
      apply setIntegral_mono_on hF.norm
        (hint.norm.const_mul (Real.exp (-kappa.re * (r - 1)))).integrableOn
        measurableSet_Ioi
      intro t _
      exact hrate t
    _ = Real.exp (-kappa.re * (r - 1)) * ∫ t in Ioi (0 : ℝ), ‖G t‖ := by
      rw [integral_const_mul]

/-- Explicit exponential bounds for all three exterior Bessel orders.  The constants on the
right are fixed finite integrals at radius one; no asymptotic expansion is used. -/
theorem modifiedBessel_K012_radial_exponential_bounds
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 1 ≤ r) :
    ‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K0Integrand kappa t‖ ∧
      ‖ModifiedBessel.K1 (kappa * (r : ℂ))‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖ ∧
      ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖ := by
  have hint0 : Integrable (fun t : ℝ ↦
      Complex.exp (-kappa * (Real.cosh t : ℂ)) * ((1 : ℝ) : ℂ)) := by
    apply (ModifiedBessel.integrable_K0Integrand hkappa).congr
    exact ae_of_all _ fun t ↦ by
      simp only [ModifiedBessel.K0Integrand]
      norm_num
  have hint1 : Integrable (fun t : ℝ ↦
      Complex.exp (-kappa * (Real.cosh t : ℂ)) * (Real.cosh t : ℂ)) := by
    apply (ModifiedBessel.integrable_K1Integrand hkappa).congr
    exact ae_of_all _ fun t ↦ by simp only [ModifiedBessel.K1Integrand]
  have hint2 : Integrable (fun t : ℝ ↦
      Complex.exp (-kappa * (Real.cosh t : ℂ)) * (Real.cosh (2 * t) : ℂ)) := by
    apply (ModifiedBessel.integrable_K2Integrand hkappa).congr
    exact ae_of_all _ fun t ↦ by simp only [ModifiedBessel.K2Integrand]
  constructor
  · simpa [ModifiedBessel.K0, ModifiedBessel.K0Integrand] using
      norm_hyperbolicIntegral_radial_le_exp hkappa (fun _ ↦ (1 : ℝ))
        continuous_const hint0 hr
  constructor
  · simpa [ModifiedBessel.K1, ModifiedBessel.K1Integrand] using
      norm_hyperbolicIntegral_radial_le_exp hkappa Real.cosh Real.continuous_cosh hint1 hr
  · simpa [ModifiedBessel.K2, ModifiedBessel.K2Integrand] using
      norm_hyperbolicIntegral_radial_le_exp hkappa (fun t ↦ Real.cosh (2 * t))
        (by fun_prop) hint2 hr

/-! ## Consequences for the cross-normalized branches -/

/-- The regular order-two cross-normalized branch vanishes at the origin. -/
@[simp] theorem plusInside_zero (kappa : ℂ) : plusInside kappa 0 = 0 := by
  simp [plusInside]

/-- The signed regular order-zero cross-normalized branch has its exact origin value. -/
@[simp] theorem minusInside_zero (kappa : ℂ) :
    minusInside kappa 0 = -ModifiedBessel.K0 kappa := by
  simp [minusInside]

end ModifiedBesselBoundaryBehavior
end FastDynamo
