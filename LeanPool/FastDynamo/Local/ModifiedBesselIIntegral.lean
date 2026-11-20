/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.ModifiedBesselIRecurrence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier integral for the modified-Bessel function `I₁`

This module derives the standard cosine-integral representation of the order-one function
directly from the regularized-hypergeometric definition.  The proof expands the
exponential under the finite interval integral, evaluates the cosine moments, and recombines
the even and odd subsequences.  In particular, it does not assume an external Bessel-function
integral formula.
-/

@[expose] public section

namespace FastDynamo.ModifiedBessel

open Complex Real Set MeasureTheory
open scoped Interval

/-- Odd cosine moments vanish on `[0, π]`: `∫₀^π cos θ ^ (2m+1) dθ = 0`, by the reduction
formula for powers of the cosine. -/
private theorem integral_cos_pow_odd_zero (m : ℕ) :
    (∫ θ : ℝ in 0..Real.pi, Real.cos θ ^ (2 * m + 1)) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        integral_cos_pow]
      simp [ih]

/-- Even cosine moments on `[0, π]` in closed form:
`∫₀^π cos θ ^ (2m) dθ = π (2m)! / (4^m (m!)²)`. -/
private theorem integral_cos_pow_even_factorial (m : ℕ) :
    (∫ θ : ℝ in 0..Real.pi, Real.cos θ ^ (2 * m)) =
      Real.pi * (2 * m).factorial /
        ((4 : ℝ) ^ m * (m.factorial : ℝ) ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, integral_cos_pow, ih]
      simp only [Real.sin_pi, Real.sin_zero, mul_zero, sub_self, zero_div, zero_add]
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
        Nat.factorial_succ (n := 2 * m + 1), Nat.factorial_succ (n := 2 * m),
        Nat.factorial_succ (n := m)]
      push_cast
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have hm2 : (2 : ℝ) * m + 2 ≠ 0 := by positivity
      field_simp [hm1, hm2]
      ring

/-- The order-one first-kind function written as its explicit power series,
`I₁ z = ∑_m z^{2m+1} / (2^{2m+1} m! (m+1)!)`, obtained from the regularized hypergeometric
definition. -/
private theorem I1_eq_explicit_tsum (z : ℂ) :
    I1 z = ∑' m : ℕ,
      z ^ (2 * m + 1) /
        ((2 : ℂ) ^ (2 * m + 1) * (m.factorial : ℂ) * ((m + 1).factorial : ℂ)) := by
  unfold I1 regularizedHGFun FormalMultilinearSeries.sum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [regularizedHGFunSeries_coeff, coeff_two, smul_eq_mul]
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hm1 : ((m + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  field_simp [hm, hm1]
  have hpow : (1 / 4 : ℂ) ^ m * 2 ^ (2 * m) = 1 := by
    rw [pow_mul, ← mul_pow]
    norm_num
  calc
    z * (z ^ 2 / 4) ^ m * 2 ^ (2 * m + 1) =
        2 * z * (z ^ 2) ^ m * ((1 / 4 : ℂ) ^ m * 2 ^ (2 * m)) := by
      simp only [div_eq_mul_inv, pow_succ]
      ring
    _ = 2 * z * (z ^ 2) ^ m := by rw [hpow, mul_one]
    _ = 2 * z ^ (2 * m + 1) := by
      have hz : z ^ (2 * m + 1) = (z ^ 2) ^ m * z := by
        rw [pow_succ, pow_mul]
      rw [hz]
      ring

/-- The `n`-th term of the exponential expansion of `exp (z cos θ) cos θ` under the angular
integral: `(z cos θ)^n / n! · cos θ`. -/
private noncomputable def I1FourierTerm (z : ℂ) (n : ℕ) (θ : ℝ) : ℂ :=
  (z * (Real.cos θ : ℂ)) ^ n / (n.factorial : ℂ) * (Real.cos θ : ℂ)

/-- Each Fourier term is bounded uniformly in `θ` by `‖z‖^n / n!`, the summable majorant used
for dominated convergence under the angular integral. -/
private theorem norm_I1FourierTerm_le (z : ℂ) (n : ℕ) (θ : ℝ) :
    ‖I1FourierTerm z n θ‖ ≤ ‖z‖ ^ n / (n.factorial : ℝ) := by
  unfold I1FourierTerm
  rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real,
    Complex.norm_natCast, Real.norm_eq_abs]
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hc0 : 0 ≤ |Real.cos θ| := abs_nonneg _
  have hz0 : 0 ≤ ‖z‖ ^ n := by positivity
  have hf0 : 0 ≤ (n.factorial : ℝ) := by positivity
  have hcp : |Real.cos θ| ^ n ≤ 1 := pow_le_one₀ hc0 hc
  calc
    (‖z‖ * |Real.cos θ|) ^ n / (n.factorial : ℝ) * |Real.cos θ| =
        (‖z‖ ^ n / (n.factorial : ℝ)) * (|Real.cos θ| ^ n * |Real.cos θ|) := by
      rw [mul_pow]
      ring
    _ ≤ (‖z‖ ^ n / (n.factorial : ℝ)) * 1 := by
      gcongr
      calc
        |Real.cos θ| ^ n * |Real.cos θ| ≤ 1 * |Real.cos θ| :=
          mul_le_mul_of_nonneg_right hcp hc0
        _ ≤ 1 := by simpa using hc
    _ = _ := mul_one _

/-- Pointwise in `θ`, the Fourier terms sum to `exp (z cos θ) cos θ`. -/
private theorem I1FourierTerm_hasSum (z : ℂ) (θ : ℝ) :
    HasSum (fun n : ℕ ↦ I1FourierTerm z n θ)
      (Complex.exp (z * (Real.cos θ : ℂ)) * (Real.cos θ : ℂ)) := by
  simpa only [I1FourierTerm, Complex.exp_eq_exp_ℂ] using
    (NormedSpace.expSeries_div_hasSum_exp
      (z * (Real.cos θ : ℂ))).mul_right (Real.cos θ : ℂ)

/-- The angular integrals of the Fourier terms sum to the integral of `exp (z cos θ) cos θ`,
by dominated convergence against the majorant `‖z‖^n / n!`. -/
private theorem I1FourierTerm_integral_hasSum (z : ℂ) :
    HasSum (fun n : ℕ ↦ ∫ θ : ℝ in 0..Real.pi, I1FourierTerm z n θ)
      (∫ θ : ℝ in 0..Real.pi,
        Complex.exp (z * (Real.cos θ : ℂ)) * (Real.cos θ : ℂ)) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) ↦ ‖z‖ ^ n / (n.factorial : ℝ)) ?_ ?_ ?_ ?_ ?_
  · intro n
    apply Continuous.aestronglyMeasurable
    unfold I1FourierTerm
    fun_prop
  · intro n
    exact Filter.Eventually.of_forall fun θ _ ↦ norm_I1FourierTerm_le z n θ
  · exact Filter.Eventually.of_forall fun θ _ ↦
      (NormedSpace.expSeries_div_hasSum_exp (‖z‖ : ℝ)).summable
  · have hs : (∑' n : ℕ, ‖z‖ ^ n / (n.factorial : ℝ)) = Real.exp ‖z‖ :=
      by simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (‖z‖ : ℝ)).tsum_eq
    simp_rw [hs]
    exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun θ _ ↦ I1FourierTerm_hasSum z θ

/-- The complex cosine moment on `[0, π]` is the real one under the inclusion `ℝ → ℂ`. -/
private theorem complex_integral_cos_pow (n : ℕ) :
    (∫ θ : ℝ in 0..Real.pi, (Real.cos θ : ℂ) ^ n) =
      Complex.ofReal (∫ θ : ℝ in 0..Real.pi, Real.cos θ ^ n) := by
  simpa only [Complex.ofReal_pow] using
    (intervalIntegral.integral_ofReal (f := fun θ : ℝ ↦ Real.cos θ ^ n))

/-- Complex form of the vanishing odd cosine moments on `[0, π]`. -/
private theorem complex_integral_cos_pow_odd_zero (m : ℕ) :
    (∫ θ : ℝ in 0..Real.pi, (Real.cos θ : ℂ) ^ (2 * m + 1)) = 0 := by
  calc
    _ = Complex.ofReal
        (∫ θ : ℝ in 0..Real.pi, Real.cos θ ^ (2 * m + 1)) :=
      complex_integral_cos_pow (2 * m + 1)
    _ = 0 := by rw [integral_cos_pow_odd_zero]; simp

/-- Complex form of the closed evaluation of the even cosine moments on `[0, π]`. -/
private theorem complex_integral_cos_pow_even_factorial (m : ℕ) :
    (∫ θ : ℝ in 0..Real.pi, (Real.cos θ : ℂ) ^ (2 * m)) =
      (Real.pi : ℂ) * ((2 * m).factorial : ℂ) /
        ((4 : ℂ) ^ m * (m.factorial : ℂ) ^ 2) := by
  rw [complex_integral_cos_pow, integral_cos_pow_even_factorial]
  push_cast
  rfl

/-- The even-index Fourier terms integrate to zero, since they carry an odd power of `cos θ`. -/
private theorem integral_I1FourierTerm_even (z : ℂ) (m : ℕ) :
    (∫ θ : ℝ in 0..Real.pi, I1FourierTerm z (2 * m) θ) = 0 := by
  calc
    (∫ θ : ℝ in 0..Real.pi, I1FourierTerm z (2 * m) θ) =
        ∫ θ : ℝ in 0..Real.pi,
          (z ^ (2 * m) / ((2 * m).factorial : ℂ)) *
            ((Real.cos θ : ℂ) ^ (2 * m + 1)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      unfold I1FourierTerm
      rw [mul_pow]
      have hcos : (Real.cos θ : ℂ) ^ (2 * m + 1) =
          (Real.cos θ : ℂ) ^ (2 * m) * Real.cos θ := by
        rw [pow_succ]
      change z ^ (2 * m) * (Real.cos θ : ℂ) ^ (2 * m) /
          ((2 * m).factorial : ℂ) * Real.cos θ =
        (z ^ (2 * m) / ((2 * m).factorial : ℂ)) *
          (Real.cos θ : ℂ) ^ (2 * m + 1)
      rw [hcos]
      ring
    _ = (z ^ (2 * m) / ((2 * m).factorial : ℂ)) *
        (∫ θ : ℝ in 0..Real.pi, (Real.cos θ : ℂ) ^ (2 * m + 1)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 0 := by
      rw [complex_integral_cos_pow_odd_zero]
      simp

/-- The odd-index Fourier terms integrate to `π z^{2m+1} / (2^{2m+1} m! (m+1)!)`, which is `π`
times the `m`-th coefficient of the power series of `I₁`. -/
private theorem integral_I1FourierTerm_odd (z : ℂ) (m : ℕ) :
    (∫ θ : ℝ in 0..Real.pi, I1FourierTerm z (2 * m + 1) θ) =
      (Real.pi : ℂ) *
        (z ^ (2 * m + 1) /
          ((2 : ℂ) ^ (2 * m + 1) * (m.factorial : ℂ) *
            ((m + 1).factorial : ℂ))) := by
  calc
    (∫ θ : ℝ in 0..Real.pi, I1FourierTerm z (2 * m + 1) θ) =
        ∫ θ : ℝ in 0..Real.pi,
          (z ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ)) *
            ((Real.cos θ : ℂ) ^ (2 * (m + 1))) := by
      apply intervalIntegral.integral_congr
      intro θ _
      unfold I1FourierTerm
      rw [mul_pow]
      have hcos : (Real.cos θ : ℂ) ^ (2 * (m + 1)) =
          (Real.cos θ : ℂ) ^ (2 * m + 1) * Real.cos θ := by
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, pow_succ]
      change z ^ (2 * m + 1) * (Real.cos θ : ℂ) ^ (2 * m + 1) /
          ((2 * m + 1).factorial : ℂ) * Real.cos θ =
        (z ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ)) *
          (Real.cos θ : ℂ) ^ (2 * (m + 1))
      rw [hcos]
      ring
    _ = (z ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ)) *
        (∫ θ : ℝ in 0..Real.pi, (Real.cos θ : ℂ) ^ (2 * (m + 1))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (Real.pi : ℂ) *
        (z ^ (2 * m + 1) /
          ((2 : ℂ) ^ (2 * m + 1) * (m.factorial : ℂ) *
            ((m + 1).factorial : ℂ))) := by
      rw [complex_integral_cos_pow_even_factorial]
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        Nat.factorial_succ (n := 2 * m + 1), Nat.factorial_succ (n := m)]
      push_cast
      have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      have h2m1 : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero (2 * m)
      have h2m2 : ((2 * m + 2 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero (2 * m + 1)
      have hfact : (((2 * m + 1).factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * m + 1)
      have hpow : (2 : ℂ) ^ (2 * m) = 4 ^ m := by
        rw [pow_mul]
        norm_num
      field_simp [hm, hm1, h2m1, h2m2, hfact]
      simp only [pow_succ]
      rw [hpow]
      ring

/-- Fourier-cosine integral normalization for the order-one modified Bessel function. -/
theorem integral_exp_mul_cos_eq_pi_mul_I1 (z : ℂ) :
    (∫ θ : ℝ in 0..Real.pi,
      Complex.exp (z * (Real.cos θ : ℂ)) * (Real.cos θ : ℂ)) =
      (Real.pi : ℂ) * I1 z := by
  let f : ℕ → ℂ := fun n ↦ ∫ θ : ℝ in 0..Real.pi, I1FourierTerm z n θ
  have hsum : Summable f := (I1FourierTerm_integral_hasSum z).summable
  have heven : Summable (fun m : ℕ ↦ f (2 * m)) := by
    exact hsum.comp_injective (i := fun m : ℕ ↦ 2 * m)
      (by intro a b h; exact Nat.mul_left_cancel (by norm_num) h)
  have hodd : Summable (fun m : ℕ ↦ f (2 * m + 1)) := by
    exact hsum.comp_injective (i := fun m : ℕ ↦ 2 * m + 1)
      (by
        intro a b h
        exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel h))
  calc
    (∫ θ : ℝ in 0..Real.pi,
        Complex.exp (z * (Real.cos θ : ℂ)) * (Real.cos θ : ℂ)) =
        ∑' n : ℕ, f n := (I1FourierTerm_integral_hasSum z).tsum_eq.symm
    _ = (∑' m : ℕ, f (2 * m)) + (∑' m : ℕ, f (2 * m + 1)) :=
      (tsum_even_add_odd heven hodd).symm
    _ = 0 + ∑' m : ℕ,
        (Real.pi : ℂ) *
          (z ^ (2 * m + 1) /
            ((2 : ℂ) ^ (2 * m + 1) * (m.factorial : ℂ) *
              ((m + 1).factorial : ℂ))) := by
      congr 1
      · simp [f, integral_I1FourierTerm_even]
      · apply tsum_congr
        intro m
        exact integral_I1FourierTerm_odd z m
    _ = (Real.pi : ℂ) * ∑' m : ℕ,
        z ^ (2 * m + 1) /
          ((2 : ℂ) ^ (2 * m + 1) * (m.factorial : ℂ) *
            ((m + 1).factorial : ℂ)) := by
      rw [zero_add, tsum_mul_left]
    _ = (Real.pi : ℂ) * I1 z := by rw [I1_eq_explicit_tsum]

end FastDynamo.ModifiedBessel
