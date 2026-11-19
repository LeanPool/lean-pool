/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianEntireSeriesBounds.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MultivariateComplexHermite
public import LeanPool.GinibrePoincare.Concrete.Configuration
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.Basic

/-! # Factorial series bounds for genuine entire Gaussian reconstruction -/

@[expose] public section
open Filter
namespace GinibrePoincare
noncomputable section

/-- The square-root factorial still dominates every exponential. This gives
absolute convergence of the normalized holomorphic Hermite series on bounded
configuration sets even with only bounded coefficients. -/
theorem summable_pow_div_sqrt_factorial (a : ℝ) :
    Summable (fun p : ℕ => a ^ p / Real.sqrt (p.factorial : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 * |a| ^ 2)
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [eventually_ge_atTop N] with p hp
  have hfac : 0 < Real.sqrt (p.factorial : ℝ) := by positivity
  have hsucc : 0 < Real.sqrt ((p + 1 : ℕ) : ℝ) := by positivity
  have hpn : (N : ℝ) ≤ p := by exact_mod_cast hp
  have hsq : 2 * |a| ≤ Real.sqrt ((p + 1 : ℕ) : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    push_cast
    nlinarith
  have hrec : a ^ (p + 1) / Real.sqrt ((p + 1).factorial : ℝ) =
      (a / Real.sqrt ((p + 1 : ℕ) : ℝ)) *
        (a ^ p / Real.sqrt (p.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), pow_succ]
    ring
  rw [hrec, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hsucc]
  apply (div_le_iff₀ hsucc).mpr
  linarith

theorem summable_holomorphicHermite_bound (n : ℕ) (R : ℝ) :
    Summable (fun p : ℕ => ComplexHermite.oneDimNormalization n p * R ^ p) := by
  simpa only [ComplexHermite.oneDimNormalization, mul_pow, div_mul_eq_mul_div,
    mul_comm (Real.sqrt (n : ℝ) ^ _) (R ^ _)] using
    summable_pow_div_sqrt_factorial (Real.sqrt n * R)

/-- Tensor products of nonnegative summable scalar bounds are summable over
the full multivariate index set. -/
theorem summable_tensor_bound (d : ℕ) {b : ℕ → ℝ}
    (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) :
    Summable (fun p : Fin d → ℕ => ∏ i, b (p i)) := by
  induction d with
  | zero => exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ d ih =>
    let e := Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)
    have hbn : (0 : (Fin d → ℕ) → ℝ) ≤ fun p => ∏ i : Fin d, b (p i) := by
      intro p
      exact Finset.prod_nonneg (fun i _ => hb0 (p i))
    have hprod : Summable (fun p : ℕ × (Fin d → ℕ) => b p.1 * ∏ i, b (p.2 i)) := by
      apply (summable_prod_of_nonneg (fun p => mul_nonneg (hb0 p.1) (hbn p.2))).mpr
      refine ⟨fun k => ih.mul_left (b k), ?_⟩
      simpa only [ih.tsum_mul_left] using hb.mul_right (∑' p : Fin d → ℕ, ∏ i, b (p i))
    have heq : (fun p : Fin (d+1) → ℕ => ∏ i, b (p i)) ∘ e =
        (fun p : ℕ × (Fin d → ℕ) => b p.1 * ∏ i, b (p.2 i)) := by
      funext p
      change (∏ i : Fin (d+1), b (Fin.cons (α := fun _ => ℕ) p.1 p.2 i)) = _
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← heq] at hprod
    exact (Equiv.summable_iff e).mp hprod

theorem summable_tensor_holomorphicHermite_bound (d n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun p : Fin d → ℕ =>
      ∏ i, ComplexHermite.oneDimNormalization n (p i) * R ^ p i) :=
  summable_tensor_bound (b := fun k => ComplexHermite.oneDimNormalization n k * R ^ k)
    d (summable_holomorphicHermite_bound n R)
    (fun k => by unfold ComplexHermite.oneDimNormalization; positivity)

theorem norm_holomorphicHermite_le_tensor_bound (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) {R : ℝ} (_hR : 0 ≤ R) {z : Configuration n}
    (hz : ∀ i, ‖z i‖ ≤ R) :
    ‖ComplexHermite.multivariateNormalized n hn p 0 z‖ ≤
      ∏ i, ComplexHermite.oneDimNormalization n (p i) * R ^ p i := by
  rw [ComplexHermite.multivariateNormalized_zero_right, norm_prod]
  apply Finset.prod_le_prod₀
  · intro i _; exact norm_nonneg _
  · intro i _
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hnrm : 0 ≤ ComplexHermite.oneDimNormalization n (p i) := by
      unfold ComplexHermite.oneDimNormalization; positivity
    rw [abs_of_nonneg hnrm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hz i) _) hnrm

/-- Bounded coefficient sequences give an absolutely convergent genuine
function series at every configuration. -/
theorem summable_holomorphicHermite_series (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (z : Configuration n) : Summable (fun p =>
      c p * ComplexHermite.multivariateNormalized n hn p 0 z) := by
  let R' := ‖z‖
  have hR' : 0 ≤ R' := norm_nonneg z
  have hz : ∀ i, ‖z i‖ ≤ R' := fun i => norm_le_pi_norm z i
  apply Summable.of_norm_bounded
    ((summable_tensor_holomorphicHermite_bound n n hR').mul_left C)
  intro p
  rw [norm_mul]
  have hCp : 0 ≤ C := (norm_nonneg (c p)).trans (hC p)
  exact mul_le_mul (hC p) (norm_holomorphicHermite_le_tensor_bound n hn p hR' hz)
    (norm_nonneg _) hCp

end
end GinibrePoincare
