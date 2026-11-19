/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianEntireDifferentiability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireSeriesBounds
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Gaussian entire differentiability

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `differentiable_holomorphicHermite_series`.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem norm_fderiv_fintype_prod_le {d : ℕ}
    (f : Fin d → Configuration d → ℂ) (B : Fin d → ℝ)
    (z : Configuration d) (hf : ∀ i, DifferentiableAt ℂ (f i) z)
    (hB : ∀ i, 0 ≤ B i) (hv : ∀ i, ‖f i z‖ ≤ B i)
    (hd : ∀ i, ‖fderiv ℂ (f i) z‖ ≤ B i) :
    ‖fderiv ℂ (fun z => ∏ i, f i z) z‖ ≤ d * ∏ i, B i := by
  rw [fderiv_finsetProd (fun i _ => hf i)]
  apply le_trans (norm_sum_le _ _)
  have ht : ∀ i : Fin d,
      ‖(∏ j ∈ Finset.univ.erase i, f j z) • fderiv ℂ (f i) z‖ ≤ ∏ j, B j := by
    intro i
    rw [norm_smul, norm_prod]
    calc
      _ ≤ (∏ j ∈ Finset.univ.erase i, B j) * B i :=
        mul_le_mul (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hv j))
          (hd i) (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hB j))
      _ = ∏ j, B j := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  calc
    _ ≤ ∑ _i : Fin d, ∏ j, B j := Finset.sum_le_sum (fun i _ => ht i)
    _ = _ := by simp

theorem norm_fderiv_normalized_coordinate_pow_le (d n k : ℕ)
    (i : Fin d) {R : ℝ} (hR : 1 ≤ R) {z : Configuration d} (hz : ‖z i‖ ≤ R) :
    ‖fderiv ℂ (fun w : Configuration d =>
      (ComplexHermite.oneDimNormalization n k : ℂ) * (w i) ^ k) z‖ ≤
      ComplexHermite.oneDimNormalization n k * (2 * R) ^ k := by
  have ha : 0 ≤ ComplexHermite.oneDimNormalization n k := by
    unfold ComplexHermite.oneDimNormalization; positivity
  have hc : DifferentiableAt ℂ (fun w : Configuration d => w i) z :=
    (differentiable_apply i) z
  change ‖fderiv ℂ (fun w : Configuration d =>
    (ComplexHermite.oneDimNormalization n k : ℂ) *
      ((fun w : Configuration d => w i) ^ k) w) z‖ ≤ _
  rw [fderiv_const_mul (hc.pow k)]
  change ‖(ComplexHermite.oneDimNormalization n k : ℂ) •
    fderiv ℂ ((fun w : Configuration d => w i) ^ k) z‖ ≤ _
  rw [fderiv_pow k hc, (hasFDerivAt_apply (𝕜 := ℂ) i z).fderiv,
    norm_smul, norm_smul, nsmul_eq_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ha]
  have hp : ‖(ContinuousLinearMap.proj i : Configuration d →L[ℂ] ℂ)‖ ≤ 1 := by
    apply (ContinuousLinearMap.proj i : Configuration d →L[ℂ] ℂ).opNorm_le_bound (by norm_num)
    intro w
    simpa using norm_le_pi_norm w i
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast Nat.lt_two_pow_self.le
  have hzpow : ‖z i‖ ^ (k - 1) ≤ R ^ k :=
    (pow_le_pow_left₀ (norm_nonneg _) hz _).trans
      (pow_le_pow_right₀ hR (Nat.sub_le k 1))
  calc
    _ = (ComplexHermite.oneDimNormalization n k * ((k : ℝ) * ‖z i‖ ^ (k-1))) *
        ‖(ContinuousLinearMap.proj i : Configuration d →L[ℂ] ℂ)‖ := by ring
    _ ≤ ComplexHermite.oneDimNormalization n k *
        ((2 : ℝ) ^ k * R ^ k) * 1 := by
      apply mul_le_mul _ hp (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hk hzpow (by positivity) (by positivity)) ha
    _ = _ := by rw [mul_one, mul_pow]

theorem norm_fderiv_holomorphicHermite_le (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) {R : ℝ} (hR : 1 ≤ R) {z : Configuration n}
    (hz : ∀ i, ‖z i‖ ≤ R) :
    ‖fderiv ℂ (ComplexHermite.multivariateNormalized n hn p 0) z‖ ≤
      n * ∏ i, ComplexHermite.oneDimNormalization n (p i) * (2 * R) ^ p i := by
  have heq : ComplexHermite.multivariateNormalized n hn p 0 =
      fun w : Configuration n => ∏ i, (ComplexHermite.oneDimNormalization n (p i) : ℂ) *
        (w i) ^ p i := by
    funext w
    exact ComplexHermite.multivariateNormalized_zero_right n hn p w
  rw [heq]
  apply norm_fderiv_fintype_prod_le
  · intro i
    exact ((differentiable_const _).mul ((differentiable_apply i).pow (p i))) z
  · intro i; unfold ComplexHermite.oneDimNormalization; positivity
  · intro i
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have ha : 0 ≤ ComplexHermite.oneDimNormalization n (p i) := by
      unfold ComplexHermite.oneDimNormalization; positivity
    rw [abs_of_nonneg ha]
    apply mul_le_mul_of_nonneg_left _ ha
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (hz i).trans (by linarith)
  · intro i
    exact norm_fderiv_normalized_coordinate_pow_le n n (p i) i hR (hz i)

/-- Every bounded-coefficient holomorphic Hermite series is genuinely entire
on the multivariate configuration space. -/
theorem differentiable_holomorphicHermite_series (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C) :
    Differentiable ℂ (fun z : Configuration n => ∑' p,
      c p * ComplexHermite.multivariateNormalized n hn p 0 z) := by
  intro z
  let R := max 1 (‖z‖ + 1)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ 2 * R := by linarith
  let F : (Fin n → ℕ) → Configuration n → ℂ := fun p w =>
    c p * ComplexHermite.multivariateNormalized n hn p 0 w
  have hF : ∀ p : Fin n → ℕ, Differentiable ℂ (F p) := by
    intro p
    change Differentiable ℂ (fun w => c p *
      ComplexHermite.multivariateNormalized n hn p 0 w)
    simp only [ComplexHermite.multivariateNormalized_zero_right]
    fun_prop
  have hbounds : ∀ (p : Fin n → ℕ) (w : Configuration n), w ∈ Metric.ball z 1 →
      ‖fderiv ℂ (F p) w‖ ≤ C * ((n : ℝ) *
        ∏ i, ComplexHermite.oneDimNormalization n (p i) * (2 * R) ^ p i) := by
    intro p w hw
    have hmono : DifferentiableAt ℂ (ComplexHermite.multivariateNormalized n hn p 0) w := by
      change DifferentiableAt ℂ (fun z => ComplexHermite.multivariateNormalized n hn p 0 z) w
      simp only [ComplexHermite.multivariateNormalized_zero_right]
      fun_prop
    change ‖fderiv ℂ (fun w => c p * ComplexHermite.multivariateNormalized n hn p 0 w) w‖ ≤ _
    rw [fderiv_const_mul hmono (c p), norm_smul]
    have hwR : ∀ i, ‖w i‖ ≤ R := fun i =>
      (norm_le_pi_norm w i).trans ((norm_lt_of_mem_ball hw).le.trans (le_max_right _ _))
    exact mul_le_mul (hC p) (norm_fderiv_holomorphicHermite_le n hn p hR hwR)
      (norm_nonneg _) ((norm_nonneg (c p)).trans (hC p))
  let B : (Fin n → ℕ) → ℝ := fun p =>
    ∏ i, ComplexHermite.oneDimNormalization n (p i) * (2 * R) ^ p i
  have hB : Summable B := summable_tensor_holomorphicHermite_bound n n hR0
  have hs : Summable (fun p : Fin n → ℕ => (C * (n : ℝ)) * B p) := hB.mul_left (C * (n : ℝ))
  have hsum := hasFDerivAt_tsum_of_isPreconnected
    (x₀ := z) (x := z) (s := Metric.ball z 1)
    (f := F) (f' := fun p w => fderiv ℂ (F p) w)
    (u := fun p : Fin n → ℕ => (C * (n : ℝ)) * B p)
    hs Metric.isOpen_ball (convex_ball z 1).isPreconnected
    (fun p w _ => (hF p w).hasFDerivAt)
    (fun p w hw => by
      change ‖fderiv ℂ (F p) w‖ ≤ (C * (n : ℝ)) * B p
      rw [mul_assoc]
      exact hbounds p w hw)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
    (summable_holomorphicHermite_series n hn c hC z)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  exact hsum.differentiableAt

end
end GinibrePoincare
