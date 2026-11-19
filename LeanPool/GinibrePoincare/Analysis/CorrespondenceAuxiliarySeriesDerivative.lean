/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliarySeriesDerivative.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireDifferentiability

/-!
# Correspondence auxiliary series derivative

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `hasFDerivAt_holomorphicHermite_series`,
`summable_fderiv_holomorphicHermite_series`.
-/

@[expose] public section
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section

/-- Termwise genuine complex Fréchet differentiation of the entire bounded
coefficient Hermite reconstruction, with all summability proved internally. -/
theorem hasFDerivAt_holomorphicHermite_series (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (z : Configuration n) :
    HasFDerivAt (fun w : Configuration n => ∑' p,
      c p * ComplexHermite.multivariateNormalized n hn p 0 w)
      (∑' p, fderiv ℂ (fun w : Configuration n =>
        c p * ComplexHermite.multivariateNormalized n hn p 0 w) z) z := by
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
  exact hsum

theorem summable_fderiv_holomorphicHermite_series (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (z : Configuration n) :
    Summable (fun p => fderiv ℂ (fun w : Configuration n =>
      c p * ComplexHermite.multivariateNormalized n hn p 0 w) z) := by
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
  apply Summable.of_norm_bounded hs
  intro p
  change ‖fderiv ℂ (F p) z‖ ≤ (C * (n : ℝ)) * B p
  rw [mul_assoc]
  exact hbounds p z (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))

end
end GinibrePoincare
