/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoDriftQuadratic.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoTaylor
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Finite dimensional Ito drift quadratic

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoDirectionalHessian_compact_drift_sum_tendsto`,
`itoDirectionalHessian_local_compact_drift_sum_tendsto`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual bilinear second differential, evaluated on two different increments. -/
def itoHessianBilinear (f : E → ℝ) (x a b : E) : ℝ :=
  iteratedFDeriv ℝ 2 f x ![a, b]

theorem itoHessianBilinear_norm_le (f : E → ℝ) (x a b : E) :
    ‖itoHessianBilinear f x a b‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖a‖ * ‖b‖ := by
  simpa [itoHessianBilinear, Fin.prod_univ_two, mul_assoc] using
    (iteratedFDeriv ℝ 2 f x).le_opNorm ![a, b]

theorem itoDirectionalHessian_add (f : E → ℝ) (x a b : E) :
    itoDirectionalHessian f x (a+b) = itoDirectionalHessian f x a +
      itoHessianBilinear f x a b + itoHessianBilinear f x b a +
      itoDirectionalHessian f x b := by
  simp only [itoDirectionalHessian, itoHessianBilinear, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_add, add_apply]
  ring

/-- Uniform operator-norm Hessian bounds control all noise-drift quadratic errors. -/
theorem itoDirectionalHessian_drift_error_le (f : E → ℝ) (x a b : E)
    (B : ℝ) (hB : ‖iteratedFDeriv ℝ 2 f x‖ ≤ B) :
    ‖itoDirectionalHessian f x (a+b) - itoDirectionalHessian f x a‖ ≤
      B * (2 * ‖a‖ * ‖b‖ + ‖b‖^2) := by
  rw [itoDirectionalHessian_add]
  have hb : itoDirectionalHessian f x b = itoHessianBilinear f x b b := by
    simp [itoDirectionalHessian, itoHessianBilinear, iteratedFDeriv_two_apply]
  rw [hb]
  have he : itoDirectionalHessian f x a + itoHessianBilinear f x a b +
      itoHessianBilinear f x b a + itoHessianBilinear f x b b -
      itoDirectionalHessian f x a = itoHessianBilinear f x a b +
        itoHessianBilinear f x b a + itoHessianBilinear f x b b := by ring
  rw [he]
  calc
    _ ≤ ‖itoHessianBilinear f x a b‖ + ‖itoHessianBilinear f x b a‖ +
        ‖itoHessianBilinear f x b b‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖iteratedFDeriv ℝ 2 f x‖ * ‖a‖ * ‖b‖) +
        (‖iteratedFDeriv ℝ 2 f x‖ * ‖b‖ * ‖a‖) +
        (‖iteratedFDeriv ℝ 2 f x‖ * ‖b‖ * ‖b‖) := by
      gcongr <;> exact itoHessianBilinear_norm_le f x _ _
    _ = ‖iteratedFDeriv ℝ 2 f x‖ * (2 * ‖a‖ * ‖b‖ + ‖b‖^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (by positivity)

/-- Finite-variation drift does not contribute to the quadratic Taylor limit. -/
theorem itoDirectionalHessian_drift_sum_tendsto (f : E → ℝ)
    (s : ℕ → Finset ℕ) (x a b : ℕ → ℕ → E)
    (B C : ℝ) (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hbnd : ∀ k, ∀ i ∈ s k, ‖iteratedFDeriv ℝ 2 f (x k i)‖ ≤ B)
    (mesh : ℕ → ℝ) (hm : Tendsto mesh atTop (𝓝 0)) (hmpos : ∀ k, 0 ≤ mesh k)
    (ha : ∀ k, ∀ i ∈ s k, ‖a k i‖ ≤ mesh k)
    (hb : ∀ k, ∀ i ∈ s k, ‖b k i‖ ≤ mesh k)
    (hv : ∀ k, ∑ i ∈ s k, ‖b k i‖ ≤ C) :
    Tendsto (fun k => ∑ i ∈ s k,
      (itoDirectionalHessian f (x k i) (a k i+b k i) -
        itoDirectionalHessian f (x k i) (a k i))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k => (3*B*C)*mesh k) atTop (𝓝 0) := by
    simpa using hm.const_mul (3*B*C)
  apply squeeze_zero_norm _ hlim
  intro k
  calc
    _ ≤ ∑ i ∈ s k, ‖itoDirectionalHessian f (x k i) (a k i+b k i) -
        itoDirectionalHessian f (x k i) (a k i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s k, B*(3*mesh k*‖b k i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (itoDirectionalHessian_drift_error_le f _ _ _ B (hbnd k i hi)).trans
      apply mul_le_mul_of_nonneg_left _ hB
      have h1 := mul_le_mul_of_nonneg_right (ha k i hi) (norm_nonneg (b k i))
      have h2 := mul_le_mul_of_nonneg_right (hb k i hi) (norm_nonneg (b k i))
      nlinarith
    _ = (3*B*mesh k)*(∑ i ∈ s k, ‖b k i‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (3*B*mesh k)*C := mul_le_mul_of_nonneg_left (hv k) (mul_nonneg (mul_nonneg (by norm_num) hB)
        (hmpos k))
    _ = _ := by ring

/-- Compact localization supplies the actual Hessian bound automatically. -/
theorem itoDirectionalHessian_compact_drift_sum_tendsto (f : E → ℝ)
    (hf : ContDiff ℝ 2 f) (K : Set E) (hK : IsCompact K)
    (s : ℕ → Finset ℕ) (x a b : ℕ → ℕ → E)
    (hx : ∀ k, ∀ i ∈ s k, x k i ∈ K) (C : ℝ) (hC : 0 ≤ C)
    (mesh : ℕ → ℝ) (hm : Tendsto mesh atTop (𝓝 0)) (hmpos : ∀ k, 0 ≤ mesh k)
    (ha : ∀ k, ∀ i ∈ s k, ‖a k i‖ ≤ mesh k)
    (hb : ∀ k, ∀ i ∈ s k, ‖b k i‖ ≤ mesh k)
    (hv : ∀ k, ∑ i ∈ s k, ‖b k i‖ ≤ C) :
    Tendsto (fun k => ∑ i ∈ s k,
      (itoDirectionalHessian f (x k i) (a k i+b k i) -
        itoDirectionalHessian f (x k i) (a k i))) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := 2) (by norm_num)).continuousOn
  exact itoDirectionalHessian_drift_sum_tendsto f s x a b (max B 0) C
    (le_max_right _ _) hC (fun k i hi => (hB _ (hx k i hi)).trans (le_max_left _ _))
    mesh hm hmpos ha hb hv

/-- Local C² compact Hessian bounds remove finite-variation drift as well. -/
theorem itoDirectionalHessian_local_compact_drift_sum_tendsto (f : E → ℝ)
    (U K : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (s : ℕ → Finset ℕ) (x a b : ℕ → ℕ → E)
    (hx : ∀ k, ∀ i ∈ s k, x k i ∈ K) (C : ℝ) (hC : 0 ≤ C)
    (mesh : ℕ → ℝ) (hm : Tendsto mesh atTop (𝓝 0)) (hmpos : ∀ k, 0 ≤ mesh k)
    (ha : ∀ k, ∀ i ∈ s k, ‖a k i‖ ≤ mesh k)
    (hb : ∀ k, ∀ i ∈ s k, ‖b k i‖ ≤ mesh k)
    (hv : ∀ k, ∑ i ∈ s k, ‖b k i‖ ≤ C) :
    Tendsto (fun k => ∑ i ∈ s k,
      (itoDirectionalHessian f (x k i) (a k i+b k i) -
        itoDirectionalHessian f (x k i) (a k i))) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv (k := 2) hf hU (by norm_num)).mono hKU)
  exact itoDirectionalHessian_drift_sum_tendsto f s x a b (max B 0) C
    (le_max_right _ _) hC (fun k i hi => (hB _ (hx k i hi)).trans (le_max_left _ _))
    mesh hm hmpos ha hb hv

end
end GinibrePoincare
