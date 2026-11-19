/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoQuadraticControl.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoConfiguration
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftVariation

/-!
# Finite dimensional Ito quadratic control

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoConfigurationQuadraticSum_le`.
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

theorem itoNorm_add_sq_le (a b : E) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a+b)
  have hsq := sq_nonneg (‖a‖-‖b‖)
  nlinarith

/-- Actual configuration quadratic sums are controlled by actual scalar noise
quadratic sums and actual drift variation. -/
theorem itoConfigurationQuadraticSum_le {n : ℕ} {ι : Type*}
    (s : Finset ι) (a b : ι → Configuration n) (m : ℝ)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ m) :
    ∑ i ∈ s, ‖a i+b i‖^2 ≤
      2*(∑ j : Fin n × Fin 2, ∑ i ∈ s, (configurationEuclideanLinearEquiv n (a i) j)^2) +
        2*m*(∑ i ∈ s, ‖b i‖) := by
  calc
    _ ≤ ∑ i ∈ s, (2*‖a i‖^2+2*‖b i‖^2) :=
      Finset.sum_le_sum (fun i hi => itoNorm_add_sq_le _ _)
    _ ≤ ∑ i ∈ s, (2*(∑ j : Fin n × Fin 2,
        (configurationEuclideanLinearEquiv n (a i) j)^2)+2*m*‖b i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have ha := itoConfiguration_norm_sq_le_coordinate_sum (a i)
      have hd := mul_le_mul_of_nonneg_right (hb i hi) (norm_nonneg (b i))
      nlinarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm]

end
end GinibrePoincare
