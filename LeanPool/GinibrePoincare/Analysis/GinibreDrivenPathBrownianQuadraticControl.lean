/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathBrownianQuadraticControl.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticConfigurationHessianSum
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoQuadraticControl
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoUniformChain
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoActualPathRemainder

/-! Actual Volterra increments are controlled by actual Brownian coordinate quadratic sums. -/

@[expose] public section
open Set MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenPath_brownian_quadratic_control {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω)
    (X : ℝ≥0 → Configuration n) (b : ℝ → Configuration n) (T : ℝ≥0)
    (hb : ContinuousOn b (Icc (0 : ℝ) T)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) T, ‖b s‖ ≤ M)
    (hX : ∀ t ∈ Icc 0 T, X t = X 0 +
      (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω 0) +
      ∫ s in (0 : ℝ)..(t : ℝ), b s) (k : ℕ) :
    itoActualPathQuadraticSum X T k ≤
      2*ginibreConfigurationBrownianCoordinateQuadraticSum n B α T k ω+
        2*(M*((T : ℝ)/((k : ℝ)+1)))*(M*(T : ℝ)) := by
  classical
  let a := fun i : Fin (k+1) =>
    ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k (i.val+1))-
      ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k i)
  let d := fun i : Fin (k+1) => itoUniformDriftIncrement b T k i
  have hi (i : Fin (k+1)) := itoVolterra_uniform_increment X
    (fun t => ginibreConfigurationBrownianNoise n B α ω t) b T hb hX k i
  have hq := itoConfigurationQuadraticSum_le Finset.univ a d
    (M*((T : ℝ)/((k : ℝ)+1)))
    (fun i hi => itoUniformDriftIncrement_norm_le b T k M hbound i)
  have hv := itoUniformDriftIncrement_variation_le b T k M hbound
  have hm : 0 ≤ 2*(M*((T : ℝ)/((k : ℝ)+1))) := by positivity
  unfold itoActualPathQuadraticSum
  simp_rw [hi]
  calc
    _ ≤ 2*(∑ p : Fin n × Fin 2, ∑ i : Fin (k+1),
        (configurationEuclideanLinearEquiv n (a i) p)^2)+
        2*(M*((T : ℝ)/((k : ℝ)+1)))*(∑ i : Fin (k+1), ‖d i‖) := hq
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hv hm)
end
end GinibrePoincare
