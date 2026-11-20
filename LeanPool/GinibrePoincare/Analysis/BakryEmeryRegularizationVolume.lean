/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BakryEmeryRegularizationVolume.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BakryEmeryRegularizationLimit
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Gaussian domination and Gibbs regularization on actual Euclidean volume. -/

@[expose] public section
namespace GinibrePoincare
open MeasureTheory
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The confinement majorant is genuinely integrable in every finite real
Hilbert dimension, including the block dimensions of Theorem 1.14. -/
theorem bakryEmery_gaussian_majorant_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : E => Real.exp (-a*‖x‖^2)) volume := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (a : ℂ)) (by simpa using ha) 0 (0 : E)).re
  convert h using 1
  funext x
  simp only [neg_mul, zero_mul, add_zero]
  change Real.exp (-(a*‖x‖^2)) = (Complex.exp (-((a : ℂ)*(‖x‖:ℂ)^2))).re
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_re]

/-- Concrete compact-test entropy convergence on actual Euclidean volume:
the Gaussian integrability input is discharged internally. -/
theorem bakryEmeryRegularizedLift_volume_entropy_tendsto
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : E → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Filter.Tendsto (fun ε : ℝ => squareEntropy (bakryEmeryNormalizedGibbs volume
      (bakryEmeryRegularizedLiftPotential n V ε)) f) (𝓝 0)
      (𝓝 (squareEntropy (bakryEmeryNormalizedGibbs volume
        (bakryEmeryEuclideanLiftPotential n V)) f)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact bakryEmeryRegularizedLift_entropy_tendsto volume n ρ V hV hρ.le hrot hc
    (by simpa only [neg_div] using
      bakryEmery_gaussian_majorant_integrable (E := E) ((n : ℝ)*ρ/2) (by positivity)) f hf hfc

/-- Concrete compact-test expectations converge under the actual volume laws. -/
theorem bakryEmeryRegularizedLift_volume_expectation_tendsto
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : E → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Filter.Tendsto (fun ε : ℝ => ∫ x, f x ∂bakryEmeryNormalizedGibbs volume
      (bakryEmeryRegularizedLiftPotential n V ε)) (𝓝 0)
      (𝓝 (∫ x, f x ∂bakryEmeryNormalizedGibbs volume
        (bakryEmeryEuclideanLiftPotential n V))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact bakryEmeryRegularizedLift_compact_expectation_tendsto volume n ρ V hV hρ.le hrot hc
    (by simpa only [neg_div] using
      bakryEmery_gaussian_majorant_integrable (E := E) ((n : ℝ)*ρ/2) (by positivity)) f hf hfc

end
end GinibrePoincare
