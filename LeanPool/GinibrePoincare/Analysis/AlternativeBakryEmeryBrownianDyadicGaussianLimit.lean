/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicGaussianLimit.lean.
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
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!
# Alternative Bakry Emery Brownian dyadic Gaussian limit

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownian_centered_gaussian_limit`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Centered real Gaussian laws are preserved by actual almost-everywhere
limits when their variances converge. The proof uses the bounded concrete
characteristic functions and dominated convergence. -/
theorem bakryBrownian_centered_gaussian_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (v : ℕ → ℝ≥0) (w : ℝ≥0) (hX : ∀ n, HasLaw (X n) (gaussianReal 0 (v n)) P)
    (hY : AEMeasurable Y P) (hLim : ∀ᵐ sample ∂P, Tendsto (fun n => X n sample) atTop (𝓝 (Y
        sample)))
    (hv : Tendsto v atTop (𝓝 w)) : HasLaw Y (gaussianReal 0 w) P := by
  refine ⟨hY,?_⟩
  apply Measure.ext_of_charFun
  funext t
  have hIntegral : Tendsto (fun n => ∫ sample, Complex.exp ((t*X n sample : ℝ)*Complex.I) ∂P)
      atTop (𝓝 (∫ sample, Complex.exp ((t*Y sample : ℝ)*Complex.I) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n
      exact (Complex.continuous_exp.measurable.comp_aemeasurable
        ((Complex.measurable_ofReal.comp_aemeasurable ((hX n).aemeasurable.const_mul t)).mul_const
            Complex.I)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall (fun sample => by rw [Complex.norm_exp_ofReal_mul_I])
    · filter_upwards [hLim] with sample hs
      exact Complex.continuous_exp.continuousAt.tendsto.comp
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul hs)).mul_const
            Complex.I)
  have hCF (n : ℕ) : (∫ sample, Complex.exp ((t*X n sample : ℝ)*Complex.I) ∂P) =
      Complex.exp (-(v n : ℝ)*t^2/2 : ℂ) := by
    have hh := congrArg (fun μ : Measure ℝ => charFun μ t) (hX n).map_eq
    rw [charFun_apply_real, integral_map (hX n).aemeasurable (by fun_prop),
        charFun_gaussianReal] at hh
    simpa only [mul_zero, Complex.ofReal_zero, zero_mul, zero_sub, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat, Function.comp_def, neg_mul,
          neg_div] using hh
  have hExp : Tendsto (fun n => Complex.exp (-(v n : ℝ)*t^2/2 : ℂ)) atTop
      (𝓝 (Complex.exp (-(w : ℝ)*t^2/2 : ℂ))) := by
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    exact (((Complex.continuous_ofReal.continuousAt.tendsto.comp
      (NNReal.continuous_coe.continuousAt.tendsto.comp hv)).neg.mul_const ((t : ℂ)^2)).div_const 2)
  have he := tendsto_nhds_unique (hIntegral.congr hCF) hExp
  rw [charFun_apply_real, integral_map hY (by fun_prop), charFun_gaussianReal]
  simpa only [mul_zero, Complex.ofReal_zero, zero_mul, zero_sub, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat, Function.comp_def, neg_mul,
        neg_div] using he

end
end GinibrePoincare
