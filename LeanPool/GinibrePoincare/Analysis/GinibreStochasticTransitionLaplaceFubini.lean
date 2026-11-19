/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionLaplaceFubini.lean.
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

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Ginibre stochastic transition Laplace Fubini

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `boundedTransitionMean_laplace_fubini`.
-/

@[expose] public section

open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- Ordinary Bochner Fubini for a genuinely integrable initial value and a
jointly measurable uniformly bounded transition mean. -/
theorem boundedTransitionMean_laplace_fubini {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (f : E → ℝ) (hf : Integrable f μ)
    (m : ℝ × E → ℝ) (hm : Measurable m) (C : ℝ) (hC : ∀ p, ‖m p‖ ≤ C)
    {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), ∫ z, f z*(Real.exp (-c*t)*m (t, z)) ∂μ)=
      ∫ z, f z*(∫ t in Ioi (0 : ℝ), Real.exp (-c*t)*m (t, z)) ∂μ := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  have he : Integrable (fun t : ℝ => Real.exp (-c*t)) ν :=
    integrableOn_exp_mul_Ioi (show -c<0 by linarith) 0
  have hs : AEStronglyMeasurable (fun p : ℝ × E => f p.2*(Real.exp (-c*p.1)*m p)) (ν.prod μ) :=
    (hf.aestronglyMeasurable.comp_snd).mul
      (((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
          hm).aestronglyMeasurable)
  have hi : Integrable (fun p : ℝ × E => f p.2*(Real.exp (-c*p.1)*m p)) (ν.prod μ) := by
    apply ((he.mul_prod hf.norm).mul_const C).mono' hs
    exact ae_of_all _ fun p => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc
        ‖f p.2‖*(Real.exp (-c*p.1)*‖m p‖) ≤ ‖f p.2‖*(Real.exp (-c*p.1)*C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC p) (Real.exp_pos _).le)
              (norm_nonneg _)
        _ = (Real.exp (-c*p.1)*‖f p.2‖)*C := by ring
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ fun z => integral_const_mul (f z) _

end
end GinibrePoincare
