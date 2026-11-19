/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionLaplaceCore.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionCoreDuhamel
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Ginibre stochastic transition Laplace core

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_core_transition_laplace_identity`.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Scalar analytic reduction for the genuine Dynkin Duhamel equation:
the exponentially weighted transition orbit solves the core resolvent
identity. All integrability follows from the actual bounded orbit values. -/
theorem boundedDuhamel_laplace_core (a b : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) (A B : ℝ)
    (hA : ∀ t ≥ 0, ‖a t‖ ≤ A) (hB : ∀ t ≥ 0, ‖b t‖ ≤ B)
    (hEq : ∀ t ≥ 0, a t = a 0 + ∫ s in (0 : ℝ)..t, b s) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t)*(a t-b t)=a 0 := by
  let d := fun t => Real.exp (-t)*(b t-a t)
  have heint : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1) zero_lt_one
  have hdint : IntegrableOn d (Ioi 0) := by
    apply (heint.const_mul (B+A)).mono' ((Real.continuous_exp.comp continuous_neg).mul (hb.sub
        ha)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖Real.exp (-t)*(b t-a t)‖≤(B+A)*Real.exp (-t)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t)*‖b t-a t‖≤Real.exp (-t)*(‖b t‖+‖a t‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
      _≤Real.exp (-t)*(B+A) := mul_le_mul_of_nonneg_left (add_le_add (hB t ht.le) (hA t ht.le))
          (Real.exp_pos _).le
      _=(B+A)*Real.exp (-t) := mul_comm _ _
  have hderiv (t : ℝ) (ht : t∈Ioi (0 : ℝ)) :
      HasDerivAt (fun s => Real.exp (-s)*a s) (d t) t := by
    have hda : HasDerivAt a (b t) t := by
      have hp := (intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 t)
        hb.aestronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt).const_add (a 0)
      apply hp.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds (show (0 : ℝ)<t from ht)] with s hs
      exact hEq s hs.le
    change HasDerivAt (fun s => Real.exp (-s)*a s) (Real.exp (-t)*(b t-a t)) t
    have hExp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa only [Pi.neg_apply, id_eq, mul_neg, one_mul, mul_one] using ((hasDerivAt_id t).neg.exp)
    exact (hExp.mul hda).congr_deriv (by ring)
  have hDecay : Tendsto (fun t : ℝ => Real.exp (-t)*a t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t => Real.exp (-t)*A)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hA t ht) (Real.exp_pos _).le
    · simpa only [zero_mul, Function.comp_apply] using
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const A
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (((Real.continuous_exp.comp continuous_neg).mul ha).continuousWithinAt)
    hderiv hdint hDecay
  have hNeg : (fun t => Real.exp (-t)*(a t-b t))=fun t => -d t := by funext t; dsimp [d]; ring
  rw [hNeg, integral_neg, hFTC]
  simp

/-- True pointwise compact-core resolvent equation of the actual original
Ginibre Brownian transition expectations, with the unit Laplace parameter. -/
theorem ginibreBrownian_core_transition_laplace_identity {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t)*
      ((∫ ω, f (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P)-
       (∫ ω, ginibreRealPaperSpeedGenerator n α f
         (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P)))=f z := by
  let L := ginibreRealPaperSpeedGenerator n α f
  have hLc : Continuous L := (continuous_ginibrePregenerator_of_core hf).const_mul _
  have hLs : HasCompactSupport L := by
    change HasCompactSupport ((fun _ => (α : ℝ)/(n : ℝ))*ginibrePregenerator n f)
    exact (hasCompactSupport_ginibrePregenerator hf.2.1).mul_left
  obtain ⟨C, hC⟩ := hf.2.1.exists_bound_of_continuous hf.1.continuous
  obtain ⟨D, hD⟩ := hLs.exists_bound_of_continuous hLc
  let a := fun t : ℝ => ∫ ω, f (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P
  let b := fun t : ℝ => ∫ ω, L (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P
  have ha := ginibreBrownian_bounded_continuous_transition_mean_continuous hn α z hz B P hB hind f
      hf.1.continuous C hC
  have hb := ginibreBrownian_bounded_continuous_transition_mean_continuous hn α z hz B P hB hind L
      hLc D hD
  have hAm : ∀ t≥0, ‖a t‖≤C := by
    intro t ht
    simpa [a] using norm_integral_le_of_norm_le_const (μ := P) (ae_of_all P (fun ω => hC _))
  have hBm : ∀ t≥0, ‖b t‖≤D := by
    intro t ht
    simpa [b] using norm_integral_le_of_norm_le_const (μ := P) (ae_of_all P (fun ω => hD _))
  have hA0 : a 0=f z := by
    simpa [a] using ginibreBrownian_core_test_transition_duhamel hn α z hz B P hB hind 0 f hf
  have he : ∀ t≥0, a t=a 0+∫ s in (0 : ℝ)..t, b s := by
    intro t ht
    simpa only [a, b, hA0, Real.coe_toNNReal t ht] using
      ginibreBrownian_core_test_transition_duhamel hn α z hz B P hB hind t.toNNReal f hf
  exact (boundedDuhamel_laplace_core a b ha hb C D hAm hBm he).trans hA0

end
end GinibrePoincare
