/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionWeightedLaplace.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionLaplaceCore

/-!
# Ginibre stochastic transition weighted Laplace

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_core_transition_weighted_laplace_identity`.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem boundedDuhamel_weighted_laplace_core (a b : ℝ → ℝ) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (ha : Continuous a) (hb : Continuous b) (A B : ℝ)
    (hA : ∀ t ≥ 0, ‖a t‖ ≤ A) (hB : ∀ t ≥ 0, ‖b t‖ ≤ B)
    (hEq : ∀ t ≥ 0, a t = a 0 + ∫ s in (0 : ℝ)..t, b s) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-ℓ*t)*(ℓ*a t-b t)=a 0 := by
  let d := fun t => Real.exp (-ℓ*t)*(b t-ℓ*a t)
  have heint : IntegrableOn (fun t : ℝ => Real.exp (-ℓ*t)) (Ioi 0) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := ℓ) hℓ
  have hdint : IntegrableOn d (Ioi 0) := by
    apply (heint.const_mul (B+ℓ*A)).mono' ((Real.continuous_exp.comp (continuous_const.mul
        continuous_id)).mul (hb.sub (continuous_const.mul ha))).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖Real.exp (-ℓ*t)*(b t-ℓ*a t)‖≤(B+ℓ*A)*Real.exp (-ℓ*t)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-ℓ*t)*‖b t-ℓ*a t‖≤Real.exp (-ℓ*t)*(‖b t‖+ℓ*‖a t‖) :=
        mul_le_mul_of_nonneg_left (by simpa [norm_mul, Real.norm_eq_abs, abs_of_pos hℓ] using
                                        norm_sub_le (b t) (ℓ*a t)) (Real.exp_pos _).le
      _≤Real.exp (-ℓ*t)*(B+ℓ*A) := mul_le_mul_of_nonneg_left (add_le_add (hB t ht.le)
          (mul_le_mul_of_nonneg_left (hA t ht.le) hℓ.le)) (Real.exp_pos _).le
      _=(B+ℓ*A)*Real.exp (-ℓ*t) := mul_comm _ _
  have hderiv (t : ℝ) (ht : t∈Ioi (0 : ℝ)) :
      HasDerivAt (fun s => Real.exp (-ℓ*s)*a s) (d t) t := by
    have hda : HasDerivAt a (b t) t := by
      have hp := (intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 t)
        hb.aestronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt).const_add (a 0)
      apply hp.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds (show (0 : ℝ)<t from ht)] with s hs
      exact hEq s hs.le
    change HasDerivAt (fun s => Real.exp (-ℓ*s)*a s) (Real.exp (-ℓ*t)*(b t-ℓ*a t)) t
    have hExp : HasDerivAt (fun s : ℝ => Real.exp (-ℓ*s)) (-ℓ*Real.exp (-ℓ*t)) t := by
      exact (((hasDerivAt_id t).const_mul (-ℓ)).exp).congr_deriv (by simp only [id_eq]; ring)
    exact (hExp.mul hda).congr_deriv (by ring)
  have hDecay : Tendsto (fun t : ℝ => Real.exp (-ℓ*t)*a t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t => Real.exp (-ℓ*t)*A)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hA t ht) (Real.exp_pos _).le
    · simpa only [zero_mul, Function.comp_apply, id_eq] using
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos
            hℓ))).mul_const A
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul ha).continuousWithinAt)
    hderiv hdint hDecay
  have hNeg : (fun t => Real.exp (-ℓ*t)*(ℓ*a t-b t))=fun t => -d t := by funext t; dsimp [d]; ring
  rw [hNeg, integral_neg, hFTC]
  simp

theorem ginibreBrownian_core_transition_weighted_laplace_identity {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-ℓ*t)*
      (ℓ*(∫ ω, f (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P)-
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
  exact (boundedDuhamel_weighted_laplace_core a b ℓ hℓ ha hb C D hAm hBm he).trans hA0

end
end GinibrePoincare
