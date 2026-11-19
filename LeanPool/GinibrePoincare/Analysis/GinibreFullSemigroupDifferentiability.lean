/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupDifferentiability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupInfinitesimal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Full positive-time differentiation on the genuine resolvent domain -/

@[expose] public section
open Filter MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A two-sided secant equals a positive difference quotient transported to
 the earlier time. -/
theorem resolventCfcOrbit_slope_range (R : H →L[ℂ] H)
    (x : H) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    slope (resolventCfcOrbit R (R x)) t s =
      resolventCfcEvolution R (Real.toNNReal (min s t))
        (resolventCfcDifferenceQuotient R |s - t| x) := by
  rcases le_total t s with hts | hst
  · have hd : 0 ≤ s - t := sub_nonneg.mpr hts
    have htime : Real.toNNReal s = Real.toNNReal t + Real.toNNReal (s - t) := by
      rw [← Real.toNNReal_add ht hd]
      congr 1
      ring
    rw [abs_of_nonneg hd, min_eq_right hts, slope_def_module,
      resolventCfcOrbit, resolventCfcOrbit, htime, resolventCfcEvolution_add]
    simp only [mul_apply_eq_comp, resolventCfcDifferenceQuotient, smul_apply,
      sub_apply, one_apply_eq_self]
    rw [← map_sub]
    exact ((resolventCfcEvolution R (Real.toNNReal t)).restrictScalars ℝ).map_smul _ _ |>.symm
  · have hd : 0 ≤ t - s := sub_nonneg.mpr hst
    have htime : Real.toNNReal t = Real.toNNReal s + Real.toNNReal (t - s) := by
      rw [← Real.toNNReal_add hs hd]
      congr 1
      ring
    rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub, min_eq_left hst, slope_def_module,
      resolventCfcOrbit, resolventCfcOrbit, htime, resolventCfcEvolution_add]
    simp only [mul_apply_eq_comp, resolventCfcDifferenceQuotient, smul_apply,
      sub_apply, one_apply_eq_self]
    rw [show s - t = -(t - s) by ring, inv_neg, neg_smul,
      show resolventCfcEvolution R (Real.toNNReal s) (R x) -
        resolventCfcEvolution R (Real.toNNReal s) (resolventCfcEvolution R (Real.toNNReal (t - s))
            (R x)) =
        -(resolventCfcEvolution R (Real.toNNReal s) (resolventCfcEvolution R (Real.toNNReal (t - s))
            (R x)) -
          resolventCfcEvolution R (Real.toNNReal s) (R x)) by abel,
      smul_neg, neg_neg, ← map_sub]
    exact ((resolventCfcEvolution R (Real.toNNReal s)).restrictScalars ℝ).map_smul _ _ |>.symm

/-- Two-sided positive-time differentiability on the entire resolvent domain. -/
theorem resolventCfcOrbit_hasDerivAt_range (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (x : H) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (resolventCfcOrbit R (R x))
      (resolventCfcEvolution R (Real.toNNReal t) (R x - x)) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  let l := 𝓝[≠] t
  have habs : Tendsto (fun s : ℝ => |s - t|) l (𝓝[Set.Ioi 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun s : ℝ => |s - t|) t := by fun_prop
      simpa only [sub_self, abs_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact abs_pos.mpr (sub_ne_zero.mpr hs)
  have hquot := (resolventCfcDifferenceQuotient_tendsto R hR hSpec hDense x).comp habs
  have htime : Tendsto (fun s : ℝ => Real.toNNReal (min s t)) l (𝓝 (Real.toNNReal t)) := by
    have hc : ContinuousAt (fun s : ℝ => Real.toNNReal (min s t)) t := by fun_prop
    simpa only [min_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he := resolventCfcEvolution_tendsto_apply R hR hSpec hDense _ _ _ _ htime hquot
  have hv : (R - 1) x = R x - x := by simp only [sub_apply, one_apply_eq_self]
  rw [hv] at he
  apply he.congr'
  have hpos : ∀ᶠ s : ℝ in l, 0 < s :=
    (eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos] with s hs
  exact (resolventCfcOrbit_slope_range R x ht.le hs.le).symm

/-- The full generator acts as the derivative at every positive time. -/
theorem resolventGenerator_orbit_hasDerivAt (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (u v : H) (hp : (u, v) ∈ (resolventGenerator R hInj).graph)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (resolventCfcOrbit R u) (resolventCfcOrbit R v t) t := by
  rw [resolventGenerator_graph R hInj] at hp
  change R (u - v) = u at hp
  have hd := resolventCfcOrbit_hasDerivAt_range R hR hSpec hDense (u - v) ht
  rw [hp] at hd
  convert hd using 1
  congr 1
  abel

/-- The actual generator-domain orbit satisfies the integrated diffusion equation. -/
theorem resolventGenerator_orbit_integral (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (u v : H) (hp : (u, v) ∈ (resolventGenerator R hInj).graph)
    {t : ℝ} (ht : 0 ≤ t) :
    resolventCfcOrbit R u t = u + ∫ s in (0 : ℝ)..t, resolventCfcOrbit R v s := by
  have hcont := resolventCfcOrbit_continuous R hR hSpec hDense u
  have hvcont := resolventCfcOrbit_continuous R hR hSpec hDense v
  have hint : IntervalIntegrable (resolventCfcOrbit R v) volume (0 : ℝ) t :=
    hvcont.intervalIntegrable (0 : ℝ) t
  have hder : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (resolventCfcOrbit R u) (resolventCfcOrbit R v s) s := by
    intro s hs
    exact resolventGenerator_orbit_hasDerivAt R hR hInj hSpec hDense u v hp hs.1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont.continuousOn hder hint
  have hz : resolventCfcOrbit R u 0 = u := by
    simp only [resolventCfcOrbit, Real.toNNReal_zero, resolventCfcEvolution_zero R hR,
      one_apply_eq_self]
  rw [hz] at he
  rw [he]
  abel

end
end GinibrePoincare
