/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralInitialCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralInitialIntervalBound
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Continuous adapted approximants for bounded integrands continuous only
at positive times. The initial discrepancy has vanishing stochastic energy. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The integrand `F` multiplied by the smooth cutoff `smoothTransition (t / ε - 1)`, which for
`ε > 0` vanishes on `t ≤ ε` and equals one on `t ≥ 2 * ε`. -/
def brownianInitialTimeCutoff {Ω : Type*} (F : ℝ≥0 → Ω → ℝ) (ε : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := Real.smoothTransition ((t : ℝ)/ε-1)*F t ω

theorem brownianInitialTimeCutoff_zero {Ω : Type*} (F : ℝ≥0 → Ω → ℝ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0) (ω : Ω) (ht : (t : ℝ) ≤ ε) :
    brownianInitialTimeCutoff F ε t ω=0 := by
  unfold brownianInitialTimeCutoff
  rw [Real.smoothTransition.zero_of_nonpos ((div_le_one hε).mpr ht |> sub_nonpos.mpr), zero_mul]

theorem brownianInitialTimeCutoff_eq {Ω : Type*} (F : ℝ≥0 → Ω → ℝ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0) (ω : Ω) (ht : 2 * ε ≤ (t : ℝ)) :
    brownianInitialTimeCutoff F ε t ω=F t ω := by
  unfold brownianInitialTimeCutoff
  have hh : 1 ≤ (t : ℝ)/ε-1 := by
    have h := (le_div_iff₀ hε).mpr ht
    linarith
  rw [Real.smoothTransition.one_of_one_le hh, one_mul]

theorem brownianInitialTimeCutoff_continuous {Ω : Type*} (F : ℝ≥0 → Ω → ℝ)
    {ε : ℝ} (hε : 0 < ε) (ω : Ω)
    (hc : ContinuousOn (fun t => F t ω) (Ioi 0)) :
    Continuous (fun t => brownianInitialTimeCutoff F ε t ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t=0
  · subst t
    have he : (fun t => brownianInitialTimeCutoff F ε t ω) =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [(NNReal.continuous_coe.continuousAt (x := 0)).eventually
        (eventually_lt_nhds hε)] with t ht
      exact brownianInitialTimeCutoff_zero F hε t ω ht.le
    exact continuousAt_const.congr he.symm
  · have hpos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht)
    exact ((Real.smoothTransition.continuous.continuousAt.comp
      ((NNReal.continuous_coe.continuousAt.div_const ε).sub_const 1)).mul
        (hc.continuousAt (isOpen_Ioi.mem_nhds hpos)))

theorem brownianInitialTimeCutoff_difference_bound {Ω : Type*}
    (F : ℝ≥0 → Ω → ℝ) (ε C : ℝ) (hb : ∀ t ω, ‖F t ω‖ ≤ C) (t : ℝ≥0) (ω : Ω) :
    ‖F t ω-brownianInitialTimeCutoff F ε t ω‖ ≤ C := by
  have hlo := Real.smoothTransition.nonneg ((t : ℝ)/ε-1)
  have hhi := Real.smoothTransition.le_one ((t : ℝ)/ε-1)
  rw [brownianInitialTimeCutoff,← one_sub_mul, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hhi)]
  exact (mul_le_mul_of_nonneg_right (show 1-Real.smoothTransition ((t : ℝ)/ε-1) ≤ 1 by linarith)
    (norm_nonneg _)).trans (by simpa using hb t ω)

theorem brownianInitialTimeCutoff_adapted {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℝ) (ε : ℝ) (G : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hF : ∀ t, @Measurable Ω ℝ (G t) _ (F t)) :
    ∀ t, @Measurable Ω ℝ (G t) _ (brownianInitialTimeCutoff F ε t) := by
  intro t
  exact (hF t).const_mul _

theorem brownianInitialTimeCutoff_bound {Ω : Type*}
    (F : ℝ≥0 → Ω → ℝ) (ε C : ℝ) (hb : ∀ t ω, ‖F t ω‖ ≤ C) (t : ℝ≥0) (ω : Ω) :
    ‖brownianInitialTimeCutoff F ε t ω‖ ≤ C := by
  rw [brownianInitialTimeCutoff, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (norm_nonneg _)).trans
    (by simpa using hb t ω)

theorem brownianUniformLeftSum_initial_cutoff_error_bound {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hb : ∀ t ω, ‖F t ω‖ ≤ C)
    (T : ℝ≥0) (hT : 0 < T) (N : ℕ) (hN : 0 < N) :
    (∫ ω, (brownianUniformLeftSum (B j) F T N ω-
      brownianUniformLeftSum (B j) (brownianInitialTimeCutoff F ε) T N ω)^2 ∂P) ≤
      C^2*(2*ε+(T : ℝ)/(N : ℝ)) := by
  have := Fintype.ofFinite ι
  let A := fun t ω => F t ω-brownianInitialTimeCutoff F ε t ω
  have hA (t : ℝ≥0) : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (A t) :=
    (hF t).sub (brownianInitialTimeCutoff_adapted F ε _ hF t)
  have hbound := brownianUniformLeftSum_initial_interval_secondMoment_le B P hB hind j A hA
    C (2*ε) hC (by positivity)
    (fun t ω => brownianInitialTimeCutoff_difference_bound F ε C hb t ω)
    (fun t ω ht => by dsimp only [A]; rw [brownianInitialTimeCutoff_eq F hε t ω ht, sub_self])
    T hT N hN
  have he (ω : Ω) : brownianUniformLeftSum (B j) A T N ω =
      brownianUniformLeftSum (B j) F T N ω-
        brownianUniformLeftSum (B j) (brownianInitialTimeCutoff F ε) T N ω := by
    simp only [brownianUniformLeftSum, A, sub_mul, Finset.sum_sub_distrib]
  simpa only [he] using hbound

end
end GinibrePoincare
