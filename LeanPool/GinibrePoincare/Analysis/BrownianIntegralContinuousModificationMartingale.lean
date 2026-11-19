/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralContinuousModificationMartingale.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationMartingaleIdentification

/-!
# Brownian integral continuous modification martingale

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `realMartingale_terminal_cauchy_exists_continuous_martingale`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- A genuine continuous martingale limit of a terminal-mean-square Cauchy
sequence, in an actual null-completed filtration. The pathwise construction,
L² identification, adaptation, and martingale identity are all derived. -/
theorem realMartingale_terminal_cauchy_exists_continuous_martingale
    {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] [P.IsComplete]
    (ℱ : Filtration ℝ≥0 mAmbient) (base : ℝ≥0 → MeasurableSpace Ω)
    (hbase : ∀ t, base t ≤ mAmbient)
    (haug : ∀ t, ℱ t = ginibreNullAugmentation P (base t))
    (F : ℕ → ℝ≥0 → Ω → ℝ) (hF : ∀ n, Martingale (F n) ℱ P)
    (T : ℝ≥0) (hT : ∀ n, MemLp (F n T) 2 P)
    (hc : ∀ n, ∀ᵐ ω ∂P, ContinuousOn (fun t => F n t ω) (Set.Icc 0 T))
    (hcap : ∀ n t ω, F n t ω = F n (min t T) ω)
    (hterm : Tendsto (fun q : ℕ × ℕ =>
      ∫ ω, (F q.2 T ω-F q.1 T ω)^2 ∂P) atTop (𝓝 0)) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      Martingale M ℱ P ∧ (∀ ω, Continuous (fun t => M t ω)) ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ t, TendstoInMeasure P (fun n => F n t) atTop (M t)) ∧
      ∀ t, Tendsto (fun n => ∫ ω, (F n t ω-M t ω)^2 ∂P) atTop (𝓝 0) := by
  obtain ⟨s, hs, L, hL⟩ := realMartingale_terminal_cauchy_exists_continuous_limit
    P ℱ F hF T hT hc hterm
  let tcap : ℝ≥0 → Set.Icc 0 T := fun t => ⟨min t T, bot_le, min_le_right _ _⟩
  let M : ℝ≥0 → Ω → ℝ := fun t ω => L ω (tcap t)
  have htcap : Continuous tcap := by
    exact Continuous.subtype_mk (continuous_id.min continuous_const) _
  have hsL2 : ∀ n t, MemLp (F n t) 2 P := by
    intro n t
    have hh := realMartingale_memLp_two_of_le P ℱ (F n) (hF n) T (min t T)
      (min_le_right _ _) (hT n)
    convert hh using 1
    funext ω
    exact hcap n t ω
  have hct : ∀ t, Tendsto (fun q : ℕ × ℕ =>
      ∫ ω, (F q.1 t ω-F q.2 t ω)^2 ∂P) atTop (𝓝 0) := by
    intro t
    have ht : Tendsto (fun q : ℕ × ℕ =>
        ∫ ω, (F q.1 T ω-F q.2 T ω)^2 ∂P) atTop (𝓝 0) := by
      convert hterm using 1
      ext q
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by ring)
    apply squeeze_zero (fun q => integral_nonneg (fun ω => sq_nonneg _)) _ ht
    intro q
    have hh := realMartingale_difference_secondMoment_le_terminal P ℱ
      (F q.1) (F q.2) (hF q.1) (hF q.2) T (min t T) (min_le_right _ _)
      (hT q.1) (hT q.2)
    simpa only [←hcap] using hh
  have hi : ∀ t, ∃ I : Lp ℝ 2 P,
      Tendsto (fun n => (hsL2 n t).toLp (F n t)) atTop (𝓝 I) :=
    fun t => actualMeanSquareCauchy_exists_L2_limit P _ (fun n => hsL2 n t) (hct t)
  choose I hI using hi
  have hMI : ∀ t, M t =ᵐ[P] (fun ω => I t ω) := by
    intro t
    apply actualL2Limit_eq_pathwise_subsequence_ae P (fun n => F n t)
      (fun n => hsL2 n t) (I t) (hI t) s hs (M t)
    filter_upwards [hL] with ω hω
    have hh := hω.tendsto_at (tcap t)
    simpa only [M, tcap,←hcap] using hh
  have hm : ∀ t, MemLp (M t) 2 P := fun t =>
    (memLp_congr_ae (hMI t)).mpr (Lp.memLp (I t))
  have hmeas : StronglyAdapted ℱ M := by
    intro t
    have hIpast := actualL2Limit_nullAugmentation_measurable P (base t) (hbase t)
      (fun n => F n t) (fun n => hsL2 n t)
      (fun n => by
        have hn := ((hF n).1 t).measurable
        rw [haug t] at hn
        exact hn) (I t) (hI t)
    have hmpast := ginibreNullAugmentation_measurable_congr P (base t)
      (M t) (fun ω => I t ω) hIpast (hMI t)
    rw [←haug t] at hmpast
    exact hmpast.stronglyMeasurable
  have hto : ∀ t, (hm t).toLp (M t) = I t := by
    intro t
    apply Lp.ext
    exact (hm t).coeFn_toLp.trans (hMI t)
  have hlim : ∀ t, Tendsto (fun n => (hsL2 n t).toLp (F n t)) atTop
      (𝓝 ((hm t).toLp (M t))) := by
    intro t
    rw [hto t]
    exact hI t
  refine ⟨M, realMartingale_of_actual_L2_limits P ℱ F hF hsL2 M hmeas hm hlim,
    (fun ω => (L ω).continuous.comp htcap), hm,?_,?_⟩
  · intro t
    exact (tendstoInMeasure_of_tendsto_Lp (hlim t)).congr
      (fun n => (hsL2 n t).coeFn_toLp) ((hm t).coeFn_toLp)
  · intro t
    have he (n : ℕ) : (∫ ω, (F n t ω-M t ω)^2 ∂P) =
        ‖(hsL2 n t).toLp (F n t)-(hm t).toLp (M t)‖^2 := by
      rw [←integral_square_eq_L2_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((hsL2 n t).toLp (F n t)) ((hm t).toLp (M t)),
        (hsL2 n t).coeFn_toLp, (hm t).coeFn_toLp] with ω hsub hFω hMω
      simp only [hsub, Pi.sub_apply, hFω, hMω]
    have hn := ((hlim t).sub (tendsto_const_nhds (x := (hm t).toLp (M t)))).norm.pow 2
    simpa only [←he, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hn

end
end GinibrePoincare
