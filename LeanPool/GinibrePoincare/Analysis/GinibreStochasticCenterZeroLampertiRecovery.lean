/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroLampertiRecovery.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiScalarFunctional

/-! A measurable center-only recovery functional uses positive-start Lamperti
increments. Its limit avoids making any integrability assertion at time zero. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The positive restart time `1 / (k + 1)`. -/
def ginibreCenterPositiveStart (k : ℕ) : ℝ≥0 := 1/(k+1)

/-- The `m + 1`-point uniform Riemann sum, over `[1 / (k + 1), t]`, of the center Lamperti
drift along the complex path `p`. -/
def ginibreCenterPositiveStartDriftSum (n : ℕ) (α : ℝ) (k m : ℕ)
    (p : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ :=
  ∑ i : Fin (m+1), ginibreLampertiCenterDrift n α
    (Complex.normSq (p (ginibreCenterPositiveStart k+
      ginibreUniformBrownianTime (t-ginibreCenterPositiveStart k) m i)))*
        ((t-ginibreCenterPositiveStart k : ℝ≥0) : ℝ)/((m : ℝ)+1)

/-- The center Lamperti functional started at time `1 / (k + 1)`: the increment of `|p|`
minus the limit of the drift Riemann sums, divided by `√(2α/n)`. -/
def ginibreCenterPositiveStartLamperti (n : ℕ) (α : ℝ) (k : ℕ)
    (p : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ :=
  (Real.sqrt (Complex.normSq (p t))-Real.sqrt (Complex.normSq (p (ginibreCenterPositiveStart k)))-
    limUnder atTop (fun m => ginibreCenterPositiveStartDriftSum n α k m p t))/
      Real.sqrt (2*α/(n : ℝ))

/-- The limit as `k → ∞` of the positive-start Lamperti functionals, set to `0` at `t = 0`. -/
def ginibreCenterPuncturedLampertiRecovery (n : ℕ) (α : ℝ)
    (p : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ :=
  if t=0 then 0 else limUnder atTop (fun k => ginibreCenterPositiveStartLamperti n α k p t)

theorem ginibreCenterPositiveStartDriftSum_measurable (n : ℕ) (α : ℝ) (k m : ℕ) (t : ℝ≥0) :
    Measurable (fun p => ginibreCenterPositiveStartDriftSum n α k m p t) := by
  apply Finset.measurable_sum
  intro i hi
  exact (((ginibreLampertiCenterDrift_measurable n α).comp
    (Complex.continuous_normSq.measurable.comp (measurable_pi_apply _))).mul_const _).div_const _

theorem ginibreCenterPositiveStartLamperti_measurable (n : ℕ) (α : ℝ) (k : ℕ) (t : ℝ≥0) :
    Measurable (fun p => ginibreCenterPositiveStartLamperti n α k p t) := by
  have hm : Measurable (fun p => limUnder atTop (fun m =>
      ginibreCenterPositiveStartDriftSum n α k m p t)) :=
    (StronglyMeasurable.limUnder (fun m =>
      (ginibreCenterPositiveStartDriftSum_measurable n α k m t).stronglyMeasurable)).measurable
  exact (((Real.continuous_sqrt.measurable.comp
    (Complex.continuous_normSq.measurable.comp (measurable_pi_apply t))).sub
      (Real.continuous_sqrt.measurable.comp
        (Complex.continuous_normSq.measurable.comp (measurable_pi_apply (ginibreCenterPositiveStart
            k))))).sub hm).div_const _

theorem ginibreCenterPuncturedLampertiRecovery_measurable (n : ℕ) (α : ℝ) :
    Measurable (ginibreCenterPuncturedLampertiRecovery n α) := by
  apply Measurable.of_eval
  intro t
  by_cases ht : t=0
  · simp only [ginibreCenterPuncturedLampertiRecovery, ht, ite_true]
    exact measurable_const
  · simp only [ginibreCenterPuncturedLampertiRecovery, ht, ite_false]
    exact (StronglyMeasurable.limUnder (fun k =>
      (ginibreCenterPositiveStartLamperti_measurable n α k t).stronglyMeasurable)).measurable

theorem ginibreCenterPositiveStartLamperti_eq_integral (n : ℕ) (α : ℝ) (k : ℕ)
    (p : ℝ≥0 → ℂ) (hp : Continuous p)
    (hpos : ∀ s : ℝ≥0, 0 < s → 0 < Complex.normSq (p s)) (t : ℝ≥0) :
    ginibreCenterPositiveStartLamperti n α k p t =
      (Real.sqrt (Complex.normSq (p t))-Real.sqrt (Complex.normSq (p (ginibreCenterPositiveStart
          k)))-
        ∫ r in (0 : ℝ)..((t-ginibreCenterPositiveStart k : ℝ≥0) : ℝ),
          ginibreLampertiCenterDrift n α
            (Complex.normSq (p (ginibreCenterPositiveStart k+r.toNNReal))))/
        Real.sqrt (2*α/(n : ℝ)) := by
  let w := fun r : ℝ => ginibreLampertiCenterDrift n α
    (Complex.normSq (p (ginibreCenterPositiveStart k+r.toNNReal)))
  have hw : Continuous w := (ginibreLampertiCenterDrift_continuousOn n α).comp_continuous
    (Complex.continuous_normSq.comp (hp.comp (continuous_const.add continuous_real_toNNReal)))
    (fun r => hpos _ (add_pos_of_pos_of_nonneg (by dsimp [ginibreCenterPositiveStart]; positivity)
        (bot_le : 0 ≤ r.toNNReal)))
  have hl := itoContinuousScalarRiemann_fin_tendsto w (t-ginibreCenterPositiveStart k)
      hw.continuousOn
  have he : (fun m => ginibreCenterPositiveStartDriftSum n α k m p t) =
      (fun m => ∑ i : Fin (m+1), w (ginibreUniformBrownianTime (t-ginibreCenterPositiveStart k) m i
          : ℝ)*
        (((t-ginibreCenterPositiveStart k : ℝ≥0) : ℝ)/((m : ℝ)+1))) := by
    funext m
    apply Finset.sum_congr rfl
    intro i hi
    simp only [w, Real.toNNReal_coe]
    rw [mul_div_assoc]
  rw [← he] at hl
  unfold ginibreCenterPositiveStartLamperti
  rw [hl.limUnder_eq]

theorem ginibreCenterPositiveStart_tendsto_zero :
    Tendsto ginibreCenterPositiveStart atTop (𝓝 0) := by
  rw [← NNReal.tendsto_coe]
  simpa [ginibreCenterPositiveStart] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- Continuous zero-start drivers are recovered from the actual positive-start
increment identities; no ordinary drift integral through zero is assumed. -/
theorem ginibreCenterPuncturedLampertiRecovery_eq (n : ℕ) (α : ℝ)
    (p : ℝ≥0 → ℂ) (β : ℝ≥0 → ℝ) (hβ : Continuous β) (hβ0 : β 0 = 0)
    (hinc : ∀ k t, ginibreCenterPositiveStart k ≤ t →
      ginibreCenterPositiveStartLamperti n α k p t = β t - β (ginibreCenterPositiveStart k)) :
    ginibreCenterPuncturedLampertiRecovery n α p = β := by
  funext t
  by_cases ht : t=0
  · simp [ginibreCenterPuncturedLampertiRecovery, ht, hβ0]
  · have htpos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht)
    have hsmall := ginibreCenterPositiveStart_tendsto_zero.eventually (gt_mem_nhds htpos)
    have hlim : Tendsto (fun k => ginibreCenterPositiveStartLamperti n α k p t) atTop (𝓝 (β t)) :=
        by
      have hc : Tendsto (fun _ : ℕ => β t) atTop (𝓝 (β t)) := tendsto_const_nhds
      have hl := hc.sub (hβ.continuousAt.tendsto.comp ginibreCenterPositiveStart_tendsto_zero)
      rw [hβ0, sub_zero] at hl
      apply hl.congr'
      filter_upwards [hsmall] with k hk
      exact (hinc k t hk.le).symm
    simp only [ginibreCenterPuncturedLampertiRecovery, ht, ite_false]
    exact hlim.limUnder_eq

end
end GinibrePoincare
