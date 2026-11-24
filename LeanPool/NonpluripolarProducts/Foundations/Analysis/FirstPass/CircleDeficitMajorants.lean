/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.CircleSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicLimits

/-!
# Passing continuous circle majorants to an extended-real submean inequality

For a continuous real boundary majorant, the nonnegative extended-real
circle deficit is exactly the finite deficit of its ordinary circle average.
Consequently a decreasing sequence of such majorants passes its ordinary
center inequalities to an extended-real target, including at negative
infinity.  This is the order-and-integration assembly used after harmonic
approximation in the local-to-global PSH theorem.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- The deficit of a real-valued circle function is the circumference times
the finite deficit of its ordinary circle average. -/
theorem circleDeficit_coe_eq_mul_finiteDeficit_circleAverage
    {g : ℂ → ℝ} (c : ℂ) {R C : ℝ}
    (hg : Continuous g)
    (hC : ∀ z ∈ sphere c |R|, g z ≤ C) :
    circleDeficit (fun z => (g z : EReal)) c 1 R C =
      ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - ((Real.circleAverage g c R : ℝ) : EReal)).toENNReal := by
  have hparam : Continuous (fun t : ℝ => g (c + circleMap 0 R t • (1 : ℂ))) := by
    fun_prop
  have hC' : ∀ t : ℝ, g (c + circleMap 0 R t • (1 : ℂ)) ≤ C := by
    intro t
    simpa [circleMap] using hC (circleMap c R t) (circleMap_mem_sphere' c R t)
  rw [circleDeficit_coe_eq c 1 R C (hparam.intervalIntegrable _ _) hC']
  have hmap : (fun t : ℝ => g (c + circleMap 0 R t • (1 : ℂ))) =
      fun t : ℝ => g (circleMap c R t) := by
    funext t
    congr 1
    simp only [circleMap, zero_add, smul_eq_mul, mul_one]
  rw [← EReal.coe_sub, EReal.real_coe_toENNReal,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
  congr 1
  rw [hmap]
  rw [Real.circleAverage]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- If an extended-real center is below the ordinary average of a continuous
real circle majorant, that majorant's boundary deficit is controlled by the
center deficit of the extended-real function. -/
theorem circleDeficit_coe_le_of_le_circleAverage
    {g : ℂ → ℝ} (c : ℂ) {R C : ℝ} (w : EReal)
    (hg : Continuous g)
    (hC : ∀ z ∈ sphere c |R|, g z ≤ C)
    (hw : w ≤ ((Real.circleAverage g c R : ℝ) : EReal)) :
    circleDeficit (fun z => (g z : EReal)) c 1 R C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - w).toENNReal := by
  rw [circleDeficit_coe_eq_mul_finiteDeficit_circleAverage c hg hC]
  gcongr
  exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hw)

/-- A decreasing family of continuous real majorants on one parametrized
circle transfers its ordinary center-average inequalities to the exact
extended-real deficit inequality of the target. -/
theorem circleSubmean_of_continuous_antitone_majorants
    {w : ℂ → EReal} (c : ℂ) {R C : ℝ} (g : ℕ → ℂ → ℝ)
    (hg : ∀ n, Continuous (g n))
    (hC : ∀ n, ∀ z ∈ sphere c |R|, g n z ≤ C)
    (hanti : ∀ t : ℝ, Antitone fun n =>
      (g n (c + circleMap 0 R t) : EReal))
    (hinf : ∀ t : ℝ, (⨅ n, (g n (c + circleMap 0 R t) : EReal)) =
      w (c + circleMap 0 R t))
    (hcenter : ∀ n, w c ≤ ((Real.circleAverage (g n) c R : ℝ) : EReal)) :
    circleDeficit w c 1 R C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - w c).toENNReal := by
  let u : ℕ → ℂ → EReal := fun n z => (g n z : EReal)
  have hm : ∀ n, Measurable fun t : ℝ =>
      ((C : EReal) - u n (c + circleMap 0 R t • (1 : ℂ))).toENNReal := by
    intro n
    exact (continuous_finiteDeficit C).measurable.comp
      (continuous_coe_real_ereal.comp (by fun_prop)).measurable
  have hanti' : ∀ t : ℝ, Antitone fun n =>
      u n (c + circleMap 0 R t • (1 : ℂ)) := by
    simpa [u] using hanti
  have hdef : circleDeficit w c 1 R C =
      ⨆ n, circleDeficit (u n) c 1 R C := by
    rw [← circleDeficit_iInf_of_antitone_of_measurable c 1 C hm hanti']
    unfold circleDeficit
    apply lintegral_congr
    intro t
    simp only [u, smul_eq_mul, mul_one]
    rw [hinf t]
  rw [hdef]
  apply iSup_le
  intro n
  exact circleDeficit_coe_le_of_le_circleAverage c (w c) (hg n) (hC n)
    (hcenter n)

end

end SGPT.Foundations.Analysis.FirstPass
