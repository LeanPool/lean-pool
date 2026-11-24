/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallSubmean

/-!
# Integrating singular disc submeans against nonnegative weights

The extended nonnegative deficit retains the value `∞` at a pole. Tonelli's
theorem therefore applies before any almost-everywhere finite representative
is chosen. The weight may itself be unbounded or take the value `∞`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A disc submean inequality remains valid after integration against any
measurable nonnegative weight whose translated discs stay in the bounded set,
provided the localized deficit is measurable. No upper semicontinuity, local
integrability or almost-everywhere finiteness of `u` is assumed. -/
theorem HasDiscSubmeanOn.weighted_circle_deficit_le {u : E → EReal} {U K : Set E}
    (hu : HasDiscSubmeanOn u U) (μ : Measure E) [SFinite μ]
    (hKU : K ⊆ U) (C : ℝ)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    (hDm : Measurable (K.indicator (fun y => ((C : EReal) - u y).toENNReal)))
    {w : E → ℝ≥0∞} (hw : Measurable w) (v : E) {r : ℝ} (hr : 0 < r)
    (hdisc : ∀ x ∈ Function.support w, affineClosedDisc x v r ⊆ K) :
    ∫⁻ t in Ioc 0 (2 * Real.pi),
        ∫⁻ x, w x * K.indicator (fun y => ((C : EReal) - u y).toENNReal)
          (x + circleMap 0 r t • v) ∂μ ≤
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ x, w x * K.indicator (fun y => ((C : EReal) - u y).toENNReal) x ∂μ := by
  classical
  let D : E → ℝ≥0∞ := K.indicator (fun y => ((C : EReal) - u y).toENNReal)
  have hD : Measurable D := hDm
  have hc : Continuous (fun p : E × ℝ => p.1 + circleMap 0 r p.2 • v) := by
    fun_prop
  have hm : Measurable (fun p : E × ℝ => w p.1 * D (p.1 + circleMap 0 r p.2 • v)) :=
    (hw.comp measurable_fst).mul (hD.comp hc.measurable)
  have hswap := lintegral_lintegral_swap (μ := μ)
    (ν := volume.restrict (Ioc 0 (2 * Real.pi)))
    (f := fun x t => w x * D (x + circleMap 0 r t • v)) hm.aemeasurable
  have hpoint (x : E) :
      ∫⁻ t in Ioc 0 (2 * Real.pi), w x * D (x + circleMap 0 r t • v) ≤
        ENNReal.ofReal (2 * Real.pi) * (w x * D x) := by
    by_cases hx : w x = 0
    · simp [hx]
    have hdiscK := hdisc x hx
    have hxK : x ∈ K := hdiscK (center_mem_affineClosedDisc x v hr.le)
    have htK (t : ℝ) : x + circleMap 0 r t • v ∈ K :=
      hdiscK (circle_mem_affineClosedDisc x v hr.le t)
    have hmangle : Measurable (fun t : ℝ => D (x + circleMap 0 r t • v)) :=
      hD.comp (by fun_prop : Continuous (fun t : ℝ => x + circleMap 0 r t • v)).measurable
    rw [lintegral_const_mul (w x) hmangle]
    have hangle : (∫⁻ t in Ioc 0 (2 * Real.pi), D (x + circleMap 0 r t • v)) =
        circleDeficit u x v r C := by
      apply lintegral_congr
      intro t
      simp [D, htK t]
    rw [hangle]
    have hs : w x * circleDeficit u x v r C ≤
        w x * (ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u x).toENNReal) := by
      gcongr
      exact hu x v r hr (hdiscK.trans hKU) C (fun y hy => hC y (hdiscK hy))
    simpa [D, hxK, mul_assoc, mul_comm, mul_left_comm] using hs
  change (∫⁻ t in Ioc 0 (2 * Real.pi),
      ∫⁻ x, w x * D (x + circleMap 0 r t • v) ∂μ) ≤
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ x, w x * D x ∂μ
  rw [← hswap]
  exact (lintegral_mono hpoint).trans_eq
    (lintegral_const_mul (ENNReal.ofReal (2 * Real.pi)) (hw.mul hD))

/-- A disc submean inequality remains valid after integration against any
measurable nonnegative weight whose translated discs stay in the bounded set.
No local integrability or almost-everywhere finiteness of `u` is assumed. -/
theorem DiscPshOn.weighted_circle_deficit_le {u : E → EReal} {U K : Set E}
    (hu : DiscPshOn u U) (μ : Measure E) [SFinite μ]
    (hK : MeasurableSet K) (hKU : K ⊆ U) (C : ℝ)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    {w : E → ℝ≥0∞} (hw : Measurable w) (v : E) {r : ℝ} (hr : 0 < r)
    (hdisc : ∀ x ∈ Function.support w, affineClosedDisc x v r ⊆ K) :
    ∫⁻ t in Ioc 0 (2 * Real.pi),
        ∫⁻ x, w x * K.indicator (fun y => ((C : EReal) - u y).toENNReal)
          (x + circleMap 0 r t • v) ∂μ ≤
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ x, w x * K.indicator (fun y => ((C : EReal) - u y).toENNReal) x ∂μ :=
  hu.submean.weighted_circle_deficit_le μ hKU C hC
    (hu.measurable_indicator_deficit hK hKU C) hw v hr hdisc

end SGPT.Foundations.Analysis
