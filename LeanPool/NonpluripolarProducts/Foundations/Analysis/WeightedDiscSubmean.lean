/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.WeightedCircleKernel

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

/-- The mean deficit bound on one disc whose whole image lies in the localization set. -/
theorem HasDiscSubmeanOn.circle_deficit_le_on_admissible_disc {u : E → EReal} {U K : Set E}
    (hu : HasDiscSubmeanOn u U) (hKU : K ⊆ U) (C : ℝ)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal)) (x v : E) {r : ℝ} (hr : 0 < r)
    (hdisc : affineClosedDisc x v r ⊆ K) :
    (∫⁻ t in Ioc 0 (2 * Real.pi), K.indicator (fun y => ((C : EReal) - u y).toENNReal)
      (x + circleMap 0 r t • v)) ≤ ENNReal.ofReal (2 * Real.pi) *
      K.indicator (fun y => ((C : EReal) - u y).toENNReal) x := by
  classical
  have hxK : x ∈ K := hdisc (center_mem_affineClosedDisc x v hr.le)
  have hangle : (∫⁻ t in Ioc 0 (2 * Real.pi),
      K.indicator (fun y => ((C : EReal) - u y).toENNReal)
        (x + circleMap 0 r t • v)) = circleDeficit u x v r C := by
    apply lintegral_congr
    intro t
    simp [hdisc (circle_mem_affineClosedDisc x v hr.le t)]
  rw [hangle, indicator_of_mem hxK]
  exact hu x v r hr (hdisc.trans hKU) C (fun y hy => hC y (hdisc hy))

variable [MeasurableSpace E] [BorelSpace E]

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
  exact weighted_circle_lintegral_le_of_pointwise μ hDm hw v r
    (fun x hx => hu.circle_deficit_le_on_admissible_disc hKU C hC x v hr (hdisc x hx))

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
