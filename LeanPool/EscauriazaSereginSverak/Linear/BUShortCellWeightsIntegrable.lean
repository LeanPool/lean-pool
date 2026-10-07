/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellWeightedIntegral
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortFixedWeight

/-!
# Local integrability of the short-time weights

The three density factors are continuous on the high strip, and their
cell bounds make their products with locally integrable energy
integrable on each cell.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The high strip has strictly positive height and time. -/
theorem bu_short_high_strip_subset_positive
    (scale : ℝ) (hscale : 0 < scale) :
    buShortHighStrip scale ⊆
      {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2} := by
  intro z hz
  have hminus : 0 < buShortYMinus scale := by
    dsimp [buShortYMinus]
    positivity
  exact ⟨hminus.trans_le hz.1,
    (by norm_num : (0 : ℝ) < 1 / 2).trans hz.2.1⟩

/-- Multiplication by a bounded continuous scalar factor preserves
integrability on a measurable cell fragment. -/
theorem bu_short_integrable_mul_bounded_on
    (S : Set ParabolicPoint) (hS : MeasurableSet S)
    (E W : ParabolicPoint → ℝ)
    (hE : IntegrableOn E S volume)
    (hWcont : ContinuousOn W S)
    (C : ℝ) (hWbound : ∀ z ∈ S, ‖W z‖ ≤ C) :
    IntegrableOn (fun z => W z * E z) S volume := by
  have hWas : AEStronglyMeasurable W (volume.restrict S) :=
    hWcont.aestronglyMeasurable hS
  have hWae : ∀ᵐ z ∂(volume.restrict S), ‖W z‖ ≤ C := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact hWbound z hz
  have h := hE.mul_bdd hWas hWae
  change Integrable (fun z => W z * E z) (volume.restrict S)
  convert h using 1
  funext z
  ring

end ESS
