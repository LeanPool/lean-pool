/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellFactor
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedCellFactor

/-!
# Integrating a bounded cell weight

A nonnegative weight bounded on a cell multiplies its quadratic energy
by at most the same cell constant.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A bounded nonnegative weight on a measurable part of a cell is
controlled by the full cell energy integral (`lem:bu-small-time`). -/
theorem bu_short_weighted_energy_cell_le
    (Cell S : Set ParabolicPoint)
    (hCell : MeasurableSet Cell) (hS : MeasurableSet S)
    (E W : ParabolicPoint → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hEInt : IntegrableOn E Cell volume)
    (hEWInt : IntegrableOn (fun z => W z * E z) (Cell ∩ S) volume)
    (hE0 : ∀ z, 0 ≤ E z)
    (hW : ∀ z ∈ Cell ∩ S, 0 ≤ W z ∧ W z ≤ C) :
    (∫ z in Cell ∩ S, W z * E z ∂(volume : Measure ParabolicPoint)) ≤
      C * (∫ z in Cell, E z ∂(volume : Measure ParabolicPoint)) := by
  have hSub : Cell ∩ S ⊆ Cell := inter_subset_left
  have hEIntSub := hEInt.mono_set hSub
  have hCEInt := hEIntSub.const_mul C
  have hpoint : ∀ᵐ z ∂(volume.restrict (Cell ∩ S)),
      W z * E z ≤ C * E z := by
    have hCS : MeasurableSet (Cell ∩ S) := hCell.inter hS
    filter_upwards [ae_restrict_mem hCS] with z hz
    exact mul_le_mul_of_nonneg_right (hW z hz).2 (hE0 z)
  have hfirst := integral_mono_ae hEWInt hCEInt hpoint
  rw [integral_const_mul] at hfirst
  have hsecond : (∫ z in Cell ∩ S, E z ∂volume) ≤
      ∫ z in Cell, E z ∂volume := by
    apply setIntegral_mono_set hEInt
    · filter_upwards [] with z
      exact hE0 z
    · exact ae_of_all _ hSub
  exact hfirst.trans (mul_le_mul_of_nonneg_left hsecond hC)

end ESS
