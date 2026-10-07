/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedRealHeatCLM
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedRealHeatStokesLaw
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildIntegral

/-!
# Heat propagation of a real Stokes integral

Heat flow through the finite interval Stokes integral adds its elapsed
time to each Stokes kernel.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Applying real heat flow to a translated Stokes integral adds the
heat elapsed time to its Stokes kernel on the interval. -/
theorem realHeatOperator_shiftedStokesIntegral
    (F : ℝ → RealTensorL2) (hF : Continuous F)
    (C : ℝ) (hFC : ∀ s, ‖F s‖ ≤ C) (hC : 0 ≤ C)
    (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) :
    realHeatOperator q hq
      (∫ τ in (0 : ℝ)..a, mildShiftedStokesIntegrand F a τ) =
      ∫ τ in (0 : ℝ)..a,
        if h : 0 < τ ∧ τ < a then
          realStokesOperator (show 0 < q + τ by
            have hτ : 0 < τ := h.1
            positivity) (F (a - τ))
        else 0 := by
  let H := realHeatOperatorCLM q hq
  have hInt : IntervalIntegrable
      (mildShiftedStokesIntegrand F a) volume 0 a :=
    mildShiftedStokesIntegrand_intervalIntegrable F hF C hFC hC a a ha
  rw [← realHeatOperatorCLM_apply]
  calc
    H (∫ τ in (0 : ℝ)..a, mildShiftedStokesIntegrand F a τ) =
      ∫ τ in (0 : ℝ)..a, H (mildShiftedStokesIntegrand F a τ) :=
        (H.intervalIntegral_comp_comm hInt).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro τ _
      by_cases h : 0 < τ ∧ τ < a
      · simp only [mildShiftedStokesIntegrand, dite_eq_left h]
        rw [realHeatOperatorCLM_apply]
        exact realHeatOperator_stokes q τ hq h.1 (F (a - τ))
      · simp [mildShiftedStokesIntegrand, h]

end CKN.Leray

end
