/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildIntegral

/-!
# Translation of the shifted Stokes integral

An earlier Stokes interval in a restarted mild equation becomes the
upper elapsed-time part after translating the integration variable.
-/

public section

open MeasureTheory
open scoped Interval ENNReal

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Translation by a nonnegative restart elapsed time identifies the
propagated earlier Stokes kernels with the upper shifted interval. -/
theorem mildShiftedStokesIntegral_translate_upper
    (F : ℝ → RealTensorL2) (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) :
    (∫ τ in (0 : ℝ)..a,
      if h : 0 < τ ∧ τ < a then
        realStokesOperator (show 0 < q + τ by
          have hτ : 0 < τ := h.1
          positivity) (F (a - τ))
      else 0) =
    ∫ σ in q..(a + q), mildShiftedStokesIntegrand F (a + q) σ := by
  calc
    (∫ τ in (0 : ℝ)..a,
      if h : 0 < τ ∧ τ < a then
        realStokesOperator (show 0 < q + τ by
          have hτ : 0 < τ := h.1
          positivity) (F (a - τ))
      else 0) =
      ∫ τ in (0 : ℝ)..a,
        mildShiftedStokesIntegrand F (a + q) (τ + q) := by
          apply intervalIntegral.integral_congr_Ioo_of_le ha
          intro τ hτ
          have hτpos : 0 < τ := hτ.1
          have hτa : τ < a := hτ.2
          have hsumPos : 0 < τ + q := by positivity
          have hsumLt : τ + q < a + q := by linarith only [hτa]
          simp only [mildShiftedStokesIntegrand,
            dite_eq_left (show 0 < τ ∧ τ < a from ⟨hτpos, hτa⟩),
            dite_eq_left (show 0 < τ + q ∧ τ + q < a + q from
              ⟨hsumPos, hsumLt⟩)]
          have hsource : a + q - (τ + q) = a - τ := by ring
          simp only [add_comm q τ, hsource]
    _ = ∫ σ in q..(a + q), mildShiftedStokesIntegrand F (a + q) σ := by
      simpa only [zero_add] using
        (intervalIntegral.integral_comp_add_right
          (fun σ => mildShiftedStokesIntegrand F (a + q) σ)
          (a := (0 : ℝ)) (b := a) q)

end CKN.Leray

end
