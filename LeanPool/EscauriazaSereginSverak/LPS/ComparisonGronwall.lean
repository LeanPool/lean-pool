/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinGronwall

/-!
# Comparison Gronwall

A nonnegative relative energy that is bounded in time and satisfies an
integral inequality with an integrable nonnegative coefficient vanishes almost
everywhere (`lem:lps-comparison`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval


noncomputable section

namespace ESS

/-- A nonnegative relative energy that is bounded in time and satisfies an
integral inequality with an integrable nonnegative coefficient vanishes almost
everywhere (`lem:lps-comparison`). -/
theorem lps_comparison_grow_zero
    {T C : ℝ} {m E : ℝ → ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hm : IntegrableOn m (Ioo 0 T))
    (hmNonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ m t)
    (hENonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ E t)
    (hmE : IntegrableOn (fun t => m t * E t) (Ioo 0 T))
    (hmENonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ m t * E t)
    (hineq : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      E t ≤ C * ∫ s in (0 : ℝ)..t, m s * E s) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), E t = 0 := by
  have hIcc : (volume.restrict (Icc 0 T) : Measure ℝ) =
      volume.restrict (Ioo 0 T) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hzero := serrin_integral_gronwall_zero (T := T) (C := C)
    (b := m) (q := E) hT.le hC
    (by rw [IntegrableOn, hIcc]; exact hm)
    (by rw [hIcc]; exact hmNonneg)
    (by rw [hIcc]; exact hENonneg)
    (by rw [hIcc]; exact hmE)
    (by rw [hIcc]; exact hmENonneg)
    (by rw [hIcc]; exact hineq)
  rw [hIcc] at hzero
  exact hzero

end ESS

end
