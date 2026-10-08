/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellSummabilitySlab
public import Mathlib.Analysis.Normed.Group.Indicator

/-!
# Regional short-time summability

Cell bounds on a measurable subregion of the short-time slab imply
integrability on that subregion.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Gaussian cell bounds restricted to a measurable short-time region
imply integrability there (`lem:bu-small-time`). -/
theorem bu_short_integrable_on_region_of_cell_bounds
    (N : ℕ) (c K : ℝ) (hc : 0 < c)
    (S : Set ParabolicPoint) (hSmeas : MeasurableSet S)
    (hSsub : S ⊆ (Set.univ ×ˢ Ioo (1 / 2 : ℝ) 1 :
      Set ParabolicPoint))
    (F : ParabolicPoint → ℝ)
    (hCellInt : ∀ (k : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048),
      IntegrableOn F
        (buShortShiftedDyadicCell (k + 1 : ℤ) m ell ∩ S) volume)
    (hCellBound : ∀ (k : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048),
      (∫ z in buShortShiftedDyadicCell (k + 1 : ℤ) m ell ∩ S,
        ‖F z‖ ∂(volume : Measure ParabolicPoint)) ≤
          K * ((2 : ℝ) ^ (N * (k + 1)) *
            Real.exp (-(c * (2 : ℝ) ^ (k + 1)))) *
              buShortSpatialProfile m) :
    IntegrableOn F S volume := by
  have hInt (k : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
      IntegrableOn (S.indicator F)
        (buShortShiftedDyadicCell (k + 1 : ℤ) m ell) volume :=
    (integrableOn_indicator_iff hSmeas).mpr (by
      simpa only [Set.inter_comm] using hCellInt k m ell)
  have hBound (k : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
      (∫ z in buShortShiftedDyadicCell (k + 1 : ℤ) m ell,
        ‖S.indicator F z‖ ∂(volume : Measure ParabolicPoint)) ≤
          K * ((2 : ℝ) ^ (N * (k + 1)) *
            Real.exp (-(c * (2 : ℝ) ^ (k + 1)))) *
              buShortSpatialProfile m := by
    simp_rw [norm_indicator_eq_indicator_norm]
    rw [setIntegral_indicator hSmeas]
    exact hCellBound k m ell
  have hSlab := bu_short_integrable_on_short_slab N c K hc
    (S.indicator F) hInt hBound
  have hRegion : IntegrableOn F
      (S ∩ (Set.univ ×ˢ Ioo (1 / 2 : ℝ) 1 : Set ParabolicPoint))
      volume := (integrableOn_indicator_iff hSmeas).mp hSlab
  simpa only [Set.inter_eq_left.mpr hSsub] using hRegion

end ESS
