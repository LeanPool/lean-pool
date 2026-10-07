/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellSummability
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCellCover

/-!
# Integrability on the short normalized slab

The abstract dyadic cell estimate controls integration on the full
short-time slab because the cells cover it almost everywhere.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Polynomially weighted Gaussian cell bounds imply integrability on
the short-time slab (`lem:bu-small-time`). -/
theorem bu_short_integrable_on_short_slab
    (N : ℕ) (c K : ℝ) (hc : 0 < c)
    (F : ParabolicPoint → ℝ)
    (hCellInt : ∀ (k : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048),
      IntegrableOn F
        (buShortShiftedDyadicCell (k + 1 : ℤ) m ell) volume)
    (hCellBound : ∀ (k : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048),
      (∫ z in buShortShiftedDyadicCell (k + 1 : ℤ) m ell,
        ‖F z‖ ∂(volume : Measure ParabolicPoint)) ≤
          K * ((2 : ℝ) ^ (N * (k + 1)) *
            Real.exp (-(c * (2 : ℝ) ^ (k + 1)))) *
              buShortSpatialProfile m) :
    IntegrableOn F
      (Set.univ ×ˢ Ioo (1 / 2 : ℝ) 1 : Set ParabolicPoint)
      volume :=
  (bu_short_integrable_on_shifted_dyadic_cells N c K hc
    F hCellInt hCellBound).congr_set_ae
      bu_short_shifted_all_cells_cover_ae.symm

end ESS
