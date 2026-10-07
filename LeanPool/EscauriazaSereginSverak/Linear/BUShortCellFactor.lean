/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellEnergyApplied

/-!
# Dyadic size of the local energy coefficient

The inverse square of the Caccioppoli radius costs one inverse power of
the dyadic time scale.
-/

public section


noncomputable section

namespace ESS

/-- The local energy coefficient on a cell is at most a fixed constant
divided by the dyadic time scale (`lem:bu-small-time`). -/
theorem bu_short_cell_energy_factor_le
    (d δ c : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hδ : d / 2 < δ) :
    let r := Real.sqrt δ / 8
    1 + 256 * (1 + c ^ 2 + 1 / r ^ 2) ≤
      (1 + 256 * (1 + c ^ 2 + 128)) / d := by
  dsimp
  let r := Real.sqrt δ / 8
  change 1 + 256 * (1 + c ^ 2 + 1 / r ^ 2) ≤
    (1 + 256 * (1 + c ^ 2 + 128)) / d
  have hδ0 : 0 < δ := (half_pos hd).trans hδ
  have hrSq : r ^ 2 = δ / 64 := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt hδ0.le]
    ring
  have hrSq0 : 0 < r ^ 2 := by rw [hrSq]; positivity
  have hInv : 1 / r ^ 2 ≤ 128 / d := by
    apply (div_le_div_iff₀ hrSq0 hd).2
    rw [hrSq]
    nlinarith only [hδ]
  have hInvD : d / r ^ 2 ≤ 128 := by
    have hmul := mul_le_mul_of_nonneg_right hInv hd.le
    have hcancel : (128 / d) * d = 128 := by field_simp
    rw [hcancel] at hmul
    calc
      d / r ^ 2 = 1 / r ^ 2 * d := by ring
      _ ≤ 128 := hmul
  apply (le_div_iff₀ hd).2
  have hC : 0 ≤ 1 + c ^ 2 := by positivity
  have hmain := mul_le_mul_of_nonneg_right hd1 hC
  have hInvProd : (1 / r ^ 2) * d ≤ 128 := by
    calc
      _ = d / r ^ 2 := by ring
      _ ≤ 128 := hInvD
  nlinarith only [hd1, hmain, hInvProd]

end ESS
