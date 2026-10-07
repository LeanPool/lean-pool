/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.DyadicCells
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Geometry of the short-time dyadic cells

Each time cell lies close to its center. This permits one Gaussian
average and one Caccioppoli estimate to control its quadratic energy in
`lem:bu-small-time`.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Time coordinates in a dyadic cell differ from the midpoint by at
most half the time-cell length. -/
theorem bu_short_dyadic_cell_time_distance_le
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (z : ParabolicPoint)
    (hz : z ∈ Foundation.buSmallTimeDyadicCell k m ell) :
    |z.2 - (Foundation.buSmallTimeDyadicCellCenter k m ell).2| ≤
      Foundation.buSmallTimeDyadicTimeLength k / 2 := by
  have ht : z.2 ∈ Foundation.buSmallTimeDyadicTimeCell k ell := hz.2
  change z.2 ∈ Set.Ioo
    (Foundation.buSmallTimeDyadicScale k / 2 +
      (ell.val : ℝ) * Foundation.buSmallTimeDyadicTimeLength k)
    (Foundation.buSmallTimeDyadicScale k / 2 +
      ((ell.val + 1 : ℕ) : ℝ) * Foundation.buSmallTimeDyadicTimeLength k) at ht
  rw [abs_le]
  constructor
  · change -(Foundation.buSmallTimeDyadicTimeLength k / 2) ≤
      z.2 - (Foundation.buSmallTimeDyadicScale k / 2 +
        ((ell.val : ℝ) + 1 / 2) * Foundation.buSmallTimeDyadicTimeLength k)
    linarith only [ht.1]
  · change z.2 - (Foundation.buSmallTimeDyadicScale k / 2 +
        ((ell.val : ℝ) + 1 / 2) * Foundation.buSmallTimeDyadicTimeLength k) ≤
        Foundation.buSmallTimeDyadicTimeLength k / 2
    have hcast : ((ell.val + 1 : ℕ) : ℝ) = (ell.val : ℝ) + 1 := by norm_cast
    rw [hcast] at ht
    linarith only [ht.2]

/-- The dyadic midpoint time lies in the same layer as its cell. -/
theorem bu_short_dyadic_cell_center_time_bounds
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
    Foundation.buSmallTimeDyadicScale k / 2 <
      (Foundation.buSmallTimeDyadicCellCenter k m ell).2 ∧
    (Foundation.buSmallTimeDyadicCellCenter k m ell).2 <
      Foundation.buSmallTimeDyadicScale k := by
  let z : ParabolicPoint := Foundation.buSmallTimeDyadicCellCenter k m ell
  have hτ : 0 < Foundation.buSmallTimeDyadicTimeLength k :=
    Foundation.buSmallTimeDyadicTimeLength_pos k
  have hn : (ell.val : ℝ) + 1 / 2 < 2048 := by
    have h := ell.isLt
    have hr : (ell.val : ℝ) + 1 ≤ 2048 := by exact_mod_cast Nat.succ_le_of_lt h
    linarith only [hr]
  have hlast : Foundation.buSmallTimeDyadicScale k / 2 +
      (2048 : ℝ) * Foundation.buSmallTimeDyadicTimeLength k =
      Foundation.buSmallTimeDyadicScale k := by
    dsimp [Foundation.buSmallTimeDyadicTimeLength]
    ring
  change Foundation.buSmallTimeDyadicScale k / 2 <
      Foundation.buSmallTimeDyadicScale k / 2 +
        ((ell.val : ℝ) + 1 / 2) * Foundation.buSmallTimeDyadicTimeLength k ∧
    Foundation.buSmallTimeDyadicScale k / 2 +
        ((ell.val : ℝ) + 1 / 2) * Foundation.buSmallTimeDyadicTimeLength k <
      Foundation.buSmallTimeDyadicScale k
  constructor
  · have hpos : 0 < (ell.val : ℝ) + 1 / 2 := by positivity
    nlinarith only [hτ, hpos]
  · calc
      _ < Foundation.buSmallTimeDyadicScale k / 2 +
          2048 * Foundation.buSmallTimeDyadicTimeLength k :=
        by simpa only [add_comm] using
          (add_lt_add_left (mul_lt_mul_of_pos_right hn hτ)
            (Foundation.buSmallTimeDyadicScale k / 2))
      _ = Foundation.buSmallTimeDyadicScale k := hlast

end ESS
