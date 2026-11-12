/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerAction
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetrySlopeAction
public import Mathlib.Tactic.LinearCombination

-- [TABLET NODE: P2999T1ShiftSlopeTransport]

/-!
# P2999T1ShiftSlopeTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P2999T1ShiftSlopeTransport (h : PartialOdometer) (w : GaussianInt) (T : ProtoTile)
    (hne : T.cells.Nonempty) (hT : PartialOdometerSquares h = T.cells) :
    PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction (.shift w) h) =
      (PartialOdometerSlope h).map (BandPackingSymmetrySlopeAction (.shift w) T) := by
-- BODY
  classical
  have triangular (n : ℤ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    rw [show (n + 1) * (n + 1 - 1) = n * (n - 1) + n * 2 by ring]
    exact Int.add_mul_ediv_right _ _ (by norm_num)
  have dx (x : GaussianInt) :
      BandPackingShiftPotential w (x + 1) - BandPackingShiftPotential w x =
        w.re * x.re + w.im * x.im := by
    simp only [BandPackingShiftPotential, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one, add_zero]
    rw [triangular]
    ring
  have dy (x : GaussianInt) :
      BandPackingShiftPotential w (x + ⟨0, 1⟩) - BandPackingShiftPotential w x =
        -w.re * x.im + w.im * x.re := by
    simp only [BandPackingShiftPotential, Zsqrtd.re_add, Zsqrtd.im_add, add_zero]
    rw [triangular]
    ring
  have value (x : GaussianInt) (hx : x ∈ h.domain) :
      (BandPackingSymmetryPartialOdometerAction (.shift w) h).value x =
        h.value x + BandPackingShiftPotential w x := by
    simp [BandPackingSymmetryPartialOdometerAction, hx]
  let H (h : PartialOdometer) (x : GaussianInt) : ℝ :=
    (h.value (x + 1) - h.value x + h.value (x + 1 + ⟨0, 1⟩) -
      h.value (x + ⟨0, 1⟩) : ℤ)
  let V (h : PartialOdometer) (x : GaussianInt) : ℝ :=
    (h.value (x + ⟨0, 1⟩) - h.value x + h.value (x + 1 + ⟨0, 1⟩) -
      h.value (x + 1) : ℤ)
  have horizontal (x : GaussianInt) (hx : x ∈ PartialOdometerSquares h) :
      H (BandPackingSymmetryPartialOdometerAction (.shift w) h) x =
        H h x + 2 * (w.re : ℝ) * x.re + (w.im : ℝ) * (2 * x.im + 1) := by
    obtain ⟨hx0, hx1, hxi, hx1i⟩ := Finset.mem_filter.mp hx
    dsimp only [H]
    rw [value _ hx1, value _ hx0, value _ hx1i, value _ hxi]
    have e :
        BandPackingShiftPotential w (x + 1) - BandPackingShiftPotential w x +
          BandPackingShiftPotential w (x + 1 + ⟨0, 1⟩) -
          BandPackingShiftPotential w (x + ⟨0, 1⟩) =
        2 * w.re * x.re + w.im * (2 * x.im + 1) := by
      rw [show x + 1 + ⟨0, 1⟩ = (x + ⟨0, 1⟩) + 1 by abel]
      calc
        _ = (BandPackingShiftPotential w (x + 1) - BandPackingShiftPotential w x) +
          (BandPackingShiftPotential w ((x + ⟨0, 1⟩) + 1) -
          BandPackingShiftPotential w (x + ⟨0, 1⟩)) := by ring
        _ = _ := by rw [dx, dx]; simp; ring
    have intEq :
        h.value (x + 1) + BandPackingShiftPotential w (x + 1) -
          (h.value x + BandPackingShiftPotential w x) +
          (h.value (x + 1 + ⟨0, 1⟩) + BandPackingShiftPotential w (x + 1 + ⟨0, 1⟩)) -
          (h.value (x + ⟨0, 1⟩) + BandPackingShiftPotential w (x + ⟨0, 1⟩)) =
        (h.value (x + 1) - h.value x + h.value (x + 1 + ⟨0, 1⟩) -
          h.value (x + ⟨0, 1⟩)) + (2 * w.re * x.re + w.im * (2 * x.im + 1)) := by
      linear_combination e
    rw [intEq]
    push_cast
    ring
  have vertical (x : GaussianInt) (hx : x ∈ PartialOdometerSquares h) :
      V (BandPackingSymmetryPartialOdometerAction (.shift w) h) x =
        V h x - 2 * (w.re : ℝ) * x.im + (w.im : ℝ) * (2 * x.re + 1) := by
    obtain ⟨hx0, hx1, hxi, hx1i⟩ := Finset.mem_filter.mp hx
    dsimp only [V]
    rw [value _ hxi, value _ hx0, value _ hx1i, value _ hx1]
    have e :
        BandPackingShiftPotential w (x + ⟨0, 1⟩) - BandPackingShiftPotential w x +
          BandPackingShiftPotential w (x + 1 + ⟨0, 1⟩) -
          BandPackingShiftPotential w (x + 1) =
        -2 * w.re * x.im + w.im * (2 * x.re + 1) := by
      calc
        _ = (BandPackingShiftPotential w (x + ⟨0, 1⟩) - BandPackingShiftPotential w x) +
          (BandPackingShiftPotential w ((x + 1) + ⟨0, 1⟩) -
          BandPackingShiftPotential w (x + 1)) := by ring
        _ = _ := by rw [dy, dy]; simp; ring
    have intEq :
        h.value (x + ⟨0, 1⟩) + BandPackingShiftPotential w (x + ⟨0, 1⟩) -
          (h.value x + BandPackingShiftPotential w x) +
          (h.value (x + 1 + ⟨0, 1⟩) + BandPackingShiftPotential w (x + 1 + ⟨0, 1⟩)) -
          (h.value (x + 1) + BandPackingShiftPotential w (x + 1)) =
        (h.value (x + ⟨0, 1⟩) - h.value x + h.value (x + 1 + ⟨0, 1⟩) -
          h.value (x + 1)) + (-2 * w.re * x.im + w.im * (2 * x.re + 1)) := by
      linear_combination e
    rw [intEq]
    push_cast
    ring
  have hs : (PartialOdometerSquares h).Nonempty := hT.symm ▸ hne
  have sq : PartialOdometerSquares (BandPackingSymmetryPartialOdometerAction (.shift w) h) =
      PartialOdometerSquares h := rfl
  have hc : ((PartialOdometerSquares h).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hs.card_pos)
  simp only [PartialOdometerSlope, sq, hs, ↓reduceIte, Option.map_some,
    BandPackingSymmetrySlopeAction, TileCentroid, hne]
  change some ((∑ x ∈ PartialOdometerSquares h,
      H (BandPackingSymmetryPartialOdometerAction (.shift w) h) x) /
      (2 * ((PartialOdometerSquares h).card : ℝ)),
      (∑ x ∈ PartialOdometerSquares h,
      V (BandPackingSymmetryPartialOdometerAction (.shift w) h) x) /
      (2 * ((PartialOdometerSquares h).card : ℝ))) = _
  have sh := Finset.sum_congr rfl horizontal
  have sv := Finset.sum_congr rfl vertical
  rw [sh, sv, ← hT]
  congr 1
  ext
  all_goals
    dsimp only [H, V]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    field_simp [hc]
    ring

end ApollonianSuperharmonic

end
