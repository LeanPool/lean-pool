/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSPotential
public import LeanPool.SplitCliqueGap.R434.OddMidpoints
public import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Modular midpoint relations on grid representatives and discrete curvature. -/

@[expose] public section

namespace GapExtremal.R434.EHPS

theorem wrap_of_cast_eq {m a b c : ℕ} (ha : a < m) (hb : b < m) (hc : c < m)
    (h : (a : ZMod m) + c = 2 * (b : ZMod m)) :
    Wrap ((a : ℝ) / m) ((b : ℝ) / m) ((c : ℝ) / m) := by
  have hz : (((a : ℤ) + c - 2 * (b : ℤ) : ℤ) : ZMod m) = 0 := by
    push_cast
    exact sub_eq_zero.mpr h
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hmN : 0 < m := by omega
  have hmI : (0 : ℤ) < m := by exact_mod_cast hmN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmN
  have haI : (a : ℤ) < m := by exact_mod_cast ha
  have hbI : (b : ℤ) < m := by exact_mod_cast hb
  have hcI : (c : ℤ) < m := by exact_mod_cast hc
  have klo : -1 ≤ k := by
    by_contra! hn
    have hmul := mul_le_mul_of_nonneg_left (show k ≤ -2 by omega) hmI.le
    nlinarith only [hk, hmul, hbI, Int.natCast_nonneg a, Int.natCast_nonneg c]
  have khi : k ≤ 1 := by
    by_contra! hn
    have hmul := mul_le_mul_of_nonneg_left (show 2 ≤ k by omega) hmI.le
    nlinarith only [hk, hmul, haI, hcI, Int.natCast_nonneg b]
  have hkR : (a : ℝ) + c - 2 * (b : ℝ) = (m : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  interval_cases k
  · right
    right
    field_simp [hmR.ne']
    norm_num at hkR
    linarith only [hkR]
  · right
    left
    field_simp [hmR.ne']
    norm_num at hkR
    linarith only [hkR]
  · left
    field_simp [hmR.ne']
    norm_num at hkR
    linarith only [hkR]

/-- Maps a cyclic grid element to its normalized real coordinates. -/
noncomputable def gridPoint (m : ℕ) (u : ZMod m × ZMod m) : Point :=
  ((u.1.val : ℝ) / m, (u.2.val : ℝ) / m)

/-- The real potential on a grid point, scaled by the square of the grid side. -/
noncomputable def gridPotential (ε : ℝ) (m : ℕ) (u : ZMod m × ZMod m) : ℝ :=
  (m : ℝ) ^ 2 * potential ε (gridPoint m u)

theorem grid_potential_bounds {ε : ℝ} {m : ℕ} {u : ZMod m × ZMod m}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hu : Region ε (gridPoint m u)) :
    0 ≤ gridPotential ε m u ∧ gridPotential ε m u ≤ 100 * (m : ℝ) ^ 2 / ε ^ 2 := by
  have hb := potential_bounds hε hε₁ hu
  refine ⟨mul_nonneg (sq_nonneg _) hb.1, ?_⟩
  calc
    gridPotential ε m u ≤ (m : ℝ) ^ 2 * (100 / ε ^ 2) :=
      mul_le_mul_of_nonneg_left hb.2 (sq_nonneg _)
    _ = _ := by ring

theorem square_nat_difference {a b : ℕ} (h : a ≠ b) :
    (1 : ℝ) ≤ ((a : ℝ) - b) ^ 2 := by
  have hh : (1 : ℝ) ≤ |(a : ℝ) - b| := by
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hR : (a : ℝ) + 1 ≤ b := by exact_mod_cast hlt
      rw [abs_of_nonpos (by linarith : (a : ℝ) - b ≤ 0)]
      linarith
    · have hR : (b : ℝ) + 1 ≤ a := by exact_mod_cast hgt
      rw [abs_of_nonneg (by linarith : 0 ≤ (a : ℝ) - b)]
      linarith
  simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hh 2

theorem grid_potential_midpoint {ε : ℝ} {m : ℕ} [NeZero m]
    {x y z : ZMod m × ZMod m} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hx : Region ε (gridPoint m x)) (hy : Region ε (gridPoint m y))
    (hz : Region ε (gridPoint m z)) (hne : x ≠ z)
    (h₁ : x.1 + z.1 = 2 * y.1) (h₂ : x.2 + z.2 = 2 * y.2) :
    1 ≤ gridPotential ε m x + gridPotential ε m z - 2 * gridPotential ε m y := by
  have hwrap₁ : Wrap (gridPoint m x).1 (gridPoint m y).1 (gridPoint m z).1 :=
    wrap_of_cast_eq (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
      (by simpa only [ZMod.natCast_zmod_val] using h₁)
  have hwrap₂ : Wrap (gridPoint m x).2 (gridPoint m y).2 (gridPoint m z).2 :=
    wrap_of_cast_eq (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
      (by simpa only [ZMod.natCast_zmod_val] using h₂)
  have h := potential_midpoint hε hε₁ hx hy hz hwrap₁ hwrap₂
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hid : (m : ℝ) ^ 2 *
      (((gridPoint m x).1 - (gridPoint m z).1) ^ 2 +
       ((gridPoint m x).2 - (gridPoint m z).2) ^ 2) =
      ((x.1.val : ℝ) - z.1.val) ^ 2 + ((x.2.val : ℝ) - z.2.val) ^ 2 := by
    simp only [gridPoint]
    field_simp [hmR]
  have hscaled := mul_le_mul_of_nonneg_left h (sq_nonneg (m : ℝ))
  rw [hid] at hscaled
  have hunit : (1 : ℝ) ≤
      ((x.1.val : ℝ) - z.1.val) ^ 2 + ((x.2.val : ℝ) - z.2.val) ^ 2 := by
    by_cases hf : x.1.val = z.1.val
    · have hs : x.2.val ≠ z.2.val := by
        intro hs
        exact hne (Prod.ext (ZMod.val_injective m hf) (ZMod.val_injective m hs))
      linarith only [square_nat_difference hs, sq_nonneg ((x.1.val : ℝ) - z.1.val)]
    · linarith only [square_nat_difference hf, sq_nonneg ((x.2.val : ℝ) - z.2.val)]
  unfold gridPotential
  nlinarith only [hscaled, hunit]

end GapExtremal.R434.EHPS
