/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSGrid
public import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! Midpoint-safe complement classes of the EHPS grid. -/

@[expose] public section

open Finset

namespace GapExtremal.R434.EHPS

/-- A three-valued code distinguishing negative, zero, and positive real numbers. -/
noncomputable def signCode (x : ℝ) : Fin 3 := by
  classical
  exact if x < 0 then 0 else if x = 0 then 1 else 2

theorem signCode_lt (x : ℝ) : signCode x = 0 ↔ x < 0 := by
  unfold signCode
  split_ifs with h h' <;> norm_num <;> linarith

theorem signCode_gt (x : ℝ) : signCode x = 2 ↔ 0 < x := by
  unfold signCode
  split_ifs with h h' <;> norm_num
  · linarith
  · linarith
  · exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h')

theorem signCode_mid {a b : ℝ} (h : signCode a = signCode b) :
    signCode ((a + b) / 2) = signCode a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : b < 0 := (signCode_lt b).mp (h.symm.trans ((signCode_lt a).mpr ha))
    exact ((signCode_lt _).mpr (by linarith)).trans ((signCode_lt _).mpr ha).symm
  · subst a
    have h0 : signCode 0 = 1 := by simp [signCode]
    rw [h0] at h
    have hb : b = 0 := by
      rcases lt_trichotomy b 0 with hb | hb | hb
      · have hz := (signCode_lt b).mpr hb
        rw [← h] at hz
        norm_num at hz
      · exact hb
      · have hz := (signCode_gt b).mpr hb
        rw [← h] at hz
        norm_num at hz
    simp [hb]
  · have hb : 0 < b := (signCode_gt b).mp (h.symm.trans ((signCode_gt a).mpr ha))
    exact ((signCode_gt _).mpr (by linarith)).trans ((signCode_gt _).mpr ha).symm

/-- The signed value of the indexed affine form at a point. -/
noncomputable def lineValue (ε : ℝ) (u : Point) (i : Fin 7) : ℝ :=
  match i.val with
  | 0 => u.1 - 1 / 2
  | 1 => u.2 - 1 / 2
  | 2 => total u - 2 / 3
  | 3 => total u - 7 / 6
  | 4 => total u - (7 / 6 + ε)
  | 5 => total u - 17 / 12
  | _ => 2 * u.1 + u.2 - (3 / 2 + ε)

/-- The coordinatewise midpoint of two points in the plane. -/
noncomputable def midpoint (u v : Point) : Point := ((u.1 + v.1) / 2, (u.2 + v.2) / 2)

theorem lineValue_mid (ε : ℝ) (u v : Point) (i : Fin 7) :
    lineValue ε (midpoint u v) i = (lineValue ε u i + lineValue ε v i) / 2 := by
  fin_cases i <;> simp [lineValue, midpoint, total] <;> ring

/-- The seven affine sign codes of a point. -/
noncomputable def profile (ε : ℝ) (u : Point) : Fin 7 → Fin 3 :=
  fun i => signCode (lineValue ε u i)

theorem profile_mid {ε : ℝ} {u v : Point} (h : profile ε u = profile ε v) :
    profile ε (midpoint u v) = profile ε u := by
  funext i
  unfold profile
  rw [lineValue_mid]
  exact signCode_mid (congrFun h i)

/-- Membership in the half-open unit square. -/
def InSquare (x : Point) : Prop := 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1

theorem region_iff_of_profile {ε : ℝ} {u v : Point}
    (hu : InSquare u) (hv : InSquare v) (h : profile ε u = profile ε v) :
    Region ε u ↔ Region ε v := by
  have hlt (i : Fin 7) : lineValue ε u i < 0 ↔ lineValue ε v i < 0 := by
    rw [← signCode_lt, ← signCode_lt]
    exact Iff.of_eq (congrArg (fun k : Fin 3 => k = 0) (congrFun h i))
  have hgt (i : Fin 7) : 0 < lineValue ε u i ↔ 0 < lineValue ε v i := by
    rw [← signCode_gt, ← signCode_gt]
    exact Iff.of_eq (congrArg (fun k : Fin 3 => k = 2) (congrFun h i))
  have h₀ := not_congr (hlt 0)
  have h₁ := hlt 1
  have h₁' := not_congr h₁
  have h₂ := hgt 2
  have h₃ := not_congr (hgt 3)
  have h₄ := not_congr (hlt 4)
  have h₅ := not_congr (hgt 5)
  have h₆ := not_congr (hlt 6)
  change ¬ u.1 - 1 / 2 < 0 ↔ ¬ v.1 - 1 / 2 < 0 at h₀
  change u.2 - 1 / 2 < 0 ↔ v.2 - 1 / 2 < 0 at h₁
  change ¬ u.2 - 1 / 2 < 0 ↔ ¬ v.2 - 1 / 2 < 0 at h₁'
  change 0 < total u - 2 / 3 ↔ 0 < total v - 2 / 3 at h₂
  change ¬ 0 < total u - 7 / 6 ↔ ¬ 0 < total v - 7 / 6 at h₃
  change ¬ total u - (7 / 6 + ε) < 0 ↔ ¬ total v - (7 / 6 + ε) < 0 at h₄
  change ¬ 0 < total u - 17 / 12 ↔ ¬ 0 < total v - 17 / 12 at h₅
  change ¬ 2 * u.1 + u.2 - (3 / 2 + ε) < 0 ↔
    ¬ 2 * v.1 + v.2 - (3 / 2 + ε) < 0 at h₆
  have h₀' := not_congr h₀
  simp only [sub_lt_zero, sub_pos, not_lt, not_le] at h₀ h₀' h₁ h₁' h₂ h₃ h₄ h₅ h₆
  unfold InSquare at hu hv
  simp only [Region, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2,
    hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, true_and, h₀, h₀', h₁, h₁', h₂, h₃, h₄, h₅, h₆]

/-- The two-dimensional cyclic grid of side length `m`. -/
abbrev Grid (m : ℕ) := ZMod m × ZMod m
/-- A class records the affine sign profile and the two coordinate parities. -/
abbrev Class := (Fin 7 → Fin 3) × Fin 2 × Fin 2

/-- Assigns each grid point its affine sign and parity class. -/
noncomputable def colour (ε : ℝ) (m : ℕ) (u : Grid m) : Class :=
  (profile ε (gridPoint m u), ⟨u.1.val % 2, Nat.mod_lt _ (by decide)⟩,
    ⟨u.2.val % 2, Nat.mod_lt _ (by decide)⟩)

theorem class_count : Fintype.card Class = 8748 := by
  simp

theorem grid_in_square {m : ℕ} [NeZero m] (x : Grid m) :
    InSquare (gridPoint m x) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  constructor
  · exact div_nonneg (by positivity) hm.le
  constructor
  · exact (div_lt_one₀ hm).mpr (by exact_mod_cast ZMod.val_lt x.1)
  constructor
  · exact div_nonneg (by positivity) hm.le
  · exact (div_lt_one₀ hm).mpr (by exact_mod_cast ZMod.val_lt x.2)

theorem grid_coord_mid {m : ℕ} [NeZero m] (hm : Odd m) (u v : ZMod m)
    (hp : u.val % 2 = v.val % 2) :
    (((oddHalf m * (u + v)).val : ℝ) / m) =
      ((u.val : ℝ) / m + (v.val : ℝ) / m) / 2 := by
  have hh : oddHalf m * (u + v) = (((u.val + v.val) / 2 : ℕ) : ZMod m) := by
    simpa only [ZMod.natCast_zmod_val] using natCast_midpoint hm hp
  have hlt : (u.val + v.val) / 2 < m := by
    have h₁ := ZMod.val_lt u
    have h₂ := ZMod.val_lt v
    omega
  rw [hh, ZMod.val_natCast_of_lt hlt]
  have hN : 2 * ((u.val + v.val) / 2) = u.val + v.val := by omega
  have hR : (2 : ℝ) * (((u.val + v.val) / 2 : ℕ) : ℝ) = (u.val : ℝ) + v.val := by
    exact_mod_cast hN
  linarith only [congrArg (fun a : ℝ => a / (m : ℝ)) hR,
    show ((2 : ℝ) * (((u.val + v.val) / 2 : ℕ) : ℝ)) / m =
      2 * ((((u.val + v.val) / 2 : ℕ) : ℝ) / m) by ring,
    add_div (u.val : ℝ) v.val m]

theorem region_mid_of_colour {m : ℕ} [NeZero m] (hm : Odd m) {ε : ℝ} {u v : Grid m}
    (hc : colour ε m u = colour ε m v) :
    Region ε (gridPoint m (oddHalf m * (u.1 + v.1), oddHalf m * (u.2 + v.2))) ↔
      Region ε (gridPoint m u) := by
  let t : Grid m := (oddHalf m * (u.1 + v.1), oddHalf m * (u.2 + v.2))
  have h₁ : u.1.val % 2 = v.1.val % 2 := congrArg (fun c : Class => c.2.1.val) hc
  have h₂ : u.2.val % 2 = v.2.val % 2 := congrArg (fun c : Class => c.2.2.val) hc
  have ht : gridPoint m t = midpoint (gridPoint m u) (gridPoint m v) :=
    Prod.ext (grid_coord_mid hm _ _ h₁) (grid_coord_mid hm _ _ h₂)
  change Region ε (gridPoint m t) ↔ Region ε (gridPoint m u)
  apply region_iff_of_profile (grid_in_square t) (grid_in_square u)
  rw [ht]
  exact profile_mid (congrArg Prod.fst hc)

end GapExtremal.R434.EHPS
