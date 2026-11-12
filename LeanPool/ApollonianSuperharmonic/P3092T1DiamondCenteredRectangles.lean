/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.TileRealization
public meta import Lean.Meta.Tactic.NormCast

-- [TABLET NODE: P3092T1DiamondCenteredRectangles]

/-!
# P3092T1DiamondCenteredRectangles

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3092T1DiamondCenteredRectangles (k : Nat) (hk : 0 < k) :
    TileRealization (DiamondTile k) =
      ⋃ j ∈ Finset.Icc 1 k,
        Set.Icc (-(j : Real), (j : Real) - 1)
          ((j : Real), 2 * (k : Real) - (j : Real) + 1) := by
-- BODY
  classical
  have hsegment (L U : Nat) (hLU : L ≤ U) (Y : Real)
      (hL : (L : Real) ≤ Y) (hU : Y ≤ (U : Real) + 1) :
      ∃ y : Nat, L ≤ y ∧ y ≤ U ∧ (y : Real) ≤ Y ∧ Y ≤ (y : Real) + 1 := by
    have hfloor : L ≤ ⌊Y⌋₊ := Nat.le_floor hL
    refine ⟨min ⌊Y⌋₊ U, Nat.le_min.mpr ⟨hfloor, hLU⟩, Nat.min_le_right _ _, ?_⟩
    by_cases h : ⌊Y⌋₊ ≤ U
    · rw [Nat.min_eq_left h]
      exact ⟨Nat.floor_le (le_trans (Nat.cast_nonneg L) hL),
        (Nat.lt_floor_add_one Y).le⟩
    · rw [Nat.min_eq_right (by omega)]
      have hUF : (U : Real) ≤ (⌊Y⌋₊ : Real) := by exact_mod_cast (by omega : U ≤ ⌊Y⌋₊)
      exact ⟨hUF.trans (Nat.floor_le (le_trans (Nat.cast_nonneg L) hL)), hU⟩
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨x, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hx, hp⟩
    change x ∈ DiamondCellDomain k at hx
    rcases Finset.mem_biUnion.mp hx with ⟨y, hy, hx⟩
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hyk := Finset.mem_range.mp hy
    have hik := Finset.mem_range.mp hi
    let r := min (y + 1) (2 * k - y)
    have hrpos : 1 ≤ r := by dsimp [r]; omega
    have hrk : r ≤ k := by dsimp [r]; omega
    have hry : r ≤ y + 1 := Nat.min_le_left _ _
    have hry' : r + y ≤ 2 * k := by dsimp [r]; omega
    have hreal_i : (i : Real) + 1 ≤ 2 * (r : Real) := by exact_mod_cast hik
    have hreal_y : (r : Real) ≤ (y : Real) + 1 := by exact_mod_cast hry
    have hreal_y' : (r : Real) + (y : Real) ≤ 2 * (k : Real) := by
      exact_mod_cast hry'
    have hreal_i0 : 0 ≤ (i : Real) := Nat.cast_nonneg _
    have hp' :
        ((i : Real) - (r : Real) ≤ p.1 ∧ (y : Real) ≤ p.2) ∧
        (p.1 ≤ (i : Real) - (r : Real) + 1 ∧ p.2 ≤ (y : Real) + 1) := by
      simpa only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
        Int.cast_sub, Int.cast_natCast] using hp
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
      ⟨Finset.mem_Icc.mpr ⟨hrpos, hrk⟩, ?_⟩⟩
    simp only [Set.mem_Icc, Prod.le_def]
    constructor <;> constructor <;> linarith [hp'.1.1, hp'.1.2, hp'.2.1, hp'.2.2]
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨j, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hj, hp⟩
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hjk⟩
    have hj2k : j ≤ 2 * k := by omega
    have hp' := hp
    simp only [Set.mem_Icc, Prod.le_def] at hp'
    have hL : ((j - 1 : Nat) : Real) ≤ p.2 := by
      simpa only [Nat.cast_sub hj1, Nat.cast_one] using hp'.1.2
    have hU : p.2 ≤ ((2 * k - j : Nat) : Real) + 1 := by
      simpa only [Nat.cast_sub hj2k, Nat.cast_mul, Nat.cast_ofNat] using hp'.2.2
    obtain ⟨y, hyl, hyu, hyp, hpy⟩ :=
      hsegment (j - 1) (2 * k - j) (by omega) p.2 hL hU
    have hyk : y < 2 * k := by omega
    let r := min (y + 1) (2 * k - y)
    have hjr : j ≤ r := by dsimp [r]; omega
    have hrpos : 0 < r := by omega
    have hjr' : (j : Real) ≤ (r : Real) := by exact_mod_cast hjr
    have hX0 : 0 ≤ p.1 + (r : Real) := by linarith [hp'.1.1]
    have hXU : p.1 + (r : Real) ≤ ((2 * r - 1 : Nat) : Real) + 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
      push_cast
      linarith [hp'.2.1]
    obtain ⟨i, hi0, hiu, hip, hpi⟩ :=
      hsegment 0 (2 * r - 1) (Nat.zero_le _) (p.1 + (r : Real)) (by simpa using hX0) hXU
    have hir : i < 2 * r := by omega
    let x : GaussianInt := ⟨(i : Int) - (r : Int), (y : Int)⟩
    have hx : x ∈ (DiamondTile k).cells := by
      change x ∈ DiamondCellDomain k
      apply Finset.mem_biUnion.mpr
      refine ⟨y, Finset.mem_range.mpr hyk, ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hir, rfl⟩
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def, x,
      Int.cast_sub, Int.cast_natCast]
    constructor <;> constructor <;> linarith

end ApollonianSuperharmonic

end
