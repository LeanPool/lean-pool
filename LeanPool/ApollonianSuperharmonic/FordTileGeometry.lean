/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordCellDomain
public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.TileArea

-- [TABLET NODE: FordTileGeometry]

/-!
# FordTileGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private theorem squareRealization (q : ℕ) (hq : 0 < q) : TileRealization (FordTile q) =
    Set.Icc (0, 0) ((q : Real), (q : Real)) := by
  ext p
  constructor
  · intro hp
    simp? [TileRealization, FordTile, FordCellDomain, ClosedSquareRealization] at hp
    rcases hp with ⟨x, y, hxy, hlt, hup⟩
    rcases hxy with ⟨hxl, hyl⟩
    rcases hup with ⟨hxu, hyu⟩
    norm_num at hxl hyl hxu hyu
    constructor
    · constructor
      · linarith
      · linarith
    · constructor
      · have hxq : x + 1 ≤ q := by omega
        have hxq' : (x : Real) + 1 ≤ q := by exact_mod_cast hxq
        linarith
      · have hyq : y + 1 ≤ q := by omega
        have hyq' : (y : Real) + 1 ≤ q := by exact_mod_cast hyq
        linarith
  · intro hp
    simp only [Set.mem_Icc, Prod.le_def] at hp
    let x : Nat := if p.1 = q then q - 1 else ⌊p.1⌋₊
    let y : Nat := if p.2 = q then q - 1 else ⌊p.2⌋₊
    have xlt : x < q := by
      dsimp [x]
      split
      · omega
      · apply (Nat.floor_lt hp.1.1).2
        exact lt_of_le_of_ne hp.2.1 ‹p.1 ≠ q›
    have ylt : y < q := by
      dsimp [y]
      split
      · omega
      · apply (Nat.floor_lt hp.1.2).2
        exact lt_of_le_of_ne hp.2.2 ‹p.2 ≠ q›
    refine ?_
    simp only [TileRealization, FordTile, FordCellDomain]
    refine Set.mem_iUnion.2 ⟨(⟨(x : Int), (y : Int)⟩ : GaussianInt), ?_⟩
    refine Set.mem_iUnion.2 ⟨?_, ?_⟩
    · simp [xlt, ylt]
    · simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor
      · constructor
        · dsimp [x]
          split
          · have hqcast : (q : Real) ≤ ((q - 1 : Nat) : Real) + 1 := by
              have hqn : q ≤ q - 1 + 1 := by omega
              exact_mod_cast hqn
            norm_num [‹p.1 = q›, hqcast]
          · exact Nat.floor_le hp.1.1
        · dsimp [y]
          split
          · have hqcast : (q : Real) ≤ ((q - 1 : Nat) : Real) + 1 := by
              have hqn : q ≤ q - 1 + 1 := by omega
              exact_mod_cast hqn
            norm_num [‹p.2 = q›, hqcast]
          · exact Nat.floor_le hp.1.2
      · constructor
        · dsimp [x]
          split
          · have hqcast : (q : Real) ≤ ((q - 1 : Nat) : Real) + 1 := by
              have hqn : q ≤ q - 1 + 1 := by omega
              exact_mod_cast hqn
            norm_num [‹p.1 = q›] at hqcast ⊢
            exact hqcast
          · have hf := Nat.lt_floor_add_one p.1
            have hfi : p.1 ≤ (((⌊p.1⌋₊ : Nat) : Int) : Real) + 1 := by
              norm_num
              linarith
            exact hfi
        · dsimp [y]
          split
          · have hqcast : (q : Real) ≤ ((q - 1 : Nat) : Real) + 1 := by
              have hqn : q ≤ q - 1 + 1 := by omega
              exact_mod_cast hqn
            norm_num [‹p.2 = q›] at hqcast ⊢
            exact hqcast
          · have hf := Nat.lt_floor_add_one p.2
            have hfi : p.2 ≤ (((⌊p.2⌋₊ : Nat) : Int) : Real) + 1 := by
              norm_num
              linarith
            exact hfi

theorem FordTileGeometry (q : Nat) (hq : 0 < q) :
    LatticeTile (FordTile q) ∧
      TileArea (FordTile q) = q * q := by
-- BODY
  constructor
  · unfold LatticeTile TopologicalDisk
    have realization_eq := squareRealization q hq
    let forward : (Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) →
        Set.Icc (0, 0) ((q : Real), (q : Real)) := fun p =>
      ⟨((q : Real) * (p.1.1 / 2 + 1 / 2),
        (q : Real) * (p.1.2 / 2 + 1 / 2)), by
        have hp := Metric.mem_closedBall.mp p.2
        simp? [Prod.dist_eq, Real.dist_eq] at hp
        rcases abs_le.mp hp.1 with ⟨hx1, hx2⟩
        rcases abs_le.mp hp.2 with ⟨hy1, hy2⟩
        have hqreal : (0 : Real) < q := by exact_mod_cast hq
        change (0, 0) ≤
            ((q : Real) * (p.1.1 / 2 + 1 / 2),
              (q : Real) * (p.1.2 / 2 + 1 / 2)) ∧
          ((q : Real) * (p.1.1 / 2 + 1 / 2),
              (q : Real) * (p.1.2 / 2 + 1 / 2)) ≤ ((q : Real), (q : Real))
        constructor <;> constructor <;> nlinarith⟩
    let backward : Set.Icc (0, 0) ((q : Real), (q : Real)) →
        (Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) := fun p =>
      ⟨(2 * (p.1.1 / q - 1 / 2), 2 * (p.1.2 / q - 1 / 2)), by
        simp? [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq]
        have hqreal : (0 : Real) < q := by exact_mod_cast hq
        rcases p.2 with ⟨⟨hx1, hy1⟩, ⟨hx2, hy2⟩⟩
        have hx : -(1 / 2 : Real) ≤ (p.1.1 / q - 1 / 2) ∧
            p.1.1 / q - 1 / 2 ≤ 1 / 2 := by
          constructor
          · apply (le_sub_iff_add_le).2
            apply (le_div_iff₀ hqreal).2
            nlinarith
          · apply (sub_le_iff_le_add).2
            apply (div_le_iff₀ hqreal).2
            nlinarith
        have hy : -(1 / 2 : Real) ≤ (p.1.2 / q - 1 / 2) ∧
            p.1.2 / q - 1 / 2 ≤ 1 / 2 := by
          constructor
          · apply (le_sub_iff_add_le).2
            apply (le_div_iff₀ hqreal).2
            nlinarith
          · apply (sub_le_iff_le_add).2
            apply (div_le_iff₀ hqreal).2
            nlinarith
        constructor
        · have ha := abs_le.mpr hx
          calc
            2 * |p.1.1 / q - 2⁻¹| ≤ 2 * (1 / 2) := by
              apply mul_le_mul_of_nonneg_left
              · simpa only [one_div] using ha
              · norm_num
            _ = 1 := by norm_num
        · have ha := abs_le.mpr hy
          calc
            2 * |p.1.2 / q - 2⁻¹| ≤ 2 * (1 / 2) := by
              apply mul_le_mul_of_nonneg_left
              · simpa only [one_div] using ha
              · norm_num
            _ = 1 := by norm_num⟩
    have inverse_forward : Function.LeftInverse backward forward := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      all_goals dsimp [forward, backward]
      all_goals field_simp
      all_goals ring
    have forward_inverse : Function.RightInverse backward forward := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      all_goals dsimp [forward, backward]
      all_goals field_simp
      all_goals ring
    let bridge : (Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) ≃
        Set.Icc (0, 0) ((q : Real), (q : Real)) :=
      { toFun := forward, invFun := backward, left_inv := inverse_forward,
        right_inv := forward_inverse }
    have rectangle_disk : Nonempty
        ((Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) ≃ₜ
          Set.Icc (0, 0) ((q : Real), (q : Real))) := by
      refine ⟨Homeomorph.mk bridge ?_ ?_⟩
      · change Continuous forward
        dsimp [forward]
        apply Continuous.subtype_mk
        rw [Metric.continuous_iff]
        intro b e he
        have hqreal : (0 : Real) < q := by exact_mod_cast hq
        refine ⟨2 * e / q, by positivity, ?_⟩
        intro a hab
        change dist (a : Real × Real) (b : Real × Real) < 2 * e / q at hab
        simp? [Prod.dist_eq, Real.dist_eq] at hab ⊢
        constructor
        · rw [show (q : Real) * (((a : Real × Real).1) / 2 + 2⁻¹) -
              (q : Real) * (((b : Real × Real).1) / 2 + 2⁻¹) =
              (q : Real) * (((a : Real × Real).1 - (b : Real × Real).1) / 2) by ring,
              abs_mul,
              abs_of_pos hqreal]
          calc
            (q : Real) * |((a : Real × Real).1 - (b : Real × Real).1) / 2| < q * (e / q) := by
              refine mul_lt_mul_of_pos_left ?_ hqreal
              have hh := hab.1
              rw [abs_div] at ⊢
              norm_num at ⊢
              have hs := div_lt_div_of_pos_right hh (by norm_num : (0 : Real) < 2)
              convert hs using 1; ring
            _ = e := by field_simp
        · rw [show (q : Real) * (((a : Real × Real).2) / 2 + 2⁻¹) -
              (q : Real) * (((b : Real × Real).2) / 2 + 2⁻¹) =
              (q : Real) * (((a : Real × Real).2 - (b : Real × Real).2) / 2) by ring,
              abs_mul,
              abs_of_pos hqreal]
          calc
            (q : Real) * |((a : Real × Real).2 - (b : Real × Real).2) / 2| < q * (e / q) := by
              refine mul_lt_mul_of_pos_left ?_ hqreal
              have hh := hab.2
              rw [abs_div] at ⊢
              norm_num at ⊢
              have hs := div_lt_div_of_pos_right hh (by norm_num : (0 : Real) < 2)
              convert hs using 1; ring
            _ = e := by field_simp
      · change Continuous backward
        dsimp [backward]
        apply Continuous.subtype_mk
        rw [Metric.continuous_iff]
        intro b e he
        refine ⟨e * q / 2, by positivity, ?_⟩
        intro a hab
        change dist (a : Real × Real) (b : Real × Real) < e * q / 2 at hab
        simp? [Prod.dist_eq, Real.dist_eq] at hab ⊢
        constructor
        · rw [show 2 * (((a : Real × Real).1) / q - 2⁻¹) -
              2 * (((b : Real × Real).1) / q - 2⁻¹) =
              2 * (((a : Real × Real).1 - (b : Real × Real).1) / q) by ring, abs_mul, abs_div,
              abs_of_pos (show (0 : Real) < 2 by norm_num),
              abs_of_pos (show (0 : Real) < q by exact_mod_cast hq)]
          calc
            2 * (|(a : Real × Real).1 - (b : Real × Real).1| / q) <
                2 * (e * q / 2) / q := by
              rw [← mul_div_assoc]
              refine div_lt_div_of_pos_right ?_ (by exact_mod_cast hq)
              exact mul_lt_mul_of_pos_left hab.1 (by norm_num)
            _ = e := by field_simp
        · rw [show 2 * (((a : Real × Real).2) / q - 2⁻¹) -
              2 * (((b : Real × Real).2) / q - 2⁻¹) =
              2 * (((a : Real × Real).2 - (b : Real × Real).2) / q) by ring, abs_mul, abs_div,
              abs_of_pos (show (0 : Real) < 2 by norm_num),
              abs_of_pos (show (0 : Real) < q by exact_mod_cast hq)]
          calc
            2 * (|(a : Real × Real).2 - (b : Real × Real).2| / q) <
                2 * (e * q / 2) / q := by
              rw [← mul_div_assoc]
              refine div_lt_div_of_pos_right ?_ (by exact_mod_cast hq)
              exact mul_lt_mul_of_pos_left hab.2 (by norm_num)
            _ = e := by field_simp
    exact realization_eq ▸ rectangle_disk
  · let cells : Finset (Nat × Nat) := Finset.range q ×ˢ Finset.range q
    have injective_coordinates : Function.Injective
        (fun a : Nat × Nat => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt)) := by
      intro a b hab
      apply Prod.ext
      · have h := congrArg (fun z : GaussianInt => z.re) hab
        change (a.1 : Int) = b.1 at h
        exact_mod_cast h
      · have h := congrArg (fun z : GaussianInt => z.im) hab
        change (a.2 : Int) = b.2 at h
        exact_mod_cast h
    calc
      (Finset.image (fun a : Nat × Nat =>
          (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt)) cells).card = cells.card :=
        Finset.card_image_of_injective cells injective_coordinates
      _ = q * q := by simp [cells]

end ApollonianSuperharmonic

end
