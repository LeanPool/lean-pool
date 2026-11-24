/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.IntervalTiling
import Mathlib.Tactic.Ring

/-!
# The closed bricks cover the enclosed wall disc

Tile each full even row by `θ` width-two bricks. Tile each shortened
odd row by `θ-1` such bricks, beginning at coordinate one. Their
left bottom corners have even coordinate sum, so they are exactly
the bricks whose boundary lines the wall retains. This cover
identifies all bounded regions in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set

/-- Every point of the enclosed disc belongs to a closed brick with
valid wall coordinates and even corner parity. -/
theorem wallEnclosedSet_subset_bricks {θ : ℕ} (hθ : 2 ≤ θ)
    {p : ℝ × ℝ} (hp : p ∈ wallEnclosedSet θ) :
    ∃ i j : ℕ, i+2 < 2*θ+1 ∧ j+1 < θ ∧ Even (i+j) ∧
      p ∈ Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1) := by
  obtain ⟨j,hj,hpRow⟩ := mem_iUnion₂.mp hp
  have hjBound : j+1 < θ := by omega
  by_cases hEven : Even j
  · have hRow : p ∈ Icc (0 : ℝ) (2*(θ : ℝ)) ×ˢ Icc (j : ℝ) ((j : ℝ)+1) := by
      simpa only [wallRowRight,wallRowLeft,ite_eq_left hEven,Nat.cast_mul,Nat.cast_ofNat,sub_zero]
        using hpRow
    have hTile := rectangle_eq_union_width_two (0 : ℝ) (j : ℝ) ((j : ℝ)+1) (by omega : 1 ≤ θ)
    simp only [zero_add] at hTile
    obtain ⟨k,hk,hpBrick⟩ := mem_iUnion₂.mp (hTile ▸ hRow)
    refine ⟨2*k,j,by omega,hjBound,?_,?_⟩
    · obtain ⟨t,ht⟩ := hEven
      exact ⟨k+t,by omega⟩
    · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hpBrick
  · have hRow : p ∈ Icc (1 : ℝ) (2*(θ : ℝ)-1) ×ˢ Icc (j : ℝ) ((j : ℝ)+1) := by
      simpa only [wallRowRight,wallRowLeft,ite_eq_right hEven,Nat.cast_mul,Nat.cast_ofNat] using
        hpRow
    have hEnd : (1 : ℝ)+2*((θ-1 : ℕ) : ℝ) = 2*(θ : ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ θ),Nat.cast_one]
      ring
    have hTile := rectangle_eq_union_width_two (1 : ℝ) (j : ℝ) ((j : ℝ)+1) (by omega : 1 ≤ θ-1)
    rw [hEnd] at hTile
    obtain ⟨k,hk,hpBrick⟩ := mem_iUnion₂.mp (hTile ▸ hRow)
    refine ⟨2*k+1,j,by omega,hjBound,?_,?_⟩
    · obtain ⟨t,ht⟩ := Nat.not_even_iff_odd.mp hEven
      exact ⟨k+t+1,by omega⟩
    · have hCast : ((2*k+1 : ℕ) : ℝ) = 1+2*(k : ℝ) := by
        push_cast
        ring
      simpa only [hCast] using hpBrick

/-- Every closed brick with valid wall coordinates is contained in the
enclosed union of rows. -/
theorem wall_brick_subset_enclosedSet {θ i j : ℕ}
    (hi : i + 2 < 2 * θ + 1) (hj : j + 1 < θ) (hEven : Even (i + j)) :
    Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1) ⊆ wallEnclosedSet θ := by
  intro p hp
  apply mem_iUnion₂.mpr
  refine ⟨j,by omega,?_,hp.2⟩
  by_cases hjEven : Even j
  · simp only [wallRowLeft,wallRowRight,ite_eq_left hjEven,Nat.cast_mul,Nat.cast_ofNat,sub_zero]
    have hiReal : (i : ℝ)+2 ≤ 2*(θ : ℝ) := by
      exact_mod_cast (show i+2 ≤ 2*θ by omega)
    exact ⟨(Nat.cast_nonneg i).trans hp.1.1,hp.1.2.trans hiReal⟩
  · obtain ⟨t,ht⟩ := Nat.not_even_iff_odd.mp hjEven
    obtain ⟨s,hs⟩ := hEven
    have hiLow : 1 ≤ i := by omega
    have hiHigh : i+2 ≤ 2*θ-1 := by omega
    have hθ : 1 ≤ 2*θ := by omega
    simp only [wallRowLeft,wallRowRight,ite_eq_right hjEven,Nat.cast_mul,Nat.cast_ofNat]
    have hiLowReal : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hiLow
    have hiHighReal : (i : ℝ)+2 ≤ 2*(θ : ℝ)-1 := by
      have h := (show ((i+2 : ℕ) : ℝ) ≤ ((2*θ-1 : ℕ) : ℝ) by exact_mod_cast hiHigh)
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,Nat.cast_sub hθ] using h
    exact ⟨hiLowReal.trans hp.1.1,hp.1.2.trans hiHighReal⟩

end GraphMinor.GM16
