/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.LatticeLines
import Mathlib.Tactic.Linarith

/-!
# Intersections of unit lattice lines

Distinct parallel unit lines can meet only at their ends. A horizontal
and a vertical line can meet only at the lattice point formed by their
fixed coordinates. These checks ensure that the planar wall edges in
XVI (4.2), page 53, meet only at the prescribed grid vertices.
-/

public section
namespace GraphMinor.GM16
open Set

/-- Two different horizontal unit lines meet only at an end of the
first one. -/
theorem horizontalLatticeLine_inter {i j k l : ℕ} (hne : (i, j) ≠ (k, l))
    {x : ℝ × ℝ} (hx : x ∈ horizontalLatticeLine i j ∩ horizontalLatticeLine k l) :
    x = latticePoint (i,j) ∨ x = latticePoint (i+1,j) := by
  have hj : j = l := Nat.cast_injective ((show x.2 = (j : ℝ) from hx.1.2).symm.trans hx.2.2)
  have hiLo : (i : ℝ) ≤ x.1 := hx.1.1.1
  have hiHi : x.1 ≤ (i : ℝ) + 1 := hx.1.1.2
  have hkLo : (k : ℝ) ≤ x.1 := hx.2.1.1
  have hkHi : x.1 ≤ (k : ℝ) + 1 := hx.2.1.2
  rcases lt_trichotomy i k with hik | hik | hki
  · have hNat : i + 1 ≤ k := by omega
    have hReal : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hNat
    right
    apply Prod.ext
    · have hEq : x.1 = (i : ℝ) + 1 := by linarith
      simpa only [latticePoint,Nat.cast_add,Nat.cast_one] using hEq
    · exact hx.1.2
  · exact (hne (Prod.ext hik hj)).elim
  · have hNat : k + 1 ≤ i := by omega
    have hReal : (k : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hNat
    left
    exact Prod.ext (by change x.1 = (i : ℝ); linarith) hx.1.2

/-- Two different vertical unit lines meet only at an end of the
first one. -/
theorem verticalLatticeLine_inter {i j k l : ℕ} (hne : (i, j) ≠ (k, l))
    {x : ℝ × ℝ} (hx : x ∈ verticalLatticeLine i j ∩ verticalLatticeLine k l) :
    x = latticePoint (i,j) ∨ x = latticePoint (i,j+1) := by
  have hne' : (j,i) ≠ (l,k) := fun heq => hne
    (Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))
  have hSwap : Prod.swap x ∈ horizontalLatticeLine j i ∩ horizontalLatticeLine l k :=
    ⟨⟨hx.1.2,hx.1.1⟩,⟨hx.2.2,hx.2.1⟩⟩
  rcases horizontalLatticeLine_inter hne' hSwap with h | h
  · left
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · right
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

/-- A horizontal and a vertical unit line meet at a lattice point. -/
theorem horizontal_vertical_LatticeLine_inter {i j k l : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ horizontalLatticeLine i j ∩ verticalLatticeLine k l) :
    x = latticePoint (k,j) := Prod.ext hx.2.1 hx.1.2

end GraphMinor.GM16
