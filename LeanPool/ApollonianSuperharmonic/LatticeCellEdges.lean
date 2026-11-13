/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeCell
public import Mathlib.Data.Finset.Insert

/-!
# Lattice cell edges

Shared elementary edge identities adapted from Wesley Pegden's Apache-2.0
Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic.LatticeCellEdges

/-- A horizontal edge determines its lower-real-coordinate endpoint. -/
theorem horizontal_unique (x y : GaussianInt)
    (h : ({x, x + 1} : Finset GaussianInt) = {y, y + 1}) : x = y := by
  have hx : x = y ∨ x = y + 1 := by
    have : x ∈ ({y, y + 1} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hy : y = x ∨ y = x + 1 := by
    have : y ∈ ({x, x + 1} : Finset GaussianInt) := by rw [h]; simp
    simpa using this
  rcases hx with hxy | hxy
  · exact hxy
  rcases hy with hyx | hyx
  · exact hyx.symm
  · exfalso
    have hre := congrArg Zsqrtd.re hxy
    have hre' := congrArg Zsqrtd.re hyx
    norm_num at hre hre'
    omega

/-- A vertical edge determines its lower-imaginary-coordinate endpoint. -/
theorem vertical_unique (x y : GaussianInt)
    (h : ({x, x + (⟨0, 1⟩ : GaussianInt)} : Finset GaussianInt) =
      {y, y + (⟨0, 1⟩ : GaussianInt)}) : x = y := by
  have hx : x = y ∨ x = y + (⟨0, 1⟩ : GaussianInt) := by
    have : x ∈ ({y, y + (⟨0, 1⟩ : GaussianInt)} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hy : y = x ∨ y = x + (⟨0, 1⟩ : GaussianInt) := by
    have : y ∈ ({x, x + (⟨0, 1⟩ : GaussianInt)} : Finset GaussianInt) := by rw [h]; simp
    simpa using this
  rcases hx with hxy | hxy
  · exact hxy
  rcases hy with hyx | hyx
  · exact hyx.symm
  · exfalso
    have him := congrArg Zsqrtd.im hxy
    have him' := congrArg Zsqrtd.im hyx
    simp at him him'
    omega

/-- A horizontal edge cannot equal a vertical edge. -/
theorem horizontal_ne_vertical (x y : GaussianInt) :
    ({x, x + 1} : Finset GaussianInt) ≠ {y, y + (⟨0, 1⟩ : GaussianInt)} := by
  intro h
  have hx : x = y ∨ x = y + (⟨0, 1⟩ : GaussianInt) := by
    have : x ∈ ({y, y + (⟨0, 1⟩ : GaussianInt)} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hx1 : x + 1 = y ∨ x + 1 = y + (⟨0, 1⟩ : GaussianInt) := by
    have : x + 1 ∈ ({y, y + (⟨0, 1⟩ : GaussianInt)} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  rcases hx with hx | hx <;> rcases hx1 with hx1 | hx1
  all_goals
    have hre := congrArg Zsqrtd.re hx
    have him := congrArg Zsqrtd.im hx
    have hre1 := congrArg Zsqrtd.re hx1
    have him1 := congrArg Zsqrtd.im hx1
    simp at hre him hre1 him1
    omega

/-- A lattice edge has a unique base point and horizontal/vertical direction tag. -/
theorem edge_encoding_injective :
    Function.Injective (fun p : GaussianInt × Bool =>
      if p.2 then ({p.1, p.1 + ⟨0, 1⟩} : Finset GaussianInt) else {p.1, p.1 + 1}) := by
  rintro ⟨z, b⟩ ⟨w, d⟩ h
  cases b <;> cases d
  · exact Prod.ext (horizontal_unique z w h) rfl
  · exact (horizontal_ne_vertical z w h).elim
  · exact (horizontal_ne_vertical w z h.symm).elim
  · exact Prod.ext (vertical_unique z w h) rfl

end ApollonianSuperharmonic.LatticeCellEdges

end
