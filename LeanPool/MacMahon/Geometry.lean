/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.MacMahon.Geometry.TargetZero
public import LeanPool.MacMahon.Geometry.TargetOne
public import LeanPool.MacMahon.Geometry.TargetTwo
public import LeanPool.MacMahon.Geometry.TargetThree
public import LeanPool.MacMahon.Geometry.TargetFour
public import LeanPool.MacMahon.Geometry.TargetFive

public import Mathlib.Tactic.FinCases

/-!
# Equivalence of physical faces and corner matching
-/

@[expose] public section
namespace MacMahon

theorem face_corner_equivalence : ∀ i j : Label, i ≠ j → ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt i j k) ↔ ∃ r : Fin 24, FaceFits (i, j) p k r := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact face_corner_01
  · exact face_corner_02
  · exact face_corner_03
  · exact face_corner_04
  · exact face_corner_05
  · exact face_corner_10
  · exact (hij rfl).elim
  · exact face_corner_12
  · exact face_corner_13
  · exact face_corner_14
  · exact face_corner_15
  · exact face_corner_20
  · exact face_corner_21
  · exact (hij rfl).elim
  · exact face_corner_23
  · exact face_corner_24
  · exact face_corner_25
  · exact face_corner_30
  · exact face_corner_31
  · exact face_corner_32
  · exact (hij rfl).elim
  · exact face_corner_34
  · exact face_corner_35
  · exact face_corner_40
  · exact face_corner_41
  · exact face_corner_42
  · exact face_corner_43
  · exact (hij rfl).elim
  · exact face_corner_45
  · exact face_corner_50
  · exact face_corner_51
  · exact face_corner_52
  · exact face_corner_53
  · exact face_corner_54
  · exact (hij rfl).elim

/-- Corner matching is exactly matching the exposed faces by proper rotations. -/
theorem builds_iff_physical (a : Inventory) (i j : Label) (h : i ≠ j) :
    Builds a (i, j) ↔ PhysicalBuilds a (i, j) := by
  constructor <;> rintro ⟨f, hf⟩ <;> refine ⟨f, ?_⟩ <;> intro k
  · exact (face_corner_equivalence i j h (f k).1 k).mp (hf k)
  · exact (face_corner_equivalence i j h (f k).1 k).mpr (hf k)

theorem universal_iff_physical (a : Inventory) : Universal a ↔ PhysicalUniversal a := by
  constructor <;> intro h i j hij
  · exact (builds_iff_physical a i j hij).mp (h i j hij)
  · exact (builds_iff_physical a i j hij).mpr (h i j hij)

end MacMahon
