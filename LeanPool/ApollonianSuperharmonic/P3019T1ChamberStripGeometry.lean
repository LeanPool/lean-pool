/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Linarith

public import LeanPool.ApollonianSuperharmonic.TriangularBoundaryStrip
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent

-- [TABLET NODE: P3019T1ChamberStripGeometry]

/-!
# P3019T1ChamberStripGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3019T1ChamberStripGeometry
    (x : Int × Int) (r s : Int) (hr : 0 < r) (hs : 0 ≤ s ∧ s ≤ r) :
    TriangularMaxIncrement x (x + (r, s)) = r ∧
    (∀ z : Int × Int, TriangularBoundaryStrip x (x + (r, s)) z ↔
      0 ≤ r * (z.2 - x.2) - s * (z.1 - x.1) ∧
        r * (z.2 - x.2) - s * (z.1 - x.1) < r) ∧
    (∀ z y : Int × Int,
      TriangularBoundaryStrip x (x + (r, s)) z →
      TriangularBoundaryStrip x (x + (r, s)) y →
      z.1 = y.1 → z = y) ∧
    (∀ z : Int × Int, TriangularBoundaryStrip x (x + (r, s)) z →
      ∀ y : Int × Int,
        (TriangularLatticeAdjacent z y ∧
          TriangularBoundaryStrip x (x + (r, s)) y) ↔
        (y = z + (1, 0) ∧ s ≤ r * (z.2 - x.2) - s * (z.1 - x.1)) ∨
        (y = z + (1, 1) ∧ r * (z.2 - x.2) - s * (z.1 - x.1) < s) ∨
        (y = z + (-1, 0) ∧ r * (z.2 - x.2) - s * (z.1 - x.1) < r - s) ∨
        (y = z + (-1, -1) ∧ r - s ≤ r * (z.2 - x.2) - s * (z.1 - x.1))) := by
-- BODY
  have hmax : TriangularMaxIncrement x (x + (r, s)) = r := by
    simp only [TriangularMaxIncrement, Prod.fst_add, Prod.snd_add]
    simp only [add_sub_cancel_left, abs_of_nonneg (le_of_lt hr),
      abs_of_nonneg hs.1, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    omega
  have hwindow : ∀ z : Int × Int,
      TriangularBoundaryStrip x (x + (r, s)) z ↔
        0 ≤ r * (z.2 - x.2) - s * (z.1 - x.1) ∧
          r * (z.2 - x.2) - s * (z.1 - x.1) < r := by
    intro z
    simp [TriangularBoundaryStrip, TriangularSignedHeight, hmax]
  refine ⟨hmax, hwindow, ?_, ?_⟩
  · intro z y hz hy he
    have hz' := (hwindow z).mp hz
    have hy' := (hwindow y).mp hy
    apply Prod.ext he
    rw [he] at hz'
    nlinarith
  · intro z hz y
    have hz' := (hwindow z).mp hz
    constructor
    · rintro ⟨hadj, hy⟩
      have hy' := (hwindow y).mp hy
      rcases hadj with he | he | he | he | he | he
      all_goals
        have he' := eq_add_of_sub_eq he
        rw [add_comm] at he'
        rw [he'] at hy'
        simp only [Prod.fst_add, Prod.snd_add] at hy'
      · exact Or.inl ⟨he', by nlinarith⟩
      · exfalso
        nlinarith
      · exact Or.inr (Or.inr (Or.inr ⟨he', by nlinarith⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨he', by nlinarith⟩))
      · exfalso
        nlinarith
      · exact Or.inr (Or.inl ⟨he', by nlinarith⟩)
    · intro hy
      rcases hy with ⟨he, hh⟩ | ⟨he, hh⟩ | ⟨he, hh⟩ | ⟨he, hh⟩
      all_goals
        subst y
        constructor
        · simp [TriangularLatticeAdjacent]
        · apply (hwindow _).mpr
          simp only [Prod.fst_add, Prod.snd_add]
          constructor <;> nlinarith

end ApollonianSuperharmonic

end
