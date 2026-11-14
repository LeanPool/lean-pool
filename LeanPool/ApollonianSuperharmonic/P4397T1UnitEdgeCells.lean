/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.Basic

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.OpenLatticeEdge
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell

-- [TABLET NODE: P4397T1UnitEdgeCells]

/-!
# P4397T1UnitEdgeCells

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace UnitEdgeCellLemmas

private theorem hfootV :
    (∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (({a, b} :
        Finset α) = {c, d}) → (a ≠ b) → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → ∀ (U : ProtoTile), ∀
        (z : GaussianInt), ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges U ↔
        z ∈ U.cells ∨ z + 1 ∈ U.cells := by
  classical
  intro pairMatch U z
  change (∃ x ∈ U.cells,
      ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) = {x, x + 1} ∨
      _ = {x, x + ⟨0, 1⟩} ∨ _ = {x + 1, x + 1 + ⟨0, 1⟩} ∨
      _ = {x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩}) ↔ _
  constructor
  · rintro ⟨x, hx, he | he | he | he⟩
    · have hm := pairMatch x (x + 1) (z + 1) (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.re hh
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
      · have hi1 := congrArg Zsqrtd.im h1
        have hi2 := congrArg Zsqrtd.im h2
        simp only [Zsqrtd.im_add, Zsqrtd.im_one] at hi1 hi2
        omega
    · have hm := pairMatch x (x + ⟨0, 1⟩) (z + 1) (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.im hh
        simp only [Zsqrtd.im_add] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (h1 ▸ hx)
      · have hi1 := congrArg Zsqrtd.im h1
        have hi2 := congrArg Zsqrtd.im h2
        simp only [Zsqrtd.im_add, Zsqrtd.im_one] at hi1 hi2
        omega
    · have hm := pairMatch (x + 1) (x + 1 + ⟨0, 1⟩) (z + 1)
        (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.im hh
        simp only [Zsqrtd.im_add, Zsqrtd.im_one] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hbase : x = z := add_right_cancel h1
        exact Or.inl (hbase ▸ hx)
      · have hi1 := congrArg Zsqrtd.im h1
        have hi2 := congrArg Zsqrtd.im h2
        simp only [Zsqrtd.im_add, Zsqrtd.im_one] at hi1 hi2
        omega
    · have hm := pairMatch (x + ⟨0, 1⟩) (x + 1 + ⟨0, 1⟩)
        (z + 1) (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.re hh
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
  · rintro (hz | hw)
    · exact ⟨z, hz, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨z + 1, hw, Or.inr (Or.inl rfl)⟩

private theorem hboundaryV :
    (∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (({a, b} :
        Finset α) = {c, d}) → (a ≠ b) → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → ∀ (U : ProtoTile), ∀
        (z : GaussianInt), ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
        BoundaryFootprintEdges U ↔
        (z + 1 ∈ U.cells ∧ z ∉ U.cells) ∨
          (z + 1 ∉ U.cells ∧ z ∈ U.cells) := by
  classical
  intro pairMatch U z
  change (∃ a : GaussianInt,
    (({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) = {a, a + 1} ∧
      ((a ∈ U.cells ∧ a - ⟨0, 1⟩ ∉ U.cells) ∨
        (a ∉ U.cells ∧ a - ⟨0, 1⟩ ∈ U.cells))) ∨
    (({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) = {a, a + ⟨0, 1⟩} ∧
      ((a ∈ U.cells ∧ a - 1 ∉ U.cells) ∨
        (a ∉ U.cells ∧ a - 1 ∈ U.cells)))) ↔ _
  constructor
  · rintro ⟨a, he | he⟩
    · rcases he with ⟨he, hx⟩
      have hm := pairMatch a (a + 1) (z + 1) (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.re hh
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
      · have hi1 := congrArg Zsqrtd.im h1
        have hi2 := congrArg Zsqrtd.im h2
        simp only [Zsqrtd.im_add, Zsqrtd.im_one] at hi1 hi2
        omega
    · rcases he with ⟨he, hx⟩
      have hm := pairMatch a (a + ⟨0, 1⟩) (z + 1) (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.im hh
        simp only [Zsqrtd.im_add] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst a
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx
      · have hi1 := congrArg Zsqrtd.im h1
        have hi2 := congrArg Zsqrtd.im h2
        simp only [Zsqrtd.im_add, Zsqrtd.im_one] at hi1 hi2
        omega
  · rintro (hx | hx)
    · exact ⟨z + 1, Or.inr ⟨by simp, by simpa [sub_eq_add_neg] using Or.inl hx⟩⟩
    · exact ⟨z + 1, Or.inr ⟨by simp, by simpa [sub_eq_add_neg] using Or.inr hx⟩⟩

private theorem hfootH :
    (∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (({a, b} :
        Finset α) = {c, d}) → (a ≠ b) → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → ∀ (U : ProtoTile), ∀
        (z : GaussianInt), ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges U ↔
        z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells := by
  classical
  intro pairMatch U z
  change (∃ x ∈ U.cells,
      ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) = {x, x + 1} ∨
      _ = {x, x + ⟨0, 1⟩} ∨ _ = {x + 1, x + 1 + ⟨0, 1⟩} ∨
      _ = {x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩}) ↔ _
  constructor
  · rintro ⟨x, hx, he | he | he | he⟩
    · have hm := pairMatch x (x + 1) (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.re hh
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (h1 ▸ hx)
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
    · have hm := pairMatch x (x + ⟨0, 1⟩) (z + ⟨0, 1⟩)
        (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.im hh
        simp only [Zsqrtd.im_add] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
    · have hm := pairMatch (x + 1) (x + 1 + ⟨0, 1⟩)
        (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.im hh
        simp only [Zsqrtd.im_add, Zsqrtd.im_one] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
    · have hm := pairMatch (x + ⟨0, 1⟩) (x + 1 + ⟨0, 1⟩)
        (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.re hh
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hbase : x = z := add_right_cancel h1
        exact Or.inl (hbase ▸ hx)
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
  · rintro (hz | hw)
    · exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
    · exact ⟨z + ⟨0, 1⟩, hw, Or.inl (by
        ext q
        simp [add_assoc, add_comm, add_left_comm])⟩

private theorem hboundaryH :
    (∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (({a, b} :
        Finset α) = {c, d}) → (a ≠ b) → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → ∀ (U : ProtoTile), ∀
        (z : GaussianInt), ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
        BoundaryFootprintEdges U ↔
        (z + ⟨0, 1⟩ ∈ U.cells ∧ z ∉ U.cells) ∨
          (z + ⟨0, 1⟩ ∉ U.cells ∧ z ∈ U.cells) := by
  classical
  intro pairMatch U z
  change (∃ a : GaussianInt,
    (({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) = {a, a + 1} ∧
      ((a ∈ U.cells ∧ a - ⟨0, 1⟩ ∉ U.cells) ∨
        (a ∉ U.cells ∧ a - ⟨0, 1⟩ ∈ U.cells))) ∨
    (({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) = {a, a + ⟨0, 1⟩} ∧
      ((a ∈ U.cells ∧ a - 1 ∉ U.cells) ∨ (a ∉ U.cells ∧ a - 1 ∈ U.cells)))) ↔ _
  constructor
  · rintro ⟨a, he | he⟩
    · rcases he with ⟨he, hx⟩
      have hm := pairMatch a (a + 1) (z + ⟨0, 1⟩)
        (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.re hh
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst a
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
    · rcases he with ⟨he, hx⟩
      have hm := pairMatch a (a + ⟨0, 1⟩) (z + ⟨0, 1⟩)
        (z + 1 + ⟨0, 1⟩) he.symm (by
        intro hh
        have h := congrArg Zsqrtd.im hh
        simp only [Zsqrtd.im_add] at h
        omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
      · have hr1 := congrArg Zsqrtd.re h1
        have hr2 := congrArg Zsqrtd.re h2
        simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr1 hr2
        omega
  · rintro (hx | hx)
    · exact ⟨z + ⟨0, 1⟩, Or.inl ⟨by
        ext q
        simp [add_assoc, add_comm, add_left_comm],
        by simpa [sub_eq_add_neg] using Or.inl hx⟩⟩
    · exact ⟨z + ⟨0, 1⟩, Or.inl ⟨by
        ext q
        simp [add_assoc, add_comm, add_left_comm],
        by simpa [sub_eq_add_neg] using Or.inr hx⟩⟩

private theorem hsegV :
    ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells ∨ z + 1 ∈ U.cells) → ∀ t : Set.Icc (0 :
        Real) 1,
        ((1 - (t : Real)) * ((z + 1).re : Real) +
            (t : Real) * ((z + 1 + ⟨0, 1⟩).re : Real),
          (1 - (t : Real)) * ((z + 1).im : Real) +
            (t : Real) * ((z + 1 + ⟨0, 1⟩).im : Real)) ∈ TileRealization U := by
  classical
  intro U z hocc t
  rcases hocc with hz | hw
  · change _ ∈ ⋃ x ∈ U.cells, ClosedSquareRealization x
    apply Set.mem_iUnion.mpr
    refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
      Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
      Int.cast_add, Int.cast_one, Int.cast_zero]
    constructor <;> constructor <;> nlinarith [t.2.1, t.2.2]
  · change _ ∈ ⋃ x ∈ U.cells, ClosedSquareRealization x
    apply Set.mem_iUnion.mpr
    refine ⟨z + 1, Set.mem_iUnion.mpr ⟨hw, ?_⟩⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
      Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
      Int.cast_add, Int.cast_one, Int.cast_zero]
    constructor <;> constructor <;> nlinarith [t.2.1, t.2.2]

private theorem hsegH :
    ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells) → ∀ t : Set.Icc
        (0 : Real) 1,
        ((1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).re : Real) +
            (t : Real) * ((z + ⟨0, 1⟩).re : Real),
          (1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).im : Real) +
            (t : Real) * ((z + ⟨0, 1⟩).im : Real)) ∈ TileRealization U := by
  classical
  intro U z hocc t
  rcases hocc with hz | hw
  · change _ ∈ ⋃ x ∈ U.cells, ClosedSquareRealization x
    apply Set.mem_iUnion.mpr
    refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
      Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
      Int.cast_add, Int.cast_one, Int.cast_zero]
    constructor <;> constructor <;> nlinarith [t.2.1, t.2.2]
  · change _ ∈ ⋃ x ∈ U.cells, ClosedSquareRealization x
    apply Set.mem_iUnion.mpr
    refine ⟨z + ⟨0, 1⟩, Set.mem_iUnion.mpr ⟨hw, ?_⟩⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
      Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
      Int.cast_add, Int.cast_one, Int.cast_zero]
    constructor <;> constructor <;> nlinarith [t.2.1, t.2.2]

private theorem hinteriorV :
    ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → (z + 1 ∈ U.cells) → OpenLatticeEdge
        (z + 1) (z + 1 + ⟨0, 1⟩) ⊆ interior (TileRealization U) := by
  classical
  intro U z hz hw
  let R : Set (Real × Real) :=
    Set.Ioo (z.re : Real) ((z.re : Real) + 2) ×ˢ
      Set.Ioo (z.im : Real) ((z.im : Real) + 1)
  have hRopen : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hRU : R ⊆ TileRealization U := by
    intro p hp
    rcases hp with ⟨hp₁, hp₂⟩
    by_cases hx : p.1 ≤ (z.re : Real) + 1
    · apply Set.mem_iUnion.mpr
      refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
        ]
      constructor <;> constructor <;> linarith [hp₁.1, hp₁.2, hp₂.1, hp₂.2]
    · apply Set.mem_iUnion.mpr
      refine ⟨z + 1, Set.mem_iUnion.mpr ⟨hw, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
        Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
        Int.cast_add, Int.cast_one, Int.cast_zero]
      constructor <;> constructor <;> linarith [hp₁.1, hp₁.2, hp₂.1, hp₂.2]
  intro p hp
  apply interior_maximal hRU hRopen
  obtain ⟨t, ht₀, ht₁, rfl⟩ := hp
  simp [R, GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_one, Zsqrtd.im_one]
  constructor <;> constructor <;> nlinarith

private theorem hinteriorH :
    ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → (z + ⟨0, 1⟩ ∈ U.cells) →
        OpenLatticeEdge (z + 1 + ⟨0, 1⟩) (z + ⟨0, 1⟩) ⊆ interior (TileRealization U) := by
  classical
  intro U z hz hw
  let R : Set (Real × Real) :=
    Set.Ioo (z.re : Real) ((z.re : Real) + 1) ×ˢ
      Set.Ioo (z.im : Real) ((z.im : Real) + 2)
  have hRopen : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hRU : R ⊆ TileRealization U := by
    intro p hp
    rcases hp with ⟨hp₁, hp₂⟩
    by_cases hy : p.2 ≤ (z.im : Real) + 1
    · apply Set.mem_iUnion.mpr
      refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
        ]
      constructor <;> constructor <;> linarith [hp₁.1, hp₁.2, hp₂.1, hp₂.2]
    · apply Set.mem_iUnion.mpr
      refine ⟨z + ⟨0, 1⟩, Set.mem_iUnion.mpr ⟨hw, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
        Zsqrtd.re_add, Zsqrtd.im_add,
        Int.cast_add, Int.cast_one, Int.cast_zero]
      constructor <;> constructor <;> linarith [hp₁.1, hp₁.2, hp₂.1, hp₂.2]
  intro p hp
  apply interior_maximal hRU hRopen
  obtain ⟨t, ht₀, ht₁, rfl⟩ := hp
  simp [R, GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_one, Zsqrtd.im_one]
  constructor <;> constructor <;> nlinarith

private theorem hsegVrev :
    (∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells ∨ z + 1 ∈ U.cells) → ∀ t : Set.Icc (0 :
        Real) 1, ((1 - (t : Real)) * ((z + 1).re : Real) + (t : Real) * ((z + 1 + ⟨0, 1⟩).re :
        Real), (1 - (t : Real)) * ((z + 1).im : Real) + (t : Real) * ((z + 1 + ⟨0, 1⟩).im :
        Real)) ∈ TileRealization U) → ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells ∨ z +
        1 ∈ U.cells) → ∀ t : Set.Icc (0 : Real) 1,
        ((1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).re : Real) +
            (t : Real) * ((z + 1).re : Real),
          (1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).im : Real) +
            (t : Real) * ((z + 1).im : Real)) ∈ TileRealization U := by
  classical
  intro hsegV U z hocc t
  let s : Set.Icc (0 : Real) 1 :=
    ⟨1 - (t : Real), ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩
  have hs := hsegV U z hocc s
  convert hs using 1; simp [s]; ring_nf; trivial

private theorem hsegHrev :
    (∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells) → ∀ t : Set.Icc
        (0 : Real) 1, ((1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).re : Real) + (t : Real) * ((z + ⟨0,
        1⟩).re : Real), (1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).im : Real) + (t : Real) * ((z + ⟨0,
        1⟩).im : Real)) ∈ TileRealization U) → ∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈
        U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells) → ∀ t : Set.Icc (0 : Real) 1,
        ((1 - (t : Real)) * ((z + ⟨0, 1⟩).re : Real) +
            (t : Real) * ((z + 1 + ⟨0, 1⟩).re : Real),
          (1 - (t : Real)) * ((z + ⟨0, 1⟩).im : Real) +
            (t : Real) * ((z + 1 + ⟨0, 1⟩).im : Real)) ∈ TileRealization U := by
  classical
  intro hsegH U z hocc t
  let s : Set.Icc (0 : Real) 1 :=
    ⟨1 - (t : Real), ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩
  have hs := hsegH U z hocc s
  convert hs using 1; simp [s]; ring_nf; trivial

private theorem edgeSym :
    ∀ (x : GaussianInt), ∀ (y : GaussianInt), OpenLatticeEdge x y = OpenLatticeEdge y x := by
  classical
  intro x y
  ext p
  constructor
  · rintro ⟨t, ht₀, ht₁, hp⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [hp]
    simp [GaussianRealPoint]
    constructor <;> ring
  · rintro ⟨t, ht₀, ht₁, hp⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [hp]
    simp [GaussianRealPoint]
    constructor <;> ring

private theorem proveV :
    (∀ (U : ProtoTile), ∀ (z : GaussianInt), ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
        FootprintEdges U ↔ z ∈ U.cells ∨ z + 1 ∈ U.cells) → (∀ (U : ProtoTile), ∀ (z :
        GaussianInt), ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges U ↔
        (z + 1 ∈ U.cells ∧ z ∉ U.cells) ∨ (z + 1 ∉ U.cells ∧ z ∈ U.cells)) → (∀ (U : ProtoTile),
        ∀ (z : GaussianInt), (z ∈ U.cells ∨ z + 1 ∈ U.cells) → ∀ t : Set.Icc (0 : Real) 1, ((1 -
        (t : Real)) * ((z + 1).re : Real) + (t : Real) * ((z + 1 + ⟨0, 1⟩).re : Real), (1 - (t :
        Real)) * ((z + 1).im : Real) + (t : Real) * ((z + 1 + ⟨0, 1⟩).im : Real)) ∈
        TileRealization U) → (∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells) → (z + 1 ∈
        U.cells) → OpenLatticeEdge (z + 1) (z + 1 + ⟨0, 1⟩) ⊆ interior (TileRealization U)) → (∀
        (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells ∨ z + 1 ∈ U.cells) → ∀ t : Set.Icc (0
        : Real) 1, ((1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).re : Real) + (t : Real) * ((z + 1).re :
        Real), (1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).im : Real) + (t : Real) * ((z + 1).im :
        Real)) ∈ TileRealization U) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), OpenLatticeEdge
        x y = OpenLatticeEdge y x) → ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (z :
        GaussianInt), ∀ (w : GaussianInt), ((a = z + 1 ∧ b = z + 1 + ⟨0, 1⟩) ∨
        (b = z + 1 ∧ a = z + 1 + ⟨0, 1⟩)) → (w = z + 1) → ∀ (U : ProtoTile), ({a, b} ∈
            FootprintEdges U ↔ z ∈ U.cells ∨ w ∈ U.cells) ∧
      ({a, b} ∈ BoundaryFootprintEdges U ↔
        (z ∈ U.cells ∧ w ∉ U.cells) ∨ (z ∉ U.cells ∧ w ∈ U.cells)) ∧
      ((z ∈ U.cells ∨ w ∈ U.cells) →
        a ∈ FootprintVertices U ∧ b ∈ FootprintVertices U ∧
          ∀ t : Set.Icc (0 : Real) 1,
            ((1 - (t : Real)) * (a.re : Real) + (t : Real) * (b.re : Real),
              (1 - (t : Real)) * (a.im : Real) + (t : Real) * (b.im : Real)) ∈
                TileRealization U) ∧
      ((z ∈ U.cells ∧ w ∈ U.cells) →
        OpenLatticeEdge a b ⊆ interior (TileRealization U)) ∧
      ((∀ j : Fin 4, LatticeVertexIncidentCell a j ∈ U.cells) →
        z ∈ U.cells ∧ w ∈ U.cells) := by
  classical
  intro hfootV hboundaryV hsegV hinteriorV hsegVrev edgeSym a b z w hcase hw U
  rcases hcase with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · subst_vars
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using hfootV U z
    · constructor
      · intro he
        rcases (hboundaryV U z).mp he with ⟨hw, hnz⟩ | ⟨hnw, hz⟩
        · exact Or.inr ⟨hnz, hw⟩
        · exact Or.inl ⟨hz, hnw⟩
      · intro hx
        rcases hx with ⟨hz, hnw⟩ | ⟨hnz, hw⟩
        · exact (hboundaryV U z).mpr (Or.inr ⟨hnw, hz⟩)
        · exact (hboundaryV U z).mpr (Or.inl ⟨hw, hnz⟩)
    · intro hocc
      have hne : U.cells.Nonempty := by
        rcases hocc with hz | hw
        · exact ⟨z, hz⟩
        · exact ⟨z + 1, hw⟩
      constructor
      · simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        rcases hocc with hz | hw
        · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
        · exact ⟨z + 1, hw, Or.inl rfl⟩
      constructor
      · simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        rcases hocc with hz | hw
        · exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
        · exact ⟨z + 1, hw, Or.inr (Or.inr (Or.inl rfl))⟩
      · intro t
        exact hsegV U z hocc t
    · intro hb
      exact hinteriorV U z hb.1 hb.2
    · intro hall
      constructor
      · simpa [LatticeVertexIncidentCell] using hall 1
      · simpa [LatticeVertexIncidentCell] using hall 0
  · subst_vars
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Finset.pair_comm] using hfootV U z
    · constructor
      · intro he
        have he' : ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
            BoundaryFootprintEdges U := by simpa [Finset.pair_comm] using he
        rcases (hboundaryV U z).mp he' with ⟨hw, hnz⟩ | ⟨hnw, hz⟩
        · exact Or.inr ⟨hnz, hw⟩
        · exact Or.inl ⟨hz, hnw⟩
      · intro hx
        rcases hx with ⟨hz, hnw⟩ | ⟨hnz, hw⟩
        · simpa [Finset.pair_comm] using (hboundaryV U z).mpr (Or.inr ⟨hnw, hz⟩)
        · simpa [Finset.pair_comm] using (hboundaryV U z).mpr (Or.inl ⟨hw, hnz⟩)
    · intro hocc
      have hne : U.cells.Nonempty := by
        rcases hocc with hz | hw
        · exact ⟨z, hz⟩
        · exact ⟨z + 1, hw⟩
      constructor
      · simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        rcases hocc with hz | hw
        · exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
        · exact ⟨z + 1, hw, Or.inr (Or.inr (Or.inl rfl))⟩
      constructor
      · simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        rcases hocc with hz | hw
        · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
        · exact ⟨z + 1, hw, Or.inl rfl⟩
      · intro t
        exact hsegVrev U z hocc t
    · intro hb
      rw [edgeSym]
      exact hinteriorV U z hb.1 hb.2
    · intro hall
      constructor
      · simpa [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hall 2
      · simpa [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hall 3

private theorem proveH :
    (∀ (U : ProtoTile), ∀ (z : GaussianInt), ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt)
        ∈ FootprintEdges U ↔ z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells) → (∀ (U : ProtoTile), ∀ (z :
        GaussianInt), ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
        BoundaryFootprintEdges U ↔ (z + ⟨0, 1⟩ ∈ U.cells ∧ z ∉ U.cells) ∨ (z + ⟨0, 1⟩ ∉ U.cells ∧
        z ∈ U.cells)) → (∀ (U : ProtoTile), ∀ (z : GaussianInt), (z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈
        U.cells) → ∀ t : Set.Icc (0 : Real) 1, ((1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).re : Real) +
        (t : Real) * ((z + ⟨0, 1⟩).re : Real), (1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).im : Real) +
        (t : Real) * ((z + ⟨0, 1⟩).im : Real)) ∈ TileRealization U) → (∀ (U : ProtoTile), ∀ (z :
        GaussianInt), (z ∈ U.cells) → (z + ⟨0, 1⟩ ∈ U.cells) → OpenLatticeEdge (z + 1 + ⟨0, 1⟩)
        (z + ⟨0, 1⟩) ⊆ interior (TileRealization U)) → (∀ (U : ProtoTile), ∀ (z : GaussianInt),
        (z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells) → ∀ t : Set.Icc (0 : Real) 1, ((1 - (t : Real)) *
        ((z + ⟨0, 1⟩).re : Real) + (t : Real) * ((z + 1 + ⟨0, 1⟩).re : Real), (1 - (t : Real)) *
        ((z + ⟨0, 1⟩).im : Real) + (t : Real) * ((z + 1 + ⟨0, 1⟩).im : Real)) ∈ TileRealization
        U) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), OpenLatticeEdge x y = OpenLatticeEdge y
        x) → ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (z : GaussianInt), ∀ (w : GaussianInt),
        ((a = z + 1 + ⟨0, 1⟩ ∧ b = z + ⟨0, 1⟩) ∨
        (b = z + 1 + ⟨0, 1⟩ ∧ a = z + ⟨0, 1⟩)) → (w = z + ⟨0, 1⟩) → ∀ (U : ProtoTile), ({a, b} ∈
            FootprintEdges U ↔ z ∈ U.cells ∨ w ∈ U.cells) ∧
      ({a, b} ∈ BoundaryFootprintEdges U ↔
        (z ∈ U.cells ∧ w ∉ U.cells) ∨ (z ∉ U.cells ∧ w ∈ U.cells)) ∧
      ((z ∈ U.cells ∨ w ∈ U.cells) →
        a ∈ FootprintVertices U ∧ b ∈ FootprintVertices U ∧
          ∀ t : Set.Icc (0 : Real) 1,
            ((1 - (t : Real)) * (a.re : Real) + (t : Real) * (b.re : Real),
              (1 - (t : Real)) * (a.im : Real) + (t : Real) * (b.im : Real)) ∈
                TileRealization U) ∧
      ((z ∈ U.cells ∧ w ∈ U.cells) →
        OpenLatticeEdge a b ⊆ interior (TileRealization U)) ∧
      ((∀ j : Fin 4, LatticeVertexIncidentCell a j ∈ U.cells) →
        z ∈ U.cells ∧ w ∈ U.cells) := by
  classical
  intro hfootH hboundaryH hsegH hinteriorH hsegHrev edgeSym a b z w hcase hw U
  rcases hcase with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · subst_vars
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Finset.pair_comm] using hfootH U z
    · constructor
      · intro he
        have he' : ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
            BoundaryFootprintEdges U := by simpa [Finset.pair_comm] using he
        rcases (hboundaryH U z).mp he' with ⟨hw, hnz⟩ | ⟨hnw, hz⟩
        · exact Or.inr ⟨hnz, hw⟩
        · exact Or.inl ⟨hz, hnw⟩
      · intro hx
        rcases hx with ⟨hz, hnw⟩ | ⟨hnz, hw⟩
        · simpa [Finset.pair_comm] using (hboundaryH U z).mpr (Or.inr ⟨hnw, hz⟩)
        · simpa [Finset.pair_comm] using (hboundaryH U z).mpr (Or.inl ⟨hw, hnz⟩)
    · intro hocc
      have hne : U.cells.Nonempty := by
        rcases hocc with hz | hw
        · exact ⟨z, hz⟩
        · exact ⟨z + ⟨0, 1⟩, hw⟩
      constructor
      · simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        rcases hocc with hz | hw
        · exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
        · exact ⟨z + ⟨0, 1⟩, hw, Or.inr (Or.inl (by abel))⟩
      constructor
      · simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        rcases hocc with hz | hw
        · exact ⟨z, hz, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨z + ⟨0, 1⟩, hw, Or.inl rfl⟩
      · intro t
        exact hsegH U z hocc t
    · intro hb
      exact hinteriorH U z hb.1 hb.2
    · intro hall
      constructor
      · simpa [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hall 2
      · simpa [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hall 1
  · subst_vars
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Finset.pair_comm] using hfootH U z
    · constructor
      · intro he
        have he' : ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
            BoundaryFootprintEdges U := by simpa [Finset.pair_comm] using he
        rcases (hboundaryH U z).mp he' with ⟨hw, hnz⟩ | ⟨hnw, hz⟩
        · exact Or.inr ⟨hnz, hw⟩
        · exact Or.inl ⟨hz, hnw⟩
      · intro hx
        rcases hx with ⟨hz, hnw⟩ | ⟨hnz, hw⟩
        · simpa [Finset.pair_comm] using (hboundaryH U z).mpr (Or.inr ⟨hnw, hz⟩)
        · simpa [Finset.pair_comm] using (hboundaryH U z).mpr (Or.inl ⟨hw, hnz⟩)
    · intro hocc
      have hne : U.cells.Nonempty := by
        rcases hocc with hz | hw
        · exact ⟨z, hz⟩
        · exact ⟨z + ⟨0, 1⟩, hw⟩
      constructor
      · simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        rcases hocc with hz | hw
        · exact ⟨z, hz, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨z + ⟨0, 1⟩, hw, Or.inl rfl⟩
      constructor
      · simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        rcases hocc with hz | hw
        · exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
        · exact ⟨z + ⟨0, 1⟩, hw, Or.inr (Or.inl (by abel))⟩
      · intro t
        exact hsegHrev U z hocc t
    · intro hb
      rw [edgeSym]
      exact hinteriorH U z hb.1 hb.2
    · intro hall
      constructor
      · simpa [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hall 3
      · simpa [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hall 0

end UnitEdgeCellLemmas

theorem P4397T1UnitEdgeCells :
    (∀ u v : GaussianInt, FourNeighborAdjacent u v → ∃ z w : GaussianInt,
      (((u = z + 1 ∧ v = z + 1 + ⟨0, 1⟩) ∨
          (v = z + 1 ∧ u = z + 1 + ⟨0, 1⟩)) ∧ w = z + 1 ∨
        ((u = z + 1 + ⟨0, 1⟩ ∧ v = z + ⟨0, 1⟩) ∨
          (v = z + 1 + ⟨0, 1⟩ ∧ u = z + ⟨0, 1⟩)) ∧
          w = z + ⟨0, 1⟩)) ∧
    (∀ u v z w : GaussianInt,
      (((u = z + 1 ∧ v = z + 1 + ⟨0, 1⟩) ∨
          (v = z + 1 ∧ u = z + 1 + ⟨0, 1⟩)) ∧ w = z + 1 ∨
        ((u = z + 1 + ⟨0, 1⟩ ∧ v = z + ⟨0, 1⟩) ∨
          (v = z + 1 + ⟨0, 1⟩ ∧ u = z + ⟨0, 1⟩)) ∧
          w = z + ⟨0, 1⟩) →
      ∀ U : ProtoTile,
        ({u, v} ∈ FootprintEdges U ↔ z ∈ U.cells ∨ w ∈ U.cells) ∧
        ({u, v} ∈ BoundaryFootprintEdges U ↔
          (z ∈ U.cells ∧ w ∉ U.cells) ∨
            (z ∉ U.cells ∧ w ∈ U.cells)) ∧
        ((z ∈ U.cells ∨ w ∈ U.cells) →
          u ∈ FootprintVertices U ∧ v ∈ FootprintVertices U ∧
          ∀ t : Set.Icc (0 : Real) 1,
            ((1 - (t : Real)) * (u.re : Real) + (t : Real) * (v.re : Real),
              (1 - (t : Real)) * (u.im : Real) + (t : Real) * (v.im : Real)) ∈
                TileRealization U) ∧
        ((z ∈ U.cells ∧ w ∈ U.cells) →
          OpenLatticeEdge u v ⊆ interior (TileRealization U)) ∧
        ((∀ j : Fin 4, LatticeVertexIncidentCell u j ∈ U.cells) →
          z ∈ U.cells ∧ w ∈ U.cells)) := by
-- BODY
  have pairMatch {α : Type} [DecidableEq α] (a b c d : α)
      (h : ({a, b} : Finset α) = {c, d}) (hab : a ≠ b) :
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    have hacd : a = c ∨ a = d := by
      have hm : a ∈ ({c, d} : Finset α) := by rw [← h]; simp
      simpa using hm
    have hbcd : b = c ∨ b = d := by
      have hm : b ∈ ({c, d} : Finset α) := by rw [← h]; simp
      simpa using hm
    rcases hacd with hac | had
    · rcases hbcd with hbc | hbd
      · exact False.elim (hab (hac.trans hbc.symm))
      · exact Or.inl ⟨hac, hbd⟩
    · rcases hbcd with hbc | hbd
      · exact Or.inr ⟨had, hbc⟩
      · exact False.elim (hab (had.trans hbd.symm))
  constructor
  · intro u v huv
    change v = u + 1 ∨ v = u - 1 ∨ v = u + ⟨0, 1⟩ ∨ v = u - ⟨0, 1⟩ at huv
    rcases huv with h | h | h | h
    · refine ⟨u - ⟨0, 1⟩, u, ?_⟩
      right
      constructor
      · right
        constructor
        · rw [h]
          abel
        · abel
      · abel
    · refine ⟨v - ⟨0, 1⟩, v, ?_⟩
      right
      constructor
      · left
        constructor
        · rw [h]
          abel
        · abel
      · abel
    · refine ⟨u - 1, u, ?_⟩
      left
      constructor
      · left
        constructor
        · abel
        · rw [h]
          abel
      · abel
    · refine ⟨v - 1, v, ?_⟩
      left
      constructor
      · right
        constructor
        · abel
        · rw [h]
          abel
      · abel
  /-
  · intro a b z w hform U
    rcases hform with ⟨hvert, hw⟩ | ⟨hhoriz, hw⟩
    · rcases hvert with ⟨⟨hu, hv⟩ | ⟨hv, hu⟩⟩
      · subst_vars
        constructor
        · change ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges U ↔ _
          simp only [FootprintEdges, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨x, hx, he⟩
            simp only [Finset.insert_eq, Finset.mem_insert, Finset.mem_singleton] at he
            rcases he with he | he | he | he
            · have : x = z + 1 ∨ x = z + 1 + ⟨0, 1⟩ := by simpa using he
              rcases this with rfl | rfl <;> simp [add_assoc, add_comm, add_left_comm] at hx ⊢
            · have : x = z ∨ x = z + 1 + ⟨0, 1⟩ := by simpa using he
              rcases this with rfl | rfl <;> simp [add_assoc, add_comm, add_left_comm] at hx ⊢
            · have : x = z + 1 ∨ x = z + 1 + ⟨0, 1⟩ := by simpa using he
              rcases this with rfl | rfl <;> simp [add_assoc, add_comm, add_left_comm] at hx ⊢
            · have : x = z ∨ x = z + 1 + ⟨0, 1⟩ := by simpa using he
              rcases this with rfl | rfl <;> simp [add_assoc, add_comm, add_left_comm] at hx ⊢
          · rintro (hz | hw)
            · refine ⟨z, hz, ?_⟩ <;> simp [add_assoc]
            · refine ⟨z + 1, hw, ?_⟩ <;> simp [add_assoc]
        constructor
        · change ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges U ↔ _
          simp only [BoundaryFootprintEdges, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨a, ⟨he, hx⟩ | ⟨he, hx⟩⟩
            · simp only [Finset.insert_eq, Finset.mem_insert, Finset.mem_singleton] at he
              have ha : a = z + 1 := by simpa using he
              subst a
              simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx
            · simp only [Finset.insert_eq, Finset.mem_insert, Finset.mem_singleton] at he
              have : a = z + 1 := by simpa using he
              subst a
              simp at he
          · rintro (⟨hz, hw⟩ | ⟨hz, hw⟩)
            · refine ⟨z + 1, Or.inr ⟨by simp, ?_⟩⟩
              simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (show (z + 1 ∈
                  U.cells ∧ z + 1 - ⟨0, 1⟩ ∉ U.cells) ∨ _ from Or.inl ⟨hw, by simpa using hz⟩)
            · refine ⟨z + 1, Or.inr ⟨by simp, ?_⟩⟩
              simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (show (z + 1 ∈
                  U.cells ∧ z + 1 - ⟨0, 1⟩ ∉ U.cells) ∨ _ from Or.inr ⟨by simpa using hw, hz⟩)
        constructor
        · intro hocc
          constructor
          · change z + 1 ∈ FootprintVertices U
            unfold FootprintVertices
            by_cases hne : U.cells.Nonempty
            · simp only [ite_eq_left hne]
              rcases hocc with hz | hw
              · exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
              · exact ⟨z + 1, hw, Or.inl rfl⟩
            · simp [hne] at hocc
          · constructor
            · change z + 1 + ⟨0, 1⟩ ∈ FootprintVertices U
              unfold FootprintVertices
              by_cases hne : U.cells.Nonempty
              · simp only [ite_eq_left hne]
                rcases hocc with hz | hw
                · exact ⟨z, hz, Or.inr (Or.inr rfl)⟩
                · exact ⟨z + 1, hw, Or.inr (Or.inr (Or.inr rfl))⟩
              · simp [hne] at hocc
            · intro t
              intro ht
              rcases hocc with hz | hw
              · change (1 - (t : Real)) • GaussianRealPoint (z + 1) + (t : Real) •
                  GaussianRealPoint (z + 1 + ⟨0, 1⟩) ∈ _ at ht
                change _ ∈ ⋃ x ∈ U.cells, ClosedSquareRealization x
                apply Set.mem_iUnion.mpr
                refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
                simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def, GaussianRealPoint]
                    at *
                simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
                  Int.cast_add, Int.cast_one, Zsqrtd.re_zero, Zsqrtd.im_zero,
                  Int.cast_zero] at *
                rcases t with ⟨t, ht0, ht1⟩
                norm_num at ht0 ht1
                constructor <;> constructor <;> norm_num <;> nlinarith
              · change (1 - (t : Real)) • GaussianRealPoint (z + 1) + (t : Real) •
                  GaussianRealPoint (z + 1 + ⟨0, 1⟩) ∈ _ at ht
                change _ ∈ ⋃ x ∈ U.cells, ClosedSquareRealization x
                apply Set.mem_iUnion.mpr
                refine ⟨z + 1, Set.mem_iUnion.mpr ⟨hw, ?_⟩⟩
                simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def, GaussianRealPoint]
                    at *
                simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
                  Int.cast_add, Int.cast_one, Zsqrtd.re_zero, Zsqrtd.im_zero,
                  Int.cast_zero] at *
                rcases t with ⟨t, ht0, ht1⟩
                norm_num at ht0 ht1
                constructor <;> constructor <;> norm_num <;> nlinarith
        constructor
        · intro hboth
          placeholder
        · intro hall
          placeholder
      · placeholder
    · placeholder
  -/
  · intro a b z w hform U
    have hfootV (U : ProtoTile) (z : GaussianInt) :
      ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges U ↔
        z ∈ U.cells ∨ z + 1 ∈ U.cells := UnitEdgeCellLemmas.hfootV pairMatch U z
    have hboundaryV (U : ProtoTile) (z : GaussianInt) :
      ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges U ↔
        (z + 1 ∈ U.cells ∧ z ∉ U.cells) ∨
          (z + 1 ∉ U.cells ∧ z ∈ U.cells) := UnitEdgeCellLemmas.hboundaryV pairMatch U z
    have hfootH (U : ProtoTile) (z : GaussianInt) :
      ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges U ↔
        z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells := UnitEdgeCellLemmas.hfootH pairMatch U z
    have hboundaryH (U : ProtoTile) (z : GaussianInt) :
      ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges U ↔
        (z + ⟨0, 1⟩ ∈ U.cells ∧ z ∉ U.cells) ∨
          (z + ⟨0, 1⟩ ∉ U.cells ∧ z ∈ U.cells) := UnitEdgeCellLemmas.hboundaryH pairMatch U z
    have hsegV (U : ProtoTile) (z : GaussianInt)
      (hocc : z ∈ U.cells ∨ z + 1 ∈ U.cells) :
      ∀ t : Set.Icc (0 : Real) 1,
        ((1 - (t : Real)) * ((z + 1).re : Real) +
            (t : Real) * ((z + 1 + ⟨0, 1⟩).re : Real),
          (1 - (t : Real)) * ((z + 1).im : Real) +
            (t : Real) * ((z + 1 + ⟨0, 1⟩).im : Real)) ∈ TileRealization U :=
                UnitEdgeCellLemmas.hsegV U z hocc
    have hsegH (U : ProtoTile) (z : GaussianInt)
      (hocc : z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells) :
      ∀ t : Set.Icc (0 : Real) 1,
        ((1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).re : Real) +
            (t : Real) * ((z + ⟨0, 1⟩).re : Real),
          (1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).im : Real) +
            (t : Real) * ((z + ⟨0, 1⟩).im : Real)) ∈ TileRealization U :=
                UnitEdgeCellLemmas.hsegH U z hocc
    have hinteriorV (U : ProtoTile) (z : GaussianInt)
      (hz : z ∈ U.cells) (hw : z + 1 ∈ U.cells) :
      OpenLatticeEdge (z + 1) (z + 1 + ⟨0, 1⟩) ⊆ interior (TileRealization U) :=
          UnitEdgeCellLemmas.hinteriorV U z hz hw
    have hinteriorH (U : ProtoTile) (z : GaussianInt)
      (hz : z ∈ U.cells) (hw : z + ⟨0, 1⟩ ∈ U.cells) :
      OpenLatticeEdge (z + 1 + ⟨0, 1⟩) (z + ⟨0, 1⟩) ⊆ interior (TileRealization U) :=
          UnitEdgeCellLemmas.hinteriorH U z hz hw
    have hsegVrev (U : ProtoTile) (z : GaussianInt)
      (hocc : z ∈ U.cells ∨ z + 1 ∈ U.cells) :
      ∀ t : Set.Icc (0 : Real) 1,
        ((1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).re : Real) +
            (t : Real) * ((z + 1).re : Real),
          (1 - (t : Real)) * ((z + 1 + ⟨0, 1⟩).im : Real) +
            (t : Real) * ((z + 1).im : Real)) ∈ TileRealization U := UnitEdgeCellLemmas.hsegVrev
                hsegV U z hocc
    have hsegHrev (U : ProtoTile) (z : GaussianInt)
      (hocc : z ∈ U.cells ∨ z + ⟨0, 1⟩ ∈ U.cells) :
      ∀ t : Set.Icc (0 : Real) 1,
        ((1 - (t : Real)) * ((z + ⟨0, 1⟩).re : Real) +
            (t : Real) * ((z + 1 + ⟨0, 1⟩).re : Real),
          (1 - (t : Real)) * ((z + ⟨0, 1⟩).im : Real) +
            (t : Real) * ((z + 1 + ⟨0, 1⟩).im : Real)) ∈ TileRealization U :=
                UnitEdgeCellLemmas.hsegHrev hsegH U z hocc
    have edgeSym (x y : GaussianInt) : OpenLatticeEdge x y = OpenLatticeEdge y x :=
        UnitEdgeCellLemmas.edgeSym x y
    have proveV (a b z w : GaussianInt)
      (hcase : (a = z + 1 ∧ b = z + 1 + ⟨0, 1⟩) ∨
        (b = z + 1 ∧ a = z + 1 + ⟨0, 1⟩))
      (hw : w = z + 1) (U : ProtoTile) :
      ({a, b} ∈ FootprintEdges U ↔ z ∈ U.cells ∨ w ∈ U.cells) ∧
      ({a, b} ∈ BoundaryFootprintEdges U ↔
        (z ∈ U.cells ∧ w ∉ U.cells) ∨ (z ∉ U.cells ∧ w ∈ U.cells)) ∧
      ((z ∈ U.cells ∨ w ∈ U.cells) →
        a ∈ FootprintVertices U ∧ b ∈ FootprintVertices U ∧
          ∀ t : Set.Icc (0 : Real) 1,
            ((1 - (t : Real)) * (a.re : Real) + (t : Real) * (b.re : Real),
              (1 - (t : Real)) * (a.im : Real) + (t : Real) * (b.im : Real)) ∈
                TileRealization U) ∧
      ((z ∈ U.cells ∧ w ∈ U.cells) →
        OpenLatticeEdge a b ⊆ interior (TileRealization U)) ∧
      ((∀ j : Fin 4, LatticeVertexIncidentCell a j ∈ U.cells) →
        z ∈ U.cells ∧ w ∈ U.cells) := UnitEdgeCellLemmas.proveV hfootV hboundaryV hsegV
            hinteriorV hsegVrev edgeSym a b z w hcase hw U
    have proveH (a b z w : GaussianInt)
      (hcase : (a = z + 1 + ⟨0, 1⟩ ∧ b = z + ⟨0, 1⟩) ∨
        (b = z + 1 + ⟨0, 1⟩ ∧ a = z + ⟨0, 1⟩))
      (hw : w = z + ⟨0, 1⟩) (U : ProtoTile) :
      ({a, b} ∈ FootprintEdges U ↔ z ∈ U.cells ∨ w ∈ U.cells) ∧
      ({a, b} ∈ BoundaryFootprintEdges U ↔
        (z ∈ U.cells ∧ w ∉ U.cells) ∨ (z ∉ U.cells ∧ w ∈ U.cells)) ∧
      ((z ∈ U.cells ∨ w ∈ U.cells) →
        a ∈ FootprintVertices U ∧ b ∈ FootprintVertices U ∧
          ∀ t : Set.Icc (0 : Real) 1,
            ((1 - (t : Real)) * (a.re : Real) + (t : Real) * (b.re : Real),
              (1 - (t : Real)) * (a.im : Real) + (t : Real) * (b.im : Real)) ∈
                TileRealization U) ∧
      ((z ∈ U.cells ∧ w ∈ U.cells) →
        OpenLatticeEdge a b ⊆ interior (TileRealization U)) ∧
      ((∀ j : Fin 4, LatticeVertexIncidentCell a j ∈ U.cells) →
        z ∈ U.cells ∧ w ∈ U.cells) := UnitEdgeCellLemmas.proveH hfootH hboundaryH hsegH
            hinteriorH hsegHrev edgeSym a b z w hcase hw U
    rcases hform with ⟨hcase, hw⟩ | ⟨hcase, hw⟩
    · exact proveV a b z w hcase hw U
    · exact proveH a b z w hcase hw U

end ApollonianSuperharmonic

end
