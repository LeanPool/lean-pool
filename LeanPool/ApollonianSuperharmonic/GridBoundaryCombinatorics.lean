/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndex

/-!
# Combinatorics of consecutive path edges and grid boundaries

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace GridBoundaryCombinatorics

/-- Membership in consecutive pairs gives an actual adjacent-list decomposition. -/
theorem consecutivePair_decompose {α : Type*} (gridPath : List α) (a b : α)
    (hab : (a, b) ∈ gridPath.zip gridPath.tail) :
    ∃ l₁ l₂ : List α, gridPath = l₁ ++ a :: b :: l₂ := by
  rw [List.mem_iff_getElem] at hab
  rcases hab with ⟨i, hi, hab⟩
  have hi' : i < gridPath.tail.length := by
    simpa [List.length_zip] using hi
  have hi0 : i < gridPath.length := by
    simp only [List.length_tail] at hi'
    omega
  have hi1 : i + 1 < gridPath.length := by
    simp only [List.length_tail] at hi'
    omega
  rw [List.getElem_zip, List.getElem_tail] at hab
  injection hab with ha hb
  refine ⟨gridPath.take i, gridPath.drop (i + 2), ?_⟩
  calc
    gridPath = gridPath.take i ++ gridPath.drop i :=
      (List.take_append_drop i gridPath).symm
    _ = gridPath.take i ++ gridPath[i] :: gridPath.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi0]
    _ = gridPath.take i ++ gridPath[i] :: gridPath[i + 1] ::
        gridPath.drop (i + 2) := by
      rw [List.drop_eq_getElem_cons hi1]
    _ = gridPath.take i ++ a :: b :: gridPath.drop (i + 2) := by
      rw [ha, hb]

/-- Both endpoints of an edge in a closed list occur in the list. -/
theorem cyclicPair_endpoints_mem {α : Type*} (gridPath : List α) (x y : α)
    (head : gridPath.head? = some x) (last : gridPath.getLast? = some y)
    (a b : α) (hab : (a, b) ∈ gridPath.zip gridPath.tail ++ [(y, x)]) :
    a ∈ gridPath ∧ b ∈ gridPath := by
  simp only [List.mem_append, List.mem_singleton] at hab
  rcases hab with hab | hab
  · exact ⟨(List.of_mem_zip hab).1, List.mem_of_mem_tail (List.of_mem_zip hab).2⟩
  · have pair : a = y ∧ b = x := Prod.mk.inj hab
    constructor
    · rw [pair.1]
      exact List.getLast?_eq_some_iff.mp last |>.choose_spec ▸ (by simp)
    · rw [pair.2]
      rcases List.head?_eq_some_iff.mp head with ⟨l, hl⟩
      rw [hl]
      simp

/-- A crossing index supported exactly on the occupied cells detects every boundary edge. -/
theorem boundaryEdge_mem_cycle_of_index_control (T : ProtoTile)
    (gridPath : List GaussianInt) (x y : GaussianInt)
    (control : let edges := gridPath.zip gridPath.tail ++ [(y, x)]
      ∀ q : LatticeCell,
        (((q + 1, q + 1 + ⟨0, 1⟩) ∉ edges ∧
            (q + 1 + ⟨0, 1⟩, q + 1) ∉ edges) →
          GridRayCrossingIndex (q + 1) gridPath = GridRayCrossingIndex q gridPath) ∧
        (((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ edges ∧
            (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∉ edges) →
          GridRayCrossingIndex (q + ⟨0, 1⟩) gridPath = GridRayCrossingIndex q gridPath))
    (unoccupied_index_zero : ∀ q : LatticeCell, q ∉ T.cells →
      GridRayCrossingIndex q gridPath = 0)
    (occupied_index_nonzero : ∀ q : LatticeCell, q ∈ T.cells →
      GridRayCrossingIndex q gridPath ≠ 0)
    (e : Finset GaussianInt) (he : e ∈ BoundaryFootprintEdges T) :
    ∃ a b : GaussianInt, e = {a, b} ∧
      ((a, b) ∈ gridPath.zip gridPath.tail ++ [(y, x)] ∨
        (b, a) ∈ gridPath.zip gridPath.tail ++ [(y, x)]) := by
  classical
  let cyclicEdges := gridPath.zip gridPath.tail ++ [(y, x)]
  rcases he with ⟨q, (⟨rfl, hxor⟩ | ⟨rfl, hxor⟩)⟩
  · refine ⟨q, q + 1, rfl, ?_⟩
    by_contra hnone
    rw [not_or] at hnone
    have hcontrol := (control (q - ⟨0, 1⟩)).2
    have heq : GridRayCrossingIndex q gridPath =
        GridRayCrossingIndex (q - ⟨0, 1⟩) gridPath := by
      have hraw := hcontrol (by
        constructor
        · simpa [cyclicEdges, Zsqrtd.ext_iff, add_assoc, add_comm,
            add_left_comm] using hnone.2
        · simpa [cyclicEdges, Zsqrtd.ext_iff, add_assoc, add_comm,
            add_left_comm] using hnone.1)
      simpa [Zsqrtd.ext_iff] using hraw
    rcases hxor with ⟨hq, hbelow⟩ | ⟨hq, hbelow⟩
    · rw [unoccupied_index_zero (q - ⟨0, 1⟩) hbelow] at heq
      exact occupied_index_nonzero q hq heq
    · rw [unoccupied_index_zero q hq] at heq
      exact occupied_index_nonzero (q - ⟨0, 1⟩) hbelow heq.symm
  · refine ⟨q, q + ⟨0, 1⟩, rfl, ?_⟩
    by_contra hnone
    rw [not_or] at hnone
    have hcontrol := (control (q - 1)).1
    have heq : GridRayCrossingIndex q gridPath =
        GridRayCrossingIndex (q - 1) gridPath := by
      have hraw := hcontrol (by
        constructor
        · simpa [cyclicEdges, Zsqrtd.ext_iff] using hnone.1
        · simpa [cyclicEdges, Zsqrtd.ext_iff] using hnone.2)
      simpa [Zsqrtd.ext_iff] using hraw
    rcases hxor with ⟨hq, hleft⟩ | ⟨hq, hleft⟩
    · rw [unoccupied_index_zero (q - 1) hleft] at heq
      exact occupied_index_nonzero q hq heq
    · rw [unoccupied_index_zero q hq] at heq
      exact occupied_index_nonzero (q - 1) hleft heq.symm

end GridBoundaryCombinatorics

end ApollonianSuperharmonic

end
