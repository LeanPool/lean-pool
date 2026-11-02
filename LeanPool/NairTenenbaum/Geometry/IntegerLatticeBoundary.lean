/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Geometry.IntegerLatticeCells
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit

/-! # Bounding lattice discrepancy by cells meeting the boundary

For every bounded set, the difference between its volume and its number of
integer lattice points is at most the number of mixed unit cells. Each such
cell contains a boundary point within distance one of its lattice corner.
-/

@[expose] public section

namespace NairTenenbaum

open Finset MeasureTheory

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem integerLatticePoint_mem_cell (m : ι → ℤ) :
    integerLatticePoint m ∈ integerLatticeCell m := by
  apply mem_integerLatticeCell.mpr
  intro i
  change (m i : ℝ) ≤ m i ∧ (m i : ℝ) < (m i : ℝ) + 1
  exact ⟨le_rfl, by linarith⟩

omit [Fintype ι] in
theorem integerLatticeCell_isPreconnected (m : ι → ℤ) : IsPreconnected (integerLatticeCell m) :=
  (convex_pi (𝕜 := ℝ) (fun _ _ => convex_Ico _ _)).isPreconnected

omit [Fintype ι] in
theorem integerLatticeCell_inter_frontier {s : Set (ι → ℝ)} {m : ι → ℤ}
    (hin : (integerLatticeCell m ∩ s).Nonempty) (hout : ¬ integerLatticeCell m ⊆ s) :
    (integerLatticeCell m ∩ frontier s).Nonempty := by
  obtain ⟨x, hxc, hxs⟩ := hin
  obtain ⟨y, hyc, hys⟩ := Set.not_subset.mp hout
  rw [frontier_eq_closure_inter_closure]
  apply isPreconnected_closed_iff.mp (integerLatticeCell_isPreconnected m)
    (closure s) (closure sᶜ) isClosed_closure isClosed_closure
  · intro z _
    by_cases hz : z ∈ s
    · exact Or.inl (subset_closure hz)
    · exact Or.inr (subset_closure hz)
  · exact ⟨x, hxc, subset_closure hxs⟩
  · exact ⟨y, hyc, subset_closure hys⟩

omit [Fintype ι] in
theorem exists_finset_integerLattice_outer_cells [Finite ι] {s : Set (ι → ℝ)}
    (hs : Bornology.IsBounded s) :
    ∃ O : Finset (ι → ℤ), ∀ m, m ∈ O ↔ (integerLatticeCell m ∩ s).Nonempty := by
  classical
  cases nonempty_fintype ι
  obtain ⟨R, hR, hbound⟩ := hs.exists_pos_norm_le
  let B := Fintype.piFinset (fun _i : ι => Icc ⌈-(R + 1)⌉ ⌊R + 1⌋)
  have hmem (m : ι → ℤ) (hm : (integerLatticeCell m ∩ s).Nonempty) : m ∈ B := by
    obtain ⟨x, hxc, hxs⟩ := hm
    have hnorm : ‖integerLatticePoint m‖ ≤ R + 1 := by
      have H := dist_triangle (integerLatticePoint m) x 0
      rw [dist_zero_right, dist_zero_right] at H
      have Hd := integerLatticeCell_dist_le_one hxc
      rw [dist_comm] at Hd
      linarith [hbound x hxs]
    apply Fintype.mem_piFinset.mpr
    intro i
    have Hi := (norm_le_pi_norm (integerLatticePoint m) i).trans hnorm
    change ‖(m i : ℝ)‖ ≤ R + 1 at Hi
    rw [Real.norm_eq_abs, abs_le] at Hi
    exact mem_Icc.mpr ⟨Int.ceil_le.mpr Hi.1, Int.le_floor.mpr Hi.2⟩
  refine ⟨B.filter (fun m => (integerLatticeCell m ∩ s).Nonempty), fun m => ?_⟩
  exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hmem m h, h⟩⟩

theorem exists_integerLattice_boundary_error {s : Set (ι → ℝ)} (hs : Bornology.IsBounded s) :
    ∃ A B : Finset (ι → ℤ),
      (∀ m, m ∈ A ↔ integerLatticePoint m ∈ s) ∧
      |(A.card : ℝ) - volume.real s| ≤ (B.card : ℝ) ∧
      ∀ m ∈ B, ∃ x ∈ frontier s, dist (integerLatticePoint m) x ≤ 1 := by
  classical
  obtain ⟨O, hO⟩ := exists_finset_integerLattice_outer_cells hs
  let A := O.filter (fun m => integerLatticePoint m ∈ s)
  let I := O.filter (fun m => integerLatticeCell m ⊆ s)
  have hAmem (m : ι → ℤ) : m ∈ A ↔ integerLatticePoint m ∈ s := by
    constructor
    · exact fun h => (mem_filter.mp h).2
    · intro h
      exact mem_filter.mpr ⟨(hO m).mpr ⟨_, integerLatticePoint_mem_cell m, h⟩, h⟩
  have hIA : I ⊆ A := by
    intro m hm
    exact (hAmem m).mpr ((mem_filter.mp hm).2 (integerLatticePoint_mem_cell m))
  have hAO : A ⊆ O := filter_subset _ _
  have hinside : integerLatticeCellUnion I ⊆ s := by
    intro x hx
    obtain ⟨m, hm, hxc⟩ := Set.mem_iUnion₂.mp hx
    exact (mem_filter.mp hm).2 hxc
  have houtside : s ⊆ integerLatticeCellUnion O := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨(fun i => ⌊x i⌋),
      (hO _).mpr ⟨x, mem_integerLatticeCell_floor x, hx⟩, mem_integerLatticeCell_floor x⟩
  refine ⟨A, O \ I, hAmem, latticeCell_volume_discrepancy_le I A O hIA hAO hinside houtside, ?_⟩
  intro m hm
  obtain ⟨hmO, hmI⟩ := mem_sdiff.mp hm
  have hnot : ¬ integerLatticeCell m ⊆ s := fun h => hmI (mem_filter.mpr ⟨hmO, h⟩)
  obtain ⟨x, hxc, hxf⟩ := integerLatticeCell_inter_frontier ((hO m).mp hmO) hnot
  exact ⟨x, hxf, by simpa only [dist_comm] using integerLatticeCell_dist_le_one hxc⟩

end NairTenenbaum
