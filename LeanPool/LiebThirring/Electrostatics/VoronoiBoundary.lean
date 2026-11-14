/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.VoronoiBasic

/-!
# Voronoi boundary decomposition and volume partition

Strict faces partition each Voronoi boundary up to triple-tie strata.
-/

public section

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LiebThirring

variable {M : ℕ}

/-- A closest nucleus fails to be uniquely closest exactly when another nucleus ties it. -/
theorem exists_tie_of_mem_closed_not_mem_cell (R : Fin M → Position)
    (k : Fin M) {x : Position} (hx : x ∈ closedVoronoiCell R k)
    (hn : x ∉ voronoiCell R k) :
    ∃ l, l ≠ k ∧ dist x (R k) = dist x (R l) := by
  classical
  change ¬ ∀ l, l ≠ k → dist x (R k) < dist x (R l) at hn
  push Not at hn
  obtain ⟨l, hl, he⟩ := hn
  exact ⟨l, hl, (hx l).antisymm he⟩

theorem closedVoronoiCells_cover (R : Fin M → Position) (hM : 0 < M) :
    (⋃ k, closedVoronoiCell R k) = univ := by
  classical
  have : NeZero M := ⟨Nat.ne_of_gt hM⟩
  apply eq_univ_of_forall
  intro x
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ
    (fun k : Fin M => dist x (R k)) Finset.univ_nonempty
  exact mem_iUnion.mpr ⟨k, fun l => hk l (Finset.mem_univ l)⟩

/-- Outside all open cells, two closest nuclei tie. -/
theorem exists_nearest_tie_of_not_mem_cells (R : Fin M → Position) (hM : 0 < M)
    {x : Position} (hx : x ∉ ⋃ k, voronoiCell R k) :
    ∃ k l, k ≠ l ∧ x ∈ closedVoronoiCell R k ∧
      dist x (R k) = dist x (R l) := by
  have hcover : x ∈ ⋃ k, closedVoronoiCell R k := by rw [closedVoronoiCells_cover R hM]; trivial
  obtain ⟨k, hk⟩ := mem_iUnion.mp hcover
  have hn : x ∉ voronoiCell R k := fun hc => hx (mem_iUnion.mpr ⟨k, hc⟩)
  obtain ⟨l, hl, he⟩ := exists_tie_of_mem_closed_not_mem_cell R k hk hn
  exact ⟨k, l, hl.symm, hk, he⟩

theorem volume_bisectorPlane (R : Fin M → Position) (hR : Function.Injective R)
    {k l : Fin M} (hkl : k ≠ l) :
    volume (bisectorPlane R k l : Set Position) = 0 := by
  apply Measure.addHaar_affineSubspace volume
  change AffineSubspace.perpBisector (R k) (R l) ≠ ⊤
  simpa only [Ne, AffineSubspace.perpBisector_eq_top] using hR.ne hkl

/-- The disjoint open cells cover ambient space up to a volume-null set. -/
theorem volume_compl_voronoiCells (R : Fin M → Position)
    (hR : Function.Injective R) (hM : 0 < M) :
    volume (⋃ k, voronoiCell R k)ᶜ = 0 := by
  classical
  let T : Set Position := ⋃ k : Fin M, ⋃ l : {l : Fin M // k ≠ l},
    (bisectorPlane R k l : Set Position)
  have hnull : volume T = 0 :=
    measure_iUnion_null fun k => measure_iUnion_null fun l => volume_bisectorPlane R hR l.property
  apply measure_mono_null _ hnull
  intro x hx
  obtain ⟨k, l, hkl, _, heq⟩ := exists_nearest_tie_of_not_mem_cells R hM hx
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨l, hkl⟩,
    (mem_bisectorPlane R k l x).mpr heq⟩⟩

end LiebThirring

end
