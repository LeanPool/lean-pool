/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionArcIncidence
import LeanPool.GraphMinor.Surface.SurfaceGraph
import Mathlib.Topology.Basic

/-!
# A neighborhood where a new edge is its old edge

For the crossing discs in XII (4.5), page 253, the subdivided
edge near a meeting must agree with the original straight chord.
The other pieces form a finite closed set avoiding the meeting.
Its complement is an open neighborhood where the old edge and
the selected new piece agree.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u v

/-- A finite closed family agrees locally with one selected piece
at any point outside all the other pieces. -/
theorem exists_open_unique_piece_agreement {S : Type u} [TopologicalSpace S]
    {ι : Type v} [Finite ι] (P : ι → Set S) (hclosed : ∀ i, IsClosed (P i))
    (i : ι) (x : S) (hunique : ∀ j, j ≠ i → x ∉ P j) :
    ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ (⋃ j, P j) ∩ U = P i ∩ U := by
  classical
  let Z : Set S := ⋃ j, if j = i then ∅ else P j
  have hZ : IsClosed Z := by
    refine isClosed_iUnion_of_finite fun j => ?_
    split_ifs <;> first | exact isClosed_empty | exact hclosed j
  have hxZ : x ∉ Z := by
    intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · have hempty : x ∈ (∅ : Set S) := by simpa only [hji, ↓reduceIte] using hj
      exact hempty
    · exact hunique j hji (by simpa only [hji, ↓reduceIte] using hj)
  refine ⟨Zᶜ, hZ.isOpen_compl, hxZ, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyZ⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    by_cases hji : j = i
    · exact ⟨hji ▸ hj, hyZ⟩
    · exact False.elim (hyZ (mem_iUnion.mpr ⟨j, by simpa only [hji, ↓reduceIte] using hj⟩))
  · rintro ⟨hy, hyZ⟩
    exact ⟨mem_iUnion.mpr ⟨i, hy⟩, hyZ⟩

/-- Near its unique meeting, a subdivision piece agrees with the
old edge. This transfers the straight-chord local model to the
new edge for the crossing discs in XII (4.5), page 253. -/
theorem exists_open_subdivision_piece_agreement {k : ℕ}
    (E M : Set ℂ) (w : Fin (k + 1) → ℂ) (P : Fin k → Set ℂ)
    (hline : ∀ i, IsLineWithEnds (P i) (w i.castSucc) (w i.succ))
    (hcover : (⋃ i, P i) = E) (havoid : ∀ r, w r ∉ E ∩ M)
    (hinter : ∀ i j, i ≠ j → P i ∩ P j ⊆ range w)
    {i : Fin k} {x : ℂ} (hx : x ∈ P i ∩ (E ∩ M)) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ E ∩ U = P i ∩ U := by
  have hunique : ∀ j, j ≠ i → x ∉ P j := by
    intro j hji hxj
    obtain ⟨r, hr⟩ := hinter i j (Ne.symm hji) ⟨hx.1, hxj⟩
    apply havoid r
    rw [hr]
    exact hx.2
  obtain ⟨U, hU, hxU, hmatch⟩ := exists_open_unique_piece_agreement P
    (fun i => (hline i).isCompact.isClosed) i x hunique
  exact ⟨U, hU, hxU, hcover ▸ hmatch⟩

end GraphMinor.GM12
