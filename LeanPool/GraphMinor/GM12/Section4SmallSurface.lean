/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Logic.Small.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Reducing the universe of a closed surface

The disc constructions used for XII (4.5) may be applied on a
small copy of the surface. A compact surface has a finite cover
by charts, and each chart is homeomorphic to the open unit disc.
Thus a finite disjoint union of small chart domains maps onto
the whole surface. This proves that the surface has a small
copy, without adding a size hypothesis to the theorem.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A closed surface has a copy in the lowest type universe:
compactness gives finitely many small chart domains covering
it. This permits the finite disc constructions for XII (4.5)
to be transported across universes. -/
theorem small_of_isClosedSurface {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) : Small.{0} S := by
  classical
  let : CompactSpace S := hS.1
  choose U hU hx he using hS.2.2
  have hcover : (univ : Set S) ⊆ ⋃ x, U x := fun x _ => mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let I := {x : S // x ∈ F}
  let : Fintype I := Fintype.ofFinite I
  let : Small.{0} I := small_of_injective (Fintype.equivFin I).injective
  let : ∀ i : I, Small.{0} ↥(U i.val) := fun i =>
    small_of_injective (Classical.choice (he i.val)).injective
  apply small_of_surjective (f := fun p : Σ i : I, U i.val => p.2.val)
  intro y
  obtain ⟨x, hxF, hyU⟩ := mem_iUnion₂.mp (hF (mem_univ y))
  exact ⟨⟨⟨x, hxF⟩, ⟨y, hyU⟩⟩, rfl⟩

end GraphMinor.GM12
