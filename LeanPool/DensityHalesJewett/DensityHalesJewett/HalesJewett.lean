/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ShelahHalesJewett.HalesJewett

/-!
# The multidimensional Hales--Jewett theorem with Shelah's bound

`Combinatorics.Line.exists_mono_of_card_eq_shelahBound`, from the `ShelahHalesJewett` project, is
the Hales--Jewett theorem in a dimension of cardinality `Combinatorics.Line.shelahBound`. Here it
is applied to the alphabet `η → α` to find a monochromatic subspace of dimension `η` over `α`.
-/

@[expose] public section

namespace Combinatorics.Subspace

/-- The multidimensional Hales--Jewett theorem with an explicit dimension: a subspace of dimension
`η` over `α` is a line over the alphabet `η → α`. -/
theorem exists_mono_of_card_eq {α κ η ι : Type*} [Fintype α] [Fintype κ] [Fintype η] [Fintype ι]
    (h : Fintype.card ι =
      Line.shelahBound (Fintype.card α ^ Fintype.card η) (Fintype.card κ) * Fintype.card η)
    (C : (ι → α) → κ) : ∃ V : Subspace η α ι, V.IsMono C := by
  classical
  set N := Line.shelahBound (Fintype.card α ^ Fintype.card η) (Fintype.card κ) with hN
  let e : Fin N × η ≃ ι := Fintype.equivOfCardEq (by simp [h])
  obtain ⟨l, hl⟩ := Line.exists_mono_of_card_eq_shelahBound (α := η → α) (ι := Fin N)
    (by simp [hN]) fun x ↦ C fun i ↦ x (e.symm i).1 (e.symm i).2
  refine ⟨l.toSubspace.reindex (Equiv.refl _) (Equiv.refl _) e, ?_⟩
  rw [reindex_isMono, Line.toSubspace_isMono]
  exact hl

end Combinatorics.Subspace
