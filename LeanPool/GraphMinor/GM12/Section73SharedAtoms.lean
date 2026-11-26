/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section77
public import LeanPool.GraphMinor.GM12.Section73Tangle
import LeanPool.GraphMinor.GM11.Theorem75
import LeanPool.GraphMinor.GM11.PaintingFacts
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Shared atoms miss the merged region

For XII (7.3)(i), page 262, an atom shared by the old and
deleted drawings misses the merged region. Otherwise it would
equal that region as a new atom. Since it contains the deleted
vertex, its old atom would then be just that vertex. An open
disc cannot be a singleton: it contains a closed disc with an
infinite boundary circle.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Atoms shared by the two drawings miss the merged region,
as used in XII (7.3)(i), page 262. Two-cellness rules out the
only possible exception, a region consisting of the deleted vertex. -/
theorem shared_atom_disjoint_deleted_region
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r)
    {a : Set S} (ha : a ∈ Γ.A ∩ (deleteVertices Γ {v}).A) : Disjoint a r := by
  apply disjoint_left.mpr
  intro x hxa hxr
  have har : a = r := atom_eq_of_inter_nonempty ha.2 (Or.inr hr) ⟨x, hxa, hxr⟩
  have hva : v ∈ a := har.symm ▸ hvr
  have hav : a = {v} := atom_eq_of_inter_nonempty ha.1 (Or.inl (Or.inl ⟨v, hv, rfl⟩))
    ⟨v, hva, rfl⟩
  have hrSingle : r = {v} := har.symm.trans hav
  obtain ⟨D, hD, hDr, _⟩ := exists_closedDisc_of_isCompact (htwo.2 r hr) isCompact_singleton
    (singleton_subset_iff.mpr hvr)
  have hInfinite := infinite_of_isOArc hD.isOArc_discBd
  apply hInfinite
  apply (finite_singleton v).subset
  exact (Surface.discBd_subset D).trans (hDr.trans hrSingle.subset)

end GraphMinor.GM12
