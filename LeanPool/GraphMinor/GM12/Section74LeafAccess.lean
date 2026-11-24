/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.RadialAccess
import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# Extending the leaf edge into its old region

The slit-disc construction for XII (7.4), pages 262--263,
continues the leaf edge by an arc into the incident region.
XI's leaf-access lemma supplies a path from the leaf whose
positive times stay in that region. Erasing repetitions gives
a line with the same ends. It meets the old drawing only at
the leaf, so it can be joined to a final segment of the edge
before constructing the lens.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- An access line from a leaf into a region touching it,
meeting the old drawing in exactly the leaf endpoint. -/
theorem exists_access_line_from_leaf
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E)
    {u v : S} (huv : u ≠ v) (hcap : closure e ∩ Γ.V = {u, v})
    (hL : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f)
    {r : Set S} (hr : r ∈ Γ.R) (hvr : v ∈ closure r) :
    ∃ (B : Set S) (z : S), IsLineWithEnds B v z ∧ z ∈ r ∧
      B \ {v} ⊆ r ∧ B ∩ Γ.U = {v} := by
  have hvCap : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
  have hvG : v ∈ Γ.U := Γ.V_subset_U hvCap.2
  obtain ⟨g, hg, hg0, hgpos⟩ := exists_path_of_leaf hS Γ he huv hcap hL hleaf hr hvr
  have hg1 : g 1 ∈ r := hgpos 1 zero_lt_one
  have hends : g 0 ≠ g 1 := by
    intro h
    exact region_subset hr hg1 (h ▸ hg0.symm ▸ hvG)
  obtain ⟨a, ha, hai, ha0, ha1, har⟩ := exists_arc_of_path hg hends
  have hline : IsLineWithEnds (range a) v (g 1) := by
    have hh := (show IsArcMap a from ⟨ha, hai⟩).isLineWithEnds
    rwa [ha0, hg0, ha1] at hh
  have hAr : range a \ {v} ⊆ r := by
    rintro x ⟨⟨s, rfl⟩, hne⟩
    obtain ⟨t, ht⟩ := har (mem_range_self s)
    have ht0 : t ≠ 0 := by
      intro heq
      exact hne (ht.symm.trans (heq ▸ hg0))
    exact ht ▸ hgpos t (lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0))
  refine ⟨range a, g 1, hline, hg1, hAr, ?_⟩
  apply Subset.antisymm
  · intro x hx
    by_contra hne
    exact region_subset hr (hAr ⟨hx.1, hne⟩) hx.2
  · refine singleton_subset_iff.mpr ⟨?_, hvG⟩
    exact ⟨0, ha0.trans hg0⟩

end GraphMinor.GM12
