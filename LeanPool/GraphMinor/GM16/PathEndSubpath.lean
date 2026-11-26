/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM16.Section5Degree

/-!
# Ends of paths inside subpaths

A subpath can contain an end of the original path only as one of its
own ends. Otherwise its two parts through that vertex supply two
different neighbors, while the original path has only one neighbor
there. This is used to join the paths in XVI (8.1), Claim (9).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09
universe u v

/-- An end of a path is never an internal vertex of one of its subpaths. -/
theorem path_start_mem_subpath_is_end {α : Type u} {β : Type v}
    {G P R : Graph α β} {a b x y : α}
    (hP : IsGraphPathWithEnds G P a b) (hR : IsGraphPathWithEnds G R x y)
    (hRP : R ≤ P) (haR : a ∈ V(R)) : a = x ∨ a = y := by
  by_cases hax : a = x
  · exact Or.inl hax
  by_cases hay : a = y
  · exact Or.inr hay
  obtain ⟨L, N, hLR, hNR, hL, hN, _, hInter, _⟩ := hR.exists_split_at haR
  obtain ⟨u, ⟨e, heu⟩, hua⟩ := path_exists_neighbor_at_start hL.symm hax
  obtain ⟨v, ⟨f, hfv⟩, hva⟩ := path_exists_neighbor_at_start hN hay
  have huP : P.Adj a u := ⟨e, (hLR.trans hRP).isLink_mono heu⟩
  have hvP : P.Adj a v := ⟨f, (hNR.trans hRP).isLink_mono hfv⟩
  have huv : u = v := path_start_neighbors_subsingleton hP huP hvP
  have huBoth : u ∈ V(L) ∩ V(N) := ⟨heu.right_mem, huv.symm ▸ hfv.right_mem⟩
  have hua' : u = a := mem_singleton_iff.mp (hInter ▸ huBoth)
  exact False.elim (hua hua')

/-- A subpath meets the two original ends only at its own ends. -/
theorem subpath_inter_ends_subset {α : Type u} {β : Type v}
    {G P R : Graph α β} {a b x y : α}
    (hP : IsGraphPathWithEnds G P a b) (hR : IsGraphPathWithEnds G R x y)
    (hRP : R ≤ P) : V(R) ∩ ({a, b} : Set α) ⊆ {x, y} := by
  rintro z ⟨hzR, rfl | hz⟩
  · exact path_start_mem_subpath_is_end hP hR hRP hzR
  · rw [mem_singleton_iff] at hz
    subst z
    exact path_start_mem_subpath_is_end hP.symm hR hRP hzR

end GraphMinor.GM16
