/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3LocalReroute
import LeanPool.GraphMinor.GM12.Section2PathHomotopy

/-!
# The retained pieces of a local rerouting

In the finite-graph construction for the circle-intersection step used
by XII (3.1), page 245, a first/last-contact replacement retains only
two outer subpaths. Each meets the closed set in one endpoint. Adding
the rerouted path to that set gives exactly the same carrier as adding
these two retained pieces. Thus the homotopy can be kept while the
new material is given by finitely many original subarcs.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The initial subpath up to the first contact meets the set exactly
at that contact. -/
theorem first_contact_subpath_inter_eq
    {S : Type*} [TopologicalSpace S] {F : Set S} {a b : S} (p : Path a b)
    {s : unitInterval} (hsF : p s ∈ F) (hfirst : ∀ r, r < s → p r ∉ F) :
    range (p.subpath 0 s) ∩ F = {p s} := by
  rw [Path.range_subpath_of_le p 0 s (unitInterval.nonneg s)]
  apply Subset.antisymm
  · rintro x ⟨⟨r, ⟨_, hrs⟩, rfl⟩, hrF⟩
    rcases eq_or_lt_of_le hrs with rfl | hrs
    · rfl
    · exact (hfirst r hrs hrF).elim
  · intro x hx
    have he : x = p s := hx
    rw [he]
    exact ⟨⟨s, ⟨unitInterval.nonneg s, le_rfl⟩, rfl⟩, hsF⟩

/-- The final subpath after the last contact meets the set exactly
at that contact. -/
theorem last_contact_subpath_inter_eq
    {S : Type*} [TopologicalSpace S] {F : Set S} {a b : S} (p : Path a b)
    {t : unitInterval} (htF : p t ∈ F) (hlast : ∀ r, t < r → p r ∉ F) :
    range (p.subpath t 1) ∩ F = {p t} := by
  rw [Path.range_subpath_of_le p t 1 (unitInterval.le_one t)]
  apply Subset.antisymm
  · rintro x ⟨⟨r, ⟨htr, _⟩, rfl⟩, hrF⟩
    rcases eq_or_lt_of_le htr with h | htr
    · exact congrArg p h.symm
    · exact (hlast r htr hrF).elim
  · intro x hx
    have he : x = p t := hx
    rw [he]
    exact ⟨⟨t, ⟨le_rfl, unitInterval.le_one t⟩, rfl⟩, htF⟩

/-- A local rerouting with the original endpoints preserves homotopy.
After adjoining the closed set, its carrier is exactly that of the two
retained outer subpaths, each attached at a single point. -/
theorem exists_homotopic_reroute_with_outer_pieces
    {S : Type*} [TopologicalSpace S] {F U V : Set S}
    (hF : IsClosed F) (hV : IsSimplyConnectedSet V) (hUV : U ⊆ V)
    (hFU : GM11.IsArcConnected (F ∩ U)) {a b : S} (p : Path a b)
    (hpU : range p ⊆ U) (hmeet : (p ⁻¹' F).Nonempty) :
    ∃ (s t : unitInterval) (q : Path a b), s ≤ t ∧ p.Homotopic q ∧
      F ∪ range q = F ∪ range (p.subpath 0 s) ∪ range (p.subpath t 1) ∧
      range (p.subpath 0 s) ∩ F = {p s} ∧ range (p.subpath t 1) ∩ F = {p t} := by
  obtain ⟨s, t, m, hst, hsF, htF, hm, _, hfirst, hlast⟩ :=
    exists_homotopic_local_reroute hF hV hUV hFU p hpU hmeet
  let q₀ := (p.subpath 0 s).trans (m.trans (p.subpath t 1))
  let q : Path a b := q₀.cast p.source.symm p.target.symm
  have hqr : range q = range (p.subpath 0 s) ∪ (range m ∪ range (p.subpath t 1)) := by
    change range q₀ = _
    rw [Path.trans_range, Path.trans_range]
  have hsub : ∀ r r', range (p.subpath r r') ⊆ V := by
    intro r r'
    rw [Path.range_subpath]
    exact (image_subset_range _ _).trans (hpU.trans hUV)
  have hqV : range q ⊆ V := by
    rw [hqr]
    exact union_subset (hsub 0 s) (union_subset ((hm.trans inter_subset_right).trans hUV)
      (hsub t 1))
  refine ⟨s, t, q, hst, paths_homotopic_of_range_in_simplyConnected hV p q
    (fun r => hUV (hpU (mem_range_self r))) (fun r => hqV (mem_range_self r)), ?_,
    first_contact_subpath_inter_eq p hsF hfirst, last_contact_subpath_inter_eq p htF hlast⟩
  rw [hqr]
  apply Subset.antisymm
  · rintro x (hxF | hxL | hxM | hxR)
    · exact Or.inl (Or.inl hxF)
    · exact Or.inl (Or.inr hxL)
    · exact Or.inl (Or.inl (hm hxM).1)
    · exact Or.inr hxR
  · rintro x ((hxF | hxL) | hxR)
    · exact Or.inl hxF
    · exact Or.inr (Or.inl hxL)
    · exact Or.inr (Or.inr (Or.inr hxR))

end GraphMinor.GM12
