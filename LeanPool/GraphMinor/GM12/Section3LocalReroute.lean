/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
public import Mathlib.Topology.Subpath
import LeanPool.GraphMinor.GM12.Section3SolidConnections
import LeanPool.GraphMinor.GM12.Section2PathHomotopy
import Mathlib.Topology.Order.Compact

/-!
# A local rerouting that preserves homotopy

The circle-intersection step of the Section 8 argument used by XII
(3.1), page 245, needs a finite graph inside the original solid set.
On a short path piece, take its first and last contacts with a closed
set whose part in the patch is arc-connected. Replace the portion
between those contacts by a path in that set. Both paths stay in a
simply connected patch, so the replacement preserves the homotopy.
The two retained outer portions have no other contacts with the set.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Reroute between the first and last contacts with a closed set
inside one simply connected patch. The joining path stays in the set,
the homotopy stays in the patch, and the retained outer portions have
no other contacts. -/
theorem exists_homotopic_local_reroute
    {S : Type*} [TopologicalSpace S] {F U V : Set S}
    (hF : IsClosed F) (hV : IsSimplyConnectedSet V) (hUV : U ⊆ V)
    (hFU : IsArcConnected (F ∩ U)) {a b : S} (p : Path a b)
    (hpU : range p ⊆ U) (hmeet : (p ⁻¹' F).Nonempty) :
    ∃ (s t : unitInterval) (m : Path (p s) (p t)),
      s ≤ t ∧ p s ∈ F ∧ p t ∈ F ∧ range m ⊆ F ∩ U ∧
      (p.subpath 0 1).Homotopic ((p.subpath 0 s).trans (m.trans (p.subpath t 1))) ∧
      (∀ r, r < s → p r ∉ F) ∧ (∀ r, t < r → p r ∉ F) := by
  have hK : IsCompact (p ⁻¹' F) := (hF.preimage p.continuous).isCompact
  obtain ⟨s, hs⟩ := hK.exists_isLeast hmeet
  obtain ⟨t, ht⟩ := hK.exists_isGreatest hmeet
  have hsF : p s ∈ F := hs.1
  have htF : p t ∈ F := ht.1
  have hsU : p s ∈ U := hpU (mem_range_self s)
  have htU : p t ∈ U := hpU (mem_range_self t)
  have hpath : IsPathConnected (F ∩ U) :=
    isPathConnected_of_isArcConnected hFU ⟨p s, hsF, hsU⟩
  obtain ⟨m, hm⟩ := hpath.joinedIn (p s) ⟨hsF, hsU⟩ (p t) ⟨htF, htU⟩
  have hmrange : range m ⊆ F ∩ U := by rintro x ⟨r, rfl⟩; exact hm r
  have hsub : ∀ r r', range (p.subpath r r') ⊆ V := by
    intro r r'
    rw [Path.range_subpath]
    exact (image_subset_range _ _).trans (hpU.trans hUV)
  have hmr : range m ⊆ V := (hmrange.trans inter_subset_right).trans hUV
  have hqr : range ((p.subpath 0 s).trans (m.trans (p.subpath t 1))) ⊆ V := by
    rw [Path.trans_range, Path.trans_range]
    exact union_subset (hsub 0 s) (union_subset hmr (hsub t 1))
  refine ⟨s, t, m, hs.2 ht.1, hsF, htF, hmrange,
    paths_homotopic_of_range_in_simplyConnected hV _ _
      (fun r => hsub 0 1 (mem_range_self r)) (fun r => hqr (mem_range_self r)), ?_, ?_⟩
  · intro r hrs hrF
    exact (not_le_of_gt hrs) (hs.2 hrF)
  · intro r htr hrF
    exact (not_le_of_gt htr) (ht.2 hrF)

end GraphMinor.GM12
