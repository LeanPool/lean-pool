/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3LocalReroute
public import LeanPool.GraphMinor.GM12.Section3ManifoldPatch
import LeanPool.GraphMinor.Surface.Cuffs

/-!
# A finite partition into rerouting patches

The circle-intersection step used by XII (3.1), page 245, replaces
short curve pieces while staying in the original union. A solid set is
arc-connected in a small open neighbourhood of each of its points.
Shrink inside a simply connected manifold patch. Off the solid set,
use its closedness to choose a disjoint neighbourhood. Pull this open
cover back to the unit interval and take a finite monotone partition.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Near each point, a solid set is arc-connected in an open subset
of a simply connected manifold patch. Away from the set this condition
holds for the empty intersection. -/
theorem exists_reroute_patch_of_solid
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsSolid F) (x : S) :
    ∃ U V : Set S, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧
      IsSimplyConnectedSet V ∧ IsArcConnected (F ∩ U) := by
  obtain ⟨V, hV, hxV, hsc⟩ := exists_simplyConnected_patch_of_isManifoldPoint (hS.2.2 x)
  by_cases hxF : x ∈ F
  · obtain ⟨U, hUV, hxU, hU, hArc⟩ := hF.1 x hxF V hV hxV
    exact ⟨U, V, hU, hxU, hUV, hsc, hArc⟩
  · refine ⟨V ∩ Fᶜ, V, hV.inter hF.2.isOpen_compl, ⟨hxV, hxF⟩,
      inter_subset_left, hsc, ?_⟩
    intro a ha
    exact (ha.2.2 ha.1).elim

/-- Every path has a finite monotone partition whose pieces stay in
rerouting patches for a fixed solid set. Each patch supplies the two
premises needed for homotopy-preserving first/last-contact replacement. -/
theorem exists_finite_reroute_partition
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsSolid F) {a b : S} (p : Path a b) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval), t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      Monotone t ∧ ∀ i : Fin n, ∃ U V : Set S,
        IsOpen U ∧ U ⊆ V ∧ IsSimplyConnectedSet V ∧ IsArcConnected (F ∩ U) ∧
        range (p.subpath (t i.castSucc) (t i.succ)) ⊆ U := by
  classical
  choose U V hU hxU hUV hsc hArc using exists_reroute_patch_of_solid hS hF
  let O : S → Set unitInterval := fun x => p ⁻¹' U x
  have hO : ∀ x, IsOpen (O x) := fun x => (hU x).preimage p.continuous
  have hcover : (univ : Set unitInterval) ⊆ ⋃ x, O x := by
    intro r _
    exact mem_iUnion.mpr ⟨p r, hxU (p r)⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hpieces⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hO hcover
  let s : Fin (n + 1) → unitInterval := fun i => t i.val
  refine ⟨n, s, ht0, hn n le_rfl, fun i j hij => hmono hij, ?_⟩
  intro i
  obtain ⟨x, hx⟩ := hpieces i.val
  refine ⟨U x, V x, hU x, hUV x, hsc x, hArc x, ?_⟩
  have hle : s i.castSucc ≤ s i.succ := hmono (Nat.le_succ i.val)
  rw [Path.range_subpath_of_le p _ _ hle]
  rintro y ⟨r, hr, rfl⟩
  exact hx hr

end GraphMinor.GM12
