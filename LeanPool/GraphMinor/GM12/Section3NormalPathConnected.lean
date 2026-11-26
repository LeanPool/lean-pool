/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3NormalRegionPaths
import LeanPool.GraphMinor.GM12.Section3ClosedCoverPaths
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM11.Section5b

/-!
# Paths avoiding all edge interiors

For the candidate-existence step used by XII (3.1), page 245,
closures of drawing regions form a finite closed cover of the surface.
Drawing carriers have empty interior, so this cover misses no point.
The region-path lemma joins representatives of meeting cover members
normally. Connectedness of the surface joins all representatives.
Every allowed point is either in a region or an incident vertex,
so the whole complement of the open edges is path-connected.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- In a connected closed surface, drawing vertices and points outside
the drawing form a path-connected set. Equivalently, any two points
outside the open edges can be joined by a normal path. -/
theorem isPathConnected_normal_points
    {S : Type*} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) : IsPathConnected (Γ.Uᶜ ∪ Γ.V) := by
  classical
  let : T2Space S := hS.2.1
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let I := {r : Set S // r ∈ Γ.R}
  let : Fintype I := (finite_R hS Γ).fintype
  have hcover : (⋃ i : I, closure i.val) = univ := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hxdense : x ∈ closure (⋃₀ Γ.R) := by
      apply mem_closure_iff.mpr
      intro O hO hxO
      obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := Γ) hS hO ⟨x, hxO⟩
      obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
      exact ⟨y, hyO, r, hr, hyr⟩
    rw [(finite_R hS Γ).closure_sUnion] at hxdense
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxdense
    exact mem_iUnion.mpr ⟨⟨r, hr⟩, hxr⟩
  have hex : ∀ i : I, i.val.Nonempty := fun i => region_nonempty i.property
  choose z hz using hex
  have hzN : ∀ i : I, z i ∈ Γ.Uᶜ ∪ Γ.V :=
    fun i => Or.inl (region_subset i.property (hz i))
  have hjoin : ∀ i j : I, JoinedIn (Γ.Uᶜ ∪ Γ.V) (z i) (z j) :=
    joinedIn_of_finite_closed_cover (fun i : I => closure i.val) z
      (fun _ => isClosed_closure) (fun i => ⟨z i, subset_closure (hz i)⟩) hcover hzN
      (fun i j hm => joinedIn_normal_points_of_meeting_region_closures hS Γ
        i.property j.property (hz i) (hz j) hm)
  have hanchor : ∀ x ∈ Γ.Uᶜ ∪ Γ.V, ∃ i : I, JoinedIn (Γ.Uᶜ ∪ Γ.V) x (z i) := by
    intro x hx
    rcases hx with hxU | hxV
    · obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
      let i : I := ⟨r, hr⟩
      refine ⟨i, joinedIn_normal_points_of_meeting_region_closures hS Γ hr hr hxr (hz i) ?_⟩
      exact ⟨x, subset_closure hxr, subset_closure hxr⟩
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
      exact ⟨i, joinedIn_normal_points_of_vertex_region hS Γ i.property hxV hxi (hz i)⟩
  apply isPathConnected_iff.mpr
  constructor
  · obtain ⟨x, _, hxU⟩ := exists_notMem_U (Γ := Γ) hS isOpen_univ Set.univ_nonempty
    exact ⟨x, Or.inl hxU⟩
  · intro x hx y hy
    obtain ⟨i, hxi⟩ := hanchor x hx
    obtain ⟨j, hyj⟩ := hanchor y hy
    exact hxi.trans ((hjoin i j).trans hyj.symm)

end GraphMinor.GM12
