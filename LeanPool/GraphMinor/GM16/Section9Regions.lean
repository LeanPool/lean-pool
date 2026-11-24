/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM14.Section3

/-!
# Regions created by clearing the battlefield discs

Each cleared disc is a region of the final drawing in XVI (8.1).
The disc avoids that drawing, and its entire boundary survives. A
region meeting it cannot cross that boundary.
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Every member of a disjoint family of cleared zones is a region of
the resulting drawing, as used in XVI (8.1), Claims (4) and (8), page 72. -/
theorem zone_mem_R_clearFamily {H : Drawing S} {d : Set S → Set S → ℕ}
    {Y : Set S} {γ : ℕ} {Λ : S → Set S}
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    {y : S} (hy : y ∈ Y) : Λ y ∈ (clearEnvelopeDrawing H Y Λ).R := by
  let K := clearEnvelopeDrawing H Y Λ
  have hBd : subBd (Λ y) ⊆ K.U := zone_boundary_subset_clearFamily hZone hdis hy
  have hΛK : Disjoint (Λ y) K.U := by
    apply disjoint_left.mpr
    intro x hxΛ hxK
    have hx := (clearFamily_U hZone) ▸ hxK
    exact hx.2 (mem_iUnion₂.mpr ⟨y, hy, hxΛ⟩)
  have hyΛ : y ∈ Λ y := (hZone y hy).z_subset (mem_singleton y)
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem (Γ := K) (hΛK.notMem_of_mem_left hyΛ)
  have hΛr : Λ y ⊆ r := subset_region hr
    (hZone y hy).isOpenDisc.isPathConnected.isConnected.isPreconnected hΛK hyΛ hyr
  have hfront : frontier (closure (Λ y)) ⊆ subBd (Λ y) := by
    rw [subBd_eq_frontier]
    exact frontier_closure_subset
  have hrDis : Disjoint r (frontier (closure (Λ y))) :=
    disjoint_left.mpr fun x hxr hxfr => region_subset hr hxr (hBd (hfront hxfr))
  have hrCl : r ⊆ closure (Λ y) :=
    (subset_or_disjoint_of_frontier isClosed_closure (region_isPreconnected hr) hrDis).resolve_right
      (fun hd => hd.notMem_of_mem_left hyr (subset_closure hyΛ))
  have hrΛ : r ⊆ Λ y := by
    intro x hxr
    have hxcl := hrCl hxr
    obtain ⟨_, hcl⟩ := isOpen_disjoint_subBd_and_closure_eq (hZone y hy).isOpenDisc.1
    rw [hcl] at hxcl
    exact hxcl.resolve_right (fun hxbd => region_subset hr hxr (hBd hxbd))
  exact subset_antisymm hrΛ hΛr ▸ hr

end GraphMinor.GM16
