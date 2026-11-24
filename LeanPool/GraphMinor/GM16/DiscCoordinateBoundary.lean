/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Section6

/-!
# Boundary points at extreme coordinates

When a disc is contained below a horizontal line in the coordinate
plane, its points on that line are boundary points. Pull an interior
neighborhood back to the plane and project it to the vertical axis.
Its image is open, so it cannot have a greatest coordinate. The same
argument at a minimum gives the bottom side. These facts identify
the common boundary sides when the wall's rows are joined.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- A point of a disc with the largest allowed vertical coordinate
belongs to its intrinsic boundary. -/
theorem mem_discBd_of_vertical_max {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D)
    {f : (ℝ × ℝ) → S} (hf : Continuous f) {p : ℝ × ℝ} {c : ℝ}
    (hBound : ∀ q, f q ∈ D → q.2 ≤ c) (hp : f p ∈ D) (hpc : p.2 = c) :
    f p ∈ discBd D := by
  rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hD]
  refine ⟨subset_closure hp,?_⟩
  intro hpInt
  have hpPre : p ∈ interior (f ⁻¹' D) :=
    preimage_interior_subset_interior_preimage hf hpInt
  have hImage : Prod.snd '' (f ⁻¹' D) ⊆ Iic c := by
    rintro y ⟨q,hq,rfl⟩
    exact hBound q hq
  have hlt : p.2 ∈ interior (Iic c) := interior_mono hImage
    (isOpenMap_snd.image_interior_subset _ ⟨p,hpPre,rfl⟩)
  rw [interior_Iic] at hlt
  exact (lt_irrefl c) (hpc ▸ hlt)

/-- The corresponding assertion for the smallest vertical coordinate. -/
theorem mem_discBd_of_vertical_min {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D)
    {f : (ℝ × ℝ) → S} (hf : Continuous f) {p : ℝ × ℝ} {c : ℝ}
    (hBound : ∀ q, f q ∈ D → c ≤ q.2) (hp : f p ∈ D) (hpc : p.2 = c) :
    f p ∈ discBd D := by
  rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hD]
  refine ⟨subset_closure hp,?_⟩
  intro hpInt
  have hpPre : p ∈ interior (f ⁻¹' D) :=
    preimage_interior_subset_interior_preimage hf hpInt
  have hImage : Prod.snd '' (f ⁻¹' D) ⊆ Ici c := by
    rintro y ⟨q,hq,rfl⟩
    exact hBound q hq
  have hlt : p.2 ∈ interior (Ici c) := interior_mono hImage
    (isOpenMap_snd.image_interior_subset _ ⟨p,hpPre,rfl⟩)
  rw [interior_Ici] at hlt
  exact (lt_irrefl c) (hpc ▸ hlt)

end GraphMinor.GM16
