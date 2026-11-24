/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM06.RegionCurve
import LeanPool.GraphMinor.GM06.RegionLocal
import LeanPool.GraphMinor.GM12.Section3DiscInteriorPush
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# Region curves which avoid the disc boundary internally

For the VI chain reduction in XII (3.2), pages 247--248, begin
with the region curve provided by VI's region-access construction.
Use closed-unit-disc coordinates and push the curve radially inward
by a continuous amount controlled by the distance to the complement
of the region. The amount vanishes at both endpoints. Thus the ends
stay fixed, while every other point stays in the region and avoids
the surface boundary.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM06

/-- A region of a proper disc drawing has curves between its closure
points whose internal points avoid the disc boundary. This is used
to turn VI chains into the normal chords in XII (3.2). -/
theorem exists_internal_region_curve
    {S : Type*} [TopologicalSpace S] (G : Drawing S)
    (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (r : Set S) (hr : r ∈ G.R) (p : S) (hp : p ∈ closure r)
    (q : S) (hq : q ∈ closure r) :
    ∃ γ : C(unitInterval, S), γ 0 = p ∧ γ 1 = q ∧
      ∀ t : unitInterval, 0 < t.val → t.val < 1 → γ t ∈ r ∧ γ t ∉ bd S := by
  obtain ⟨γ, hγ0, hγ1, hγr⟩ := GM06.exists_region_curve G hDisc hProper r hr p hp q hq
  obtain ⟨e⟩ := hDisc
  have hopen : IsOpen (e ⁻¹' r) := (GM06.isOpen_region ⟨e⟩ G hr).preimage e.continuous
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hopen
  let f : C(unitInterval, ClosedUnitDisc) := ⟨e.symm ∘ γ, e.symm.continuous.comp γ.continuous⟩
  have hfO : ∀ t : unitInterval, 0 < t.val → t.val < 1 → (f t).val ∈ O := by
    intro t ht0 ht1
    change f t ∈ (Subtype.val : ClosedUnitDisc → EuclideanPlane) ⁻¹' O
    rw [hOeq]
    change e (e.symm (γ t)) ∈ r
    rw [e.apply_symm_apply]
    exact hγr t ⟨ht0, ht1⟩
  obtain ⟨g, hg0, hg1, hg⟩ := exists_interior_disc_curve hO f hfO
  let ψ : C(unitInterval, S) := ⟨e ∘ g, e.continuous.comp g.continuous⟩
  have hψ0 : ψ 0 = p := by
    change e (g 0) = p
    rw [hg0]
    change e (e.symm (γ 0)) = p
    rw [e.apply_symm_apply, hγ0]
  have hψ1 : ψ 1 = q := by
    change e (g 1) = q
    rw [hg1]
    change e (e.symm (γ 1)) = q
    rw [e.apply_symm_apply, hγ1]
  refine ⟨ψ, hψ0, hψ1, ?_⟩
  intro t ht0 ht1
  obtain ⟨hgtO, hgtN⟩ := hg t ht0 ht1
  have hψr : ψ t ∈ r := by
    change g t ∈ e ⁻¹' r
    rw [← hOeq]
    exact hgtO
  refine ⟨hψr, ?_⟩
  intro hψbd
  have hbd := image_bd_homeomorph e
  rw [bd_closedUnitDisc] at hbd
  rw [← hbd] at hψbd
  obtain ⟨z, hz, hze⟩ := hψbd
  have hzg : z = g t := e.injective hze
  have hnorm : ‖(g t).val‖ = 1 := by
    rw [← hzg]
    have hz' : z.val ∈ UnitCircle := hz
    exact mem_sphere_zero_iff_norm.mp hz'
  exact hgtN.ne hnorm

end GraphMinor.GM12
