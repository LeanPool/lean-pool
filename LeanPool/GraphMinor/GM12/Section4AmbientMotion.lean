/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section4ArcMotion
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Endpoint motion in an arbitrary closed connected surface

The ambient motion used for XII (4.3), claim (7), page 251, is
invariant under homeomorphisms. Carry the arc and the forbidden
closed set to a surface model, perform the strip slide, and
conjugate the resulting homeomorphism back.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- An ambient homeomorphism moves one end of an arc to the other
and fixes any closed set disjoint from the arc. -/
theorem exists_ambient_endpoint_motion
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a : unitInterval → S} (ha : IsArcMap a)
    {F : Set S} (hF : IsClosed F) (havoid : Disjoint (range a) F) :
    ∃ e : S ≃ₜ S, e (a 1) = a 0 ∧ ∀ x ∈ F, e x = x := by
  let : CompactSpace S := hS.1
  have hsurf : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨n, m, c, ⟨e⟩⟩ := classification S hsurf inferInstance
  let : T2Space (SurfaceModel n m c) := e.t2Space
  have hM : IsClosedSurface (SurfaceModel n m c) := by
    refine ⟨e.compactSpace, e.t2Space, ?_⟩
    intro x
    have hx := (isInteriorPoint_homeomorph_iff e (e.symm x)).mpr (hS.2.2 (e.symm x))
    simpa only [e.apply_symm_apply] using hx
  let a' : unitInterval → SurfaceModel n m c := fun t => e (a t)
  let F' : Set (SurfaceModel n m c) := e.symm ⁻¹' F
  have ha' : IsArcMap a' := ⟨e.continuous.comp ha.1, e.injective.comp ha.2⟩
  have hF' : IsClosed F' := hF.preimage e.symm.continuous
  have havoid' : Disjoint (range a') F' := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, rfl⟩ hx
    have hx' : a t ∈ F := by simpa only [F', a', mem_preimage, e.symm_apply_apply] using hx
    exact Set.disjoint_left.mp havoid (mem_range_self t) hx'
  obtain ⟨g, hgend, hgfix⟩ := exists_endpoint_motion_of_arc hM ha' hF' havoid'
  refine ⟨(e.trans g).trans e.symm, ?_, ?_⟩
  · change e.symm (g (e (a 1))) = a 0
    rw [show g (e (a 1)) = e (a 0) from hgend, e.symm_apply_apply]
  · intro x hx
    change e.symm (g (e x)) = x
    rw [hgfix (e x) (by simpa only [F', mem_preimage, e.symm_apply_apply] using hx),
      e.symm_apply_apply]

end GraphMinor.GM12
