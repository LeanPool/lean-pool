/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallRigidity
import LeanPool.GraphMinor.GM16.WallFaceDiscs
import LeanPool.GraphMinor.GM16.RigidDiscFaces

/-!
# Rigidity for drawings with the wall's support

The disc-face and common-line geometry of the wall depends on its
support rather than its marked vertices. A drawing obtained by
putting more vertices on its edge lines has the same regions and
face closures. The disc-face criterion therefore proves rigidity
for the subdivision drawing in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM14

/-- Any drawing with the support of the coordinate wall is rigid.
This includes the subdivisions in the last paragraph of XVI (4.2). -/
theorem sphereWall_same_support_isRigid {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ)
    (f : (ℝ × ℝ) → S) (hf : IsOpenEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {D : Drawing S} (hSupport : D.U=Γ.drawing.U) : IsRigid D := by
  have hR : D.R=Γ.drawing.R := congrArg (fun U => componentsIn (univ \ U)) hSupport
  apply isRigid_of_disc_faces hS
  · intro r hr
    have hFace := sphereWall_disc_faces hS hSphere (by omega : 2≤θ) hEven f hf.isEmbedding Γ hV hE
      (hR ▸ hr)
    simpa only [hSupport] using hFace
  · intro r hr s hs hne a b hab ha hb
    exact sphereWall_face_join_lines hS hSphere hθ hEven f hf Γ hV hE
      r (hR ▸ hr) s (hR ▸ hs) hne a b hab ha hb

end GraphMinor.GM16
