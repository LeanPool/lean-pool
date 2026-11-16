/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate

/-!
# BandLayoutFaceSupport

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandLayoutFaceSupport

/-- Shared firstFace fact. -/
theorem firstFace :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face), (∀ (h :
            cert.modified.plane.Face), ((∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i
            = a) ∧ ∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i = c) → h = f ∨ h = g)
            → (f1 = f ∨ f1 = g) ) := by
  classical
  intro q cfg C₀ T cert a c f1 f g hfaces
  apply hfaces
  constructor
  · exact ⟨0, by simp [f1, a, cert.modified_face_vertices, SixSubtileFaceVertices]⟩
  · exact ⟨2, by simp [f1, c, cert.modified_face_vertices, SixSubtileFaceVertices]⟩

/-- Shared thirdFace fact. -/
theorem thirdFace :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face), (∀ (h :
            cert.modified.plane.Face), ((∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i
            = a) ∧ ∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i = c) → h = f ∨ h = g)
            → (f3 = f ∨ f3 = g) ) := by
  classical
  intro q cfg C₀ T cert a c f3 f g hfaces
  apply hfaces
  constructor
  · exact ⟨0, by simp [f3, a, cert.modified_face_vertices, SixSubtileFaceVertices]⟩
  · exact ⟨1, by simp [f3, c, cert.modified_face_vertices, SixSubtileFaceVertices]⟩

end BandLayoutFaceSupport
end ApollonianSuperharmonic

end
