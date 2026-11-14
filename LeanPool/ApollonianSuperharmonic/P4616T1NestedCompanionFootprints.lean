/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality

-- [TABLET NODE: P4616T1NestedCompanionFootprints]

/-!
# P4616T1NestedCompanionFootprints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4616T1NestedCompanionFootprints
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T) :
    let a := BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)
    FootprintVertices (TileTranslation (cert.P 1 true)
        ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * a)) =
      FootprintVertices (cert.Q 1 true) ∧
    FootprintVertices (TileTranslation (cert.P 1 false)
        ((⟨0, 1⟩ : GaussianInt) * a)) =
      FootprintVertices (cert.S 1 false) := by
-- BODY
  have hA := (cert.outer_occurrence 0 true).2.2
  have hB := (cert.outer_occurrence 0 false).2.2
  have hC := (cert.outer_occurrence 1 true).2.2
  have hD := (cert.outer_occurrence 1 false).2.2
  have hQ := (cert.plus_occurrence 1 true).2.2
  have hS := (cert.minus_occurrence 1 false).2.2
  have hr := congrArg GaussianRealPoint
    (VectorRecursionLaws
      ![cfg.firstPredecessor 0, cfg.firstPredecessor 3,
        cfg.firstPredecessor 1, cfg.firstPredecessor 2]
      (SemiProperQuadruple.rotate
        (SemiProperQuadruple.rotate cfg.firstProper.1))).2.2.1
  have hf := congrArg GaussianRealPoint
    (((VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).2.2.2.2
      cfg.firstProper 2).1)
  have hQband : BandPrototile (q 2) (cert.Q 1 true) := by
    simpa [cfg.firstParentTwo] using (cert.plus_occurrence 1 true).1
  have hSband : BandPrototile (q 2) (cert.S 1 false) := by
    simpa [cfg.firstParentTwo] using (cert.minus_occurrence 1 false).1
  dsimp only
  constructor
  · obtain ⟨hc, ha⟩ := BandPrototileCentroidUnique (q 2)
      (TileTranslation (cert.P 1 true) ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
        BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)))
      (cert.Q 1 true)
      (BandPrototileTranslation _ _ _ (cert.outer_occurrence 1 true).1) hQband
      (by
        rw [(TileTranslationFormulas _ _).2.2.2.2.1]
        apply Prod.ext <;>
          simp [Prod.ext_iff, GaussianRealPoint, pow_succ, cfg.secondVectorOne,
            cfg.firstChild, cfg.firstParentTwo, cfg.firstParentThree] at * <;>
          linarith)
    exact (ProtoTileObservableExtensionality _ _ hc ha).1
  · obtain ⟨hc, ha⟩ := BandPrototileCentroidUnique (q 2)
      (TileTranslation (cert.P 1 false) ((⟨0, 1⟩ : GaussianInt) *
        BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)))
      (cert.S 1 false)
      (BandPrototileTranslation _ _ _ (cert.outer_occurrence 1 false).1) hSband
      (by
        rw [(TileTranslationFormulas _ _).2.2.2.2.1]
        apply Prod.ext <;>
          simp [Prod.ext_iff, GaussianRealPoint, cfg.secondVectorOne,
            cfg.firstChild, cfg.firstParentTwo, cfg.firstParentThree] at * <;>
          linarith)
    exact (ProtoTileObservableExtensionality _ _ hc ha).1

end ApollonianSuperharmonic

end
