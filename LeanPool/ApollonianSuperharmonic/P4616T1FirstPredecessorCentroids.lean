/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P4616T1FirstPredecessorCentroids]

/-!
# P4616T1FirstPredecessorCentroids

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4616T1FirstPredecessorCentroids
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T) :
    let r := cfg.firstPredecessor
    let U : Fin 4 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
      cert.P 0 false, cert.P 0 false]
    let W : Fin 4 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
      cert.P 1 true, cert.P 2 true]
    let H : Fin 4 → ProtoTile := ![
      TileTranslation (cert.P 0 false) (cert.u + cert.v),
      TileTranslation (cert.P 0 false) cert.v,
      TileTranslation (cert.P 0 true) (-cert.u - cert.v),
      TileTranslation (cert.P 0 true) (-cert.v)]
    let j : Fin 4 → Fin 3 := ![1, 2, 1, 2]
    let s : Fin 4 → Fin 4 := ![3, 0, 1, 2]
    ∀ k,
      TileCentroid (W k) - TileCentroid (U k) = (1 / 2 : Real) •
        GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (s k).val *
          (BandVectors.1 (r (j k).succ) (r 0) +
            BandVectors.1 (r 0) (r (j k).succ))) ∧
      TileCentroid (TileTranslation (U k)
        ((⟨0, 1⟩ : GaussianInt) ^ (s k).val *
          (if Even (s k).val then BandVectors.1 (r (j k).succ) (r 0)
            else BandVectors.1 (r 0) (r (j k).succ)))) =
        TileCentroid (H k) := by
-- BODY
  have hA := (cert.outer_occurrence 0 true).2.2
  have hB := (cert.outer_occurrence 0 false).2.2
  have hC := (cert.outer_occurrence 1 true).2.2
  have hD := (cert.outer_occurrence 1 false).2.2
  have hE := (cert.outer_occurrence 2 true).2.2
  have hF := (cert.outer_occurrence 2 false).2.2
  have hs := congrArg GaussianRealPoint (VectorRecursionLaws q cfg.proper.1).1
  have h20 := congrArg GaussianRealPoint cfg.firstVectorTwo
  have hf2 := congrArg GaussianRealPoint
    (((VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).2.2.2.2
      cfg.firstProper 1).1)
  have hf3 := congrArg GaussianRealPoint
    (((VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).2.2.2.2
      cfg.firstProper 2).1)
  have hqf1 := congrArg GaussianRealPoint
    (((VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper 0).1)
  have hqf2 := congrArg GaussianRealPoint
    (((VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper 1).1)
  have hqi1 := congrArg GaussianRealPoint (VectorRecursionLaws q cfg.proper.1).2.2.1
  have hqi2 := congrArg GaussianRealPoint
    (VectorRecursionLaws ![q 0, q 2, q 3, q 1]
      (SemiProperQuadruple.rotate cfg.proper.1)).2.2.1
  dsimp only
  intro k
  fin_cases k <;>
    norm_num [show Even (0 : Nat) from by decide,
      show ¬Even (1 : Nat) from by decide,
      show Even (2 : Nat) from by decide,
      show ¬Even (3 : Nat) from by decide]
  all_goals
    constructor
    all_goals
      try rw [(TileTranslationFormulas _ _).2.2.2.2.1]
      try rw [(TileTranslationFormulas _ _).2.2.2.2.1]
      apply Prod.ext
      all_goals
        simp [Prod.ext_iff, GaussianRealPoint, pow_succ, cert.period_u, cert.period_v,
          cfg.firstChild, cfg.firstParentTwo, cfg.firstParentThree] at *; linarith

end ApollonianSuperharmonic

end
