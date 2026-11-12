/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow
public import LeanPool.ApollonianSuperharmonic.BandOriginalOccurrenceIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex
public import LeanPool.ApollonianSuperharmonic.P3055T1ExteriorCentralIncidence
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms
public import LeanPool.ApollonianSuperharmonic.P3055T1SignedCentroidNormalForms
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: BandOrderedGeneralSelectedContactRowExists]

/-!
# BandOrderedGeneralSelectedContactRowExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralSelectedContactRowExists
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    ∀ (a b : PeriodicSubtileIndex),
      (a = ⟨.A, -1, -1⟩ ∨ a = ⟨.A, 0, -1⟩ ∨
       a = ⟨.C, 1, 0⟩ ∨ a = ⟨.C, 1, 1⟩ ∨
       a = ⟨.E, 0, 1⟩ ∨ a = ⟨.E, -1, 0⟩ ∨
       a = ⟨.B, 1, 1⟩ ∨ a = ⟨.B, 0, 1⟩ ∨
       a = ⟨.D, -1, 0⟩ ∨ a = ⟨.D, -1, -1⟩ ∨
       a = ⟨.F, 0, -1⟩ ∨ a = ⟨.F, 1, 0⟩) →
      (b = ⟨.A, 0, 0⟩ ∨ b = ⟨.B, 0, 0⟩ ∨
       b = ⟨.C, 0, 0⟩ ∨ b = ⟨.D, 0, 0⟩ ∨
       b = ⟨.E, 0, 0⟩ ∨ b = ⟨.F, 0, 0⟩) →
      (FootprintEdges (occurrence a) ∩ FootprintEdges (occurrence b)).Nonempty →
      Nonempty (BandOrderedGeneralSelectedContactRow q cfg C₀ T cert a b) := by
-- BODY
  classical
  intro occurrence a b ha hb hedge
  have hab : a ≠ b := by
    intro he
    subst b
    rcases ha with h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst a <;> simp at hb
  have hinc : AllowedSubtileIncidence a b :=
    (BandOriginalOccurrenceIntersectionClassification q cfg C₀ T cert
      a b hab).1 hedge
  obtain ⟨_, _, h31, _, h01, h02, _, hr2, hr3, ht1⟩ :=
    P3055T1ParentVectorNormalForms q cfg
  have hcent := P3055T1SignedCentroidNormalForms q cfg C₀ T cert
  dsimp only at hcent
  have translated (U : ProtoTile) (z : GaussianInt) :
      TileCentroid (TileTranslation U z) = TileCentroid U + GaussianRealPoint z :=
    (TileTranslationFormulas U z).2.2.2.2.1
  rcases P3055T1ExteriorCentralIncidence a b ha hb hinc with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveL1 (by decide +kernel) ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveS1 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, hr2]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveL2 (by decide +kernel) ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, h31]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveS2 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, hr3]
    apply Prod.ext <;> simp [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveL3 (by decide +kernel) ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveS3 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, ht1]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveS4 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, hr2]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveS5 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, hr3]
    apply Prod.ext <;> simp [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.positiveS6 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, ht1]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedL1 (by decide +kernel) ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedS1 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, hr2]
    apply Prod.ext <;> simp [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedL2 (by decide +kernel) ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, h31]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedS2 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, hr3]
    apply Prod.ext <;> simp [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedL3 (by decide +kernel) ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02]
    apply Prod.ext <;> simp [GaussianRealPoint,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedS3 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, ht1]
    apply Prod.ext <;> simp [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedS4 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, hr2]
    apply Prod.ext <;> simp [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedS5 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, hr3]
    apply Prod.ext <;> simp [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
  · refine ⟨BandOrderedGeneralSelectedContactRow.reflectedS6 ?_⟩
    simp only [SubtileOccurrenceInterpretation, translated, hcent,
      cert.period_u, cert.period_v, h01, h02, ht1]
    apply Prod.ext <;> simp [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring

end ApollonianSuperharmonic

end
