/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4261T1PlacedOdometer
public import LeanPool.ApollonianSuperharmonic.P3055T1SignedCentroidNormalForms
public import LeanPool.ApollonianSuperharmonic.P4387T1ParentSlopeNormalForms
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P4387T1PlacedCoordinates]

/-!
# P4387T1PlacedCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4387T1PlacedCoordinates
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T₀ : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (h₀ : PartialOdometer) (C : BandCircle) (T : ProtoTile)
    (h : PartialOdometer) (a : PeriodicSubtileIndex)
    (pa : P4261T1PlacedOdometer cert h₀ C T h a) :
    let F := fun (J V W : GaussianInt) (x : PeriodicSubtileIndex) =>
      (1 / 2 : ℝ) • GaussianRealPoint
        (match x.label with
        | .A => (1 - J) * W | .B => -((1 - J) * W)
        | .C => -((1 - J) * (V + W)) | .D => (1 - J) * (V + W)
        | .E => (1 - J) * V | .F => -((1 - J) * V)) +
      GaussianRealPoint
        ((x.first : GaussianInt) * (V - J * (V + W)) +
          (x.second : GaussianInt) * (W + J * V))
    TileCentroid T = TileCentroid T₀ +
      F ⟨0, 1⟩ (BandVectors.1 (q 2) (q 1)) (BandVectors.1 (q 3) (q 2)) a ∧
    pa.slope = pa.rootSlope +
      F (-⟨0, 1⟩) (BandVectors.2 (q 2) (q 1)) (BandVectors.2 (q 3) (q 2)) a := by
-- BODY
  dsimp only
  have vc := P3055T1SignedCentroidNormalForms q cfg C₀ T₀ cert
  have vf := P3055T1ParentVectorNormalForms q cfg
  have af := P4387T1ParentSlopeNormalForms q cfg
  dsimp only at vc vf af
  have translated (X : ProtoTile) (z : GaussianInt) :
      TileCentroid (TileTranslation X z) =
        TileCentroid X + GaussianRealPoint z := by
    rw [(TileTranslationFormulas X z).2.2.2.2.1]
    rfl
  constructor
  · rw [pa.centroid]
    cases hl : a.label <;>
      simp only [SubtileOccurrenceInterpretation, hl, translated]
    all_goals
      rw [vc, cert.period_u, cert.period_v, vf.2.2.2.2.1, vf.2.2.2.2.2.1]
      apply Prod.ext <;>
        simp [GaussianRealPoint, -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;>
        ring
  · have hs := pa.slope_offset
    cases hl : a.label <;> simp only [hl] at hs ⊢
    all_goals
      simp? [af.1, af.2.2.2.2.1, af.2.2.2.2.2.1] at hs
      have h₁ := congrArg Prod.fst hs
      have h₂ := congrArg Prod.snd hs
      apply Prod.ext
      all_goals
        simp [P4250T1SlopeOffset, GaussianRealPoint,
          -GaussianInt.intCast_re, -GaussianInt.intCast_im] at h₁ h₂ ⊢
        linarith

end ApollonianSuperharmonic

end
