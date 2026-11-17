/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms

-- [TABLET NODE: P3055T1SignedCentroidNormalForms]

/-!
# P3055T1SignedCentroidNormalForms

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3055T1SignedCentroidNormalForms
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    let I : GaussianInt := ⟨0, 1⟩
    let U := BandVectors.1 (q 2) (q 1)
    let W := BandVectors.1 (q 3) (q 2)
    ∀ (j : Fin 3) (s : Bool),
      TileCentroid (cert.P j s) = TileCentroid T +
        (if s = true then (1 : ℝ) else -1) •
          ((1 / 2 : ℝ) • GaussianRealPoint
            (if j = 0 then (1 - I) * W
             else if j = 1 then -(1 - I) * (U + W)
             else (1 - I) * U)) := by
-- BODY
  dsimp only
  intro j s
  have hp := (cert.outer_occurrence j s).2.2
  have h13 := (P3055T1ParentVectorNormalForms q cfg).1
  fin_cases j <;> cases s
  all_goals
    norm_num [h13] at hp ⊢
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    apply Prod.ext
    all_goals
      simp [GaussianRealPoint] at hx hy ⊢
      linarith

end ApollonianSuperharmonic

end
