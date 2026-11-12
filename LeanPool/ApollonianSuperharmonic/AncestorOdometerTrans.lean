/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.AncestorTile

-- [TABLET NODE: AncestorOdometerTrans]

/-!
# AncestorOdometerTrans

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem AncestorOdometerTrans
    (C₁ C₂ C₃ : CircleCoordinates) (T₁ T₂ T₃ : ProtoTile)
    (h₁ h₂ h₃ : PartialOdometer)
    (h12 : AncestorOdometer C₁ C₂ T₁ T₂ h₁ h₂)
    (h23 : AncestorOdometer C₂ C₃ T₂ T₃ h₂ h₃) :
    AncestorOdometer C₁ C₃ T₁ T₃ h₁ h₃ := by
-- BODY
  rcases h12 with ⟨hO2, hT12, hdom1, hsub12, hval12⟩
  rcases h23 with ⟨hO3, hT23, hdom2, hsub23, hval23⟩
  refine ⟨hO3, hT12.trans hT23, hdom1, hsub12.trans hsub23, ?_⟩
  intro x hx
  rw [hval12 x hx, hval23 x (hsub12 hx)]

end ApollonianSuperharmonic

end
