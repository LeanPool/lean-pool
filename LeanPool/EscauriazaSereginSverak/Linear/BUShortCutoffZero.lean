/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffL2

/-!
# Cutoff data outside the scalar support

Every specified weak derivative of the cutoff field vanishes off the
closed support of its smooth scalar factor.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The cutoff field and all its specified weak derivative data vanish
outside the topological support of the scalar cutoff. -/
theorem buCut_data_zero_off_support
    (κ : Vec3 × ℝ → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (hz : z ∉ buCutSupportSet κ) :
    buCutField κ v z = 0 ∧
      buCutDw κ v Dv z = 0 ∧
      buCutD2 κ v Dv D2v z = 0 ∧
      buCutDt κ v Dtv z = 0 := by
  have hnot : parabolicHomeomorph z ∉ tsupport κ := hz
  have hscalar : buCutScalar κ z = 0 :=
    image_eq_zero_of_notMem_tsupport (f := κ) hnot
  have hsp (j : Fin 3) : spatialPartial (buCutScalar κ) j z = 0 := by
    have h := CKN.spatialPartial_eq_zero_off_tsupport hnot j
    convert h using 1
    rcases z with ⟨y, s⟩
    rfl
  have hsecond (j k : Fin 3) :
      spatialSecondPartial (buCutScalar κ) j k z = 0 := by
    have h := CKN.spatialSecondPartial_eq_zero_off_tsupport hnot j k
    convert h using 1
    rcases z with ⟨y, s⟩
    rfl
  have htime : timePartial (buCutScalar κ) z = 0 := by
    have h := CKN.timePartial_eq_zero_off_tsupport hnot
    convert h using 1
    rcases z with ⟨y, s⟩
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [buCutField, hscalar]
  · funext i j
    simp [buCutDw, hscalar, hsp]
  · funext i j k
    simp [buCutD2, hscalar, hsp, hsecond]
  · funext i
    simp [buCutDt, hscalar, htime]

end ESS
