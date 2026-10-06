/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatSq

/-!
# Continuity of cutoff error coefficients

The scalar coefficients in the short-time heat error are continuous and
therefore bounded on each compact cutoff support.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The absolute scalar heat derivative of the smooth cutoff. -/
@[expose] def buShortCutoffHeatScalarSize (scale R : ℝ) (hR : 0 < R)
    (ε : ℝ) (z : ParabolicPoint) : ℝ :=
  |timePartial (buCutScalar (buShortFullCutoff scale R hR ε)) z +
    ∑ j : Fin 3,
      spatialSecondPartial
        (buCutScalar (buShortFullCutoff scale R hR ε)) j j z|

/-- The spatial derivative size of the smooth cutoff is continuous. -/
theorem buShortCutoffGradientSize_continuous
    (scale R : ℝ) (hR : 0 < R) (ε : ℝ) :
    Continuous (buShortCutoffGradientSize scale R hR ε) := by
  let κ := buShortFullCutoff scale R hR ε
  have hκ : ContDiff ℝ (⊤ : ℕ∞) κ :=
    buShortFullCutoff_smooth scale R hR ε
  have hsp (j : Fin 3) : Continuous
      (fun z : ParabolicPoint => spatialPartial (buCutScalar κ) j z) := by
    have h := (spatialPartial_contDiff hκ j).continuous.comp
      parabolicHomeomorph.continuous
    convert h using 1
    funext z
    rcases z with ⟨y, s⟩
    rfl
  change Continuous (fun z : ParabolicPoint =>
    ∑ j : Fin 3, |spatialPartial (buCutScalar κ) j z|)
  fun_prop

/-- The absolute heat derivative of the smooth cutoff is continuous. -/
theorem buShortCutoffHeatScalarSize_continuous
    (scale R : ℝ) (hR : 0 < R) (ε : ℝ) :
    Continuous (buShortCutoffHeatScalarSize scale R hR ε) := by
  let κ := buShortFullCutoff scale R hR ε
  have hκ : ContDiff ℝ (⊤ : ℕ∞) κ :=
    buShortFullCutoff_smooth scale R hR ε
  have ht : Continuous
      (fun z : ParabolicPoint => timePartial (buCutScalar κ) z) := by
    have h := (contDiff_timePartial hκ).continuous.comp
      parabolicHomeomorph.continuous
    convert h using 1
    funext z
    rcases z with ⟨y, s⟩
    rfl
  have hsp (j : Fin 3) : Continuous
      (fun z : ParabolicPoint =>
        spatialSecondPartial (buCutScalar κ) j j z) := by
    have h := (spatialPartial_contDiff
      (spatialPartial_contDiff hκ j) j).continuous.comp
        parabolicHomeomorph.continuous
    convert h using 1
    funext z
    rcases z with ⟨y, s⟩
    rfl
  change Continuous (fun z : ParabolicPoint =>
    |timePartial (buCutScalar κ) z +
      ∑ j : Fin 3, spatialSecondPartial (buCutScalar κ) j j z|)
  fun_prop

end ESS
