/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupFields

/-!
# The rescaled pressure decomposition

The whole-space pressure is extended by zero only in time, while its harmonic
remainder is extended by zero from the original cylinder. Their sum equals the
rescaled original pressure on the rescaled source domain (`lem:pressure-split`).
-/

public section


open Set CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Time extension of the whole-space pressure from the source time interval. -/
@[expose] def blowupTimeExtendedPressure (p₁ : ParabolicPoint → ℝ) :
    ParabolicPoint → ℝ :=
  fun z => (Ioo (-1 : ℝ) 0).indicator (fun t => p₁ (z.1, t)) z.2

/-- The rescaled whole-space pressure, extended by zero only in time. -/
@[expose] def blowupRieszPressure (x₀ : Vec3) (t₀ r : ℝ)
    (p₁ : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  parabolicRescalePressure x₀ t₀ r (blowupTimeExtendedPressure p₁)

/-- The rescaled harmonic remainder of the fixed original pressure split. -/
@[expose] def blowupPressureRemainder (x₀ : Vec3) (t₀ r : ℝ)
    (p p₁ : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  parabolicRescalePressure x₀ t₀ r
    (goodPointDomain.indicator (fun z => p z - p₁ z))

/-- The fixed pressure split is preserved on the rescaled source cylinder. -/
theorem blowupPressure_eq_riesz_add_remainder_of_mem
    (x₀ : Vec3) (t₀ r : ℝ) (p p₁ : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (hz : z ∈ blowupDomain x₀ t₀ r) :
    blowupPressure x₀ t₀ r p z =
      blowupRieszPressure x₀ t₀ r p₁ z +
        blowupPressureRemainder x₀ t₀ r p p₁ z := by
  let y := parabolicTranslate x₀ t₀ (parabolicScale r z)
  have hy : y ∈ goodPointDomain := hz
  have htime : y.2 ∈ Ioo (-1 : ℝ) 0 := hy.2
  rw [blowupPressure_eq_of_mem x₀ t₀ r p z hz]
  simp only [blowupRieszPressure, blowupPressureRemainder,
    parabolicRescalePressure, blowupTimeExtendedPressure]
  rw [show parabolicTranslate x₀ t₀ (parabolicScale r z) = y from rfl,
    Set.indicator_of_mem htime, Set.indicator_of_mem hy]
  have hEta : ((y.1, y.2) : ParabolicPoint) = y := by
    cases y
    rfl
  rw [hEta]
  ring

end ESS
