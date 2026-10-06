/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification

/-!
# Fourier symbols for the force pressure

The force pressure symbol has order minus one. Its spatial gradient is the
bounded orthogonal projection onto the frequency direction.
-/

public section

open MeasureTheory
open scoped FourierTransform
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The order-one scalar force-pressure symbol in `lem:force-pressure`,
defined to be zero at the origin. -/
@[expose]
def forcePressureMultiplierSymbol (ξ : L2Vec3) (v : ComplexVec3) : ℂ :=
  if ξ = 0 then 0 else
    -Complex.I * inner ℂ (complexifyFrequency ξ) v /
      ((2 * Real.pi * ‖ξ‖ ^ 2 : ℝ) : ℂ)

/-- The frequency symbol of the spatial gradient of the force pressure. -/
@[expose]
def forcePressureGradientSymbol (ξ : L2Vec3) (v : ComplexVec3) : ComplexVec3 :=
  if ξ = 0 then 0 else
    ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (complexifyFrequency ξ) v) •
      complexifyFrequency ξ

/-- The force-pressure gradient symbol is measurable in frequency and input. -/
theorem forcePressureGradientSymbol_measurable :
    Measurable (fun p : L2Vec3 × ComplexVec3 =>
      forcePressureGradientSymbol p.1 p.2) := by
  have hformula : (fun p : L2Vec3 × ComplexVec3 =>
      forcePressureGradientSymbol p.1 p.2) = fun p =>
      p.2 - lerayApplyFormula p.1 p.2 := by
    funext p
    by_cases hξ : p.1 = 0
    · simp [forcePressureGradientSymbol, lerayApplyFormula,
        inverseFrequencyNormSq, hξ, complexifyFrequency]
    · simp [forcePressureGradientSymbol, lerayApplyFormula,
        inverseFrequencyNormSq, hξ]
  rw [hformula]
  exact measurable_snd.sub lerayApplyFormula_measurable

/-- The force-pressure gradient symbol is bounded by twice the input norm. -/
theorem forcePressureGradientSymbol_norm_le (ξ : L2Vec3) (v : ComplexVec3) :
    ‖forcePressureGradientSymbol ξ v‖ ≤ 2 * ‖v‖ := by
  have hformula : forcePressureGradientSymbol ξ v = v - lerayApplyFormula ξ v := by
    by_cases hξ : ξ = 0
    · subst ξ
      simp [forcePressureGradientSymbol, lerayApplyFormula,
        inverseFrequencyNormSq, complexifyFrequency]
    · simp [forcePressureGradientSymbol, lerayApplyFormula,
        inverseFrequencyNormSq, hξ]
  rw [hformula]
  calc
    ‖v - lerayApplyFormula ξ v‖ ≤ ‖v‖ + ‖lerayApplyFormula ξ v‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + ‖v‖ := by
      gcongr
      rw [← leraySymbol_apply_eq_formula]
      exact leraySymbol_norm_le ξ v
    _ = 2 * ‖v‖ := by ring

/-- Differentiating the scalar order-one symbol gives the bounded projection
onto the frequency direction. -/
theorem forcePressureMultiplierSymbol_spatialDeriv (ξ : L2Vec3)
    (v : ComplexVec3) (k : Fin 3) :
    (2 * Real.pi * Complex.I : ℂ) * (ξ k : ℂ) *
        forcePressureMultiplierSymbol ξ v = forcePressureGradientSymbol ξ v k := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [forcePressureMultiplierSymbol, forcePressureGradientSymbol]
  · simp [forcePressureMultiplierSymbol, forcePressureGradientSymbol, hξ]
    have hdenR : (2 * Real.pi * ‖ξ‖ ^ 2 : ℝ) ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) Real.pi_ne_zero
      · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ)
    have hdenC : ((2 * Real.pi * ‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hdenR
    have hnormC : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))
    field_simp [hdenC, hnormC]
    rw [Complex.I_sq]
    simp only [complexifyFrequency]
    ring

/-- The bounded multiplier for the gradient of the force pressure on spatial
complex `L²`. -/
@[expose]
noncomputable def forcePressureGradientFourierMultiplier
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    Lp (α := L2Vec3) ComplexVec3 2 :=
  measurableFourierMultiplier
    (fun p : L2Vec3 × ComplexVec3 => forcePressureGradientSymbol p.1 p.2)
    forcePressureGradientSymbol_measurable 2
    (by intro ξ z; exact forcePressureGradientSymbol_norm_le ξ z) v

/-- The gradient multiplier is bounded on spatial complex `L²`. -/
theorem forcePressureGradientFourierMultiplier_norm_le
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    ‖forcePressureGradientFourierMultiplier v‖ ≤ 2 * ‖v‖ := by
  exact measurableFourierMultiplier_norm_le
    (m := fun p : L2Vec3 × ComplexVec3 => forcePressureGradientSymbol p.1 p.2)
    forcePressureGradientSymbol_measurable 2
    (by intro ξ z; exact forcePressureGradientSymbol_norm_le ξ z) v

/-- The pressure gradient in physical spatial real `L²`, expressed as the
complement of the Leray projection. -/
@[expose]
noncomputable def forcePressureGradientL2 (f : RealVectorL2) : RealVectorL2 :=
  f - realLerayProjection f

/-- The physical force-pressure gradient has the dimension-only `L²` bound
obtained from the Leray projection. -/
theorem forcePressureGradientL2_norm_le (f : RealVectorL2) :
    ‖forcePressureGradientL2 f‖ ≤ 2 * ‖f‖ := by
  rw [forcePressureGradientL2]
  calc
    ‖f - realLerayProjection f‖ ≤ ‖f‖ + ‖realLerayProjection f‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := by
      gcongr
      exact realLerayProjection_norm_le f
    _ = 2 * ‖f‖ := by ring

@[expose]
def forcePressureCoordinateEquiv : L2Vec3 ≃L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

@[expose]
def forcePressureToCoordinate : L2Vec3 →L[ℝ] Vec3 :=
  forcePressureCoordinateEquiv.toContinuousLinearMap

@[expose]
def forcePressureToHilbert : Vec3 →L[ℝ] L2Vec3 :=
  forcePressureCoordinateEquiv.symm.toContinuousLinearMap

/-- The pointwise representative of the bounded `I - ℙ` force-pressure
gradient multiplier on a real spatial `L²` class. -/
@[expose]
def forcePressureGradientRepresentative (f : RealVectorL2) : Vec3 → Vec3 :=
  fun x => forcePressureToCoordinate (f (WithLp.toLp 2 x))

theorem forcePressureInput_memLp (f : Vec3 → Vec3)
    (hf : MemLp f 2 volume) :
    MemLp (fun y : L2Vec3 => forcePressureToHilbert (f (WithLp.ofLp y)))
      2 volume := by
  have hcoord : MemLp (fun y : L2Vec3 => f (WithLp.ofLp y)) 2 volume :=
    hf.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
  exact hcoord.continuousLinearMap_comp forcePressureToHilbert

@[expose]
def forcePressureInputL2 (f : Vec3 → Vec3)
    (hf : MemLp f 2 volume) : RealVectorL2 :=
  (forcePressureInput_memLp f hf).toLp
    (fun y : L2Vec3 => forcePressureToHilbert (f (WithLp.ofLp y)))

/-- The pointwise `I - ℙ` force-pressure gradient applied to a coordinate
field known to lie in spatial `L²`. -/
@[expose]
def forcePressureGradientFunction (f : Vec3 → Vec3)
    (hf : MemLp f 2 volume) : Vec3 → Vec3 :=
  forcePressureGradientRepresentative
    (forcePressureGradientL2 (forcePressureInputL2 f hf))

/-- The pointwise representative of the force-pressure gradient is in spatial
`L²`, with the bounded multiplier estimate inherited from
`forcePressureGradientL2`. -/
theorem forcePressureGradientFunction_memLp (f : Vec3 → Vec3)
    (hf : MemLp f 2 volume) :
    MemLp (forcePressureGradientFunction f hf) 2 volume := by
  let g : RealVectorL2 := forcePressureGradientL2 (forcePressureInputL2 f hf)
  have hmem : MemLp (fun y : L2Vec3 => forcePressureToCoordinate (g y))
      2 volume :=
    (Lp.memLp g).continuousLinearMap_comp forcePressureToCoordinate
  change MemLp (fun x : Vec3 => forcePressureToCoordinate
    (g (WithLp.toLp 2 x))) 2 volume
  exact hmem.comp_measurePreserving vec3ToL2Vec3_measurePreserving

end CKN.Leray
