/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureMassSource

/-!
# Blowup Energy Pressure Integral

Local energy bounds for the rescaled sequence in the endpoint regularity argument.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace ESS

/-- Pressure mass and twice the Dirichlet energy bound the integral of their
sum on the same open past cylinder. -/
theorem blowup_energyPressure_integral_bound
    (R a : ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (Cg Cp : ℝ)
    (hgInt : IntegrableOn (fun z => spatialGradientSq v Dv z)
      (vec3Ball 0 R ×ˢ Ioo a 0) volume)
    (hgBound : 2 * (∫ (z : ParabolicPoint) in vec3Ball 0 R ×ˢ Ioo a 0,
      spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) ≤ Cg)
    (hpMem : MemLp p (3 / 2 : ℝ≥0∞)
      ((volume : Measure ParabolicPoint).restrict (vec3Ball 0 R ×ˢ Ioo a 0)))
    (hpBound : (∫ (z : ParabolicPoint) in vec3Ball 0 R ×ˢ Ioo a 0,
      |p z| ^ (3 / 2 : ℝ) ∂(volume : Measure ParabolicPoint)) ≤ Cp) :
    IntegrableOn (fun z => |p z| ^ (3 / 2 : ℝ) +
      spatialGradientSq v Dv z)
      (vec3Ball 0 R ×ˢ Ioo a 0) volume ∧
    (∫ (z : ParabolicPoint) in vec3Ball 0 R ×ˢ Ioo a 0,
      (|p z| ^ (3 / 2 : ℝ) + spatialGradientSq v Dv z)
      ∂(volume : Measure ParabolicPoint)) ≤ Cp + Cg := by
  let S : Set ParabolicPoint := vec3Ball 0 R ×ˢ Ioo a 0
  have hcoeff : ((3 / 2 : ℝ≥0∞).toReal) = (3 / 2 : ℝ) := by norm_num
  have hpInt : IntegrableOn (fun z : ParabolicPoint => |p z| ^ (3 / 2 : ℝ))
      S volume := by
    change Integrable (fun z : ParabolicPoint => |p z| ^ (3 / 2 : ℝ))
      ((volume : Measure ParabolicPoint).restrict S)
    have h := hpMem.integrable_norm_rpow
      (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ⊤)
    simpa only [S, hcoeff, Real.norm_eq_abs] using h
  have hsumInt : IntegrableOn (fun z => |p z| ^ (3 / 2 : ℝ) +
      spatialGradientSq v Dv z) S volume := hpInt.add hgInt
  have hgnonneg : 0 ≤ (∫ (z : ParabolicPoint) in S,
      spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) := by
    apply integral_nonneg
    intro z
    dsimp [spatialGradientSq]
    positivity
  have hsumEq :
      (∫ (z : ParabolicPoint) in S,
        |p z| ^ (3 / 2 : ℝ) + spatialGradientSq v Dv z
        ∂(volume : Measure ParabolicPoint)) =
      (∫ (z : ParabolicPoint) in S,
        |p z| ^ (3 / 2 : ℝ) ∂(volume : Measure ParabolicPoint)) +
      (∫ (z : ParabolicPoint) in S,
        spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) :=
    integral_add hpInt hgInt
  refine ⟨hsumInt, ?_⟩
  calc
    (∫ (z : ParabolicPoint) in S,
      |p z| ^ (3 / 2 : ℝ) + spatialGradientSq v Dv z
      ∂(volume : Measure ParabolicPoint)) =
        (∫ (z : ParabolicPoint) in S,
          |p z| ^ (3 / 2 : ℝ) ∂(volume : Measure ParabolicPoint)) +
        (∫ (z : ParabolicPoint) in S,
          spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) := hsumEq
    _ ≤ (∫ (z : ParabolicPoint) in S,
          |p z| ^ (3 / 2 : ℝ) ∂(volume : Measure ParabolicPoint)) +
        2 * (∫ (z : ParabolicPoint) in S,
          spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) := by
      gcongr
      linarith only [hgnonneg]
    _ ≤ Cp + Cg := add_le_add hpBound hgBound

end ESS
