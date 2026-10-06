/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyLpBound

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace ESS

/-- On a fixed past cylinder, the local gradient energy is bounded by the
volume, the cubic velocity mass, and the pressure `3/2` mass. -/
theorem blowupEnergyCutoff_gradient_bound_of_masses
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), b < 0 →
      ∀ {q : ℝ} {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ},
      IsSuitableWeakSolutionIntegrable
        (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) q u Du p 0 →
      MemLp (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) 3
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))) →
      MemLp p (3 / 2 : ℝ≥0∞)
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))) →
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b),
        spatialGradientSq u Du z) ≤
        (8 + 3 * C) *
          (volume.restrict
            (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))).real Set.univ +
        (8 + 8 * C) *
          (∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0),
            (vec3EuclideanNorm (u z)) ^ 3) +
        4 * C *
          (∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0),
            |p z| ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hgrad⟩ := blowupEnergyCutoff_gradient_bound_of_lp R hR
  refine ⟨C, hC, fun a b hb q u Du p hsol hu hp => ?_⟩
  let outer := spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0)
  let μ : Measure ParabolicPoint := volume.restrict outer
  let U : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (u z)
  let : IsFiniteMeasure μ := blowupEnergyOuter_finiteMeasure R a hR
  have hUpos (z : ParabolicPoint) : 0 ≤ U z := vec3EuclideanNorm_nonneg _
  have hUcube : Integrable (fun z => U z ^ 3) μ := by
    have hh := hu.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa [U, Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      Real.rpow_natCast] using hh
  have hpPow : Integrable (fun z => |p z| ^ (3 / 2 : ℝ)) μ := by
    have hh := hp.integrable_norm_rpow (by norm_num) (by finiteness)
    simpa [Real.norm_eq_abs] using hh
  have hmajorant : Integrable (fun z =>
      (8 + 3 * C) * U z ^ 2 + 3 * C * U z ^ 3 +
        6 * C * |p z| * U z) μ :=
    blowupEnergyMajorant_integrable μ U p hu hp C
  have hcubic : Integrable (fun z =>
      (8 + 3 * C) + (8 + 8 * C) * U z ^ 3 +
        4 * C * |p z| ^ (3 / 2 : ℝ)) μ :=
    ((integrable_const _).add (hUcube.const_mul _)).add
      (hpPow.const_mul _)
  have hmono :
      (∫ z : ParabolicPoint,
        (8 + 3 * C) * U z ^ 2 + 3 * C * U z ^ 3 +
          6 * C * |p z| * U z ∂μ) ≤
      ∫ z : ParabolicPoint,
        (8 + 3 * C) + (8 + 8 * C) * U z ^ 3 +
          4 * C * |p z| ^ (3 / 2 : ℝ) ∂μ := by
    apply integral_mono_ae hmajorant hcubic
    filter_upwards [] with z
    exact blowupEnergyMajorant_le_cubic_pressure C (U z) (p z) hC (hUpos z)
  have hsplit :
      (∫ z : ParabolicPoint,
        (8 + 3 * C) + (8 + 8 * C) * U z ^ 3 +
          4 * C * |p z| ^ (3 / 2 : ℝ) ∂μ) =
      (8 + 3 * C) * μ.real Set.univ +
        (8 + 8 * C) * (∫ z, U z ^ 3 ∂μ) +
        4 * C * (∫ z, |p z| ^ (3 / 2 : ℝ) ∂μ) := by
    have hA : Integrable
        (fun z => (8 + 3 * C) + (8 + 8 * C) * U z ^ 3) μ :=
      (integrable_const _).add (hUcube.const_mul _)
    rw [integral_add hA (hpPow.const_mul _),
      integral_add (integrable_const _) (hUcube.const_mul _),
      integral_const, integral_const_mul, integral_const_mul]
    ring
  have hM :
      (∫ z in outer,
        (8 + 3 * C) * U z ^ 2 + 3 * C * U z ^ 3 +
          6 * C * |p z| * U z) ≤
      (8 + 3 * C) * μ.real Set.univ +
        (8 + 8 * C) * (∫ z in outer, U z ^ 3) +
        4 * C * (∫ z in outer, |p z| ^ (3 / 2 : ℝ)) := by
    simpa only [μ] using hmono.trans_eq hsplit
  exact hgrad a b hb
    ((8 + 3 * C) * μ.real Set.univ +
      (8 + 8 * C) * (∫ z in outer, U z ^ 3) +
      4 * C * (∫ z in outer, |p z| ^ (3 / 2 : ℝ)))
    hsol hu hp hM

end ESS
