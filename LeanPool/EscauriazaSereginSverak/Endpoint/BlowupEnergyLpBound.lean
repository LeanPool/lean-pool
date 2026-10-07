/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyMajorant

/-!
# Blowup Energy Lp Bound

Local energy bounds for the rescaled sequence in the endpoint regularity argument.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace ESS

/-- Uniform `L³` velocity and `L^(3/2)` pressure data make the local-energy
bound applicable on a fixed past cylinder. -/
theorem blowupEnergyCutoff_gradient_bound_of_lp
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), b < 0 →
      ∀ {q : ℝ} {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
        (M : ℝ),
      IsSuitableWeakSolutionIntegrable
        (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) q u Du p 0 →
      MemLp (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) 3
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))) →
      MemLp p (3 / 2 : ℝ≥0∞)
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))) →
      (∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0),
        (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
          3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
          6 * C * |p z| * vec3EuclideanNorm (u z)) ≤ M →
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b),
        spatialGradientSq u Du z) ≤ M := by
  obtain ⟨C, hC, hbound⟩ := blowupEnergyCutoff_gradient_bound_of_majorant R hR
  refine ⟨C, hC, fun a b hb q u Du p M hsol hu hp hM => ?_⟩
  let outer := spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0)
  let μ : Measure ParabolicPoint := volume.restrict outer
  let : IsFiniteMeasure μ := blowupEnergyOuter_finiteMeasure R a hR
  have hint : IntegrableOn (fun z : ParabolicPoint =>
      (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
        3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
        6 * C * |p z| * vec3EuclideanNorm (u z)) outer volume := by
    exact blowupEnergyMajorant_integrable μ
      (fun z => vec3EuclideanNorm (u z)) p hu hp C
  exact hbound a b hb M hsol hint hM

end ESS
