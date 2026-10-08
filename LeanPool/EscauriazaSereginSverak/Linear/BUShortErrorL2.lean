/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortErrorContinuity
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEnergyL2

/-!
# Quadratic integrability of cutoff errors

For fixed cutoff parameters the error in the weak heat equation is
quadratically integrable on the compact support of the scalar cutoff.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The squared heat error of a fixed smooth cutoff is integrable on
any compact set carrying `L²` field and weak-gradient data. -/
theorem bu_short_cutoff_error_sq_integrable
    (scale R ε c₁ : ℝ) (hR : 0 < R)
    (K : Set ParabolicPoint) (hK : IsCompact K)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hv : MemLp v 2 (volume.restrict K))
    (hDv : MemLp Dv 2 (volume.restrict K)) :
    IntegrableOn (fun z =>
      buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2)
      K volume := by
  let M := buShortCutoffGradientSize scale R hR ε
  let L := buShortCutoffHeatScalarSize scale R hR ε
  let A : ParabolicPoint → ℝ := fun z => 3 * (c₁ * scale) * M z + L z
  let C : ParabolicPoint → ℝ := fun z => 18 * M z
  let B : ParabolicPoint → ℝ := fun z =>
    buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hM : Continuous M :=
    buShortCutoffGradientSize_continuous scale R hR ε
  have hL : Continuous L :=
    buShortCutoffHeatScalarSize_continuous scale R hR ε
  have hA : Continuous A := by
    dsimp [A]
    fun_prop
  have hC : Continuous C := by
    dsimp [C]
    fun_prop
  obtain ⟨hvInt, hGInt⟩ :=
    bu_memLp_quadratic_energy_integrable K v Dv hv hDv
  have hAInt : IntegrableOn (fun z => A z ^ 2 *
      vec3EuclideanNorm (v z) ^ 2) K volume :=
    bu_integrableOn_mul_continuous_compact hK _ _ hvInt
      (hA.pow 2).continuousOn
  have hCInt : IntegrableOn (fun z => C z ^ 2 *
      spatialGradientSq v Dv z) K volume :=
    bu_integrableOn_mul_continuous_compact hK _ _ hGInt
      (hC.pow 2).continuousOn
  have hBmeas : AEStronglyMeasurable (fun z => B z ^ 2)
      (volume.restrict K) := by
    have hAmeas : AEStronglyMeasurable A (volume.restrict K) :=
      hA.continuousOn.aestronglyMeasurable_of_isCompact hK hKmeas
    have hCmeas : AEStronglyMeasurable C (volume.restrict K) :=
      hC.continuousOn.aestronglyMeasurable_of_isCompact hK hKmeas
    have hvmeas : AEStronglyMeasurable
        (fun z => vec3EuclideanNorm (v z)) (volume.restrict K) :=
      continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        hv.aestronglyMeasurable
    have hGmeas : AEStronglyMeasurable
        (fun z => Real.sqrt (spatialGradientSq v Dv z))
        (volume.restrict K) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        hGInt.aestronglyMeasurable
    have h := ((hAmeas.mul hvmeas).add (hCmeas.mul hGmeas)).pow 2
    convert h using 1
    funext z
    dsimp [B, buShortCutoffHeatErrorSize, A, C, M, L,
      buShortCutoffHeatScalarSize]
  have hbound (z : ParabolicPoint) :
      B z ^ 2 ≤ 2 * (A z ^ 2 * vec3EuclideanNorm (v z) ^ 2 +
        C z ^ 2 * spatialGradientSq v Dv z) := by
    have hG : 0 ≤ spatialGradientSq v Dv z := by
      dsimp [spatialGradientSq]
      positivity
    have hsqrt : Real.sqrt (spatialGradientSq v Dv z) ^ 2 =
        spatialGradientSq v Dv z := Real.sq_sqrt hG
    have hB : B z = A z * vec3EuclideanNorm (v z) +
        C z * Real.sqrt (spatialGradientSq v Dv z) := by
      dsimp [B, A, C, L, M, buShortCutoffHeatErrorSize,
        buShortCutoffHeatScalarSize]
    rw [hB]
    nlinarith only [sq_nonneg (A z * vec3EuclideanNorm (v z) -
      C z * Real.sqrt (spatialGradientSq v Dv z)), hsqrt]
  change Integrable (fun z => B z ^ 2) (volume.restrict K)
  have hRhs : Integrable (fun z => 2 *
      (A z ^ 2 * vec3EuclideanNorm (v z) ^ 2 +
        C z ^ 2 * spatialGradientSq v Dv z)) (volume.restrict K) :=
    (hAInt.add hCInt).const_mul 2
  apply Integrable.mono' hRhs hBmeas
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hbound z

end ESS
