/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSliceUniform

/-!
# Blowup Gradient Component

Gradient estimates for the rescaled sequence used in endpoint compactness.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- The squared Euclidean norm of one gradient row is at most the full
Dirichlet density. -/
theorem blowup_gradient_component_sq_le
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (i : Fin 3) (z : ParabolicPoint) :
    vec3EuclideanNorm (Du z i) ^ 2 ≤ spatialGradientSq u Du z := by
  have hnonneg : 0 ≤ ∑ j : Fin 3, (Du z i j) ^ (2 : ℕ) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rw [vec3EuclideanNorm, Real.sq_sqrt hnonneg]
  dsimp only [spatialGradientSq]
  exact Finset.single_le_sum
    (fun j _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))
    (Finset.mem_univ i)

/-- A finite Dirichlet integral bounds the squared `L²` seminorm of
each Euclidean gradient row. -/
theorem blowup_gradient_component_eLpNorm_sq_le
    (S : Set ParabolicPoint)
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (i : Fin 3)
    (hDu : AEStronglyMeasurable Du (volume.restrict S))
    (hgrad : IntegrableOn (fun z => spatialGradientSq u Du z) S volume) :
    eLpNorm (fun z => vec3EuclideanNorm (Du z i)) 2
      (volume.restrict S) ^ (2 : ℝ) ≤
        ENNReal.ofReal
          (∫ (z : ParabolicPoint) in S,
            spatialGradientSq u Du z ∂(volume : Measure ParabolicPoint)) := by
  let μ : Measure ParabolicPoint := volume.restrict S
  let g : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (Du z i)
  have hgm : AEStronglyMeasurable g μ := by
    have hcont : Continuous (fun v : Fin 3 → Vec3 => vec3EuclideanNorm (v i)) :=
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp (continuous_apply i)
    exact hcont.comp_aestronglyMeasurable hDu
  have hgpos (z : ParabolicPoint) : 0 ≤ g z := vec3EuclideanNorm_nonneg _
  have hgradpos : ∀ᵐ z ∂μ, 0 ≤ spatialGradientSq u Du z := by
    filter_upwards [] with z
    dsimp [spatialGradientSq]
    positivity
  have hpowequal :
      eLpNorm g 2 μ ^ (2 : ℝ) =
        ∫⁻ z, ENNReal.ofReal (g z ^ (2 : ℕ)) ∂μ := by
    have h := eLpNorm_nnreal_pow_eq_lintegral
      (p := (2 : NNReal)) (f := g) (by norm_num) hgm
    norm_num at h ⊢
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hgpos _),
      ENNReal.ofReal_pow (hgpos _) 2] using h
  have hpoint (z : ParabolicPoint) :
      ENNReal.ofReal (g z ^ (2 : ℕ)) ≤
        ENNReal.ofReal (spatialGradientSq u Du z) :=
    ENNReal.ofReal_le_ofReal (blowup_gradient_component_sq_le u Du i z)
  have hlin :
      (∫⁻ z, ENNReal.ofReal (g z ^ (2 : ℕ)) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal (spatialGradientSq u Du z) ∂μ :=
    lintegral_mono hpoint
  have hreal :
      ENNReal.ofReal
        (∫ (z : ParabolicPoint) in S,
          spatialGradientSq u Du z ∂(volume : Measure ParabolicPoint)) =
        ∫⁻ z, ENNReal.ofReal (spatialGradientSq u Du z) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hgrad hgradpos
  exact hpowequal.trans_le (hlin.trans_eq hreal.symm)

/-- A real Dirichlet bound gives a uniform bound for one gradient row's
space-time `L²` seminorm. -/
theorem blowup_gradient_component_eLpNorm_le_of_integral_bound
    (S : Set ParabolicPoint)
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (i : Fin 3) (C : ℝ)
    (hDu : AEStronglyMeasurable Du (volume.restrict S))
    (hgrad : IntegrableOn (fun z => spatialGradientSq u Du z) S volume)
    (hbound : (∫ (z : ParabolicPoint) in S,
      spatialGradientSq u Du z ∂(volume : Measure ParabolicPoint)) ≤ C) :
    eLpNorm (fun z => vec3EuclideanNorm (Du z i)) 2
      (volume.restrict S) ≤ (ENNReal.ofReal C) ^ (1 / 2 : ℝ) := by
  have hsq := blowup_gradient_component_eLpNorm_sq_le S u Du i hDu hgrad
  have hpow :
      eLpNorm (fun z => vec3EuclideanNorm (Du z i)) 2
        (volume.restrict S) ^ (2 : ℝ) ≤ ENNReal.ofReal C :=
    hsq.trans (ENNReal.ofReal_le_ofReal hbound)
  have hroot := ENNReal.rpow_le_rpow hpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    eLpNorm (fun z => vec3EuclideanNorm (Du z i)) 2
        (volume.restrict S) =
      (eLpNorm (fun z => vec3EuclideanNorm (Du z i)) 2
        (volume.restrict S) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_mul]
          norm_num
    _ ≤ (ENNReal.ofReal C) ^ (1 / 2 : ℝ) := hroot

end ESS
