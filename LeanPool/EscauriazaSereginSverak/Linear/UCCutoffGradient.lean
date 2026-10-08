/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffCollar

/-!
# Gradient comparison for Gaussian cutoff absorption

A finite dimensional estimate compares the original gradient after
multiplication by the cutoff with the weak gradient of the cut off field.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
attribute [local instance] Classical.propDecidable

noncomputable section

namespace ESS

private theorem uc_matrix_sqrt_le_three_of_components
    (A : Fin 3 → Fin 3 → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M) :
    Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, A i j ^ 2) ≤ 3 * M := by
  have hsq (i j : Fin 3) : A i j ^ 2 ≤ M ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hM).2 (hA i j)
    simpa only [sq_abs] using h
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, A i j ^ 2) ≤
      9 * M ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, M ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hsq i j
      _ = 9 * M ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  calc
    Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, A i j ^ 2) ≤
        Real.sqrt (9 * M ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 3 * M := by
      have heq : 9 * M ^ 2 = (3 * M) ^ 2 := by ring
      rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-- The gradient of a compact cutoff controls the cutoff factor times
the original gradient, with a correction supported on the collar. -/
theorem ucGaussianCutoff_gradient_absorption
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    {z : ParabolicPoint} (hz : z ∈ ucCylinder ρ) :
    ucGaussianCutoff ρ hρ ε z *
      Real.sqrt (spatialGradientSq v Dv z) ≤
        3 * (Real.sqrt (spatialGradientSq
          (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
            (ucInitialTimeCutoff ε) v)
          (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
            (ucInitialTimeCutoff ε) v Dv) z) +
          (if z ∈ ucCutoffRegion ρ then
            cutoffGradientConstant / ρ else 0) *
            vec3EuclideanNorm (v z)) := by
  let ξ := ucGaussianCutoff ρ hρ ε z
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let M := if z ∈ ucCutoffRegion ρ then cutoffGradientConstant / ρ else 0
  let U := Real.sqrt (spatialGradientSq Z DZ z) +
    M * vec3EuclideanNorm (v z)
  have hξ : 0 ≤ ξ := (ucGaussianCutoff_bounds hρ ε z).1
  have hM : 0 ≤ M :=
    (abs_nonneg _).trans
      (ucGaussianCutoff_spatialPartial_abs_local_bound hρ ε hz 0)
  have hU : 0 ≤ U := by
    dsimp [U]
    apply add_nonneg (Real.sqrt_nonneg _)
    exact mul_nonneg hM (vec3EuclideanNorm_nonneg _)
  have hcomp (i j : Fin 3) : |ξ * Dv z i j| ≤ U := by
    let d := spatialPartial (ucGaussianCutoff ρ hρ ε) j z
    have hformula : DZ z i j = ξ * Dv z i j + v z i * d := rfl
    have hdiff : ξ * Dv z i j = DZ z i j - v z i * d := by
      rw [hformula]
      ring
    have htri : |ξ * Dv z i j| ≤ |DZ z i j| + |v z i * d| := by
      rw [hdiff]
      simpa only [abs_neg, sub_eq_add_neg] using
        (abs_add_le (DZ z i j) (-(v z i * d)))
    have hdz := uc_gradient_component_le Z DZ z i j
    have hv := abs_apply_le_vec3EuclideanNorm (v z) i
    have hd : |d| ≤ M :=
      ucGaussianCutoff_spatialPartial_abs_local_bound hρ ε hz j
    have hprod : |v z i * d| ≤ vec3EuclideanNorm (v z) * M := by
      rw [abs_mul]
      exact mul_le_mul hv hd (abs_nonneg _) (vec3EuclideanNorm_nonneg _)
    exact htri.trans (by dsimp [U]; linarith only [hdz, hprod])
  have hmatrix := uc_matrix_sqrt_le_three_of_components
    (fun i j => ξ * Dv z i j) U hU hcomp
  have hscaleSq : (∑ i : Fin 3, ∑ j : Fin 3,
      (ξ * Dv z i j) ^ 2) = ξ ^ 2 * spatialGradientSq v Dv z := by
    simp only [spatialGradientSq]
    simp_rw [mul_pow]
    simp_rw [← Finset.mul_sum]
  have hroot : Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      (ξ * Dv z i j) ^ 2) =
      ξ * Real.sqrt (spatialGradientSq v Dv z) := by
    rw [hscaleSq, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hξ]
  rw [hroot] at hmatrix
  exact hmatrix

end ESS
