/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffOperator
public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffGradient

/-!
# Gradient of a scalar cutoff field

The weak product gradient controls the cutoff factor times the original
gradient, with an explicit term for derivatives of the scalar cutoff.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A pointwise gradient comparison for the scalar cutoff used in
`lem:bu-small-time`. -/
theorem buCut_gradient_absorption
    (κ : Vec3 × ℝ → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint)
    (hκ : 0 ≤ buCutScalar κ z)
    (M : ℝ) (hM : 0 ≤ M)
    (hderiv : ∀ j : Fin 3,
      |spatialPartial (buCutScalar κ) j z| ≤ M) :
    buCutScalar κ z * Real.sqrt (spatialGradientSq v Dv z) ≤
      3 * (Real.sqrt (spatialGradientSq
        (buCutField κ v) (buCutDw κ v Dv) z) +
        M * vec3EuclideanNorm (v z)) := by
  let ξ := buCutScalar κ z
  let Z := buCutField κ v
  let DZ := buCutDw κ v Dv
  let U := Real.sqrt (spatialGradientSq Z DZ z) +
    M * vec3EuclideanNorm (v z)
  have hU : 0 ≤ U := by
    dsimp [U]
    exact add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg hM (vec3EuclideanNorm_nonneg _))
  have hcomp (i j : Fin 3) : |ξ * Dv z i j| ≤ U := by
    let d := spatialPartial (buCutScalar κ) j z
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
    have hd : |d| ≤ M := hderiv j
    have hprod : |v z i * d| ≤ vec3EuclideanNorm (v z) * M := by
      rw [abs_mul]
      exact mul_le_mul hv hd (abs_nonneg _) (vec3EuclideanNorm_nonneg _)
    exact htri.trans (by dsimp [U]; linarith only [hdz, hprod])
  have hsq (i j : Fin 3) : (ξ * Dv z i j) ^ 2 ≤ U ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hU).2 (hcomp i j)
    simpa only [sq_abs] using h
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
      (ξ * Dv z i j) ^ 2) ≤ 9 * U ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, U ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hsq i j
      _ = 9 * U ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hmatrix : Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      (ξ * Dv z i j) ^ 2) ≤ 3 * U := by
    calc
      _ ≤ Real.sqrt (9 * U ^ 2) := Real.sqrt_le_sqrt hsum
      _ = 3 * U := by
        rw [show 9 * U ^ 2 = (3 * U) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hscaleSq : (∑ i : Fin 3, ∑ j : Fin 3,
      (ξ * Dv z i j) ^ 2) = ξ ^ 2 * spatialGradientSq v Dv z := by
    simp only [spatialGradientSq]
    simp_rw [mul_pow]
    simp_rw [← Finset.mul_sum]
  have hroot : Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      (ξ * Dv z i j) ^ 2) =
      ξ * Real.sqrt (spatialGradientSq v Dv z) := by
    rw [hscaleSq, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hκ]
  rw [hroot] at hmatrix
  exact hmatrix

end ESS
