/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGradient

/-!
# Pointwise heat bound for a scalar cutoff

The weak heat operator of a scalar cutoff field is bounded by the scaled
equation and the first and second cutoff derivatives.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The cutoff error in the weak heat operator is bounded by the scalar
heat derivative and the spatial gradient of the cutoff. -/
theorem buCut_heat_error_le
    (κ : Vec3 × ℝ → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint)
    (M : ℝ) (hM : 0 ≤ M)
    (hderiv : ∀ j : Fin 3,
      |spatialPartial (buCutScalar κ) j z| ≤ M) :
    vec3EuclideanNorm (buCutHeatError κ v Dv z) ≤
      |timePartial (buCutScalar κ) z +
        ∑ j : Fin 3,
          spatialSecondPartial (buCutScalar κ) j j z| *
        vec3EuclideanNorm (v z) +
      18 * M * Real.sqrt (spatialGradientSq v Dv z) := by
  let A := timePartial (buCutScalar κ) z +
    ∑ j : Fin 3, spatialSecondPartial (buCutScalar κ) j j z
  let d : Fin 3 → ℝ := fun j => spatialPartial (buCutScalar κ) j z
  have heq : buCutHeatError κ v Dv z =
      A • v z + (2 : ℝ) • (fun i => ∑ j : Fin 3, d j * Dv z i j) := by
    funext i
    simp only [buCutHeatError, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    dsimp [A, d]
  rw [heq]
  calc
    vec3EuclideanNorm (A • v z + (2 : ℝ) •
      (fun i => ∑ j : Fin 3, d j * Dv z i j)) ≤
      vec3EuclideanNorm (A • v z) +
        vec3EuclideanNorm ((2 : ℝ) •
          (fun i => ∑ j : Fin 3, d j * Dv z i j)) :=
      vec3EuclideanNorm_add_le _ _
    _ = |A| * vec3EuclideanNorm (v z) +
          2 * vec3EuclideanNorm
            (fun i => ∑ j : Fin 3, d j * Dv z i j) := by
      rw [vec3EuclideanNorm_smul, vec3EuclideanNorm_smul]
      norm_num
    _ ≤ |A| * vec3EuclideanNorm (v z) +
          2 * (9 * M * Real.sqrt (spatialGradientSq v Dv z)) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (uc_gradient_contraction_le v Dv z d M hM hderiv)
          (by norm_num))
    _ = _ := by dsimp [A]; ring

/-- The scaled heat inequality passes to a scalar cutoff field with an
explicit cutoff-derivative error. -/
theorem buCut_heat_le
    (κ : Vec3 × ℝ → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (z : ParabolicPoint)
    (c : ℝ) (hc : 0 ≤ c)
    (hκ : 0 ≤ buCutScalar κ z)
    (M : ℝ) (hM : 0 ≤ M)
    (hderiv : ∀ j : Fin 3,
      |spatialPartial (buCutScalar κ) j z| ≤ M)
    (hheat : vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
      c * (Real.sqrt (spatialGradientSq v Dv z) +
        vec3EuclideanNorm (v z))) :
    vec3EuclideanNorm
      (ucWeakHeatVector (buCutD2 κ v Dv D2v) (buCutDt κ v Dtv) z) ≤
      c * (vec3EuclideanNorm ((buCutField κ v) z) +
        3 * Real.sqrt (spatialGradientSq
          (buCutField κ v) (buCutDw κ v Dv) z)) +
      (3 * c * M +
        |timePartial (buCutScalar κ) z +
          ∑ j : Fin 3,
            spatialSecondPartial (buCutScalar κ) j j z|) *
          vec3EuclideanNorm (v z) +
      18 * M * Real.sqrt (spatialGradientSq v Dv z) := by
  let ξ := buCutScalar κ z
  let Z := buCutField κ v
  let DZ := buCutDw κ v Dv
  let L := ucWeakHeatVector D2v Dtv z
  have hmain : ξ * vec3EuclideanNorm L ≤
      c * (vec3EuclideanNorm (Z z) +
        3 * Real.sqrt (spatialGradientSq Z DZ z)) +
      3 * c * M * vec3EuclideanNorm (v z) := by
    have hgrad := buCut_gradient_absorption κ v Dv z hκ M hM hderiv
    have hnorm : ξ * vec3EuclideanNorm (v z) =
        vec3EuclideanNorm (Z z) := by
      change ξ * vec3EuclideanNorm (v z) = vec3EuclideanNorm (ξ • v z)
      rw [vec3EuclideanNorm_smul, abs_of_nonneg hκ]
    calc
      ξ * vec3EuclideanNorm L ≤
          ξ * (c * (Real.sqrt (spatialGradientSq v Dv z) +
            vec3EuclideanNorm (v z))) :=
        mul_le_mul_of_nonneg_left hheat hκ
      _ = c * (ξ * Real.sqrt (spatialGradientSq v Dv z) +
            ξ * vec3EuclideanNorm (v z)) := by ring
      _ ≤ c * (3 * (Real.sqrt (spatialGradientSq Z DZ z) +
            M * vec3EuclideanNorm (v z)) +
            vec3EuclideanNorm (Z z)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        rw [hnorm]
        exact add_le_add hgrad le_rfl
      _ = _ := by ring
  rw [buCutHeat_eq κ v Dv D2v Dtv z]
  have htri := vec3EuclideanNorm_add_le (ξ • L)
    (buCutHeatError κ v Dv z)
  have herror := buCut_heat_error_le κ v Dv z M hM hderiv
  rw [vec3EuclideanNorm_smul, abs_of_nonneg hκ] at htri
  calc
    _ ≤ ξ * vec3EuclideanNorm L +
        vec3EuclideanNorm (buCutHeatError κ v Dv z) := htri
    _ ≤ (c * (vec3EuclideanNorm (Z z) +
          3 * Real.sqrt (spatialGradientSq Z DZ z)) +
          3 * c * M * vec3EuclideanNorm (v z)) +
        (|timePartial (buCutScalar κ) z +
          ∑ j : Fin 3, spatialSecondPartial (buCutScalar κ) j j z| *
          vec3EuclideanNorm (v z) +
          18 * M * Real.sqrt (spatialGradientSq v Dv z)) :=
      add_le_add hmain herror
    _ = _ := by ring

end ESS
