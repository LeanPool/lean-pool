/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupCutoffSpatialBound

public section

open CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS

/-- The local-energy right-hand density for the fixed spatial cutoff is
bounded by the velocity and pressure densities with one coefficient that
does not depend on the upper time cutoff. -/
theorem blowupEnergyCutoff_localEnergyRhs_le
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), b < 0 →
      ∀ (u : Vec3 × ℝ → Vec3) (p : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ),
      localEnergyRhs u p 0 (blowupEnergyCutoff R a b) z ≤
        (vec3EuclideanNorm (u z)) ^ 2 * (8 + 3 * C) +
          |(vec3EuclideanNorm (u z)) ^ 2 + 2 * p z| *
            (3 * C * vec3EuclideanNorm (u z)) := by
  obtain ⟨C, hC, hcoef⟩ := blowupEnergyCutoff_coefficient_bounds R hR
  refine ⟨C, hC, fun a b hb u p z => ?_⟩
  obtain ⟨htime, hfirst, hsecond⟩ := hcoef a b hb z
  let U : ℝ := vec3EuclideanNorm (u z)
  let S : ℝ := ∑ i : Fin 3,
    u z i * spatialPartialProd (blowupEnergyCutoff R a b) i z
  have hU : 0 ≤ U := vec3EuclideanNorm_nonneg _
  have hLap : (∑ i : Fin 3,
      spatialSecondPartialProd (blowupEnergyCutoff R a b) i i z) ≤ 3 * C := by
    rw [Fin.sum_univ_three]
    have h₀ := (le_abs_self _).trans (hsecond 0)
    have h₁ := (le_abs_self _).trans (hsecond 1)
    have h₂ := (le_abs_self _).trans (hsecond 2)
    linarith only [h₀, h₁, h₂]
  have hS : |S| ≤ 3 * C * U := by
    have hterm (i : Fin 3) :
        |u z i * spatialPartialProd (blowupEnergyCutoff R a b) i z| ≤ U * C := by
      rw [abs_mul]
      exact mul_le_mul (abs_apply_le_vec3EuclideanNorm (u z) i)
        (hfirst i) (abs_nonneg _) hU
    calc
      |S| ≤ ∑ i : Fin 3,
          |u z i * spatialPartialProd (blowupEnergyCutoff R a b) i z| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, U * C := Finset.sum_le_sum fun i _ => hterm i
      _ = 3 * C * U := by simp; ring
  have hmain :
      timePartialProd (blowupEnergyCutoff R a b) z +
        ∑ i : Fin 3,
          spatialSecondPartialProd (blowupEnergyCutoff R a b) i i z ≤
        8 + 3 * C := add_le_add htime hLap
  have hSle : S ≤ 3 * C * U := (le_abs_self _).trans hS
  have hSneg : -S ≤ 3 * C * U := (neg_le_abs _).trans hS
  change U ^ 2 * _ + (U ^ 2 + 2 * p z) * S + 2 * (∑ i, (0 : Vec3) i * u z i) *
    blowupEnergyCutoff R a b z ≤ _
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  have hfirstPart := mul_le_mul_of_nonneg_left hmain (sq_nonneg U)
  have hsecondPart : (U ^ 2 + 2 * p z) * S ≤
      |U ^ 2 + 2 * p z| * (3 * C * U) := by
    by_cases hp : 0 ≤ U ^ 2 + 2 * p z
    · rw [abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left hSle hp
    · rw [abs_of_neg (lt_of_not_ge hp)]
      have hmul := mul_le_mul_of_nonneg_left hSneg
        (neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp)))
      nlinarith only [hmul]
  exact add_le_add hfirstPart hsecondPart

/-- The same density bound in the power form used with slice `L³` and
pressure `L^(3/2)` estimates. -/
theorem blowupEnergyCutoff_localEnergyRhs_power_le
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), b < 0 →
      ∀ (u : Vec3 × ℝ → Vec3) (p : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ),
      localEnergyRhs u p 0 (blowupEnergyCutoff R a b) z ≤
        (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
          3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
          6 * C * |p z| * vec3EuclideanNorm (u z) := by
  obtain ⟨C, hC, hbound⟩ := blowupEnergyCutoff_localEnergyRhs_le R hR
  refine ⟨C, hC, fun a b hb u p z => ?_⟩
  let U : ℝ := vec3EuclideanNorm (u z)
  have hU : 0 ≤ U := vec3EuclideanNorm_nonneg _
  have hpress : |U ^ 2 + 2 * p z| ≤ U ^ 2 + 2 * |p z| := by
    calc
      |U ^ 2 + 2 * p z| ≤ |U ^ 2| + |2 * p z| := abs_add_le _ _
      _ = U ^ 2 + 2 * |p z| := by
        rw [abs_of_nonneg (sq_nonneg U), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmult : 0 ≤ 3 * C * U := by positivity
  have hpressPart := mul_le_mul_of_nonneg_right hpress hmult
  have h := hbound a b hb u p z
  change localEnergyRhs u p 0 (blowupEnergyCutoff R a b) z ≤
    U ^ 2 * (8 + 3 * C) + |U ^ 2 + 2 * p z| * (3 * C * U) at h
  calc
    localEnergyRhs u p 0 (blowupEnergyCutoff R a b) z ≤
        U ^ 2 * (8 + 3 * C) + |U ^ 2 + 2 * p z| * (3 * C * U) := h
    _ ≤ U ^ 2 * (8 + 3 * C) + (U ^ 2 + 2 * |p z|) * (3 * C * U) :=
      add_le_add_right hpressPart _
    _ = (8 + 3 * C) * U ^ 2 + 3 * C * U ^ 3 + 6 * C * |p z| * U := by ring

end ESS
