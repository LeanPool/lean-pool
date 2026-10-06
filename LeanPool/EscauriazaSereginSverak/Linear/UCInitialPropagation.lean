/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCRadiusGeometry
public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialBall

/-!
# Initial ball from the Gaussian estimate

The box estimate in `lem:uc-gaussian` and continuity at time zero force the
trace to vanish on its output ball.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A Gaussian box estimate propagates a zero initial trace from its center
to the entire inner output ball (`thm:uc`). -/
theorem uc_initial_ball_vanishing
    (R T : ℝ) (hR : 0 < R) (hT : 0 < T)
    (x₀ : Vec3)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (spaceTimeSet (vec3Ball x₀ R) (Ico 0 T)))
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball x₀ R) (Ioo 0 T)
      w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hzero : w (x₀, 0) = 0)
    (hgauss : ∃ γ C : ℝ, 0 < γ ∧ γ < 3 / 16 ∧ 0 < C ∧
      ∀ (x : Vec3) (t : ℝ), 0 < t → t ≤ γ * T →
        vec3EuclideanNorm (x - x₀) ≤ ucRadiusFraction * R →
        (16 / 100) * t ≤ vec3EuclideanNorm (x - x₀) ^ 2 →
        (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t)))
          (Ioo t (2 * t)), vec3EuclideanNorm (w z) ^ 2) ≤
          C * ucLocalEnergy x₀ R T w Dw *
            Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t))) :
    ∀ x ∈ vec3Ball x₀ (ucRadiusFraction * R), w (x, 0) = 0 := by
  have hL2w : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
          ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
            ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ) := by
        apply lintegral_mono
        intro z
        exact le_add_of_nonneg_right (by positivity) |>.trans
          (le_add_of_nonneg_right (by positivity) |>.trans
            (le_add_of_nonneg_right (by positivity)))
      _ < ⊤ := hL2
  obtain ⟨γ, C, hγ, _, _, hbox⟩ := hgauss
  intro x hx
  by_cases hxx₀ : x = x₀
  · simpa only [hxx₀] using hzero
  have hxR : x ∈ vec3Ball x₀ R := by
    have hβ := ucRadiusFraction_pos_lt_one.2
    have hβR : ucRadiusFraction * R ≤ R := by
      nlinarith only [hβ, hR]
    exact (mem_vec3Ball).2 (((mem_vec3Ball).1 hx).trans_le hβR)
  let d : ℝ := vec3EuclideanNorm (x - x₀)
  have hdnonneg : 0 ≤ d := vec3EuclideanNorm_nonneg _
  have hd : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := le_antisymm (le_of_not_gt hnot) hdnonneg
    have hd0' : vecEuclideanNorm (x - x₀) = 0 := by
      simpa [d, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot,
        pow_two] using hd0
    have hsub : x - x₀ = 0 := vecEuclideanNorm_eq_zero_iff.mp hd0'
    exact hxx₀ (sub_eq_zero.mp hsub)
  let δ : ℝ := min (γ * T) (d ^ 2 / (16 / 100))
  have hδ : 0 < δ := lt_min (mul_pos hγ hT) (by positivity)
  have hb : 0 < d ^ 2 / 2 := by positivity
  have hbox' (t : ℝ) (ht : 0 < t) (htδ : t < δ) :
      (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t)))
        (Ioo t (2 * t)), vec3EuclideanNorm (w z) ^ 2) ≤
          (C * ucLocalEnergy x₀ R T w Dw) *
            Real.exp (-((d ^ 2 / 2) / t)) := by
    have htγ : t ≤ γ * T := (htδ.trans_le (min_le_left _ _)).le
    have htd : (16 / 100 : ℝ) * t ≤ d ^ 2 := by
      have htbound : t < d ^ 2 / (16 / 100) :=
        htδ.trans_le (min_le_right _ _)
      nlinarith only [htbound]
    have hxbound : d ≤ ucRadiusFraction * R := ((mem_vec3Ball).1 hx).le
    have h := hbox x t ht htγ hxbound htd
    have heq : -((d ^ 2 / 2) / t) = -(d ^ 2) / (2 * t) := by
      field_simp [ne_of_gt ht]
    rw [heq]
    simpa only [d, mul_assoc] using h
  exact uc_gaussian_box_bound_to_trace R T hT x₀ x hxR w
    hcont hweak.1 hL2w (d ^ 2 / 2)
    (C * ucLocalEnergy x₀ R T w Dw) δ hb hδ hbox'

end ESS
