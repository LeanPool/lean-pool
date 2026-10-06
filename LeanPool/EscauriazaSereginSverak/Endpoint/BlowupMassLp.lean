/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyMassBound

public section

open MeasureTheory CKN CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A finite `L^p` seminorm bound controls the real integral of the
corresponding power. -/
theorem blowup_integral_norm_rpow_le_of_eLpNorm_le
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure α) (f : α → E) (p : ℝ) (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hbound : eLpNorm f (ENNReal.ofReal p) μ ≤ B) :
    (∫ z, ‖f z‖ ^ p ∂μ) ≤ B.toReal ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpTop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hInt : 0 ≤ (∫ z, ‖f z‖ ^ p ∂μ) :=
    integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have heq : eLpNorm f (ENNReal.ofReal p) μ =
      ENNReal.ofReal ((∫ z, ‖f z‖ ^ p ∂μ) ^ p⁻¹) := by
    simpa only [hpt] using hf.eLpNorm_eq_integral_rpow_norm hp0 hpTop
  have hrootNonneg : 0 ≤ (∫ z, ‖f z‖ ^ p ∂μ) ^ p⁻¹ :=
    Real.rpow_nonneg hInt _
  have hroot : (∫ z, ‖f z‖ ^ p ∂μ) ^ p⁻¹ ≤ B.toReal := by
    have h := ENNReal.toReal_mono hB.ne (heq ▸ hbound)
    simpa only [ENNReal.toReal_ofReal hrootNonneg] using h
  have hpow := Real.rpow_le_rpow hrootNonneg hroot hp.le
  have hrewrite : ((∫ z, ‖f z‖ ^ p ∂μ) ^ p⁻¹) ^ p =
      (∫ z, ‖f z‖ ^ p ∂μ) := by
    rw [← Real.rpow_mul hInt, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  simpa only [hrewrite] using hpow

/-- Fixed local `L³` velocity and `L^(3/2)` pressure bounds control the
gradient energy on every inner past cylinder with a time-uniform constant. -/
theorem blowupEnergyCutoff_gradient_bound_of_norms
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), b < 0 →
      ∀ {q : ℝ} {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
        (Bᵤ Bₚ : ℝ≥0∞), Bᵤ < ⊤ → Bₚ < ⊤ →
      IsSuitableWeakSolutionIntegrable
        (CKN.euclideanBall 0 (R + 1)) (Set.Ioo (a - 2) 0) q u Du p 0 →
      MemLp (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) 3
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Set.Ioo (a - 2) 0))) →
      MemLp p (3 / 2 : ℝ≥0∞)
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Set.Ioo (a - 2) 0))) →
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) 3
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Set.Ioo (a - 2) 0))) ≤ Bᵤ →
      eLpNorm p (3 / 2 : ℝ≥0∞)
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Set.Ioo (a - 2) 0))) ≤ Bₚ →
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Set.Ioo a b),
        spatialGradientSq u Du z) ≤
        (8 + 3 * C) *
          (volume.restrict
            (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Set.Ioo (a - 2) 0))).real Set.univ +
        (8 + 8 * C) * Bᵤ.toReal ^ 3 +
        4 * C * Bₚ.toReal ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := blowupEnergyCutoff_gradient_bound_of_masses R hR
  refine ⟨C, hC, fun a b hb q u Du p Bᵤ Bₚ hBᵤ hBₚ hsol hu hp hnbᵤ hnbₚ => ?_⟩
  let outer := spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Set.Ioo (a - 2) 0)
  let μ : Measure ParabolicPoint := volume.restrict outer
  let U : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (u z)
  have hUpos (z : ParabolicPoint) : 0 ≤ U z := vec3EuclideanNorm_nonneg _
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hthree : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
  have hUbound : (∫ z in outer, U z ^ 3) ≤ Bᵤ.toReal ^ 3 := by
    have hh := blowup_integral_norm_rpow_le_of_eLpNorm_le μ U 3
      (by norm_num) (hthree ▸ hu) Bᵤ hBᵤ (hthree ▸ hnbᵤ)
    simpa [U, Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      Real.rpow_natCast] using hh
  have hpbound : (∫ z in outer, |p z| ^ (3 / 2 : ℝ)) ≤
      Bₚ.toReal ^ (3 / 2 : ℝ) := by
    have hh := blowup_integral_norm_rpow_le_of_eLpNorm_le μ p (3 / 2)
      (by norm_num) (hcoeff ▸ hp) Bₚ hBₚ (hcoeff ▸ hnbₚ)
    simpa [Real.norm_eq_abs] using hh
  have hA : 0 ≤ 8 + 8 * C := by positivity
  have hP : 0 ≤ 4 * C := by positivity
  have h := hmass a b hb hsol hu hp
  calc
    2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Set.Ioo a b),
      spatialGradientSq u Du z) ≤
        (8 + 3 * C) * μ.real Set.univ +
          (8 + 8 * C) * (∫ z in outer, U z ^ 3) +
          4 * C * (∫ z in outer, |p z| ^ (3 / 2 : ℝ)) := by
      simpa only [μ, outer, U] using h
    _ ≤ (8 + 3 * C) * μ.real Set.univ +
        (8 + 8 * C) * Bᵤ.toReal ^ 3 +
        4 * C * Bₚ.toReal ^ (3 / 2 : ℝ) := by
      exact add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left hUbound hA) _)
        (mul_le_mul_of_nonneg_left hpbound hP)

end ESS
