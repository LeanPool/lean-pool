/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatCommutatorIntegral

/-!
# The pointwise heat bound from the cut-off representation

If `w(x, s)` is given by the cut-off heat representation, with the flux `Y` bounded by `Λ` and
the potential `U` bounded by `M` on the backward window, then `|w(x, s)| ≤ C (ρΛ + M/ρ)`: the
main term gains the factor `ρ` from the integral of the kernel gradient and the cutoff term costs
`ρ⁻¹`. This is the final step of the pointwise heat bound of the interior estimates in the proof
of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section
namespace CIV



/-- A kernel supported in the window, integrable before `s`, against a function bounded by `Λ`
on the window. -/
theorem abs_integral_kernel_mul_le {K F : ParabolicPoint → ℝ} {x : Vec3} {s ρ Λ : ℝ}
    (hK : IntegrableOn (fun z => K z) {z : ParabolicPoint | z.2 < s})
    (hsupp : ∀ z : ParabolicPoint, z.2 < s →
      z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s → K z = 0)
    (hF : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s, |F z| ≤ Λ) :
    |∫ z in {z : ParabolicPoint | z.2 < s}, K z * F z| ≤
      Λ * ∫ z in {z : ParabolicPoint | z.2 < s}, |K z| := by
  have hUm : MeasurableSet {z : ParabolicPoint | z.2 < s} :=
    measurableSet_lt measurable_snd measurable_const
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _))
    (hK.abs.const_mul Λ) ((ae_restrict_iff' hUm).mpr (Filter.Eventually.of_forall ?_))
  intro z hz
  show |K z * F z| ≤ Λ * |K z|
  by_cases hw : z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
  · rw [abs_mul, mul_comm Λ]
    exact mul_le_mul_of_nonneg_left (hF z hw) (abs_nonneg _)
  · rw [hsupp z hz hw, zero_mul, abs_zero, mul_zero]

/-- The pointwise heat bound, given the cut-off heat representation of `w(x, s)`. -/
theorem heat_pointwise_bound_of_decomposition : ∃ C : ℝ, 0 < C ∧ ∀ (w : ParabolicPoint → ℝ)
    (U Y : Fin 3 → ParabolicPoint → ℝ) (x : Vec3) (s ρ Λ M : ℝ), 0 < ρ → ρ ≤ 1 →
    (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s, ∀ j, |Y j z| ≤ Λ) →
    (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s, ∀ l, |U l z| ≤ M) →
    w (x, s) =
      -(∑ j, ∫ z in {z : ParabolicPoint | z.2 < s},
          spatialPartial (serrinHeatWeight x s ρ) j z * Y j z) -
        ∑ l, ∫ z in {z : ParabolicPoint | z.2 < s},
          U l z * spatialPartial (serrinCutoffKernel x s ρ) l z →
    |w (x, s)| ≤ C * (ρ * Λ + M / ρ) := by
  obtain ⟨C₃, hC₃, hC₃b⟩ := serrinHeatWeight_spatialPartial_integral
  obtain ⟨C₄, hC₄, hC₄b⟩ := serrinCutoffKernel_spatialPartial_integral
  refine ⟨3 * C₃ + 3 * C₄, by positivity, ?_⟩
  intro w U Y x s ρ Λ M hρ hρ1 hY hU hdec
  have hc : ((x, s) : ParabolicPoint) ∈
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s := by
    refine ⟨?_, ?_, le_rfl⟩
    · show vec3EuclideanNorm (x - x) ≤ ρ
      rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le
    · show s - ρ ^ 2 ≤ s
      have := sq_nonneg ρ
      linarith only [this]
  have hΛ : 0 ≤ Λ := (abs_nonneg _).trans (hY _ hc 0)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hU _ hc 0)
  have hmain : ∀ j, |∫ z in {z : ParabolicPoint | z.2 < s},
      spatialPartial (serrinHeatWeight x s ρ) j z * Y j z| ≤ Λ * (C₃ * ρ) := by
    intro j
    obtain ⟨hi, hb⟩ := hC₃b x s ρ hρ hρ1 j
    refine (abs_integral_kernel_mul_le hi (fun z hz hw =>
      (spatialPartial_serrinKernels_eq_zero x hρ hz hw j).1) (fun z hz => hY z hz j)).trans ?_
    exact mul_le_mul_of_nonneg_left hb hΛ
  have hcut : ∀ l, |∫ z in {z : ParabolicPoint | z.2 < s},
      U l z * spatialPartial (serrinCutoffKernel x s ρ) l z| ≤ M * (C₄ / ρ) := by
    intro l
    obtain ⟨hi, hb⟩ := hC₄b x s ρ hρ hρ1 l
    have e : ∫ z in {z : ParabolicPoint | z.2 < s},
        U l z * spatialPartial (serrinCutoffKernel x s ρ) l z =
        ∫ z in {z : ParabolicPoint | z.2 < s},
          spatialPartial (serrinCutoffKernel x s ρ) l z * U l z := by
      congr 1; funext z; ring
    rw [e]
    refine (abs_integral_kernel_mul_le hi (fun z hz hw =>
      (spatialPartial_serrinKernels_eq_zero x hρ hz hw l).2) (fun z hz => hU z hz l)).trans ?_
    exact mul_le_mul_of_nonneg_left hb hM
  rw [hdec]
  have h1 : |∑ j, ∫ z in {z : ParabolicPoint | z.2 < s},
      spatialPartial (serrinHeatWeight x s ρ) j z * Y j z| ≤ 3 * (Λ * (C₃ * ρ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _j : Fin 3, Λ * (C₃ * ρ) := Finset.sum_le_sum (fun j _ => hmain j)
      _ = 3 * (Λ * (C₃ * ρ)) := by simp
  have h2 : |∑ l, ∫ z in {z : ParabolicPoint | z.2 < s},
      U l z * spatialPartial (serrinCutoffKernel x s ρ) l z| ≤ 3 * (M * (C₄ / ρ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _l : Fin 3, M * (C₄ / ρ) := Finset.sum_le_sum (fun l _ => hcut l)
      _ = 3 * (M * (C₄ / ρ)) := by simp
  refine (abs_sub _ _).trans ?_
  rw [abs_neg]
  have h3 : 3 * (Λ * (C₃ * ρ)) + 3 * (M * (C₄ / ρ)) ≤ (3 * C₃ + 3 * C₄) * (ρ * Λ + M / ρ) := by
    have hMρ : 0 ≤ M / ρ := div_nonneg hM hρ.le
    have e1 : 3 * (Λ * (C₃ * ρ)) = 3 * C₃ * (ρ * Λ) := by ring
    have e2 : 3 * (M * (C₄ / ρ)) = 3 * C₄ * (M / ρ) := by ring
    rw [e1, e2]
    nlinarith only [mul_nonneg hC₃.le hMρ, mul_nonneg hC₄.le (mul_nonneg hρ.le hΛ)]
  linarith only [h1, h2, h3]

end CIV
