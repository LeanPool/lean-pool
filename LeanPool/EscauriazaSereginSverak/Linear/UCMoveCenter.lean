/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCMoveGeometry

/-!
# Transfer of integral flatness to a nearby center

The Gaussian estimate, a finite spatial cover, and overlapping time slabs
propagate infinite-order integral vanishing within its spatial reach.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Gaussian box decay moves integral flatness from one center to every
center in its inner output ball (`thm:uc`). -/
theorem uc_move_center_integral_flatness
    (x₀ y₀ : Vec3) (R T : ℝ) (hR : 0 < R) (hT : 0 < T)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)) volume)
    (hflat : UCIntegralFlatness x₀ R T w)
    (hgauss : ∃ γ C : ℝ, 0 < γ ∧ γ < 3 / 16 ∧ 0 < C ∧
      ∀ (x : Vec3) (t : ℝ), 0 < t → t ≤ γ * T →
        vec3EuclideanNorm (x - x₀) ≤ ucRadiusFraction * R →
        (16 / 100) * t ≤ vec3EuclideanNorm (x - x₀) ^ 2 →
        (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t)))
          (Ioo t (2 * t)), vec3EuclideanNorm (w z) ^ 2) ≤
          C * ucLocalEnergy x₀ R T w Dw *
            Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)))
    (hy : y₀ ∈ vec3Ball x₀ (ucRadiusFraction * R)) :
    UCIntegralFlatness y₀ R T w := by
  by_cases hyneq : y₀ = x₀
  · simpa only [hyneq] using hflat
  obtain ⟨γ, C, hγ, _, _, hbox⟩ := hgauss
  obtain ⟨L, S, δ, hL, hS, hδ, hδL, hδS, hUsub, hgeom⟩ :=
    uc_move_center_geometry x₀ y₀ R T γ hR hT hγ hy hyneq
  obtain ⟨F, _, hF⟩ := uc_unit_ball_finite_half_cover
  have hFpos : 0 < F.card := by
    have h0 : (0 : Vec3) ∈ closure (vec3Ball 0 1) := by
      rw [closure_vec3Ball (by norm_num)]
      simp only [Set.mem_ofPred_eq, sub_zero, vec3EuclideanNorm_zero]
      norm_num
    obtain ⟨c, hc, _⟩ := hF 0 h0
    exact Finset.card_pos.mpr ⟨c, hc⟩
  let d : ℝ := vec3EuclideanNorm (y₀ - x₀)
  have hd0 : 0 ≤ d := vec3EuclideanNorm_nonneg _
  have hd : 0 < d := by
    by_contra hnot
    have hd0' : d = 0 := le_antisymm (le_of_not_gt hnot) hd0
    have hnorm : vecEuclideanNorm (y₀ - x₀) = 0 := by
      simpa [d, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq,
        vecDot, pow_two] using hd0'
    exact hyneq (sub_eq_zero.mp (vecEuclideanNorm_eq_zero_iff.mp hnorm))
  let b : ℝ := d ^ 2 / 8
  have hb : 0 < b := by dsimp [b]; positivity
  let A : ℝ := |C * ucLocalEnergy x₀ R T w Dw|
  have hA : 0 ≤ A := abs_nonneg _
  have hboxUniform (r : ℝ) (hr : 0 < r) (hrδ : r < δ)
      (n : ℕ) (c : Vec3) (hc : c ∈ vec3Ball y₀ (2 * r)) :
      (∫ z in spaceTimeSet
        (vec3Ball c (Real.sqrt
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))))
        (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))),
        vec3EuclideanNorm (w z) ^ 2) ≤
          A * Real.exp (-(b /
            ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))) := by
    let t : ℝ := (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2
    have ht : 0 < t := by dsimp [t]; positivity
    obtain ⟨hcupper, hclower, htime, htd⟩ :=
      hgeom r hr hrδ n c hc
    have hgauss' := hbox c t ht htime hcupper htd
    have hnorm0 : 0 ≤ vec3EuclideanNorm (c - x₀) :=
      vec3EuclideanNorm_nonneg _
    have hnormSq : d ^ 2 / 4 ≤
        vec3EuclideanNorm (c - x₀) ^ 2 := by
      change d / 2 ≤ vec3EuclideanNorm (c - x₀) at hclower
      nlinarith only [hclower, hd, hnorm0]
    have hArg : -(vec3EuclideanNorm (c - x₀) ^ 2) / (2 * t) ≤
        -(b / t) := by
      dsimp [b]
      have hmul := mul_le_mul_of_nonneg_right hnormSq ht.le
      have hArg' : (-vec3EuclideanNorm (c - x₀) ^ 2) / (2 * t) ≤
          (-(d ^ 2 / 8)) / t := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * t) ht).mpr
        nlinarith only [hmul]
      convert hArg' using 1 ; ring
    have hExp : Real.exp
        (-(vec3EuclideanNorm (c - x₀) ^ 2) / (2 * t)) ≤
        Real.exp (-(b / t)) := Real.exp_le_exp.mpr hArg
    have hcoeff : C * ucLocalEnergy x₀ R T w Dw ≤ A :=
      le_abs_self _
    have hgauss'' : (∫ z in spaceTimeSet
        (vec3Ball c (Real.sqrt (2 * t))) (Ioo t (2 * t)),
        vec3EuclideanNorm (w z) ^ 2) ≤
          C * ucLocalEnergy x₀ R T w Dw *
            Real.exp (-(vec3EuclideanNorm (c - x₀) ^ 2) / (2 * t)) :=
      hgauss'
    calc
      _ ≤ C * ucLocalEnergy x₀ R T w Dw *
          Real.exp (-(vec3EuclideanNorm (c - x₀) ^ 2) / (2 * t)) :=
        hgauss''
      _ ≤ A * Real.exp
          (-(vec3EuclideanNorm (c - x₀) ^ 2) / (2 * t)) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
      _ ≤ A * Real.exp (-(b / t)) :=
        mul_le_mul_of_nonneg_left hExp hA
  exact uc_gaussian_neighborhood_flatness F hF hFpos y₀ R T
    L S δ A b hL hS hδ hδL hδS hA hb w
    (hInt.mono_set hUsub) hboxUniform

end ESS
