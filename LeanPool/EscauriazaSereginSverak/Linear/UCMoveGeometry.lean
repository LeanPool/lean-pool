/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCNeighborhoodBoxes

/-!
# Geometry for moving a Gaussian center

A small neighborhood of a new center stays inside the source cylinder,
and its covering centers satisfy the Gaussian output conditions.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The geometric parameters for transferring Gaussian decay to a nearby
spatial center. -/
theorem uc_move_center_geometry
    (x₀ y₀ : Vec3) (R T γ : ℝ)
    (hR : 0 < R) (hT : 0 < T) (hγ : 0 < γ)
    (hy : y₀ ∈ vec3Ball x₀ (ucRadiusFraction * R))
    (hyneq : y₀ ≠ x₀) :
    ∃ L S δ : ℝ, 0 < L ∧ 0 < S ∧ 0 < δ ∧
      δ ≤ L / 4 ∧ δ ≤ Real.sqrt (S / 2) ∧
      spaceTimeSet (vec3Ball y₀ L) (Ioo 0 S) ⊆
        spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T) ∧
      ∀ (r : ℝ), 0 < r → r < δ → ∀ n : ℕ,
        ∀ c ∈ vec3Ball y₀ (2 * r),
          vec3EuclideanNorm (c - x₀) ≤ ucRadiusFraction * R ∧
          vec3EuclideanNorm (y₀ - x₀) / 2 ≤
            vec3EuclideanNorm (c - x₀) ∧
          (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2 ≤ γ * T ∧
          (16 / 100 : ℝ) *
            ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2) ≤
              vec3EuclideanNorm (c - x₀) ^ 2 := by
  let d : ℝ := vec3EuclideanNorm (y₀ - x₀)
  have hd0 : 0 ≤ d := vec3EuclideanNorm_nonneg _
  have hd : 0 < d := by
    by_contra hnot
    have hd0' : d = 0 := le_antisymm (le_of_not_gt hnot) hd0
    have hnorm : vecEuclideanNorm (y₀ - x₀) = 0 := by
      simpa [d, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq,
        vecDot, pow_two] using hd0'
    exact hyneq (sub_eq_zero.mp (vecEuclideanNorm_eq_zero_iff.mp hnorm))
  have hβ := ucRadiusFraction_pos_lt_one
  have hdβ : d < ucRadiusFraction * R := (mem_vec3Ball).mp hy
  have hdR : d < R := by
    have hβR : ucRadiusFraction * R ≤ R := by
      nlinarith only [hβ.2, hR]
    exact hdβ.trans_le hβR
  let L : ℝ := (R - d) / 2
  let S : ℝ := T / 2
  have hL : 0 < L := by dsimp [L]; linarith only [hdR]
  have hS : 0 < S := by dsimp [S]; linarith only [hT]
  let δ : ℝ := min (L / 4)
    (min (Real.sqrt (S / 2))
      (min ((ucRadiusFraction * R - d) / 4)
        (min (d / 8) (Real.sqrt (γ * T / 2)))))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min (by positivity)
    apply lt_min (by positivity)
    apply lt_min (by linarith only [hdβ])
    exact lt_min (by positivity) (by positivity)
  have hδL : δ ≤ L / 4 := min_le_left _ _
  have hδS : δ ≤ Real.sqrt (S / 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδmargin : δ ≤ (ucRadiusFraction * R - d) / 4 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hδd : δ ≤ d / 8 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hδtime : δ ≤ Real.sqrt (γ * T / 2) :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨L, S, δ, hL, hS, hδ, hδL, hδS, ?_, ?_⟩
  · intro z hz
    constructor
    · have htri := vec3EuclideanNorm_add_le (z.1 - y₀) (y₀ - x₀)
      have heq : z.1 - y₀ + (y₀ - x₀) = z.1 - x₀ := by abel
      rw [heq] at htri
      have hzL : vec3EuclideanNorm (z.1 - y₀) < L :=
        (mem_vec3Ball).mp hz.1
      apply (mem_vec3Ball).mpr
      dsimp [L] at hzL
      linarith only [htri, hzL, hdR]
    · exact ⟨hz.2.1, hz.2.2.trans (by dsimp [S]; linarith only [hT])⟩
  · intro r hr hrδ n c hc
    let t : ℝ := (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htbound : t ≤ r ^ 2 := by
      have hp : (3 / 4 : ℝ) ^ n ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg r)
      dsimp [t]
      nlinarith only [hm, sq_nonneg r]
    have hδsq : δ ^ 2 ≤ γ * T / 2 := by
      have hγT : 0 ≤ γ * T / 2 := by positivity
      have hs := (sq_le_sq₀ hδ.le (Real.sqrt_nonneg _)).mpr hδtime
      rwa [Real.sq_sqrt hγT] at hs
    have htime : t ≤ γ * T := by
      have hrδsq : r ^ 2 ≤ δ ^ 2 :=
        (sq_le_sq₀ hr.le hδ.le).mpr hrδ.le
      nlinarith only [htbound, hrδsq, hδsq, mul_pos hγ hT]
    have hcnear : vec3EuclideanNorm (c - y₀) < 2 * r :=
      (mem_vec3Ball).mp hc
    have hcnear' : vec3EuclideanNorm (y₀ - c) < 2 * r := by
      rw [← vec3EuclideanNorm_neg (c - y₀), neg_sub] at hcnear
      exact hcnear
    have hupper : vec3EuclideanNorm (c - x₀) ≤
        vec3EuclideanNorm (c - y₀) + d := by
      have htri := vec3EuclideanNorm_add_le (c - y₀) (y₀ - x₀)
      have heq : c - y₀ + (y₀ - x₀) = c - x₀ := by abel
      simpa only [heq, d] using htri
    have hlower : d ≤ vec3EuclideanNorm (y₀ - c) +
        vec3EuclideanNorm (c - x₀) := by
      have htri := vec3EuclideanNorm_add_le (y₀ - c) (c - x₀)
      have heq : y₀ - c + (c - x₀) = y₀ - x₀ := by abel
      simpa only [heq, d] using htri
    have hcenterUpper : vec3EuclideanNorm (c - x₀) ≤
        ucRadiusFraction * R := by
      linarith only [hupper, hcnear, hrδ, hδmargin, hdβ]
    have hcenterLower : d / 2 ≤ vec3EuclideanNorm (c - x₀) := by
      linarith only [hlower, hcnear', hrδ, hδd, hd]
    have htd : (16 / 100 : ℝ) * t ≤
        vec3EuclideanNorm (c - x₀) ^ 2 := by
      have hrδsq : r ^ 2 ≤ δ ^ 2 :=
        (sq_le_sq₀ hr.le hδ.le).mpr hrδ.le
      have hδdSq : δ ^ 2 ≤ d ^ 2 / 64 := by
        nlinarith only [hδd, hδ.le, hd]
      have hcenterSq : d ^ 2 / 4 ≤ vec3EuclideanNorm (c - x₀) ^ 2 := by
        nlinarith only [hcenterLower, hd,
          vec3EuclideanNorm_nonneg (c - x₀)]
      nlinarith only [htbound, hrδsq, hδdSq, hcenterSq]
    exact ⟨hcenterUpper, hcenterLower, htime, htd⟩

end ESS
