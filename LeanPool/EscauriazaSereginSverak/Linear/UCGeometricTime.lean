/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCBallCover

/-!
# Overlapping geometric time slabs

The slabs overlap so that every positive time belongs to one of them.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A geometric sequence of overlapping time slabs covers `(0,r²)`. -/
theorem uc_geometric_time_cover
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hsr : s < r ^ 2) :
    ∃ n : ℕ,
      (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2 < s ∧
      s < 2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hx : 0 < s / r ^ 2 := div_pos hs hr2
  have hx1 : s / r ^ 2 ≤ 1 := (div_le_one hr2).mpr hsr.le
  obtain ⟨n, hlow, hupp⟩ := exists_nat_pow_near_of_lt_one
    hx hx1 (by norm_num : (0 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
  have hpow : 0 < (3 / 4 : ℝ) ^ n := pow_pos (by norm_num) _
  have hlow' : (3 / 4 : ℝ) ^ (n + 1) * r ^ 2 < s := by
    have h := mul_lt_mul_of_pos_right hlow hr2
    simpa only [div_mul_cancel₀ _ hr2.ne'] using h
  have hupp' : s ≤ (3 / 4 : ℝ) ^ n * r ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hupp hr2.le
    simpa only [div_mul_cancel₀ _ hr2.ne'] using h
  refine ⟨n, ?_, ?_⟩
  · rw [pow_succ] at hlow'
    have hfactor : (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2 <
        (3 / 4) ^ n * (3 / 4) * r ^ 2 := by
      have hp : 0 < (3 / 4 : ℝ) ^ n * r ^ 2 := mul_pos hpow hr2
      nlinarith only [hp]
    exact hfactor.trans hlow'
  · have hfactor : (3 / 4 : ℝ) ^ n * r ^ 2 <
        2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2) := by
      have hp : 0 < (3 / 4 : ℝ) ^ n * r ^ 2 := mul_pos hpow hr2
      nlinarith only [hp]
    exact hupp'.trans_lt hfactor

/-- The half-radius spatial cover fits inside each Gaussian time-slab box. -/
theorem uc_geometric_cover_radius_le
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    r / (2 : ℝ) ^ (n + 1) ≤
      Real.sqrt (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)) := by
  let q : ℝ := r / (2 : ℝ) ^ (n + 1)
  let t : ℝ := (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ 2 * t := by dsimp [t]; positivity
  have hpow : (1 / 4 : ℝ) ^ n ≤ (3 / 4 : ℝ) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hqSq : q ^ 2 = r ^ 2 / 4 * (1 / 4 : ℝ) ^ n := by
    dsimp [q]
    have hpowid : (2⁻¹ : ℝ) ^ (n * 2) = (1 / 4 : ℝ) ^ n := by
      rw [mul_comm n 2, pow_mul]
      norm_num
    rw [div_pow, pow_succ (2 : ℝ) n, mul_pow]
    ring_nf
    rw [hpowid]
  have hfactor : r ^ 2 / 4 * (1 / 4 : ℝ) ^ n ≤
      r ^ 2 / 4 * (3 / 4 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hfactor2 : r ^ 2 / 4 * (3 / 4 : ℝ) ^ n ≤ 2 * t := by
    dsimp [t]
    have hp : 0 ≤ r ^ 2 * (3 / 4 : ℝ) ^ n := by positivity
    nlinarith only [hp]
  have hsq : q ^ 2 ≤ 2 * t := hqSq ▸ hfactor.trans hfactor2
  have hle : q ≤ Real.sqrt (2 * t) :=
    (sq_le_sq₀ hq (Real.sqrt_nonneg _)).mp
      (by rwa [Real.sq_sqrt ht])
  exact hle

/-- The geometric slabs cover the full local positive-time cylinder. -/
theorem uc_geometric_slabs_cover
    (x : Vec3) (r : ℝ) (hr : 0 < r) :
    spaceTimeSet (vec3Ball x r) (Ioo 0 (r ^ 2)) ⊆
      ⋃ n : ℕ, spaceTimeSet (vec3Ball x r)
        (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))) := by
  intro z hz
  obtain ⟨n, hlow, hupp⟩ :=
    uc_geometric_time_cover r z.2 hr hz.2.1 hz.2.2
  exact mem_iUnion.mpr ⟨n, ⟨hz.1, ⟨hlow, hupp⟩⟩⟩

end ESS
