/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffDerivatives
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Radii for unique-continuation propagation

The radii in `thm:uc` increase from the initial Gaussian ball toward the
full source ball.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The fraction of each remaining radius reached by one Gaussian
continuation step. -/
@[expose] def ucRadiusFraction : ℝ := (3 / 8) * Real.sqrt (2 / 100)

/-- The radius reached after `n` continuation steps in `thm:uc`. -/
@[expose] def ucRadius (R : ℝ) (n : ℕ) : ℝ :=
  R * (1 - (1 - ucRadiusFraction) ^ (n + 1))

/-- The continuation fraction lies strictly between zero and one. -/
theorem ucRadiusFraction_pos_lt_one :
    0 < ucRadiusFraction ∧ ucRadiusFraction < 1 := by
  have hμ : 0 < Real.sqrt (2 / 100 : ℝ) := by positivity
  have hμsq : Real.sqrt (2 / 100 : ℝ) ^ 2 = 1 / 50 := by norm_num
  have hμhalf : Real.sqrt (2 / 100 : ℝ) < 1 / 2 := by
    nlinarith only [hμ, hμsq]
  unfold ucRadiusFraction
  constructor
  · positivity
  · nlinarith only [hμhalf]

/-- The first radius equals the Gaussian lemma's initial spatial radius. -/
theorem ucRadius_zero (R : ℝ) :
    ucRadius R 0 = ucRadiusFraction * R := by
  simp [ucRadius]
  ring

/-- The radii follow the affine recurrence in the proof of `thm:uc`. -/
theorem ucRadius_succ (R : ℝ) (n : ℕ) :
    ucRadius R (n + 1) =
      ucRadius R n + ucRadiusFraction * (R - ucRadius R n) := by
  simp only [ucRadius, Nat.add_assoc, pow_succ]
  ring

/-- Every continuation radius is positive and below the original radius. -/
theorem ucRadius_pos_lt (R : ℝ) (hR : 0 < R) (n : ℕ) :
    0 < ucRadius R n ∧ ucRadius R n < R := by
  let q : ℝ := 1 - ucRadiusFraction
  have hβ := ucRadiusFraction_pos_lt_one
  have hq : 0 < q ∧ q < 1 := by
    dsimp [q]
    constructor <;> linarith only [hβ.1, hβ.2]
  have hpow0 : 0 < q ^ (n + 1) := pow_pos hq.1 _
  have hpow1 : q ^ (n + 1) < 1 := by
    exact (pow_lt_one₀ hq.1.le hq.2 (Nat.succ_ne_zero n))
  dsimp [ucRadius]
  constructor
  · exact mul_pos hR (by linarith only [hpow1])
  · have hfactor : 1 - q ^ (n + 1) < 1 := by
      linarith only [hpow0]
    have := mul_lt_mul_of_pos_left hfactor hR
    simpa only [mul_one, q] using this

/-- Every point in the source ball lies inside some continuation radius. -/
theorem ucRadius_eventually_covers
    (R d : ℝ) (hR : 0 < R) (hd : d < R) :
    ∃ n : ℕ, d < ucRadius R n := by
  let q : ℝ := 1 - ucRadiusFraction
  have hβ := ucRadiusFraction_pos_lt_one
  have hq : q < 1 := by dsimp [q]; linarith only [hβ.1]
  have hmargin : 0 < (R - d) / R := div_pos (sub_pos.mpr hd) hR
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hmargin hq
  refine ⟨n, ?_⟩
  have hq0 : 0 ≤ q := by dsimp [q]; linarith only [hβ.2]
  have hnonneg : 0 ≤ q ^ n := pow_nonneg hq0 _
  have hpow : q ^ (n + 1) ≤ q ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right hnonneg hq.le
  have hpowSmall : q ^ (n + 1) < (R - d) / R := lt_of_le_of_lt hpow hn
  have hmul := (lt_div_iff₀ hR).1 hpowSmall
  dsimp [ucRadius]
  change d < R * (1 - q ^ (n + 1))
  nlinarith only [hmul]

/-- Every radius is at least the initial Gaussian radius. -/
theorem ucRadius_initial_le
    (R : ℝ) (hR : 0 < R) (n : ℕ) :
    ucRadius R 0 ≤ ucRadius R n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      have hr := (ucRadius_pos_lt R hR n).2
      have hβ := ucRadiusFraction_pos_lt_one.1
      rw [ucRadius_succ]
      exact ih.trans (le_add_of_nonneg_right (mul_nonneg hβ.le (sub_nonneg.mpr hr.le)))

/-- A point in the next radius lies within the Gaussian reach of a center
strictly inside the current radius. -/
theorem uc_radius_step_center
    (R : ℝ) (hR : 0 < R) (n : ℕ) (x : Vec3)
    (hinner : ucRadius R n ≤ vec3EuclideanNorm x)
    (houter : vec3EuclideanNorm x < ucRadius R (n + 1)) :
    ∃ x₀ : Vec3,
      x₀ ∈ vec3Ball 0 (ucRadius R n) ∧
      x₀ ∈ vec3Ball 0 R ∧
      x ∈ vec3Ball x₀
        (ucRadiusFraction * (R - vec3EuclideanNorm x₀)) := by
  let r : ℝ := ucRadius R n
  let d : ℝ := vec3EuclideanNorm x
  let β : ℝ := ucRadiusFraction
  let M : ℝ := ucRadius R (n + 1) - d
  let s : ℝ := r - M / 2
  let x₀ : Vec3 := (s / d) • x
  have hβ := ucRadiusFraction_pos_lt_one
  have hr : 0 < r ∧ r < R := ucRadius_pos_lt R hR n
  have hd : 0 < d := lt_of_lt_of_le hr.1 hinner
  have hM : 0 < M := sub_pos.mpr houter
  have hβR : β * R ≤ r := by
    calc
      β * R = ucRadius R 0 := (ucRadius_zero R).symm
      _ ≤ r := ucRadius_initial_le R hR n
  have hMle : M ≤ r := by
    have hstep := ucRadius_succ R n
    dsimp [M, r, d, β] at *
    have hβR' : ucRadiusFraction * (R - ucRadius R n) ≤
        ucRadiusFraction * R := by
      exact mul_le_mul_of_nonneg_left (by linarith only [hr.1]) hβ.1.le
    linarith only [hinner, hβR, hβR', hstep]
  have hs : 0 < s := by dsimp [s]; linarith only [hr.1, hMle]
  have hslt : s < r := by dsimp [s]; linarith only [hM]
  have hsd : s < d := lt_of_lt_of_le hslt hinner
  have hnormx₀ : vec3EuclideanNorm x₀ = s := by
    dsimp [x₀]
    rw [vec3EuclideanNorm_smul, abs_of_pos (div_pos hs hd)]
    change (s / d) * d = s
    field_simp [hd.ne']
  have hdiff : x - x₀ = (1 - s / d) • x := by
    dsimp [x₀]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnormdiff : vec3EuclideanNorm (x - x₀) = d - s := by
    rw [hdiff, vec3EuclideanNorm_smul]
    have hcoef : 0 < 1 - s / d := by
      apply sub_pos.mpr
      exact (div_lt_one hd).2 hsd
    rw [abs_of_pos hcoef]
    change (1 - s / d) * d = d - s
    field_simp [hd.ne']
  have hgap : β * (R - s) - (d - s) = (1 + β) * M / 2 := by
    dsimp [s, M, r, d, β]
    rw [ucRadius_succ]
    ring
  have hgapPos : 0 < (1 + β) * M / 2 := by
    have hβ0 : 0 < β := hβ.1
    positivity
  refine ⟨x₀, ?_, ?_, ?_⟩
  · apply (mem_vec3Ball).2
    simpa only [sub_zero, hnormx₀] using hslt
  · apply (mem_vec3Ball).2
    simpa only [sub_zero, hnormx₀] using hslt.trans hr.2
  · apply (mem_vec3Ball).2
    rw [hnormdiff, hnormx₀]
    linarith only [hgap, hgapPos]

end ESS
