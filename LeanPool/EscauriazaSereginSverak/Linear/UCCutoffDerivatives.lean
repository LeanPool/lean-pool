/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffAdmissible

/-!
# Derivatives of the Gaussian cutoff

The spatial and temporal derivatives separate because the Gaussian cutoff
is a product of a spatial factor and two time factors.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The combined time factor of the Gaussian cutoff. -/
@[expose] def ucGaussianTimeCutoff (ε s : ℝ) : ℝ :=
  ucFinalTimeCutoff s * ucInitialTimeCutoff ε s

/-- The combined time factor is smooth. -/
theorem ucGaussianTimeCutoff_smooth (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ucGaussianTimeCutoff ε) :=
  ucFinalTimeCutoff_smooth.mul (ucInitialTimeCutoff_smooth ε)

/-- The derivative of the combined time cutoff is the sum of its two
transition derivatives. -/
theorem ucGaussianTimeCutoff_deriv (ε s : ℝ) :
    deriv (ucGaussianTimeCutoff ε) s =
      deriv ucFinalTimeCutoff s * ucInitialTimeCutoff ε s +
        ucFinalTimeCutoff s * deriv (ucInitialTimeCutoff ε) s := by
  have hη : DifferentiableAt ℝ ucFinalTimeCutoff s :=
    ucFinalTimeCutoff_smooth.differentiable (by simp) s
  have hχ : DifferentiableAt ℝ (ucInitialTimeCutoff ε) s :=
    (ucInitialTimeCutoff_smooth ε).differentiable (by simp) s
  change deriv (ucFinalTimeCutoff * ucInitialTimeCutoff ε) s = _
  exact (hη.hasDerivAt.mul hχ.hasDerivAt).deriv

/-- The combined time cutoff takes values between zero and one. -/
theorem ucGaussianTimeCutoff_bounds (ε s : ℝ) :
    0 ≤ ucGaussianTimeCutoff ε s ∧ ucGaussianTimeCutoff ε s ≤ 1 := by
  obtain ⟨hη0, hη1⟩ := ucFinalTimeCutoff_bounds s
  obtain ⟨hχ0, hχ1⟩ := ucInitialTimeCutoff_bounds ε s
  unfold ucGaussianTimeCutoff
  constructor
  · positivity
  · calc
      ucFinalTimeCutoff s * ucInitialTimeCutoff ε s ≤
          1 * ucInitialTimeCutoff ε s :=
        mul_le_mul_of_nonneg_right hη1 hχ0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hχ1 (by norm_num)
      _ = 1 := by ring

/-- The combined time cutoff has a derivative bound separating the final
transition from the initial transition. -/
theorem ucGaussianTimeCutoff_abs_deriv_bound
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    |deriv (ucGaussianTimeCutoff ε) s| ≤ 32 + 8 / ε := by
  rw [ucGaussianTimeCutoff_deriv]
  have hη := ucFinalTimeCutoff_abs_deriv_le s
  have hχ := ucInitialTimeCutoff_abs_deriv_le hε s
  obtain ⟨hη0, hη1⟩ := ucFinalTimeCutoff_bounds s
  obtain ⟨hχ0, hχ1⟩ := ucInitialTimeCutoff_bounds ε s
  have hηabs : |ucFinalTimeCutoff s| ≤ 1 := by
    simpa only [abs_of_nonneg hη0] using hη1
  have hχabs : |ucInitialTimeCutoff ε s| ≤ 1 := by
    simpa only [abs_of_nonneg hχ0] using hχ1
  calc
    |deriv ucFinalTimeCutoff s * ucInitialTimeCutoff ε s +
        ucFinalTimeCutoff s * deriv (ucInitialTimeCutoff ε) s| ≤
      |deriv ucFinalTimeCutoff s * ucInitialTimeCutoff ε s| +
        |ucFinalTimeCutoff s * deriv (ucInitialTimeCutoff ε) s| :=
          abs_add_le _ _
    _ = |deriv ucFinalTimeCutoff s| * |ucInitialTimeCutoff ε s| +
        |ucFinalTimeCutoff s| * |deriv (ucInitialTimeCutoff ε) s| := by
          rw [abs_mul, abs_mul]
    _ ≤ 32 * 1 + 1 * (8 / ε) := by
      have hχderiv0 : 0 ≤ 8 / ε := by positivity
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_right hη (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hχabs (by norm_num))
      · exact (mul_le_mul_of_nonneg_right hηabs (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hχ (by norm_num))
    _ = 32 + 8 / ε := by ring

/-- The first spatial derivative is carried entirely by the spatial
factor. -/
theorem ucGaussianCutoff_spatialPartial
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    (z : ParabolicPoint) (j : Fin 3) :
    spatialPartial (ucGaussianCutoff ρ hρ ε) j z =
      spatialPartial
        (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j z *
          ucGaussianTimeCutoff ε z.2 := by
  rcases z with ⟨x, s⟩
  have hfun : ucGaussianCutoff ρ hρ ε =
      fun q : ParabolicPoint =>
        ucSpatialCutoff ρ hρ q.1 * ucGaussianTimeCutoff ε q.2 := by
    funext q
    simp [ucGaussianCutoff, ucCutoffScalar,
      ucGaussianTimeCutoff, mul_assoc]
  rw [hfun]
  have hθ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => ucSpatialCutoff ρ hρ q.1) :=
    (ucSpatialCutoff_smooth hρ).comp contDiff_fst
  simpa only [ParabolicPoint] using
    (spatialPartial_mul_time (ψ :=
      fun q : Vec3 × ℝ => ucSpatialCutoff ρ hρ q.1)
      (χ := ucGaussianTimeCutoff ε) hθ j (x, s))

/-- The second spatial derivative is carried entirely by the spatial
factor. -/
theorem ucGaussianCutoff_spatialSecondPartial
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    (z : ParabolicPoint) (i j : Fin 3) :
    spatialSecondPartial (ucGaussianCutoff ρ hρ ε) i j z =
      spatialSecondPartial
        (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) i j z *
          ucGaussianTimeCutoff ε z.2 := by
  rcases z with ⟨x, s⟩
  have hfun : ucGaussianCutoff ρ hρ ε =
      fun q : ParabolicPoint =>
        ucSpatialCutoff ρ hρ q.1 * ucGaussianTimeCutoff ε q.2 := by
    funext q
    simp [ucGaussianCutoff, ucCutoffScalar,
      ucGaussianTimeCutoff, mul_assoc]
  rw [hfun]
  have hθ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => ucSpatialCutoff ρ hρ q.1) :=
    (ucSpatialCutoff_smooth hρ).comp contDiff_fst
  simpa only [ParabolicPoint] using
    (spatialSecondPartial_mul_time (ψ :=
      fun q : Vec3 × ℝ => ucSpatialCutoff ρ hρ q.1)
      (χ := ucGaussianTimeCutoff ε) hθ i j (x, s))

/-- The time derivative is carried entirely by the combined time factor. -/
theorem ucGaussianCutoff_timePartial
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ) (z : ParabolicPoint) :
    timePartial (ucGaussianCutoff ρ hρ ε) z =
      ucSpatialCutoff ρ hρ z.1 * deriv (ucGaussianTimeCutoff ε) z.2 := by
  rcases z with ⟨x, s⟩
  have hfun : ucGaussianCutoff ρ hρ ε =
      fun q : ParabolicPoint =>
        ucSpatialCutoff ρ hρ q.1 * ucGaussianTimeCutoff ε q.2 := by
    funext q
    simp [ucGaussianCutoff, ucCutoffScalar,
      ucGaussianTimeCutoff, mul_assoc]
  rw [hfun]
  have hθ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => ucSpatialCutoff ρ hρ q.1) :=
    (ucSpatialCutoff_smooth hρ).comp contDiff_fst
  have hτ := ucGaussianTimeCutoff_smooth ε
  have h := timePartial_mul_time (ψ :=
    fun q : Vec3 × ℝ => ucSpatialCutoff ρ hρ q.1)
    (χ := ucGaussianTimeCutoff ε) hθ hτ (x, s)
  have hzero : timePartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) (x, s) = 0 := by
    unfold timePartial
    change (fderiv ℝ (Function.const ℝ (ucSpatialCutoff ρ hρ x)) s) 1 = 0
    simp
  change timePartial
      (fun q : ParabolicPoint =>
        ucSpatialCutoff ρ hρ q.1 * ucGaussianTimeCutoff ε q.2) (x, s) =
      timePartial (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) (x, s) *
        ucGaussianTimeCutoff ε s +
        ucSpatialCutoff ρ hρ x * deriv (ucGaussianTimeCutoff ε) s at h
  rw [hzero, zero_mul, zero_add] at h
  exact h

/-- The first spatial derivatives of the Gaussian cutoff obey the CKN ball
cutoff bound. -/
theorem ucGaussianCutoff_spatialPartial_bound
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    (z : ParabolicPoint) (j : Fin 3) :
    |spatialPartial (ucGaussianCutoff ρ hρ ε) j z| ≤
      cutoffGradientConstant / ρ := by
  rw [ucGaussianCutoff_spatialPartial hρ ε z j, abs_mul]
  obtain ⟨hτ0, hτ1⟩ := ucGaussianTimeCutoff_bounds ε z.2
  rw [abs_of_nonneg hτ0]
  have hθ := ucSpatialCutoff_spatialPartial_bound hρ z j
  have hcoef : 0 ≤ cutoffGradientConstant / ρ :=
    (abs_nonneg _).trans hθ
  calc
    |spatialPartial
        (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j z| *
        ucGaussianTimeCutoff ε z.2 ≤
      (cutoffGradientConstant / ρ) * ucGaussianTimeCutoff ε z.2 :=
        mul_le_mul_of_nonneg_right hθ hτ0
    _ ≤ (cutoffGradientConstant / ρ) * 1 :=
      mul_le_mul_of_nonneg_left hτ1 hcoef
    _ = _ := by ring

/-- The second spatial derivatives of the Gaussian cutoff obey the CKN ball
cutoff bound. -/
theorem ucGaussianCutoff_spatialSecondPartial_bound
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    (z : ParabolicPoint) (i j : Fin 3) :
    |spatialSecondPartial (ucGaussianCutoff ρ hρ ε) i j z| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  rw [ucGaussianCutoff_spatialSecondPartial hρ ε z i j, abs_mul]
  obtain ⟨hτ0, hτ1⟩ := ucGaussianTimeCutoff_bounds ε z.2
  rw [abs_of_nonneg hτ0]
  have hθ := ucSpatialCutoff_spatialSecondPartial_bound hρ z i j
  have hcoef : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 :=
    (abs_nonneg _).trans hθ
  calc
    |spatialSecondPartial
        (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) i j z| *
        ucGaussianTimeCutoff ε z.2 ≤
      (cutoffSecondDerivativeConstant / ρ ^ 2) *
        ucGaussianTimeCutoff ε z.2 :=
        mul_le_mul_of_nonneg_right hθ hτ0
    _ ≤ (cutoffSecondDerivativeConstant / ρ ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hτ1 hcoef
    _ = _ := by ring

/-- The time derivative of the Gaussian cutoff is bounded by a final-time
constant and the inverse initial transition length. -/
theorem ucGaussianCutoff_timePartial_bound
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (z : ParabolicPoint) :
    |timePartial (ucGaussianCutoff ρ hρ ε) z| ≤ 32 + 8 / ε := by
  rw [ucGaussianCutoff_timePartial hρ ε z, abs_mul]
  obtain ⟨hθ0, hθ1⟩ := ucSpatialCutoff_bounds hρ z.1
  rw [abs_of_nonneg hθ0]
  have hτ := ucGaussianTimeCutoff_abs_deriv_bound hε z.2
  have hτ0 : 0 ≤ 32 + 8 / ε := by positivity
  calc
    ucSpatialCutoff ρ hρ z.1 * |deriv (ucGaussianTimeCutoff ε) z.2| ≤
      1 * |deriv (ucGaussianTimeCutoff ε) z.2| :=
        mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _)
    _ ≤ 1 * (32 + 8 / ε) :=
      mul_le_mul_of_nonneg_left hτ (by norm_num)
    _ = _ := by ring

end ESS
