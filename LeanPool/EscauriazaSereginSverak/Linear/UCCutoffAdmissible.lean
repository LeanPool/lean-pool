/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCSpatialCutoff
public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoff

/-!
# Support of the Gaussian cutoff

The product cutoff in `lem:uc-gaussian` is smooth, compactly supported
inside the normalized cylinder, and equals one on the inner box after its
initial transition.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The scalar cutoff used in the Gaussian unique-continuation estimate. -/
@[expose] def ucGaussianCutoff (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) :
    ParabolicPoint → ℝ :=
  ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε)

/-- The Gaussian scalar cutoff is smooth. -/
theorem ucGaussianCutoff_smooth (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ucGaussianCutoff ρ hρ ε z) := by
  unfold ucGaussianCutoff ucCutoffScalar
  exact (((ucSpatialCutoff_smooth hρ).comp contDiff_fst).mul
    (ucFinalTimeCutoff_smooth.comp contDiff_snd)).mul
    ((ucInitialTimeCutoff_smooth ε).comp contDiff_snd)

/-- The support of the Gaussian scalar cutoff lies in a fixed compact
spatial ball and a closed positive-time interval. -/
theorem ucGaussianCutoff_support_subset
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    Function.support (ucGaussianCutoff ρ hρ ε) ⊆
      euclideanClosedBall 0 (3 * ρ / 4) ×ˢ Icc ε (7 / 4) := by
  intro z hz
  have hθne : ucSpatialCutoff ρ hρ z.1 ≠ 0 := by
    intro hzero
    exact hz (by simp [ucGaussianCutoff, ucCutoffScalar, hzero])
  have hηne : ucFinalTimeCutoff z.2 ≠ 0 := by
    intro hzero
    exact hz (by simp [ucGaussianCutoff, ucCutoffScalar, hzero])
  have hχne : ucInitialTimeCutoff ε z.2 ≠ 0 := by
    intro hzero
    exact hz (by simp [ucGaussianCutoff, ucCutoffScalar, hzero])
  have hθsupport : z.1 ∈ tsupport (ucSpatialCutoff ρ hρ) :=
    subset_tsupport _ (Function.mem_support.mpr hθne)
  have hθball : z.1 ∈ euclideanBall 0 (3 * ρ / 4) :=
    mollifiedBallCutoff_tsupport_subset_outer 0 hρ hθsupport
  have hθclosed : z.1 ∈ euclideanClosedBall 0 (3 * ρ / 4) := by
    change euclideanSqDist z.1 0 ≤ (3 * ρ / 4) ^ 2
    exact hθball.le
  have hεtime : ε ≤ z.2 := by
    by_contra hnot
    exact hχne (ucInitialTimeCutoff_eq_zero hε (le_of_lt (lt_of_not_ge hnot)))
  have hηtime : z.2 ≤ 7 / 4 := by
    by_contra hnot
    exact hηne (ucFinalTimeCutoff_eq_zero (le_of_lt (lt_of_not_ge hnot)))
  exact ⟨hθclosed, ⟨hεtime, hηtime⟩⟩

/-- The Gaussian cutoff has compact support. -/
theorem ucGaussianCutoff_hasCompactSupport
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    HasCompactSupport (ucGaussianCutoff ρ hρ ε) := by
  let Kprod : Set (Vec3 × ℝ) :=
    euclideanClosedBall (0 : Vec3) (3 * ρ / 4) ×ˢ Icc ε (7 / 4)
  have hKprod : IsCompact Kprod :=
    (isCompact_euclideanClosedBall (0 : Vec3) (by positivity)).prod isCompact_Icc
  let K : Set ParabolicPoint := parabolicHomeomorph.symm '' Kprod
  have hK : IsCompact K := parabolicHomeomorph.symm.isCompact_image.mpr hKprod
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  exact ⟨(z.1, z.2), ucGaussianCutoff_support_subset hρ hε hz, rfl⟩

/-- The topological support stays strictly inside the positive-time
normalized cylinder. -/
theorem ucGaussianCutoff_tsupport_subset_cylinder
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    tsupport (ucGaussianCutoff ρ hρ ε) ⊆ ucCylinder ρ := by
  let K : Set ParabolicPoint :=
    parabolicHomeomorph.symm ''
      (euclideanClosedBall (0 : Vec3) (3 * ρ / 4) ×ˢ Icc ε (7 / 4))
  have hKclosed : IsClosed K := by
    have hKprod : IsCompact
        (euclideanClosedBall (0 : Vec3) (3 * ρ / 4) ×ˢ Icc ε (7 / 4)) :=
      (isCompact_euclideanClosedBall (0 : Vec3) (by positivity)).prod isCompact_Icc
    exact (parabolicHomeomorph.symm.isCompact_image.mpr hKprod).isClosed
  have hsupport : Function.support (ucGaussianCutoff ρ hρ ε) ⊆ K := by
    intro z hz
    exact ⟨(z.1, z.2), ucGaussianCutoff_support_subset hρ hε hz, rfl⟩
  have hts : tsupport (ucGaussianCutoff ρ hρ ε) ⊆ K :=
    closure_minimal hsupport hKclosed
  intro z hz
  obtain ⟨q, hq, rfl⟩ := hts hz
  constructor
  · apply (mem_vec3Ball).2
    have hsp : q.1 ∈ euclideanBall 0 ρ :=
      euclideanClosedBall_subset_euclideanBall
        (show (0 : ℝ) ≤ 3 * ρ / 4 by positivity)
        (by linarith only [hρ]) hq.1
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1 hsp
  · exact ⟨lt_of_lt_of_le hε hq.2.1,
      lt_of_le_of_lt hq.2.2 (by norm_num)⟩

/-- The Gaussian cutoff equals one on the interior after the initial-time
transition. -/
theorem ucGaussianCutoff_eq_one_on_inner
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {z : ParabolicPoint} (hz : z ∈ ucInnerRegion ρ)
    (hs : 2 * ε ≤ z.2) :
    ucGaussianCutoff ρ hρ ε z = 1 := by
  have hθ := ucSpatialCutoff_eq_one hρ hz.1
  have hη := ucFinalTimeCutoff_eq_one hz.2.2.le
  have hχ := ucInitialTimeCutoff_eq_one hε hs
  simp [ucGaussianCutoff, ucCutoffScalar, hθ, hη, hχ]

/-- The Gaussian cutoff takes values between zero and one. -/
theorem ucGaussianCutoff_bounds
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ) (z : ParabolicPoint) :
    0 ≤ ucGaussianCutoff ρ hρ ε z ∧
      ucGaussianCutoff ρ hρ ε z ≤ 1 := by
  obtain ⟨hθ0, hθ1⟩ := ucSpatialCutoff_bounds hρ z.1
  obtain ⟨hη0, hη1⟩ := ucFinalTimeCutoff_bounds z.2
  obtain ⟨hχ0, hχ1⟩ := ucInitialTimeCutoff_bounds ε z.2
  dsimp [ucGaussianCutoff, ucCutoffScalar]
  constructor
  · positivity
  · have hprod : ucSpatialCutoff ρ hρ z.1 * ucFinalTimeCutoff z.2 ≤ 1 := by
      calc
        _ ≤ 1 * ucFinalTimeCutoff z.2 :=
          mul_le_mul_of_nonneg_right hθ1 hη0
        _ ≤ 1 * 1 :=
          mul_le_mul_of_nonneg_left hη1 (by norm_num)
        _ = 1 := by ring
    calc
      _ ≤ 1 * ucInitialTimeCutoff ε z.2 :=
        mul_le_mul_of_nonneg_right hprod hχ0
      _ ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left hχ1 (by norm_num)
      _ = 1 := by ring

end ESS
