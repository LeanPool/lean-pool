/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotentialCutoff

/-!
# Decay estimates for compact Riesz potential approximations

This file proves the uniform integrable bounds and pointwise convergence used
to extend pressure duality to decaying potential tests.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The Laplacian error introduced by the spatial cutoff, used by
`lem:riesz-duality`. -/
@[expose]
def rieszPressurePotentialLaplacianCutoffError
    (ψ : Vec3 × ℝ → ℝ) (n : ℕ) (z : Vec3 × ℝ) : ℝ :=
  rieszPressureJointLaplacian (rieszPressurePotentialCutoffTest ψ n) z -
    rieszPressureJointLaplacian ψ z

/-- The Hessian error introduced by the spatial cutoff, used by
`lem:riesz-duality`. -/
@[expose]
def rieszPressurePotentialHessianCutoffError
    (ψ : Vec3 × ℝ → ℝ) (i j : Fin 3) (n : ℕ) (z : Vec3 × ℝ) : ℝ :=
  rieszPressureJointHessian (rieszPressurePotentialCutoffTest ψ n) i j z -
    rieszPressureJointHessian ψ i j z

/-- The spatial product rule for the cutoff Laplacian, used by
`lem:riesz-duality`. -/
theorem rieszPressurePotentialCutoffTest_laplacian_formula
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ)
    (z : Vec3 × ℝ) :
    rieszPressureJointLaplacian (rieszPressurePotentialCutoffTest ψ n) z =
      rieszPressurePotentialCutoff n z.1 * rieszPressureJointLaplacian ψ z +
        2 * CKN.spatialGradDot (rieszPressurePotentialCutoff n)
          (fun x => ψ (x, z.2)) z.1 +
        ψ z * CKN.spatialLaplacian (rieszPressurePotentialCutoff n) z.1 := by
  let η := rieszPressurePotentialCutoff n
  let ψt : Vec3 → ℝ := fun x => ψ (x, z.2)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadius_pos n)
  have hψt : ContDiff ℝ (⊤ : ℕ∞) ψt := by
    exact hψ.comp (contDiff_id.prodMk contDiff_const)
  have hcutSlice := rieszPressure_sliceLaplacian_eq_joint
    (rieszPressurePotentialCutoffTest_contDiff hψ n) z
  have hψSlice := rieszPressure_sliceLaplacian_eq_joint hψ z
  rw [← hcutSlice]
  change CKN.spatialLaplacian (fun x => η x * ψt x) z.1 = _
  rw [CKN.spatialLaplacian_mul_smooth hη hψt]
  dsimp [ψt]
  rw [hψSlice]

/-- The spatial product rule for a cutoff Hessian component, used by
`lem:riesz-duality`. -/
theorem rieszPressurePotentialCutoffTest_hessian_formula
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    rieszPressureJointHessian (rieszPressurePotentialCutoffTest ψ n) i j z =
      CKN.mixedSecond (rieszPressurePotentialCutoff n) i j z.1 * ψ z +
      CKN.spatialDeriv (rieszPressurePotentialCutoff n) j z.1 *
        rieszPressureJointDirection ψ i z +
      CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 *
        rieszPressureJointDirection ψ j z +
      rieszPressurePotentialCutoff n z.1 * rieszPressureJointHessian ψ i j z := by
  let η := rieszPressurePotentialCutoff n
  let ψt : Vec3 → ℝ := fun x => ψ (x, z.2)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadius_pos n)
  have hψt : ContDiff ℝ (⊤ : ℕ∞) ψt := by
    exact hψ.comp (contDiff_id.prodMk contDiff_const)
  have hcutSlice := rieszPressure_sliceMixedSecond_eq_joint
    (rieszPressurePotentialCutoffTest_contDiff hψ n) i j z
  have hψSlice := rieszPressure_sliceMixedSecond_eq_joint hψ i j z
  have hdirI := rieszPressure_sliceSpatialDeriv_eq_joint hψ i z
  have hdirJ := rieszPressure_sliceSpatialDeriv_eq_joint hψ j z
  rw [← hcutSlice]
  change CKN.mixedSecond (fun x => η x * ψt x) i j z.1 = _
  rw [CKN.spatialSecondDeriv_mul_smooth hη hψt i j z.1]
  dsimp [ψt]
  rw [hψSlice, hdirI, hdirJ]

private theorem rieszPressurePotentialProfile_nonneg
    {K : Set ℝ} (z : Vec3 × ℝ) :
    0 ≤ rieszPressurePotentialSpatialProfile K z := by
  by_cases hz : z.2 ∈ K
  · simp [rieszPressurePotentialSpatialProfile, hz]
    positivity
  · simp [rieszPressurePotentialSpatialProfile, hz]

private theorem rieszPressurePotentialRpow_euclidean_le_norm
    (x : Vec3) (k : ℝ) (hk : k ≤ 0) :
    (1 + vec3EuclideanNorm x) ^ k ≤ (1 + ‖x‖) ^ k := by
  have hnorm0 := CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm x
  have hEq : CKN.vecEuclideanNorm x = vec3EuclideanNorm x := by
    rw [CKN.vecEuclideanNorm, CKN.vecNormSq_eq_sum_sq,
      CKN.Foundation.Parabolic.vec3EuclideanNorm]
  have hnorm : ‖x‖ ≤ CKN.vecEuclideanNorm x := by simpa [hEq] using hnorm0
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by linarith only [hnorm0]) hk

private theorem rieszPressurePotentialCutoffConstants_nonneg :
    0 ≤ CKN.cutoffGradientConstant ∧
      0 ≤ CKN.cutoffSecondDerivativeConstant := by
  have hg := CKN.mollifiedBallCutoff_gradient_bound 0
    (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
  have hh := CKN.mollifiedBallCutoff_second_derivative_bound 0
    (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
  constructor
  · have h := le_trans (CKN.vecEuclideanNorm_nonneg _) hg
    simpa using h
  · have h := le_trans (norm_nonneg _) hh
    simpa using h

private theorem rieszPressurePotentialCutoff_scale_reciprocal_bound
    {n : ℕ} {x : Vec3}
    (hx : x ∈ CKN.euclideanBall 0
      (3 * rieszPressurePotentialCutoffRadius n / 4)) :
    1 / rieszPressurePotentialCutoffScale n ≤ 3 / (1 + ‖x‖) := by
  have hR : 1 ≤ rieszPressurePotentialCutoffScale n :=
    rieszPressurePotentialCutoffScale_ge_one n
  have hRpos : 0 < rieszPressurePotentialCutoffScale n :=
    rieszPressurePotentialCutoffScale_pos n
  have hnorm0 := CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm x
  have hEq : CKN.vecEuclideanNorm x = vec3EuclideanNorm x := by
    rw [CKN.vecEuclideanNorm, CKN.vecNormSq_eq_sum_sq,
      CKN.Foundation.Parabolic.vec3EuclideanNorm]
  have hnorm : ‖x‖ ≤ CKN.vecEuclideanNorm x := by simpa [hEq] using hnorm0
  have houter := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (div_pos (mul_pos (by norm_num) (rieszPressurePotentialCutoffRadius_pos n))
      (by norm_num))).1 hx
  rw [sub_zero, rieszPressurePotentialCutoff_outer n] at houter
  have hnormOuter : ‖x‖ < 15 * rieszPressurePotentialCutoffScale n / 13 :=
    lt_of_le_of_lt hnorm houter
  have hden : 1 + ‖x‖ ≤ 3 * rieszPressurePotentialCutoffScale n := by
    calc
      1 + ‖x‖ = ‖x‖ + 1 := by ring
      _ ≤ 15 * rieszPressurePotentialCutoffScale n / 13 + 1 :=
        add_le_add_left hnormOuter.le 1
      _ ≤ 3 * rieszPressurePotentialCutoffScale n := by
        nlinarith only [hR]
  apply (div_le_div_iff₀ hRpos (by positivity)).2
  simpa only [one_mul] using hden

private theorem rieszPressurePotentialCutoff_gradient_profile_bound
    (n : ℕ) (i : Fin 3) (x : Vec3) :
    |CKN.spatialDeriv (rieszPressurePotentialCutoff n) i x| ≤
      3 * CKN.cutoffGradientConstant / (1 + ‖x‖) := by
  let S := rieszPressurePotentialCutoffScale n
  let ρ := rieszPressurePotentialCutoffRadius n
  by_cases hx : x ∈ CKN.euclideanBall 0 (3 * ρ / 4) \
      CKN.euclideanClosedBall 0 (13 * ρ / 20)
  · have hbase := rieszPressurePotentialCutoff_gradient_bound n i x
    have hrec := rieszPressurePotentialCutoff_scale_reciprocal_bound
      (n := n) (x := x) hx.1
    have hconst := rieszPressurePotentialCutoffConstants_nonneg.1
    calc
      |CKN.spatialDeriv (rieszPressurePotentialCutoff n) i x| ≤
          CKN.cutoffGradientConstant / S := by simpa [S] using hbase
      _ = CKN.cutoffGradientConstant * (1 / S) := by ring
      _ ≤ CKN.cutoffGradientConstant * (3 / (1 + ‖x‖)) :=
        mul_le_mul_of_nonneg_left hrec hconst
      _ = 3 * CKN.cutoffGradientConstant / (1 + ‖x‖) := by ring
  · have hzero := CKN.mollifiedBallCutoff_derivatives_vanish_outside_annulus 0
      (rieszPressurePotentialCutoffRadius_pos n) hx
    have hgrad : CKN.classicalGradient (rieszPressurePotentialCutoff n) x = 0 := by
      simpa [rieszPressurePotentialCutoff] using hzero.1
    have hsp : CKN.spatialDeriv (rieszPressurePotentialCutoff n) i x = 0 := by
      change CKN.classicalGradient (rieszPressurePotentialCutoff n) x i = 0
      exact congrFun hgrad i
    rw [hsp, abs_zero]
    exact div_nonneg (mul_nonneg (by norm_num)
      rieszPressurePotentialCutoffConstants_nonneg.1) (by positivity)

private theorem rieszPressurePotentialCutoff_hessian_profile_bound
    (n : ℕ) (i j : Fin 3) (x : Vec3) :
    |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j x| ≤
      9 * CKN.cutoffSecondDerivativeConstant / (1 + ‖x‖) ^ 2 := by
  let S := rieszPressurePotentialCutoffScale n
  let ρ := rieszPressurePotentialCutoffRadius n
  by_cases hx : x ∈ CKN.euclideanBall 0 (3 * ρ / 4) \
      CKN.euclideanClosedBall 0 (13 * ρ / 20)
  · have hbase := rieszPressurePotentialCutoff_hessian_component_bound n i j x
    have hrec := rieszPressurePotentialCutoff_scale_reciprocal_bound
      (n := n) (x := x) hx.1
    have hconst := rieszPressurePotentialCutoffConstants_nonneg.2
    have hSpos : 0 < S := rieszPressurePotentialCutoffScale_pos n
    have hs : 0 < S ^ 2 := pow_pos hSpos _
    have hn : 0 < (1 + ‖x‖) ^ 2 := pow_pos (by positivity) _
    calc
      |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j x| ≤
          CKN.cutoffSecondDerivativeConstant / S ^ 2 := hbase
      _ ≤ 9 * CKN.cutoffSecondDerivativeConstant / (1 + ‖x‖) ^ 2 := by
        rw [div_le_div_iff₀ hs hn]
        have hrec' : 1 + ‖x‖ ≤ 3 * S := by
          apply (div_le_div_iff₀ hSpos
            (by positivity : 0 < 1 + ‖x‖)).1 at hrec
          simpa only [one_mul] using hrec
        have hsq : (1 + ‖x‖) ^ 2 ≤ (3 * S) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).2 hrec'
        have hsq' : (1 + ‖x‖) ^ 2 ≤ 9 * S ^ 2 := by
          nlinarith only [hsq]
        have hmul := mul_le_mul_of_nonneg_left hsq' hconst
        nlinarith only [hmul]
  · have hzero := CKN.mollifiedBallCutoff_derivatives_vanish_outside_annulus 0
      (rieszPressurePotentialCutoffRadius_pos n) hx
    have hhess : fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x = 0 := by
      simpa [rieszPressurePotentialCutoff] using hzero.2
    have hcomp : CKN.mixedSecond (rieszPressurePotentialCutoff n) i j x = 0 := by
      have hη := CKN.mollifiedBallCutoff_smooth 0
        (rieszPressurePotentialCutoffRadius_pos n)
      have hgrad : ContDiff ℝ (⊤ : ℕ∞)
          (CKN.classicalGradient (rieszPressurePotentialCutoff n)) := by
        rw [contDiff_pi]
        intro k
        change ContDiff ℝ (⊤ : ℕ∞)
          (CKN.spatialDeriv (rieszPressurePotentialCutoff n) k)
        exact CKN.contDiff_spatialDeriv_smooth hη k
      change CKN.spatialDeriv
        (CKN.spatialDeriv (rieszPressurePotentialCutoff n) j) i x = 0
      change (fderiv ℝ (fun y : Vec3 =>
        CKN.classicalGradient (rieszPressurePotentialCutoff n) y j) x)
        (CKN.basisVec i) = 0
      rw [fderiv_apply (hgrad.differentiable (by norm_num) x) j, hhess]
      rfl
    rw [hcomp, abs_zero]
    exact div_nonneg (mul_nonneg (by norm_num)
      rieszPressurePotentialCutoffConstants_nonneg.2) (by positivity)

private theorem rieszPressurePotentialCutoff_laplacian_profile_bound
    (n : ℕ) (x : Vec3) :
    |CKN.spatialLaplacian (rieszPressurePotentialCutoff n) x| ≤
      27 * CKN.cutoffSecondDerivativeConstant / (1 + ‖x‖) ^ 2 := by
  rw [CKN.spatialLaplacian]
  calc
    |∑ i : Fin 3, CKN.spatialDeriv
        (CKN.spatialDeriv (rieszPressurePotentialCutoff n) i) i x| ≤
        ∑ i : Fin 3, |CKN.mixedSecond (rieszPressurePotentialCutoff n) i i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3,
        9 * CKN.cutoffSecondDerivativeConstant / (1 + ‖x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact rieszPressurePotentialCutoff_hessian_profile_bound n i i x
    _ = 27 * CKN.cutoffSecondDerivativeConstant / (1 + ‖x‖) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

private theorem rieszPressurePotential_rpow1_mul_rpow3
    {a : ℝ} (ha : 0 < a) :
    a⁻¹ * a ^ (-(3 : ℝ)) = a ^ (-(4 : ℝ)) := by
  rw [← Real.rpow_neg_one a, ← Real.rpow_add ha (-(1 : ℝ)) (-(3 : ℝ))]
  norm_num

private theorem rieszPressurePotential_rpow2_mul_rpow2
    {a : ℝ} (ha : 0 < a) :
    (a ^ 2)⁻¹ * a ^ (-(2 : ℝ)) = a ^ (-(4 : ℝ)) := by
  have hpow2 : (a ^ 2)⁻¹ = a ^ (-(2 : ℝ)) := by
    calc
      (a ^ 2)⁻¹ = (a ^ (2 : ℝ))⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast a 2).symm
      _ = a ^ (-(2 : ℝ)) := (Real.rpow_neg (le_of_lt ha) (2 : ℝ)).symm
  rw [hpow2, ← Real.rpow_add ha (-(2 : ℝ)) (-(2 : ℝ))]
  norm_num

private theorem rieszPressurePotentialDecay_value_bound_norm
    {ψ : Vec3 × ℝ → ℝ} (hdecay : RieszPressurePotentialDecay ψ)
    (z : Vec3 × ℝ) :
    ∃ C0 ≥ 0, |ψ z| ≤ C0 * (1 + ‖z.1‖) ^ (-(2 : ℝ)) := by
  obtain ⟨C0, hC0, hbound⟩ := hdecay.value_bound
  refine ⟨C0, hC0, ?_⟩
  exact (hbound z).trans (mul_le_mul_of_nonneg_left
    (rieszPressurePotentialRpow_euclidean_le_norm z.1 (-(2 : ℝ)) (by norm_num)) hC0)

private theorem rieszPressurePotentialDecay_direction_bound_norm
    {ψ : Vec3 × ℝ → ℝ} (hdecay : RieszPressurePotentialDecay ψ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    ∃ C1 ≥ 0, |rieszPressureJointDirection ψ i z| ≤
      C1 * (1 + ‖z.1‖) ^ (-(3 : ℝ)) := by
  obtain ⟨C1, hC1, hbound⟩ := hdecay.gradient_bound
  refine ⟨C1, hC1, ?_⟩
  exact (hbound i z).trans (mul_le_mul_of_nonneg_left
    (rieszPressurePotentialRpow_euclidean_le_norm z.1 (-(3 : ℝ)) (by norm_num)) hC1)

/-- The Hessian decay bound in the CKN Euclidean norm, used by
`lem:riesz-duality`. -/
theorem rieszPressurePotentialDecay_hessian_bound_norm
    {ψ : Vec3 × ℝ → ℝ} (hdecay : RieszPressurePotentialDecay ψ)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    |rieszPressureJointHessian ψ i j z| ≤
      Classical.choose hdecay.hessian_bound * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
  have hspec := Classical.choose_spec hdecay.hessian_bound
  exact (hspec.2 i j z).trans (mul_le_mul_of_nonneg_left
    (rieszPressurePotentialRpow_euclidean_le_norm z.1 (-(4 : ℝ)) (by norm_num))
    hspec.1)

/-- The Laplacian decay bound in the CKN Euclidean norm, used by
`lem:riesz-duality`. -/
theorem rieszPressurePotentialDecay_laplacian_bound_norm
    {ψ : Vec3 × ℝ → ℝ} (hdecay : RieszPressurePotentialDecay ψ)
    (z : Vec3 × ℝ) :
    |rieszPressureJointLaplacian ψ z| ≤
      (3 * Classical.choose hdecay.hessian_bound) *
        (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
  let C2 := Classical.choose hdecay.hessian_bound
  have hspec := Classical.choose_spec hdecay.hessian_bound
  have hE := rieszPressurePotentialRpow_euclidean_le_norm z.1
    (-(4 : ℝ)) (by norm_num)
  rw [rieszPressureJointLaplacian]
  calc
    |∑ i : Fin 3, rieszPressureJointHessian ψ i i z| ≤
        ∑ i : Fin 3, |rieszPressureJointHessian ψ i i z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, C2 * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hspec.2 i i z
    _ ≤ ∑ _i : Fin 3, C2 * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left hE hspec.1
    _ = (3 * C2) * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- A smooth potential with a zero spatial slice has zero spatial Hessian on
that slice, used by `lem:riesz-duality`. -/
theorem rieszPressureJointHessian_zero_of_slice_zero
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {z : Vec3 × ℝ} (hzero : (fun x : Vec3 => f (x, z.2)) = fun _ => (0 : ℝ))
    (i j : Fin 3) : rieszPressureJointHessian f i j z = 0 := by
  rw [← rieszPressure_sliceMixedSecond_eq_joint hf i j z]
  rw [hzero]
  have hdir : CKN.spatialDeriv (fun _ : Vec3 => (0 : ℝ)) j = fun _ => 0 := by
    funext x
    simp [CKN.spatialDeriv]
  rw [CKN.mixedSecond, hdir]
  simp [CKN.spatialDeriv]

/-- A smooth potential with a zero spatial slice has zero spatial Laplacian on
that slice, used by `lem:riesz-duality`. -/
theorem rieszPressureJointLaplacian_zero_of_slice_zero
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {z : Vec3 × ℝ} (hzero : (fun x : Vec3 => f (x, z.2)) = fun _ => (0 : ℝ)) :
    rieszPressureJointLaplacian f z = 0 := by
  rw [← rieszPressure_sliceLaplacian_eq_joint hf z]
  rw [hzero]
  have hdir (i : Fin 3) :
      CKN.spatialDeriv (fun _ : Vec3 => (0 : ℝ)) i = fun _ => 0 := by
    funext x
    simp [CKN.spatialDeriv]
  simp [CKN.spatialLaplacian, hdir]

private theorem abs_four_add_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc
    |a + b + c + d| = |((a + b) + c) + d| := rfl
    _ ≤ |(a + b) + c| + |d| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |d| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ ((|a| + |b|) + |c|) + |d| := by
      exact add_le_add (add_le_add (abs_add_le a b) (le_refl _)) (le_refl _)

private theorem abs_three_add_le (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  calc
    |a + b + c| = |(a + b) + c| := rfl
    _ ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := add_le_add (abs_add_le _ _) (le_refl _)

/-- A uniform spatially integrable bound for the cutoff Hessian error,
used by `lem:riesz-duality`. -/
theorem rieszPressurePotentialHessianCutoffError_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set ℝ} (hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0)
    (hdecay : RieszPressurePotentialDecay ψ)
    (i j : Fin 3) (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressurePotentialHessianCutoffError ψ i j n z| ≤
      (Classical.choose hdecay.hessian_bound +
        6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
        9 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound) *
        rieszPressurePotentialSpatialProfile K z := by
  let C0 := Classical.choose hdecay.value_bound
  let C1 := Classical.choose hdecay.gradient_bound
  let C2 := Classical.choose hdecay.hessian_bound
  have hvalueSpec := Classical.choose_spec hdecay.value_bound
  have hgradientSpec := Classical.choose_spec hdecay.gradient_bound
  have hhessianSpec := Classical.choose_spec hdecay.hessian_bound
  have hC0 : 0 ≤ C0 := hvalueSpec.1
  have hC1 : 0 ≤ C1 := hgradientSpec.1
  have hC2 : 0 ≤ C2 := hhessianSpec.1
  have hvalue := hvalueSpec.2
  have hgradient := hgradientSpec.2
  have hhessian := hhessianSpec.2
  have hconstants := rieszPressurePotentialCutoffConstants_nonneg
  have hM : 0 ≤ C2 + 6 * CKN.cutoffGradientConstant * C1 +
      9 * CKN.cutoffSecondDerivativeConstant * C0 := by
    exact add_nonneg
      (add_nonneg hC2 (mul_nonneg (mul_nonneg (by norm_num) hconstants.1) hC1))
      (mul_nonneg (mul_nonneg (by norm_num) hconstants.2) hC0)
  by_cases ht : z.2 ∈ K
  · let a : ℝ := 1 + ‖z.1‖
    have ha : 0 < a := by dsimp [a]; positivity
    have hprofile : rieszPressurePotentialSpatialProfile K z =
        a ^ (-(4 : ℝ)) := by
      simp [rieszPressurePotentialSpatialProfile, a, ht]
    have hvalue' : |ψ z| ≤ C0 * a ^ (-(2 : ℝ)) := by
      have hpow := rieszPressurePotentialRpow_euclidean_le_norm z.1
        (-(2 : ℝ)) (by norm_num)
      exact (hvalue z).trans (mul_le_mul_of_nonneg_left hpow hC0)
    have hgradient' (k : Fin 3) :
        |rieszPressureJointDirection ψ k z| ≤ C1 * a ^ (-(3 : ℝ)) := by
      have hpow := rieszPressurePotentialRpow_euclidean_le_norm z.1
        (-(3 : ℝ)) (by norm_num)
      exact (hgradient k z).trans (mul_le_mul_of_nonneg_left hpow hC1)
    have hhessian' (k l : Fin 3) :
        |rieszPressureJointHessian ψ k l z| ≤ C2 * a ^ (-(4 : ℝ)) := by
      have hpow := rieszPressurePotentialRpow_euclidean_le_norm z.1
        (-(4 : ℝ)) (by norm_num)
      exact (hhessian k l z).trans (mul_le_mul_of_nonneg_left hpow hC2)
    have hcutgrad (k : Fin 3) :
        |CKN.spatialDeriv (rieszPressurePotentialCutoff n) k z.1| ≤
          3 * CKN.cutoffGradientConstant * a⁻¹ := by
      simpa [a, div_eq_mul_inv, mul_assoc] using
        rieszPressurePotentialCutoff_gradient_profile_bound n k z.1
    have hcuthess (k l : Fin 3) :
        |CKN.mixedSecond (rieszPressurePotentialCutoff n) k l z.1| ≤
          9 * CKN.cutoffSecondDerivativeConstant * (a ^ 2)⁻¹ := by
      simpa [a, div_eq_mul_inv, mul_assoc] using
        rieszPressurePotentialCutoff_hessian_profile_bound n k l z.1
    have heta := rieszPressurePotentialCutoff_bounds n z.1
    have heta' : |rieszPressurePotentialCutoff n z.1 - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith only [heta.1, heta.2]
    have hmain : |(rieszPressurePotentialCutoff n z.1 - 1) *
        rieszPressureJointHessian ψ i j z| ≤ C2 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        |rieszPressurePotentialCutoff n z.1 - 1| *
            |rieszPressureJointHessian ψ i j z| ≤
            1 * (C2 * a ^ (-(4 : ℝ)) ) := by
              exact mul_le_mul heta' (hhessian' i j)
                (abs_nonneg _)
                (by norm_num)
        _ = C2 * a ^ (-(4 : ℝ)) := by ring
    have hcross₁ :
        |CKN.spatialDeriv (rieszPressurePotentialCutoff n) j z.1 *
          rieszPressureJointDirection ψ i z| ≤
          3 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        |CKN.spatialDeriv (rieszPressurePotentialCutoff n) j z.1| *
            |rieszPressureJointDirection ψ i z| ≤
            (3 * CKN.cutoffGradientConstant * a⁻¹) *
              (C1 * a ^ (-(3 : ℝ))) := by
                exact mul_le_mul (hcutgrad j) (hgradient' i)
                  (abs_nonneg _)
                  (mul_nonneg (mul_nonneg (by norm_num) hconstants.1)
                    (inv_nonneg.mpr (le_of_lt ha)))
        _ = 3 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) := by
          calc
            _ = (3 * CKN.cutoffGradientConstant * C1) *
                (a⁻¹ * a ^ (-(3 : ℝ))) := by ring
            _ = 3 * CKN.cutoffGradientConstant * C1 *
                a ^ (-(4 : ℝ)) := by
              rw [rieszPressurePotential_rpow1_mul_rpow3 ha]
    have hcross₂ :
        |CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 *
          rieszPressureJointDirection ψ j z| ≤
          3 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        |CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1| *
            |rieszPressureJointDirection ψ j z| ≤
            (3 * CKN.cutoffGradientConstant * a⁻¹) *
              (C1 * a ^ (-(3 : ℝ))) := by
                exact mul_le_mul (hcutgrad i) (hgradient' j)
                  (abs_nonneg _)
                  (mul_nonneg (mul_nonneg (by norm_num) hconstants.1)
                    (inv_nonneg.mpr (le_of_lt ha)))
        _ = 3 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) := by
          calc
            _ = (3 * CKN.cutoffGradientConstant * C1) *
                (a⁻¹ * a ^ (-(3 : ℝ))) := by ring
            _ = 3 * CKN.cutoffGradientConstant * C1 *
                a ^ (-(4 : ℝ)) := by
              rw [rieszPressurePotential_rpow1_mul_rpow3 ha]
    have hcutvalue :
        |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j z.1 * ψ z| ≤
          9 * CKN.cutoffSecondDerivativeConstant * C0 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j z.1| * |ψ z| ≤
            (9 * CKN.cutoffSecondDerivativeConstant * (a ^ 2)⁻¹) *
              (C0 * a ^ (-(2 : ℝ))) := by
                exact mul_le_mul (hcuthess i j) hvalue'
                  (abs_nonneg _)
                  (mul_nonneg (mul_nonneg (by norm_num) hconstants.2)
                    (inv_nonneg.mpr (sq_nonneg a)))
        _ = 9 * CKN.cutoffSecondDerivativeConstant * C0 * a ^ (-(4 : ℝ)) := by
          calc
            _ = (9 * CKN.cutoffSecondDerivativeConstant * C0) *
                ((a ^ 2)⁻¹ * a ^ (-(2 : ℝ))) := by ring
            _ = 9 * CKN.cutoffSecondDerivativeConstant * C0 *
                a ^ (-(4 : ℝ)) := by
              rw [rieszPressurePotential_rpow2_mul_rpow2 ha]
    have herrFormula : rieszPressurePotentialHessianCutoffError ψ i j n z =
        (rieszPressurePotentialCutoff n z.1 - 1) *
            rieszPressureJointHessian ψ i j z +
          CKN.spatialDeriv (rieszPressurePotentialCutoff n) j z.1 *
            rieszPressureJointDirection ψ i z +
          CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 *
            rieszPressureJointDirection ψ j z +
          CKN.mixedSecond (rieszPressurePotentialCutoff n) i j z.1 * ψ z := by
      simp only [rieszPressurePotentialHessianCutoffError]
      rw [rieszPressurePotentialCutoffTest_hessian_formula hψ n i j z]
      ring
    rw [herrFormula]
    calc
      |(rieszPressurePotentialCutoff n z.1 - 1) *
          rieszPressureJointHessian ψ i j z +
        CKN.spatialDeriv (rieszPressurePotentialCutoff n) j z.1 *
          rieszPressureJointDirection ψ i z +
        CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 *
          rieszPressureJointDirection ψ j z +
        CKN.mixedSecond (rieszPressurePotentialCutoff n) i j z.1 * ψ z| ≤
        |(rieszPressurePotentialCutoff n z.1 - 1) *
          rieszPressureJointHessian ψ i j z| +
        |CKN.spatialDeriv (rieszPressurePotentialCutoff n) j z.1 *
          rieszPressureJointDirection ψ i z| +
        |CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 *
          rieszPressureJointDirection ψ j z| +
        |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j z.1 * ψ z| :=
        abs_four_add_le _ _ _ _
      _ = |(rieszPressurePotentialCutoff n z.1 - 1) *
            rieszPressureJointHessian ψ i j z| +
          |CKN.spatialDeriv (rieszPressurePotentialCutoff n) j z.1 *
            rieszPressureJointDirection ψ i z| +
          (|CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 *
            rieszPressureJointDirection ψ j z| +
            |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j z.1 * ψ z|) := by ring
      _ ≤ C2 * a ^ (-(4 : ℝ)) +
          3 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) +
          (3 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) +
            9 * CKN.cutoffSecondDerivativeConstant * C0 * a ^ (-(4 : ℝ)) ) :=
        add_le_add (add_le_add hmain hcross₁) (add_le_add hcross₂ hcutvalue)
      _ = (C2 + 6 * CKN.cutoffGradientConstant * C1 +
          9 * CKN.cutoffSecondDerivativeConstant * C0) *
          a ^ (-(4 : ℝ) ) := by ring
      _ = (C2 + 6 * CKN.cutoffGradientConstant * C1 +
          9 * CKN.cutoffSecondDerivativeConstant * C0) *
          rieszPressurePotentialSpatialProfile K z := by rw [← hprofile]
  · have hsourceSlice : (fun x : Vec3 => ψ (x, z.2)) = fun _ => 0 := by
      funext x
      exact hzero z.2 ht x
    have htestSmooth := rieszPressurePotentialCutoffTest_contDiff hψ n
    have htestSlice : (fun x : Vec3 =>
        rieszPressurePotentialCutoffTest ψ n (x, z.2)) = fun _ => 0 := by
      funext x
      simp [rieszPressurePotentialCutoffTest, hzero z.2 ht x]
    have hsource := rieszPressureJointHessian_zero_of_slice_zero hψ hsourceSlice i j
    have htest := rieszPressureJointHessian_zero_of_slice_zero
      htestSmooth htestSlice i j
    simp [rieszPressurePotentialHessianCutoffError, hsource, htest,
      rieszPressurePotentialSpatialProfile, ht]

/-- A uniform spatially integrable bound for the cutoff Laplacian error,
used by `lem:riesz-duality`. -/
theorem rieszPressurePotentialLaplacianCutoffError_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set ℝ} (hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0)
    (hdecay : RieszPressurePotentialDecay ψ) (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressurePotentialLaplacianCutoffError ψ n z| ≤
      (3 * Classical.choose hdecay.hessian_bound +
        18 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
        27 * CKN.cutoffSecondDerivativeConstant *
          Classical.choose hdecay.value_bound) *
        rieszPressurePotentialSpatialProfile K z := by
  let C0 := Classical.choose hdecay.value_bound
  let C1 := Classical.choose hdecay.gradient_bound
  let C2 := Classical.choose hdecay.hessian_bound
  have hvalueSpec := Classical.choose_spec hdecay.value_bound
  have hgradientSpec := Classical.choose_spec hdecay.gradient_bound
  have hhessianSpec := Classical.choose_spec hdecay.hessian_bound
  have hC0 : 0 ≤ C0 := hvalueSpec.1
  have hC1 : 0 ≤ C1 := hgradientSpec.1
  have hC2 : 0 ≤ C2 := hhessianSpec.1
  have hvalue := hvalueSpec.2
  have hgradient := hgradientSpec.2
  have hhessian := hhessianSpec.2
  have hconstants := rieszPressurePotentialCutoffConstants_nonneg
  have hM : 0 ≤ 3 * C2 + 18 * CKN.cutoffGradientConstant * C1 +
      27 * CKN.cutoffSecondDerivativeConstant * C0 := by
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) hC2)
        (mul_nonneg (mul_nonneg (by norm_num) hconstants.1) hC1))
      (mul_nonneg (mul_nonneg (by norm_num) hconstants.2) hC0)
  by_cases ht : z.2 ∈ K
  · let a : ℝ := 1 + ‖z.1‖
    have ha : 0 < a := by dsimp [a]; positivity
    have hprofile : rieszPressurePotentialSpatialProfile K z =
        a ^ (-(4 : ℝ)) := by
      simp [rieszPressurePotentialSpatialProfile, a, ht]
    have hvalue' : |ψ z| ≤ C0 * a ^ (-(2 : ℝ)) := by
      have hpow := rieszPressurePotentialRpow_euclidean_le_norm z.1
        (-(2 : ℝ)) (by norm_num)
      exact (hvalue z).trans (mul_le_mul_of_nonneg_left hpow hC0)
    have hgradient' (k : Fin 3) :
        |rieszPressureJointDirection ψ k z| ≤ C1 * a ^ (-(3 : ℝ)) := by
      have hpow := rieszPressurePotentialRpow_euclidean_le_norm z.1
        (-(3 : ℝ)) (by norm_num)
      exact (hgradient k z).trans (mul_le_mul_of_nonneg_left hpow hC1)
    have hhessian' (k l : Fin 3) :
        |rieszPressureJointHessian ψ k l z| ≤ C2 * a ^ (-(4 : ℝ)) := by
      have hpow := rieszPressurePotentialRpow_euclidean_le_norm z.1
        (-(4 : ℝ)) (by norm_num)
      exact (hhessian k l z).trans (mul_le_mul_of_nonneg_left hpow hC2)
    have hcutgrad (k : Fin 3) :
        |CKN.spatialDeriv (rieszPressurePotentialCutoff n) k z.1| ≤
          3 * CKN.cutoffGradientConstant * a⁻¹ := by
      simpa [a, div_eq_mul_inv, mul_assoc] using
        rieszPressurePotentialCutoff_gradient_profile_bound n k z.1
    have hcutlap :
        |CKN.spatialLaplacian (rieszPressurePotentialCutoff n) z.1| ≤
          27 * CKN.cutoffSecondDerivativeConstant * (a ^ 2)⁻¹ := by
      simpa [a, div_eq_mul_inv, mul_assoc] using
        rieszPressurePotentialCutoff_laplacian_profile_bound n z.1
    have heta := rieszPressurePotentialCutoff_bounds n z.1
    have heta' : |rieszPressurePotentialCutoff n z.1 - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith only [heta.1, heta.2]
    have hlapSource : |rieszPressureJointLaplacian ψ z| ≤
        3 * C2 * a ^ (-(4 : ℝ)) := by
      rw [rieszPressureJointLaplacian]
      calc
        |∑ k : Fin 3, rieszPressureJointHessian ψ k k z| ≤
            ∑ k : Fin 3, |rieszPressureJointHessian ψ k k z| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin 3, C2 * a ^ (-(4 : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hhessian' k k
        _ = 3 * C2 * a ^ (-(4 : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
    have hgradDot :
        |CKN.spatialGradDot (rieszPressurePotentialCutoff n)
          (fun x => ψ (x, z.2)) z.1| ≤
          9 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) := by
      unfold CKN.spatialGradDot
      calc
        |∑ k : Fin 3, CKN.spatialDeriv
            (rieszPressurePotentialCutoff n) k z.1 *
            CKN.spatialDeriv (fun x => ψ (x, z.2)) k z.1| ≤
            ∑ k : Fin 3, |CKN.spatialDeriv
              (rieszPressurePotentialCutoff n) k z.1 *
              CKN.spatialDeriv (fun x => ψ (x, z.2)) k z.1| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin 3,
            (3 * CKN.cutoffGradientConstant * a⁻¹) *
              (C1 * a ^ (-(3 : ℝ))) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          have hslice := rieszPressure_sliceSpatialDeriv_eq_joint hψ k z
          rw [hslice]
          exact mul_le_mul (hcutgrad k) (hgradient' k)
            (abs_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) hconstants.1)
              (inv_nonneg.mpr (le_of_lt ha)))
        _ = 9 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          calc
            3 * ((3 * CKN.cutoffGradientConstant * a⁻¹) *
                (C1 * a ^ (-(3 : ℝ)))) =
                9 * CKN.cutoffGradientConstant * C1 *
                  (a⁻¹ * a ^ (-(3 : ℝ))) := by ring
            _ = 9 * CKN.cutoffGradientConstant * C1 *
                a ^ (-(4 : ℝ)) := by
              rw [rieszPressurePotential_rpow1_mul_rpow3 ha]
    have hmain : |(rieszPressurePotentialCutoff n z.1 - 1) *
        rieszPressureJointLaplacian ψ z| ≤ 3 * C2 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        |rieszPressurePotentialCutoff n z.1 - 1| *
            |rieszPressureJointLaplacian ψ z| ≤
            1 * (3 * C2 * a ^ (-(4 : ℝ))) :=
          mul_le_mul heta' hlapSource
            (abs_nonneg (rieszPressureJointLaplacian ψ z))
            (by norm_num : 0 ≤ (1 : ℝ))
        _ = 3 * C2 * a ^ (-(4 : ℝ)) := by ring
    have hmiddle : |2 * CKN.spatialGradDot (rieszPressurePotentialCutoff n)
        (fun x => ψ (x, z.2)) z.1| ≤
        18 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      calc
        2 * |CKN.spatialGradDot (rieszPressurePotentialCutoff n)
            (fun x => ψ (x, z.2)) z.1| ≤
            2 * (9 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hgradDot (by norm_num)
        _ = 18 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) := by ring
    have hlast : |ψ z * CKN.spatialLaplacian
        (rieszPressurePotentialCutoff n) z.1| ≤
        27 * CKN.cutoffSecondDerivativeConstant * C0 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        |ψ z| * |CKN.spatialLaplacian
            (rieszPressurePotentialCutoff n) z.1| ≤
            (C0 * a ^ (-(2 : ℝ))) *
              (27 * CKN.cutoffSecondDerivativeConstant * (a ^ 2)⁻¹) :=
          mul_le_mul hvalue' hcutlap
            (abs_nonneg (CKN.spatialLaplacian (rieszPressurePotentialCutoff n) z.1))
            (mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _))
        _ = 27 * CKN.cutoffSecondDerivativeConstant * C0 *
            a ^ (-(4 : ℝ)) := by
          calc
            _ = (27 * CKN.cutoffSecondDerivativeConstant * C0) *
                (a ^ (-(2 : ℝ)) * (a ^ 2)⁻¹) := by ring
            _ = 27 * CKN.cutoffSecondDerivativeConstant * C0 *
                a ^ (-(4 : ℝ)) := by
              rw [mul_comm (a ^ (-(2 : ℝ))) ((a ^ 2)⁻¹),
                rieszPressurePotential_rpow2_mul_rpow2 ha]
    have herrFormula : rieszPressurePotentialLaplacianCutoffError ψ n z =
        (rieszPressurePotentialCutoff n z.1 - 1) *
            rieszPressureJointLaplacian ψ z +
          2 * CKN.spatialGradDot (rieszPressurePotentialCutoff n)
            (fun x => ψ (x, z.2)) z.1 +
          ψ z * CKN.spatialLaplacian (rieszPressurePotentialCutoff n) z.1 := by
      simp only [rieszPressurePotentialLaplacianCutoffError]
      rw [rieszPressurePotentialCutoffTest_laplacian_formula hψ n z]
      ring
    rw [herrFormula]
    calc
      |(rieszPressurePotentialCutoff n z.1 - 1) *
          rieszPressureJointLaplacian ψ z +
        2 * CKN.spatialGradDot (rieszPressurePotentialCutoff n)
          (fun x => ψ (x, z.2)) z.1 +
        ψ z * CKN.spatialLaplacian (rieszPressurePotentialCutoff n) z.1| ≤
        |(rieszPressurePotentialCutoff n z.1 - 1) *
          rieszPressureJointLaplacian ψ z| +
        |2 * CKN.spatialGradDot (rieszPressurePotentialCutoff n)
          (fun x => ψ (x, z.2)) z.1| +
        |ψ z * CKN.spatialLaplacian (rieszPressurePotentialCutoff n) z.1| :=
        abs_three_add_le _ _ _
      _ ≤ 3 * C2 * a ^ (-(4 : ℝ)) +
          18 * CKN.cutoffGradientConstant * C1 * a ^ (-(4 : ℝ)) +
          27 * CKN.cutoffSecondDerivativeConstant * C0 * a ^ (-(4 : ℝ)) :=
        add_le_add (add_le_add hmain hmiddle) hlast
      _ = (3 * C2 + 18 * CKN.cutoffGradientConstant * C1 +
          27 * CKN.cutoffSecondDerivativeConstant * C0) * a ^ (-(4 : ℝ)) := by ring
      _ = (3 * C2 + 18 * CKN.cutoffGradientConstant * C1 +
          27 * CKN.cutoffSecondDerivativeConstant * C0) *
          rieszPressurePotentialSpatialProfile K z := by rw [← hprofile]
  · have hsourceSlice : (fun x : Vec3 => ψ (x, z.2)) = fun _ => 0 := by
      funext x
      exact hzero z.2 ht x
    have htestSmooth := rieszPressurePotentialCutoffTest_contDiff hψ n
    have htestSlice : (fun x : Vec3 =>
        rieszPressurePotentialCutoffTest ψ n (x, z.2)) = fun _ => 0 := by
      funext x
      simp [rieszPressurePotentialCutoffTest, hzero z.2 ht x]
    have hsource := rieszPressureJointLaplacian_zero_of_slice_zero hψ hsourceSlice
    have htest := rieszPressureJointLaplacian_zero_of_slice_zero
      htestSmooth htestSlice
    simp [rieszPressurePotentialLaplacianCutoffError, hsource, htest,
      rieszPressurePotentialSpatialProfile, ht]

end CKN.Leray

end
