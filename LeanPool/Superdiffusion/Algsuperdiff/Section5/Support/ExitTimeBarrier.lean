/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.FieldDivergenceTest
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ZeroTraceSupNorm
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# ExitTimeBarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A barrier from below for the homogenized exit-time problem

The homogenized exit time on `y + □_n` is bounded below on the inner cube
`y + □_{n-1}` by comparison with a barrier: a smooth bump supported strictly
inside `y + □_n`, equal to a constant `A` on a ball containing the inner cube,
and scaled so that its Laplacian is small enough that it is a subsolution of
`-σ Δ · = 1`.

The scaling is the only quantitative point.  A fixed bump `η` on the unit scale
has a bounded Laplacian, `|Δη| ≤ K(d)` on the ball of radius `1/2`; the rescaled
bump `x ↦ A η(3^{-n}(x - y))` therefore has `|Δ| ≤ A 3^{-2n} K`, so the choice
`A = 3^{2n} / (σ K)` makes `-σ Δ` at most `1` — and the barrier reaches the
height `A = 3^{2n}/(σK)`, which is the exit-time scale up to the constant `K`.

The ambient norm on `Vec d` is the supremum norm, so its balls *are* the cubes:
`cubeSetAt y n = Metric.ball y (3^n/2)`.  A single bump with `rIn = 1/6` and
`rOut = 1/3` therefore covers the whole inner cube and is supported strictly
inside the cube, with no dependence on the dimension in the geometry.

## Main definitions

* `referenceBump d` — the unit-scale bump, `1` on the ball of radius `1/6`,
  supported in the ball of radius `1/3`.
* `exitTimeBarrier y n A` — the rescaled barrier of height `A` on `y + □_n`.

## Main results

* `exists_exitTimeBarrier` — the barrier as a zero-trace Sobolev function,
  with its height on the inner cube and its subsolution property.

## References

* ABK26, the exit-time comparison of Section 5.2.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The reference bump and its Laplacian -/

/-- **The unit-scale bump**: equal to `1` on the ball of radius `1/6` and
supported in the ball of radius `1/3`. -/
def referenceBump (d : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / 6
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem contDiff_referenceBump (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) fun z : Vec d => referenceBump d z :=
  (referenceBump d).contDiff

theorem contDiff_euclideanCoordDeriv_referenceBump (d : ℕ) (i : Fin d) :
    ContDiff ℝ 1 fun z : Vec d => euclideanCoordDeriv i (fun w => referenceBump d w) z := by
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      fun z : Vec d => fderiv ℝ (fun w : Vec d => referenceBump d w) z :=
    (contDiff_referenceBump d).fderiv_right (by exact_mod_cast le_top)
  exact (h2.clm_apply contDiff_const).of_le (by exact_mod_cast le_top)

/-- **The Laplacian of the reference bump.** -/
def bumpLaplacian (d : ℕ) : Vec d → ℝ :=
  vecFieldDiv (euclideanGradient fun z : Vec d => referenceBump d z)

theorem bumpLaplacian_eq (d : ℕ) (t : Vec d) :
    bumpLaplacian d t = ∑ i : Fin d,
      (fderiv ℝ (fun w : Vec d =>
        euclideanCoordDeriv i (fun s : Vec d => referenceBump d s) w) t) (basisVec i) := rfl

theorem continuous_bumpLaplacian (d : ℕ) : Continuous (bumpLaplacian d) := by
  rw [show bumpLaplacian d = fun t : Vec d => ∑ i : Fin d,
      (fderiv ℝ (fun w : Vec d =>
        euclideanCoordDeriv i (fun s : Vec d => referenceBump d s) w) t) (basisVec i) from
    funext fun t => bumpLaplacian_eq d t]
  exact continuous_finsetSum Finset.univ fun i _ =>
    (((contDiff_euclideanCoordDeriv_referenceBump d i).continuous_fderiv
      (by simp)).clm_apply continuous_const)

/-- **The Laplacian of the reference bump is bounded on the ball of radius
`1/2`**, the range of the rescaled argument over the cube. -/
theorem exists_bumpLaplacian_bound (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : Vec d, ‖t‖ ≤ 1 / 2 → |bumpLaplacian d t| ≤ K := by
  obtain ⟨K0, hK0⟩ := (isCompact_closedBall (0 : Vec d) (1 / 2 : ℝ)).exists_bound_of_continuousOn
    (continuous_bumpLaplacian d).continuousOn
  refine ⟨max K0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t ht => ?_⟩
  have hmem : t ∈ Metric.closedBall (0 : Vec d) (1 / 2 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using ht
  exact le_trans (by simpa [Real.norm_eq_abs] using hK0 t hmem) (le_max_left _ _)

/-! ## 2. The rescaled barrier -/

/-- **The barrier of height `A` on `y + □_n`.** -/
def exitTimeBarrier (y : Vec d) (n : ℤ) (A : ℝ) : Vec d → ℝ :=
  fun z => A * referenceBump d (((3 : ℝ) ^ n)⁻¹ • (z - y))

private theorem fderiv_scale_comp {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (c : ℝ) (y : Vec d)
    (z e : Vec d) :
    (fderiv ℝ (fun w => f (c • (w - y))) z) e = c * (fderiv ℝ f (c • (z - y))) e := by
  have hS : HasFDerivAt (fun w : Vec d => c • (w - y))
      (c • ContinuousLinearMap.id ℝ (Vec d)) z := ((hasFDerivAt_id z).sub_const y).const_smul c
  have hcomp : HasFDerivAt (fun w : Vec d => f (c • (w - y)))
      ((fderiv ℝ f (c • (z - y))).comp (c • ContinuousLinearMap.id ℝ (Vec d))) z :=
    (hf.differentiable (by simp) (c • (z - y))).hasFDerivAt.comp z hS
  rw [hcomp.fderiv]
  simp

private theorem contDiff_exitTimeBarrier (y : Vec d) (n : ℤ) (A : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (exitTimeBarrier y n A) := by
  have hS : ContDiff ℝ (⊤ : ℕ∞) fun w : Vec d => ((3 : ℝ) ^ n)⁻¹ • (w - y) :=
    (contDiff_id.sub contDiff_const).const_smul _
  exact contDiff_const.mul ((contDiff_referenceBump d).comp hS)

private theorem euclideanGradient_exitTimeBarrier (y : Vec d) (n : ℤ) (A : ℝ)
    (z : Vec d) (i : Fin d) :
    euclideanGradient (exitTimeBarrier y n A) z i =
      A * ((3 : ℝ) ^ n)⁻¹ *
        euclideanCoordDeriv i (fun w : Vec d => referenceBump d w)
          (((3 : ℝ) ^ n)⁻¹ • (z - y)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      fun w : Vec d => referenceBump d (((3 : ℝ) ^ n)⁻¹ • (w - y)) := by
    have hS : ContDiff ℝ (⊤ : ℕ∞) fun w : Vec d => ((3 : ℝ) ^ n)⁻¹ • (w - y) :=
      (contDiff_id.sub contDiff_const).const_smul _
    exact (contDiff_referenceBump d).comp hS
  have hdiff : DifferentiableAt ℝ
      (fun w : Vec d => referenceBump d (((3 : ℝ) ^ n)⁻¹ • (w - y))) z :=
    (hg.differentiable (by simp)).differentiableAt
  show (fderiv ℝ (exitTimeBarrier y n A) z) (basisVec i) = _
  rw [show exitTimeBarrier y n A =
      fun w : Vec d => A * referenceBump d (((3 : ℝ) ^ n)⁻¹ • (w - y)) from rfl,
    fderiv_const_mul hdiff A]
  rw [smul_apply, smul_eq_mul, mul_assoc]
  congr 1
  exact fderiv_scale_comp ((contDiff_referenceBump d).of_le (by exact_mod_cast le_top)) _ y z _

private theorem vecFieldDiv_euclideanGradient_exitTimeBarrier (y : Vec d) (n : ℤ) (A : ℝ)
    (z : Vec d) :
    vecFieldDiv (euclideanGradient (exitTimeBarrier y n A)) z =
      A * (((3 : ℝ) ^ n)⁻¹) ^ (2 : ℕ) * bumpLaplacian d (((3 : ℝ) ^ n)⁻¹ • (z - y)) := by
  have hterm : ∀ i : Fin d,
      (fderiv ℝ (fun w => euclideanGradient (exitTimeBarrier y n A) w i) z) (basisVec i) =
        A * ((3 : ℝ) ^ n)⁻¹ * ((3 : ℝ) ^ n)⁻¹ *
          (fderiv ℝ (fun w : Vec d => euclideanCoordDeriv i (fun t => referenceBump d t) w)
            (((3 : ℝ) ^ n)⁻¹ • (z - y))) (basisVec i) := by
    intro i
    rw [show (fun w => euclideanGradient (exitTimeBarrier y n A) w i) =
        fun w : Vec d => A * ((3 : ℝ) ^ n)⁻¹ *
          euclideanCoordDeriv i (fun t : Vec d => referenceBump d t)
            (((3 : ℝ) ^ n)⁻¹ • (w - y)) from
      funext fun w => euclideanGradient_exitTimeBarrier y n A w i]
    have hdiff : DifferentiableAt ℝ
        (fun w : Vec d => euclideanCoordDeriv i (fun t : Vec d => referenceBump d t)
          (((3 : ℝ) ^ n)⁻¹ • (w - y))) z := by
      have hS : ContDiff ℝ 1 fun w : Vec d => ((3 : ℝ) ^ n)⁻¹ • (w - y) :=
        (contDiff_id.sub contDiff_const).const_smul _
      exact (((contDiff_euclideanCoordDeriv_referenceBump d i).comp hS).differentiable
        (by simp)).differentiableAt
    rw [fderiv_const_mul hdiff (A * ((3 : ℝ) ^ n)⁻¹), smul_apply,
      smul_eq_mul,
      fderiv_scale_comp (contDiff_euclideanCoordDeriv_referenceBump d i)
        (((3 : ℝ) ^ n)⁻¹) y z (basisVec i)]
    ring
  rw [vecFieldDiv_apply, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum,
    bumpLaplacian_eq]
  ring

/-! ## 3. The barrier as a zero-trace Sobolev function -/

private theorem hasCompactSupport_exitTimeBarrier (y : Vec d) (n : ℤ) (A : ℝ) :
    tsupport (exitTimeBarrier y n A) ⊆ Metric.closedBall y ((3 : ℝ) ^ n / 3) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro z hz
  by_contra hout
  have hz' : referenceBump d (((3 : ℝ) ^ n)⁻¹ • (z - y)) ≠ 0 := by
    intro h0
    exact hz (by simp [exitTimeBarrier, h0])
  have hmem : ((3 : ℝ) ^ n)⁻¹ • (z - y) ∈ Function.support fun t : Vec d => referenceBump d t :=
    hz'
  rw [show (Function.support fun t : Vec d => referenceBump d t) =
      Metric.ball (0 : Vec d) (referenceBump d).rOut from (referenceBump d).support_eq] at hmem
  rw [Metric.mem_ball, dist_zero_right, norm_smul] at hmem
  have hnorm : ‖z - y‖ < (3 : ℝ) ^ n / 3 := by
    have hinv : ‖((3 : ℝ) ^ n)⁻¹‖ = ((3 : ℝ) ^ n)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hinv] at hmem
    have : ((3 : ℝ) ^ n)⁻¹ * ‖z - y‖ < 1 / 3 := hmem
    calc ‖z - y‖ = (3 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * ‖z - y‖) := by
          field_simp
      _ < (3 : ℝ) ^ n * (1 / 3) := by
          exact mul_lt_mul_of_pos_left this h3
      _ = (3 : ℝ) ^ n / 3 := by ring
  exact hout (by simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm.le)

/-- **The rescaled barrier**, as a zero-trace Sobolev function on `y + □_n`,
with its height on the inner cube and its subsolution property. -/
theorem exists_exitTimeBarrier (d : ℕ) (y : Vec d) (n : ℤ) {sig : ℝ} (hsig : 0 < sig)
    {K : ℝ} (hK : 0 < K) (hKbd : ∀ t : Vec d, ‖t‖ ≤ 1 / 2 → |bumpLaplacian d t| ≤ K) :
    ∃ v : H10Function (cubeSetAt y n),
      Continuous v.toH1Function.toFun ∧
      (∀ x ∈ cubeSetAt y (n - 1),
          v.toH1Function.toFun x = ((3 : ℝ) ^ n) ^ (2 : ℕ) / (sig * K)) ∧
        ∀ phi : H10Function (cubeSetAt y n), (∀ x, 0 ≤ phi.toH1Function.toFun x) →
          sig * ∫ x in cubeSetAt y n,
              vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume ≤
            ∫ x in cubeSetAt y n, phi.toH1Function.toFun x ∂volume := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  set A : ℝ := ((3 : ℝ) ^ n) ^ (2 : ℕ) / (sig * K) with hA_def
  set bar : Vec d → ℝ := exitTimeBarrier y n A with hbar_def
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) bar := contDiff_exitTimeBarrier y n A
  have hsupp : tsupport bar ⊆ Metric.closedBall y ((3 : ℝ) ^ n / 3) :=
    hasCompactSupport_exitTimeBarrier y n A
  have hball : Metric.closedBall y ((3 : ℝ) ^ n / 3) ⊆ cubeSetAt y n := by
    rw [cubeSetAt_eq_ball]
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith only [hz, h3]
  have hcs : HasCompactSupport bar :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      (Function.support_subset_iff'.2 fun z hz => by
        by_contra hne
        exact hz (hsupp (subset_closure hne)))
  -- the zero-trace witness
  have hmemL2 : MemScalarL2 (cubeSetAt y n) bar := by
    simpa only [MemScalarL2, volumeMeasureOn] using
      (hsmooth.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞)) hcs).restrict _
  have hgradL2 : MemVectorL2 (cubeSetAt y n) (euclideanGradient bar) :=
    memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hsmooth hcs
  refine ⟨{ toFun := bar
            grad := euclideanGradient bar
            memL2 := hmemL2
            gradMemL2 := fun i => memScalarL2_coord_of_memVectorL2 hgradL2 i
            hasWeakGradient := HasWeakGradientOn.of_contDiff
              (hsmooth.of_le (by exact_mod_cast le_top))
            approx := fun _ => bar
            approx_smooth := fun _ => hsmooth
            approx_hasCompactSupport := fun _ => hcs
            approx_support_subset := fun _ => hsupp.trans hball
            tendsto_approx := by simp
            tendsto_approx_grad := fun i => by
              have hz : (fun x : Vec d =>
                  (fderiv ℝ bar x) (basisVec i) - euclideanGradient bar x i) =
                fun _ : Vec d => (0 : ℝ) := funext fun x => sub_self _
              simp [hz] }, hsmooth.continuous, ?_, ?_⟩
  · intro x hx
    show bar x = A
    have hin : ‖((3 : ℝ) ^ n)⁻¹ • (x - y)‖ ≤ (referenceBump d).rIn := by
      rw [cubeSetAt_eq_ball, Metric.mem_ball, dist_eq_norm] at hx
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hsucc : (3 : ℝ) ^ (n - 1) = (3 : ℝ) ^ n / 3 := by
        rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
        simp
      rw [hsucc] at hx
      have hpos : (0 : ℝ) < ((3 : ℝ) ^ n)⁻¹ := by positivity
      show ((3 : ℝ) ^ n)⁻¹ * ‖x - y‖ ≤ 1 / 6
      calc ((3 : ℝ) ^ n)⁻¹ * ‖x - y‖ ≤ ((3 : ℝ) ^ n)⁻¹ * ((1 / 2 : ℝ) * ((3 : ℝ) ^ n / 3)) :=
            mul_le_mul_of_nonneg_left hx.le hpos.le
        _ = 1 / 6 := by field_simp; ring
    rw [hbar_def, exitTimeBarrier,
      (referenceBump d).one_of_mem_closedBall (by simpa [Metric.mem_closedBall,
        dist_zero_right] using hin), mul_one]
  · intro phi hphi
    have : IsFiniteMeasure (volume.restrict (cubeSetAt y n)) :=
      (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
    have hFC1 : ∀ i : Fin d, ContDiff ℝ 1 fun z => euclideanGradient bar z i := by
      intro i
      have h2 : ContDiff ℝ (⊤ : ℕ∞) fun z : Vec d => fderiv ℝ bar z :=
        hsmooth.fderiv_right (by exact_mod_cast le_top)
      exact (h2.clm_apply contDiff_const).of_le (by exact_mod_cast le_top)
    have hibp := integral_vecDot_h10Grad_eq_neg_integral_vecFieldDiv_mul
      (measurableSet_cubeSetAt y n)
      (isOpenBoundedConvexDomain_cubeSetAt y n).isBoundedDomain
      (F := euclideanGradient bar) hFC1 phi
    have hlapbd : ∀ x ∈ cubeSetAt y n,
        -(sig * vecFieldDiv (euclideanGradient bar) x) ≤ 1 := by
      intro x hx
      have hin : ‖((3 : ℝ) ^ n)⁻¹ • (x - y)‖ ≤ 1 / 2 := by
        rw [cubeSetAt_eq_ball, Metric.mem_ball, dist_eq_norm] at hx
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        have hpos : (0 : ℝ) < ((3 : ℝ) ^ n)⁻¹ := by positivity
        calc ((3 : ℝ) ^ n)⁻¹ * ‖x - y‖ ≤ ((3 : ℝ) ^ n)⁻¹ * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left hx.le hpos.le
          _ = 1 / 2 := by field_simp
      have hb := hKbd _ hin
      rw [hbar_def, vecFieldDiv_euclideanGradient_exitTimeBarrier]
      have hAc : A * (((3 : ℝ) ^ n)⁻¹) ^ (2 : ℕ) = (sig * K)⁻¹ := by
        rw [hA_def]
        field_simp
      rw [hAc]
      have habs : |bumpLaplacian d (((3 : ℝ) ^ n)⁻¹ • (x - y))| ≤ K := hb
      rw [abs_le] at habs
      have hsK : (0 : ℝ) < sig * K := mul_pos hsig hK
      have hkey : -((sig * K)⁻¹ * bumpLaplacian d (((3 : ℝ) ^ n)⁻¹ • (x - y))) ≤ K⁻¹ *
          sig⁻¹ * K := by
        have h1 : -bumpLaplacian d (((3 : ℝ) ^ n)⁻¹ • (x - y)) ≤ K := by
          linarith only [habs.1]
        have h2 : (0 : ℝ) < (sig * K)⁻¹ := by positivity
        calc -((sig * K)⁻¹ * bumpLaplacian d (((3 : ℝ) ^ n)⁻¹ • (x - y)))
            = (sig * K)⁻¹ * (-bumpLaplacian d (((3 : ℝ) ^ n)⁻¹ • (x - y))) := by ring
          _ ≤ (sig * K)⁻¹ * K := mul_le_mul_of_nonneg_left h1 h2.le
          _ = K⁻¹ * sig⁻¹ * K := by rw [mul_inv]; ring
      have hfin : sig * (K⁻¹ * sig⁻¹ * K) = 1 := by field_simp
      calc -(sig * ((sig * K)⁻¹ * bumpLaplacian d (((3 : ℝ) ^ n)⁻¹ • (x - y))))
          = sig * (-((sig * K)⁻¹ * bumpLaplacian d (((3 : ℝ) ^ n)⁻¹ • (x - y)))) := by ring
        _ ≤ sig * (K⁻¹ * sig⁻¹ * K) := mul_le_mul_of_nonneg_left hkey hsig.le
        _ = 1 := hfin
    have hintPhi : Integrable phi.toH1Function.toFun (volume.restrict (cubeSetAt y n)) :=
      phi.toH1Function.memL2.integrable (by norm_num)
    have hdivL2 : MemScalarL2 (cubeSetAt y n) (vecFieldDiv (euclideanGradient bar)) :=
      memScalarL2_of_continuous_of_isBoundedDomain (measurableSet_cubeSetAt y n)
        (isOpenBoundedConvexDomain_cubeSetAt y n).isBoundedDomain
        (continuous_finsetSum Finset.univ fun i _ =>
          (((hFC1 i).continuous_fderiv (by simp)).clm_apply continuous_const))
    have hintProd : Integrable
        (fun x => (-(sig * vecFieldDiv (euclideanGradient bar) x)) * phi.toH1Function.toFun x)
        (volume.restrict (cubeSetAt y n)) := by
      have := (hdivL2.const_mul (-sig)).integrable_mul phi.toH1Function.memL2
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]
      ring
    rw [hibp]
    calc sig * -∫ x in cubeSetAt y n,
            vecFieldDiv (euclideanGradient bar) x * phi.toH1Function.toFun x ∂volume
        = ∫ x in cubeSetAt y n,
            (-(sig * vecFieldDiv (euclideanGradient bar) x)) * phi.toH1Function.toFun x
              ∂volume := by
          rw [← integral_neg, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
      _ ≤ ∫ x in cubeSetAt y n, phi.toH1Function.toFun x ∂volume := by
          refine integral_mono_ae hintProd hintPhi ?_
          refine (ae_restrict_iff' (measurableSet_cubeSetAt y n)).2 ?_
          refine Filter.Eventually.of_forall fun x hx => ?_
          calc (-(sig * vecFieldDiv (euclideanGradient bar) x)) * phi.toH1Function.toFun x
              ≤ 1 * phi.toH1Function.toFun x :=
                mul_le_mul_of_nonneg_right (hlapbd x hx) (hphi x)
            _ = phi.toH1Function.toFun x := one_mul _

end

end Algsuperdiff.Section5.Support
