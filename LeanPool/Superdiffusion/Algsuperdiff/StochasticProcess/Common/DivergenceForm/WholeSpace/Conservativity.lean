/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Geometry
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Representative
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationInterior
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution
public import LeanPool.HighContrastHomogenization.Support.Sobolev.FiniteLpCoordinate
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Minimal
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.PointwiseDecay

/-!
# Conservativity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Conservativity of the whole-space analytic resolvent

The defect `1 - mu R^{U_m}_mu 1` is represented as an `H¹` solution of the
homogeneous shifted equation.  Interior decay along the cubic exhaustion
then removes the defect in the limit.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Topology
open MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- A fixed `H¹₀` representative of the local resolvent of one. -/
def cubeOneResolventH10 (mu : PositiveShift) (m : ℕ) :
    H10Function (wholeSpaceCube d m) :=
  Classical.choose (ZeroTraceSobolev.exists_h10Function
    (isOpenBoundedConvexDomain_wholeSpaceCube d m)
    (alphaShiftedSolution A.a mu.property A.hnu
      (A.cubeEllipticity m)
      (boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (measurable_const : Measurable (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
        (D := 1) (fun _ ↦ by norm_num))))

/-- The chosen representative has the prescribed zero-trace Sobolev class. -/
theorem cubeOneResolventH10_value (mu : PositiveShift) (m : ℕ) :
    (A.cubeOneResolventH10 mu m).toH1Function.toScalarL2 =
      alphaShiftedResolvent A.a mu.property A.hnu
        (A.cubeEllipticity m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (measurable_const : Measurable
            (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
          (D := 1) (fun _ ↦ by norm_num)) := by
  simpa only [alphaShiftedResolvent_apply] using!
    (Classical.choose_spec (ZeroTraceSobolev.exists_h10Function
    (isOpenBoundedConvexDomain_wholeSpaceCube d m)
    (alphaShiftedSolution A.a mu.property A.hnu
      (A.cubeEllipticity m)
      (boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (measurable_const : Measurable (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
        (D := 1) (fun _ ↦ by norm_num))))).1

omit [NeZero d] in
/-- The volume of the `m`th exhaustion cube. -/
theorem volume_wholeSpaceCube_toReal (m : ℕ) :
    (volume (wholeSpaceCube d m)).toReal = (2 * (3 : ℝ) ^ m) ^ d := by
  have hab : (fun _ : Fin d ↦ -((3 : ℝ) ^ m)) ≤
      fun i ↦ -((3 : ℝ) ^ m) + 2 * (3 : ℝ) ^ m := by
    intro i
    have hp : 0 ≤ (3 : ℝ) ^ m := pow_nonneg (by norm_num) _
    linarith only [hp]
  rw [wholeSpaceCube, axisCube, Real.volume_pi_Ioo_toReal hab,
    show (fun i : Fin d ↦
      (-((3 : ℝ) ^ m) + 2 * (3 : ℝ) ^ m) - -((3 : ℝ) ^ m)) =
        (fun _ : Fin d ↦ 2 * (3 : ℝ) ^ m) from by funext i; ring,
    Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]

omit [NeZero d] in
/-- The constant-one datum on a cube has the expected volume-order `L²`
bound. -/
theorem norm_cubeConstantOne_le (m : ℕ) :
    ‖boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (measurable_const : Measurable (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
        (D := 1) (fun _ ↦ by norm_num)‖ ≤
      Real.sqrt ((volume (wholeSpaceCube d m)).toReal) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU
      (measurable_const : Measurable (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
      (D := 1) (fun _ ↦ by norm_num)
  have hbound : ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d m), ‖F x‖ ≤ (1 : ℝ) := by
    filter_upwards [abs_boundedMeasurableToScalarL2_le hU
      (measurable_const : Measurable
        (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
      (D := 1) (fun _ ↦ by norm_num)] with x hx
    simpa only [Real.norm_eq_abs, abs_one] using hx
  have hLp := eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) (Lp.aestronglyMeasurable F) hbound
  have hLp' : eLpNorm (fun x ↦ F x) 2
        (volumeMeasureOn (wholeSpaceCube d m)) ≤
      volume (wholeSpaceCube d m) ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal 1 := by
    simpa only [volumeMeasureOn, Measure.restrict_apply_univ] using hLp
  change ‖F‖ ≤ _
  rw [Lp.norm_def]
  have htop : volume (wholeSpaceCube d m) ≠ ⊤ :=
    hU.isBoundedDomain.isBounded.measure_lt_top.ne
  have htoReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) htop)
      ENNReal.ofReal_ne_top) hLp'
  calc
    (eLpNorm (fun x ↦ F x) 2
        (volumeMeasureOn (wholeSpaceCube d m))).toReal ≤
        (volume (wholeSpaceCube d m) ^ (2 : ENNReal).toReal⁻¹ *
          ENNReal.ofReal 1).toReal := htoReal
    _ = Real.sqrt ((volume (wholeSpaceCube d m)).toReal) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal zero_le_one, mul_one,
        ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat]
      norm_num
      rw [← Real.sqrt_eq_rpow]

/-- The constant-one function as an `H¹` function on a cube. -/
def cubeConstantOneH1 (m : ℕ) : H1Function (wholeSpaceCube d m) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_wholeSpaceCube d m)
    (contDiff_const : ContDiff ℝ 1 (fun _ : Vec d ↦ (1 : ℝ)))

/-- The `H¹` boundary defect `1 - mu R^{U_m}_mu 1`. -/
def cubeBoundaryRemainderH1 (mu : PositiveShift) (m : ℕ) :
    H1Function (wholeSpaceCube d m) :=
  cubeConstantOneH1 m -
    (mu : ℝ) • (A.cubeOneResolventH10 mu m).toH1Function

/-- The `H¹` boundary defect agrees almost everywhere with the analytic
pointwise defect. -/
theorem cubeBoundaryRemainder_ae (mu : PositiveShift) (m : ℕ) :
    (A.cubeBoundaryRemainderH1 mu m).toFun =ᵐ[
        volumeMeasureOn (wholeSpaceCube d m)]
      fun x ↦ 1 - (mu : ℝ) *
        A.analyticCubeResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
          measurable_const (D := 1) (fun _ ↦ by norm_num) m x := by
  have hzcoe := (A.cubeOneResolventH10 mu m).toH1Function.coeFn_toScalarL2
  have hzclass := A.cubeOneResolventH10_value mu m
  have hanalytic := A.analyticCubeResolvent_ae mu
    (f := fun _ : Vec d ↦ (1 : ℝ)) measurable_const
    (D := 1) (fun _ ↦ by norm_num) m
  filter_upwards [hzcoe, hanalytic] with x hz ha
  simp only [cubeBoundaryRemainderH1, cubeConstantOneH1,
    H1Function.sub_toFun, H1Function.smul_toFun,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]
  rw [← hz, hzclass, ← ha]

/-- The boundary defect lies between zero and one almost everywhere. -/
theorem cubeBoundaryRemainder_abs_le_one_ae (mu : PositiveShift) (m : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d m),
      |(A.cubeBoundaryRemainderH1 mu m).toFun x| ≤ 1 := by
  filter_upwards [A.cubeBoundaryRemainder_ae mu m] with x hx
  rw [hx, abs_of_nonneg]
  · have hr0 := A.analyticCubeResolvent_nonneg mu measurable_const
      (f := fun _ : Vec d ↦ (1 : ℝ)) (fun _ ↦ by norm_num)
      (D := 1) (fun _ ↦ by norm_num) m x
    exact sub_le_self 1 (mul_nonneg mu.property.le hr0)
  · have hr := A.abs_analyticCubeResolvent_le mu measurable_const
      (f := fun _ : Vec d ↦ (1 : ℝ)) (D := 1) (by norm_num)
      (fun _ ↦ by norm_num) m x
    have hr0 := A.analyticCubeResolvent_nonneg mu measurable_const
      (f := fun _ : Vec d ↦ (1 : ℝ)) (fun _ ↦ by norm_num)
      (D := 1) (fun _ ↦ by norm_num) m x
    rw [abs_of_nonneg hr0] at hr
    have hmul := mul_le_mul_of_nonneg_left hr mu.property.le
    rw [show (mu : ℝ) * (1 / (mu : ℝ)) = 1 by
      rw [one_div, mul_inv_cancel₀ mu.property.ne']] at hmul
    exact sub_nonneg.mpr hmul

/-- The cube boundary defect solves the homogeneous shifted equation.  This
form is independent of any global small-contrast assumption and is the PDE
input for both the original and localized interior-decay routes. -/
theorem cubeBoundaryRemainder_isScalarForcedWeakSolution
    (mu : PositiveShift) (m : ℕ) :
    IsScalarForcedWeakSolution A.a (wholeSpaceCube d m)
      (fun y ↦ -((mu : ℝ) * (A.cubeBoundaryRemainderH1 mu m).toFun y))
      (A.cubeBoundaryRemainderH1 mu m) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let u := A.cubeBoundaryRemainderH1 mu m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU
      (measurable_const : Measurable
        (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
      (D := 1) (fun _ ↦ by norm_num)
  let z : H10Function (wholeSpaceCube d m) := A.cubeOneResolventH10 mu m
  have hzclass : ZeroTraceSobolev.ofH10Function z =
      alphaShiftedSolution A.a mu.property A.hnu
        (A.cubeEllipticity m) F := by
    apply ZeroTraceSobolev.ext
    · simpa only [ZeroTraceSobolev.toL2_ofH10Function, z, F] using!
        A.cubeOneResolventH10_value mu m
    · exact (Classical.choose_spec (ZeroTraceSobolev.exists_h10Function hU
        (alphaShiftedSolution A.a mu.property A.hnu
          (A.cubeEllipticity m) F))).2
  have hzweak : IsAlphaShiftedWeakSolution A.a (wholeSpaceCube d m)
      (mu : ℝ) F (ZeroTraceSobolev.ofH10Function z) := by
    rw [hzclass]
    exact alphaShiftedSolution_isAlphaShiftedWeakSolution A.a mu.property
      A.hnu (A.cubeEllipticity m) F
  have hzscalar :=
    isScalarForcedWeakSolution_sub_alpha_mul_of_isAlphaShiftedWeakSolution
      z hzweak
  constructor
  · convert u.memL2.const_smul (-(mu : ℝ)) using 1
    funext y
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  · intro phi
    have hFcoe := boundedMeasurableToScalarL2_coeFn hU
      (measurable_const : Measurable
        (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
      (D := 1) (fun _ : wholeSpaceCube d m ↦ by norm_num)
    have hmem := ae_restrict_mem (μ := volume) hU.isOpen.measurableSet
    have hsource : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m), F y = 1 := by
      filter_upwards [hFcoe, hmem] with y hy hyU
      rw [hy, domainExtension_of_mem hyU]
    calc
      (∫ y in wholeSpaceCube d m,
          vecDot (matVecMul (A.a y) (u.grad y))
            (phi.toH1Function.grad y) ∂volume) =
          -(mu : ℝ) * ∫ y in wholeSpaceCube d m,
            vecDot (matVecMul (A.a y) (z.toH1Function.grad y))
              (phi.toH1Function.grad y) ∂volume := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        simp only [u, cubeBoundaryRemainderH1, cubeConstantOneH1,
          H1Function.sub_grad, H1Function.smul_grad,
          H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
          H1Function.ofContDiffOnIsSobolevRegularDomain, fderiv_const_apply,
          zero_apply]
        have hgrad : ((fun _ : Fin d ↦ (0 : ℝ)) -
            (mu : ℝ) • z.toH1Function.grad y) =
            (-(mu : ℝ)) • z.toH1Function.grad y := by
          ext i
          simpa only [Pi.sub_apply, Pi.smul_apply, zero_sub, smul_eq_mul] using
            (neg_mul (mu : ℝ) (z.toH1Function.grad y i)).symm
        rw [hgrad, matVecMul_smul, vecDot_smul_left]
      _ = -(mu : ℝ) * ∫ y in wholeSpaceCube d m,
          (F y - (mu : ℝ) * z.toH1Function.toFun y) *
            phi.toH1Function.toFun y ∂volume := by
        rw [hzscalar.2 phi]
      _ = ∫ y in wholeSpaceCube d m,
          (-((mu : ℝ) * u.toFun y)) *
            phi.toH1Function.toFun y ∂volume := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hsource] with y hy
        simp only [u, cubeBoundaryRemainderH1, cubeConstantOneH1,
          H1Function.sub_toFun, H1Function.smul_toFun,
          H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
          H1Function.ofContDiffOnIsSobolevRegularDomain]
        rw [hy]
        ring

/-- Inner radius of the cutoff used to measure distance from the boundary of
the `m`th cube. -/
def cubeBoundaryCutoffInnerRadius (m : ℕ) : ℝ := (3 : ℝ) ^ m / 2

/-- Outer transition radius of the boundary cutoff. -/
def cubeBoundaryCutoffOuterRadius (m : ℕ) : ℝ := 3 * (3 : ℝ) ^ m / 4

/-- A smooth localization supported strictly inside the `m`th cube and equal
to one on its central half ball. -/
def cubeBoundaryCutoff (m : ℕ) : Vec d → ℝ :=
  QuantitativeBallCutoff.canonicalFun 0
    (cubeBoundaryCutoffInnerRadius m) (cubeBoundaryCutoffOuterRadius m)

private theorem cubeBoundaryCutoff_radii (m : ℕ) :
    0 < cubeBoundaryCutoffInnerRadius m ∧
      cubeBoundaryCutoffInnerRadius m < cubeBoundaryCutoffOuterRadius m := by
  unfold cubeBoundaryCutoffInnerRadius cubeBoundaryCutoffOuterRadius
  have hp : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) _
  constructor <;> linarith only [hp]

omit [NeZero d] in
/-- The boundary localization is smooth. -/
theorem contDiff_cubeBoundaryCutoff (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeBoundaryCutoff (d := d) m) :=
  QuantitativeBallCutoff.canonicalFun_smooth 0
    (cubeBoundaryCutoff_radii m).1 (cubeBoundaryCutoff_radii m).2

omit [NeZero d] in
/-- The boundary localization has compact support. -/
theorem hasCompactSupport_cubeBoundaryCutoff (m : ℕ) :
    HasCompactSupport (cubeBoundaryCutoff (d := d) m) :=
  QuantitativeBallCutoff.canonicalFun_hasCompactSupport 0
    (cubeBoundaryCutoff_radii m).1 (cubeBoundaryCutoff_radii m).2

omit [NeZero d] in
/-- The support of the boundary localization lies inside its cube. -/
theorem tsupport_cubeBoundaryCutoff_subset (m : ℕ) :
    tsupport (cubeBoundaryCutoff (d := d) m) ⊆ wholeSpaceCube d m := by
  let R : ℝ := 7 * (3 : ℝ) ^ m / 8
  have hp : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) _
  have hsR : cubeBoundaryCutoffOuterRadius m < R := by
    unfold cubeBoundaryCutoffOuterRadius R
    linarith only [hp]
  refine (QuantitativeBallCutoff.canonicalFun_tsupport_subset_euclideanBall
    (0 : Vec d) (cubeBoundaryCutoff_radii m).1
      (cubeBoundaryCutoff_radii m).2 hsR).trans ?_
  intro y hy
  rw [mem_wholeSpaceCube_iff]
  have hynorm : euclideanNorm (y - 0) < R :=
    Decay.euclideanNorm_sub_lt_of_mem_euclideanBall (le_of_lt (by positivity)) hy
  have hR : R < (3 : ℝ) ^ m := by
    unfold R
    linarith only [hp]
  intro i
  have hi : |y i| < (3 : ℝ) ^ m := by
    have hynorm0 : euclideanNorm y < R := by
      simpa only [sub_zero] using hynorm
    exact (HCPolySupport.abs_coordinate_le_euclideanNorm y i).trans_lt
      (hynorm0.trans hR)
  exact (abs_lt.mp hi)

omit [NeZero d] in
/-- The full active support of the boundary cutoff lies in the origin-centred
ball of radius `3^m`.  This is the carrier used by the localized split-skew
coefficient bounds. -/
theorem tsupport_cubeBoundaryCutoff_subset_euclideanBall (m : ℕ) :
    tsupport (cubeBoundaryCutoff (d := d) m) ⊆
      euclideanBall 0 ((3 : ℝ) ^ m) := by
  exact QuantitativeBallCutoff.canonicalFun_tsupport_subset_euclideanBall
    (0 : Vec d) (cubeBoundaryCutoff_radii m).1
      (cubeBoundaryCutoff_radii m).2 (by
        unfold cubeBoundaryCutoffOuterRadius
        have hp : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) _
        linarith only [hp])

omit [NeZero d] in
/-- The boundary localization is one throughout its inner ball. -/
theorem cubeBoundaryCutoff_eq_one {m : ℕ} {y : Vec d}
    (hy : y ∈ euclideanBall 0 (cubeBoundaryCutoffInnerRadius m)) :
    cubeBoundaryCutoff (d := d) m y = 1 :=
  QuantitativeBallCutoff.canonicalFun_eq_one_on_inner
    (cubeBoundaryCutoff_radii m).1 (cubeBoundaryCutoff_radii m).2 hy

omit [NeZero d] in
/-- A nonzero derivative of the boundary localization lies outside its inner
radius. -/
theorem cubeBoundaryCutoffInnerRadius_le_euclideanNorm {m : ℕ} {y : Vec d}
    (hy : fderiv ℝ (cubeBoundaryCutoff (d := d) m) y ≠ 0) :
    cubeBoundaryCutoffInnerRadius m ≤ euclideanNorm (y - 0) := by
  by_contra hnot
  have hlt : euclideanNorm (y - 0) < cubeBoundaryCutoffInnerRadius m :=
    lt_of_not_ge hnot
  have hr0 : 0 ≤ cubeBoundaryCutoffInnerRadius m :=
    (cubeBoundaryCutoff_radii m).1.le
  have hyBall : y ∈ euclideanBall 0 (cubeBoundaryCutoffInnerRadius m) := by
    change euclideanSqDist y 0 < cubeBoundaryCutoffInnerRadius m ^ 2
    rw [show euclideanSqDist y 0 = euclideanNorm (y - 0) ^ 2 by
      rw [euclideanNorm_sq]; rfl]
    exact (sq_lt_sq₀ (euclideanNorm_nonneg _) hr0).2 hlt
  exact hy (Decay.fderiv_eq_zero_of_eventuallyEq_one
    (isOpen_euclideanBall 0 (cubeBoundaryCutoffInnerRadius m))
    (fun z hz ↦ cubeBoundaryCutoff_eq_one hz) hyBall)

/-- A volume-order budget for the gradient of the boundary defect on every
subset of the cube. -/
theorem cubeBoundaryRemainder_gradient_budget (mu : PositiveShift) (m : ℕ)
    {W : Set (Vec d)} (hW : W ⊆ wholeSpaceCube d m) :
    vectorLpSizeOn W 2 (A.cubeBoundaryRemainderH1 mu m).grad ≤
      (mu : ℝ) * (min (mu : ℝ) A.nu)⁻¹ *
        (volume (wholeSpaceCube d m)).toReal := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU
      (measurable_const : Measurable (fun _ : wholeSpaceCube d m ↦ (1 : ℝ)))
      (D := 1) (fun _ ↦ by norm_num)
  let z : H10Function (wholeSpaceCube d m) := A.cubeOneResolventH10 mu m
  have hzclass : ZeroTraceSobolev.ofH10Function z =
      alphaShiftedSolution A.a mu.property A.hnu
        (A.cubeEllipticity m) F := by
    apply ZeroTraceSobolev.ext
    · simpa only [ZeroTraceSobolev.toL2_ofH10Function, z, F] using!
        A.cubeOneResolventH10_value mu m
    · exact (Classical.choose_spec (ZeroTraceSobolev.exists_h10Function hU
        (alphaShiftedSolution A.a mu.property A.hnu
          (A.cubeEllipticity m) F))).2
  have hconst : (cubeConstantOneH1 (d := d) m).gradToHilbertVectorL2 = 0 := by
    refine (Lp.ext_iff).2 ?_
    filter_upwards [(cubeConstantOneH1 (d := d) m).coeFn_gradToHilbertVectorL2,
      MeasureTheory.Lp.coeFn_zero (E := HilbertVec d) (p := (2 : ENNReal))
        (volumeMeasureOn (wholeSpaceCube d m))] with y hy hzero
    rw [hy, hzero]
    apply HilbertVec.ext
    intro i
    simp only [cubeConstantOneH1,
      H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      H1Function.ofContDiffOnIsSobolevRegularDomain, hilbertifyVecField,
      HilbertVec.ofVec, PiLp.toLp_apply, fderiv_const_apply,
      zero_apply, Pi.zero_apply]
    rfl
  have hlocal := vectorLpSizeOn_grad_le_norm_gradToHilbertVectorL2 hW
    (A.cubeBoundaryRemainderH1 mu m)
  have hgrad :
      ‖(A.cubeBoundaryRemainderH1 mu m).gradToHilbertVectorL2‖ =
        (mu : ℝ) * ‖z.toH1Function.gradToHilbertVectorL2‖ := by
    rw [cubeBoundaryRemainderH1, sub_eq_add_neg,
      ← neg_smul,
      H1Function.gradToHilbertVectorL2_add,
      H1Function.gradToHilbertVectorL2_smul, hconst, zero_add,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos mu.property]
  rw [hgrad] at hlocal
  refine hlocal.trans ?_
  have hzgrad : ‖z.toH1Function.gradToHilbertVectorL2‖ ≤
      ‖alphaShiftedSolution A.a mu.property A.hnu
        (A.cubeEllipticity m) F‖ := by
    rw [← ZeroTraceSobolev.gradient_ofH10Function, hzclass]
    exact ZeroTraceSobolev.norm_gradient_le _
  have hsolutionBound :
      ‖alphaShiftedSolution A.a mu.property A.hnu
        (A.cubeEllipticity m) F‖ ≤
      (min (mu : ℝ) A.nu)⁻¹ *
        (volume (wholeSpaceCube d m)).toReal := by
    have hV1 : 1 ≤ (volume (wholeSpaceCube d m)).toReal := by
      rw [volume_wholeSpaceCube_toReal]
      have ht1 : 1 ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      exact one_le_pow₀ (by linarith only [ht1])
    have hsqrt : Real.sqrt ((volume (wholeSpaceCube d m)).toReal) ≤
        (volume (wholeSpaceCube d m)).toReal := by
      have hs0 := Real.sqrt_nonneg ((volume (wholeSpaceCube d m)).toReal)
      have hs2 := Real.sq_sqrt (le_trans zero_le_one hV1)
      nlinarith only [hs0, hs2, hV1]
    exact (norm_alphaShiftedSolution_apply_le A.a mu.property
      A.hnu (A.cubeEllipticity m) F).trans
      ((mul_le_mul_of_nonneg_left (norm_cubeConstantOne_le (d := d) m)
        (inv_nonneg.mpr (le_of_lt (lt_min mu.property A.hnu)))).trans
      (mul_le_mul_of_nonneg_left hsqrt
        (inv_nonneg.mpr (le_of_lt (lt_min mu.property A.hnu)))))
  have hzbound := hzgrad.trans hsolutionBound
  calc
    (mu : ℝ) * ‖z.toH1Function.gradToHilbertVectorL2‖ ≤
        (mu : ℝ) * ((min (mu : ℝ) A.nu)⁻¹ *
          (volume (wholeSpaceCube d m)).toReal) :=
      mul_le_mul_of_nonneg_left hzbound mu.property.le
    _ = (mu : ℝ) * (min (mu : ℝ) A.nu)⁻¹ *
        (volume (wholeSpaceCube d m)).toReal := by ring

/-- The explicit coordinate-gradient budget of the boundary localization. -/
def cubeBoundaryCutoffGradientBudget (m : ℕ) : ℝ :=
  (d : ℝ) * (smoothTransitionProfile.derivBound *
    (2 * (d : ℝ) /
      (cubeBoundaryCutoffOuterRadius m - cubeBoundaryCutoffInnerRadius m))) ^ 2

/-- A scale-independent upper bound for the coordinate-gradient budget of the
boundary localization. -/
def cubeBoundaryCutoffUniformGradientBudget : ℝ :=
  (d : ℝ) * (smoothTransitionProfile.derivBound * (8 * (d : ℝ))) ^ 2

omit [NeZero d] in
private theorem cubeBoundaryCutoffGradientBudget_le_uniform (m : ℕ) :
    cubeBoundaryCutoffGradientBudget (d := d) m ≤
      cubeBoundaryCutoffUniformGradientBudget (d := d) := by
  have ht0 : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) _
  have ht1 : 1 ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdiff : cubeBoundaryCutoffOuterRadius m -
      cubeBoundaryCutoffInnerRadius m = (3 : ℝ) ^ m / 4 := by
    unfold cubeBoundaryCutoffOuterRadius cubeBoundaryCutoffInnerRadius
    ring
  have hratio : 2 * (d : ℝ) / ((3 : ℝ) ^ m / 4) ≤ 8 * (d : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < (3 : ℝ) ^ m / 4)]
    have hmul : 2 * (d : ℝ) ≤ 2 * (d : ℝ) * (3 : ℝ) ^ m :=
      le_mul_of_one_le_right (mul_nonneg (by norm_num) hd0) ht1
    calc 2 * (d : ℝ) ≤ 2 * (d : ℝ) * (3 : ℝ) ^ m := hmul
      _ = 8 * (d : ℝ) * ((3 : ℝ) ^ m / 4) := by ring
  unfold cubeBoundaryCutoffGradientBudget cubeBoundaryCutoffUniformGradientBudget
  rw [hdiff]
  have hratio0 : 0 ≤ 2 * (d : ℝ) / ((3 : ℝ) ^ m / 4) := by positivity
  have hright0 : 0 ≤ smoothTransitionProfile.derivBound * (8 * (d : ℝ)) :=
    mul_nonneg smoothTransitionProfile.derivBound_nonneg (by positivity)
  have hproduct := mul_le_mul_of_nonneg_left hratio
    smoothTransitionProfile.derivBound_nonneg
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀
      (mul_nonneg smoothTransitionProfile.derivBound_nonneg hratio0)
      hright0).2 hproduct) hd0

omit [NeZero d] in
/-- The coordinate-gradient square of the boundary cutoff is bounded by the
scale-independent cutoff budget. -/
theorem cubeBoundaryCutoff_gradSq_le_uniform (m : ℕ) (y : Vec d) :
    vecNormSq (fun i ↦
      (fderiv ℝ (cubeBoundaryCutoff (d := d) m) y) (basisVec i)) ≤
      cubeBoundaryCutoffUniformGradientBudget (d := d) := by
  exact (Decay.vecNormSq_fderiv_ballCutoff_le 0
    (cubeBoundaryCutoff_radii m).1 (cubeBoundaryCutoff_radii m).2 y).trans
      (cubeBoundaryCutoffGradientBudget_le_uniform (d := d) m)

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
