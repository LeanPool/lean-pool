/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationCauchy

/-!
# ExitMeanValueIdentificationWhole

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The whole-space resolvent is an `H¹` function of every exhaustion cube

The Dirichlet resolvents of the exhaustion cubes converge to the whole-space resolvent
pointwise, and their gradients are Cauchy in `L²` of every fixed cube by the Caccioppoli
estimate.  Both convergences are handed to the closed `H¹` graph of the cube, which returns an
`H¹` function whose value function is the whole-space resolvent *on the nose* — the exact
pointwise representative survives the limit, which matters because every later argument reads
its values pointwise.

Passing to the limit in the level equations identifies the forcing: the whole-space resolvent
`psi = R_mu f` solves

  `-div (a grad psi) = f - mu psi`   weakly on every exhaustion cube.

Subtracting the Green potential of that residual leaves the whole-space harmonic part, which is
weakly `a`-harmonic on the cube and differs from `psi` by a named zero-trace Sobolev function.
This is the level-`m` statement of `ExitMeanValueIdentificationLevel.lean` with the level objects
replaced by their limits, and no weak-compactness argument is used anywhere.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The elliptic pairing as a Hilbert inner product -/

omit [NeZero d] in
/-- The flux pairing of two `H¹` gradients is an inner product against the continuous
coefficient operator. -/
theorem setIntegral_flux_eq_inner {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (u w : H1Function U) :
    (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (w.grad x) ∂volume) =
      inner ℝ (hilbertCoeffOperator hEll u.gradToHilbertVectorL2) w.gradToHilbertVectorL2 := by
  rw [show u.gradToHilbertVectorL2 = toHilbertVectorL2OfVecField u.grad_memVectorL2 from rfl,
    show w.gradToHilbertVectorL2 = toHilbertVectorL2OfVecField w.grad_memVectorL2 from rfl,
    hilbertCoeffOperator_toHilbertVectorL2OfVecField,
    inner_toHilbertVectorL2OfVecField_eq_integral]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The whole-space residual -/

/-- The residual of the whole-space resolvent: the datum less the shift times the resolvent. -/
def wholeSpaceResidual (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) : Vec d → ℝ :=
  fun y ↦ f y - (mu : ℝ) * A.analyticMinimalResolventReal mu f hf hfD y

theorem measurable_wholeSpaceResidual (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.wholeSpaceResidual mu hf hfD) :=
  hf.sub ((A.measurable_analyticMinimalResolventReal mu hf hfD).const_mul _)

theorem abs_wholeSpaceResidual_le (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (y : Vec d) :
    |A.wholeSpaceResidual mu hf hfD y| ≤ 2 * D := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
  have hbound := A.abs_analyticMinimalResolventReal_le mu hf hfD y
  have hsecond : |(mu : ℝ) * A.analyticMinimalResolventReal mu f hf hfD y| ≤ D := by
    rw [abs_mul, abs_of_pos hmu]
    calc
      (mu : ℝ) * |A.analyticMinimalResolventReal mu f hf hfD y| ≤ (mu : ℝ) * (D / (mu : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hmu.le
      _ = D := mul_div_cancel₀ D hmu.ne'
  refine (abs_sub _ _).trans ?_
  linarith only [hfD y, hsecond]

/-! ## `L²` membership of the limit objects on a cube -/

omit [NeZero d] in
private theorem memL2On_of_bound {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {g : Vec d → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    MemL2On U g := by
  let := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hgC x

theorem memL2On_analyticMinimalResolventReal (v : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    MemL2On (wholeSpaceCube d v) (A.analyticMinimalResolventReal mu f hf hfD) :=
  memL2On_of_bound (isOpenBoundedConvexDomain_wholeSpaceCube d v)
    (A.measurable_analyticMinimalResolventReal mu hf hfD)
    (A.abs_analyticMinimalResolventReal_le mu hf hfD)

theorem memL2On_wholeSpaceResidual (v : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    MemL2On (wholeSpaceCube d v) (A.wholeSpaceResidual mu hf hfD) :=
  memL2On_of_bound (isOpenBoundedConvexDomain_wholeSpaceCube d v)
    (A.measurable_wholeSpaceResidual mu hf hfD)
    (A.abs_wholeSpaceResidual_le mu hf hfD)

/-! ## The approximating sequence on a fixed cube -/

/-- The Dirichlet resolvent of the exhaustion cube of index `v + 1 + n`, restricted to the cube
of index `v`. -/
def cubeApproxSolution (v n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) : H1Function (wholeSpaceCube d v) :=
  (A.cubeLevelSolution (v + 1 + n) mu hf hfD).restrict
    (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
    (wholeSpaceCube_mono (le_trans (Nat.le_succ v) (Nat.le_add_right (v + 1) n)))

theorem cubeApproxSolution_toFun (v n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    (A.cubeApproxSolution v n mu hf hfD).toFun =
      A.analyticCubeResolvent mu f hf hfD (v + 1 + n) :=
  A.cubeLevelSolution_toFun (v + 1 + n) mu hf hfD

theorem cubeApproxSolution_grad (v n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    (A.cubeApproxSolution v n mu hf hfD).grad =
      (A.cubeLevelSolution (v + 1 + n) mu hf hfD).grad := rfl

theorem isScalarForcedWeakSolution_cubeApproxSolution (v n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    IsScalarForcedWeakSolution A.a (wholeSpaceCube d v)
      (A.cubeLevelResidual (v + 1 + n) mu hf hfD) (A.cubeApproxSolution v n mu hf hfD) :=
  (A.isScalarForcedWeakSolution_cubeLevelSolution (v + 1 + n) mu hf hfD).restrictSubset
    (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
    (wholeSpaceCube_mono (le_trans (Nat.le_succ v) (Nat.le_add_right (v + 1) n)))

/-! ## Convergence of the approximating sequence -/

private theorem tendsto_shifted_setIntegral (v w : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    Tendsto (fun n : ℕ ↦ ∫ x in wholeSpaceCube d w,
        (A.analyticCubeResolvent mu f hf hfD (v + 1 + n) x -
          A.analyticMinimalResolventReal mu f hf hfD x) ^ 2 ∂volume) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ v + 1 + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat (v + 1)
  exact (A.tendsto_setIntegral_analyticCubeResolvent_sub_sq w mu hf hD hfD).comp hshift

/-- **The values converge in `L²` of the cube.** -/
theorem tendsto_toScalarL2_cubeApproxSolution (v : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    Tendsto (fun n : ℕ ↦ (A.cubeApproxSolution v n mu hf hfD).toScalarL2) atTop
      (𝓝 (toScalarL2 (A.memL2On_analyticMinimalResolventReal v mu hf hfD))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n : ℕ,
      ‖(A.cubeApproxSolution v n mu hf hfD).toScalarL2 -
          toScalarL2 (A.memL2On_analyticMinimalResolventReal v mu hf hfD)‖ =
        Real.sqrt (∫ x in wholeSpaceCube d v,
          (A.analyticCubeResolvent mu f hf hfD (v + 1 + n) x -
            A.analyticMinimalResolventReal mu f hf hfD x) ^ 2 ∂volume) := by
    intro n
    have h := norm_toScalarL2_sub_sq (A.cubeApproxSolution v n mu hf hfD)
      (A.memL2On_analyticMinimalResolventReal v mu hf hfD)
    rw [A.cubeApproxSolution_toFun v n mu hf hfD] at h
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hsq]
  have hzero : Real.sqrt 0 = 0 := Real.sqrt_zero
  rw [← hzero]
  exact (Real.continuous_sqrt.tendsto 0).comp (A.tendsto_shifted_setIntegral v v mu hf hD hfD)

private theorem integrable_analyticCubeResolvent_sub_sq (v : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (k : ℕ) :
    Integrable (fun x ↦ (A.analyticCubeResolvent mu f hf hfD k x -
      A.analyticMinimalResolventReal mu f hf hfD x) ^ 2)
      (volumeMeasureOn (wholeSpaceCube d v)) := by
  let := (isOpenBoundedConvexDomain_wholeSpaceCube d
    v).isBoundedDomain.isFiniteMeasure_restrict_volume
  refine Integrable.mono' (integrable_const ((2 * (D / (mu : ℝ))) ^ 2))
    (((A.measurable_analyticCubeResolvent mu hf hfD k).sub
      (A.measurable_analyticMinimalResolventReal mu hf hfD)).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with x
  have h1 := A.abs_analyticCubeResolvent_le mu hf hD hfD k x
  have h2 := A.abs_analyticMinimalResolventReal_le mu hf hfD x
  have habs : |A.analyticCubeResolvent mu f hf hfD k x -
      A.analyticMinimalResolventReal mu f hf hfD x| ≤ 2 * (D / (mu : ℝ)) := by
    refine (abs_sub _ _).trans ?_
    linarith only [h1, h2]
  have hsq := pow_le_pow_left₀ (abs_nonneg (A.analyticCubeResolvent mu f hf hfD k x -
    A.analyticMinimalResolventReal mu f hf hfD x)) habs 2
  rw [sq_abs] at hsq
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq

/-- **The gradients are Cauchy in `L²` of the cube.**  This is the Caccioppoli estimate against
the `L²` convergence of the values on the next cube. -/
theorem cauchySeq_gradToHilbertVectorL2_cubeApproxSolution (v : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    CauchySeq fun n : ℕ ↦ (A.cubeApproxSolution v n mu hf hfD).gradToHilbertVectorL2 := by
  obtain ⟨C, hC, hCbound⟩ := A.exists_cubeCauchyConstant v mu hf hfD
  set a : ℕ → ℝ := fun n ↦ ∫ x in wholeSpaceCube d (v + 1),
    (A.analyticCubeResolvent mu f hf hfD (v + 1 + n) x -
      A.analyticMinimalResolventReal mu f hf hfD x) ^ 2 ∂volume with ha
  have hatend : Tendsto a atTop (𝓝 0) := A.tendsto_shifted_setIntegral v (v + 1) mu hf hD hfD
  rw [Metric.cauchySeq_iff]
  intro eps heps
  have hdelta : (0 : ℝ) < eps ^ 2 / (4 * (C + 1)) := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hatend) _ hdelta
  refine ⟨N, fun k hk m hm ↦ ?_⟩
  have hak : a k < eps ^ 2 / (4 * (C + 1)) := by
    have := hN k hk
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self (a k)).trans_lt this
  have ham : a m < eps ^ 2 / (4 * (C + 1)) := by
    have := hN m hm
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self (a m)).trans_lt this
  -- the value difference on the larger cube
  have hcross : (∫ x in wholeSpaceCube d (v + 1),
      (A.analyticCubeResolvent mu f hf hfD (v + 1 + k) x -
        A.analyticCubeResolvent mu f hf hfD (v + 1 + m) x) ^ 2 ∂volume) ≤ 2 * a k + 2 * a m := by
    have hint : Integrable (fun x ↦ 2 * (A.analyticCubeResolvent mu f hf hfD (v + 1 + k) x -
        A.analyticMinimalResolventReal mu f hf hfD x) ^ 2 +
        2 * (A.analyticCubeResolvent mu f hf hfD (v + 1 + m) x -
          A.analyticMinimalResolventReal mu f hf hfD x) ^ 2)
        (volumeMeasureOn (wholeSpaceCube d (v + 1))) :=
      ((A.integrable_analyticCubeResolvent_sub_sq (v + 1) mu hf hD hfD (v + 1 + k)).const_mul
        2).add ((A.integrable_analyticCubeResolvent_sub_sq (v + 1) mu hf hD hfD
          (v + 1 + m)).const_mul 2)
    have hle : (∫ x in wholeSpaceCube d (v + 1),
        (A.analyticCubeResolvent mu f hf hfD (v + 1 + k) x -
          A.analyticCubeResolvent mu f hf hfD (v + 1 + m) x) ^ 2 ∂volume) ≤
        ∫ x in wholeSpaceCube d (v + 1),
          (2 * (A.analyticCubeResolvent mu f hf hfD (v + 1 + k) x -
            A.analyticMinimalResolventReal mu f hf hfD x) ^ 2 +
            2 * (A.analyticCubeResolvent mu f hf hfD (v + 1 + m) x -
              A.analyticMinimalResolventReal mu f hf hfD x) ^ 2) ∂volume := by
      refine integral_mono_of_nonneg ?_ hint ?_
      · filter_upwards with x
        positivity
      · filter_upwards with x
        nlinarith only [sq_nonneg (A.analyticCubeResolvent mu f hf hfD (v + 1 + k) x +
          A.analyticCubeResolvent mu f hf hfD (v + 1 + m) x -
          2 * A.analyticMinimalResolventReal mu f hf hfD x)]
    refine hle.trans (le_of_eq ?_)
    rw [integral_add ((A.integrable_analyticCubeResolvent_sub_sq (v + 1) mu hf hD hfD
      (v + 1 + k)).const_mul 2) ((A.integrable_analyticCubeResolvent_sub_sq (v + 1) mu hf hD hfD
        (v + 1 + m)).const_mul 2), integral_const_mul, integral_const_mul]
  -- the Caccioppoli estimate
  have hgrad := hCbound (v + 1 + k) (v + 1 + m) (Nat.le_add_right (v + 1) k)
    (Nat.le_add_right (v + 1) m)
  have hnormsq : ‖(A.cubeApproxSolution v k mu hf hfD).gradToHilbertVectorL2 -
      (A.cubeApproxSolution v m mu hf hfD).gradToHilbertVectorL2‖ ^ 2 ≤ C * (2 * a k + 2 * a m) := by
    rw [norm_gradToHilbertVectorL2_sub_sq]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hcross hC)
    simpa only [A.cubeApproxSolution_grad] using hgrad
  have hlt : ‖(A.cubeApproxSolution v k mu hf hfD).gradToHilbertVectorL2 -
      (A.cubeApproxSolution v m mu hf hfD).gradToHilbertVectorL2‖ ^ 2 < eps ^ 2 := by
    refine hnormsq.trans_lt ?_
    have hCpos : (0 : ℝ) < C + 1 := by linarith only [hC]
    have hsum : 2 * a k + 2 * a m < 4 * (eps ^ 2 / (4 * (C + 1))) := by linarith only [hak, ham]
    have hstep : C * (2 * a k + 2 * a m) ≤ C * (4 * (eps ^ 2 / (4 * (C + 1)))) :=
      mul_le_mul_of_nonneg_left hsum.le hC
    have hval : C * (4 * (eps ^ 2 / (4 * (C + 1)))) = C / (C + 1) * eps ^ 2 := by
      field_simp
    rw [hval] at hstep
    have hfrac : C / (C + 1) < 1 := by
      rw [div_lt_one hCpos]
      linarith only []
    have heps2 : (0 : ℝ) < eps ^ 2 := by positivity
    calc C * (2 * a k + 2 * a m) ≤ C / (C + 1) * eps ^ 2 := hstep
      _ < 1 * eps ^ 2 := by
        exact mul_lt_mul_of_pos_right hfrac heps2
      _ = eps ^ 2 := one_mul _
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 heps.le hlt

/-! ## The whole-space resolvent on a cube -/

/-- **The whole-space resolvent is an `H¹` function of every exhaustion cube and solves the
shifted equation there.**  Its value function is the exact continuous representative of the
resolvent, not merely a function almost everywhere equal to it. -/
theorem exists_h1Function_analyticMinimalResolventReal (v : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ∃ z : H1Function (wholeSpaceCube d v),
      z.toFun = A.analyticMinimalResolventReal mu f hf hfD ∧
        IsScalarForcedWeakSolution A.a (wholeSpaceCube d v)
          (A.wholeSpaceResidual mu hf hfD) z := by
  let := (isOpenBoundedConvexDomain_wholeSpaceCube d
    v).isBoundedDomain.isFiniteMeasure_restrict_volume
  have hEll := A.cubeEllipticity v
  have hpsiL2 := A.memL2On_analyticMinimalResolventReal v mu hf hfD
  obtain ⟨Gz, hGz⟩ := cauchySeq_tendsto_of_complete
    (A.cauchySeq_gradToHilbertVectorL2_cubeApproxSolution v mu hf hD hfD)
  have hmem : ((toScalarL2 hpsiL2 : ScalarL2 (wholeSpaceCube d v)), Gz) ∈
      h1GraphClosedSubmodule (U := wholeSpaceCube d v) :=
    mem_h1GraphClosedSubmodule_of_tendsto_h1Function
      (fun n ↦ A.cubeApproxSolution v n mu hf hfD)
      (A.tendsto_toScalarL2_cubeApproxSolution v mu hf hD hfD) hGz
  have hwval : (toH1FunctionOfMemH1Graph (U := wholeSpaceCube d v) _ hmem).toScalarL2 =
      toScalarL2 hpsiL2 :=
    toH1FunctionOfMemH1Graph_toScalarL2 (U := wholeSpaceCube d v) _ hmem
  have hwgrad : (toH1FunctionOfMemH1Graph (U := wholeSpaceCube d v) _ hmem).gradToHilbertVectorL2 =
      Gz :=
    toH1FunctionOfMemH1Graph_gradToHilbertVectorL2 (U := wholeSpaceCube d v) _ hmem
  set wlim : H1Function (wholeSpaceCube d v) :=
    toH1FunctionOfMemH1Graph (U := wholeSpaceCube d v) _ hmem with hwlim
  have hae : A.analyticMinimalResolventReal mu f hf hfD
      =ᵐ[volumeMeasureOn (wholeSpaceCube d v)] wlim.toFun := by
    filter_upwards [coeFn_toScalarL2 hpsiL2, wlim.coeFn_toScalarL2] with x h1 h2
    rw [← h1, ← hwval, h2]
  obtain ⟨z, hzfun, hzgrad⟩ := exists_h1Function_toFun_eq wlim hpsiL2 hae
  have hzghil : z.gradToHilbertVectorL2 = Gz := by
    rw [← hwgrad]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [H1Function.coeFn_gradToHilbertVectorL2 z,
      H1Function.coeFn_gradToHilbertVectorL2 wlim] with x h1 h2
    rw [h1, h2, hzgrad]
  refine ⟨z, hzfun, A.memL2On_wholeSpaceResidual v mu hf hfD, fun phi ↦ ?_⟩
  -- the left-hand sides converge, by continuity of the coefficient operator
  have hlhs : Tendsto (fun n : ℕ ↦ ∫ x in wholeSpaceCube d v, vecDot (matVecMul (A.a x)
      ((A.cubeApproxSolution v n mu hf hfD).grad x)) (phi.toH1Function.grad x) ∂volume)
      atTop (𝓝 (∫ x in wholeSpaceCube d v, vecDot (matVecMul (A.a x) (z.grad x))
        (phi.toH1Function.grad x) ∂volume)) := by
    have hcont : Continuous fun G : HilbertVectorL2 (wholeSpaceCube d v) ↦
        inner ℝ (hilbertCoeffOperator hEll G) phi.toH1Function.gradToHilbertVectorL2 :=
      (hilbertCoeffOperator hEll).continuous.inner continuous_const
    have hlim := (hcont.tendsto Gz).comp hGz
    rw [setIntegral_flux_eq_inner hEll z phi.toH1Function, hzghil]
    refine hlim.congr fun n ↦ ?_
    exact (setIntegral_flux_eq_inner hEll (A.cubeApproxSolution v n mu hf hfD)
      phi.toH1Function).symm
  -- the right-hand sides converge, by dominated convergence
  have hrhs : Tendsto (fun n : ℕ ↦ ∫ x in wholeSpaceCube d v,
      A.cubeLevelResidual (v + 1 + n) mu hf hfD x * phi.toH1Function.toFun x ∂volume) atTop
      (𝓝 (∫ x in wholeSpaceCube d v,
        A.wholeSpaceResidual mu hf hfD x * phi.toH1Function.toFun x ∂volume)) := by
    have hphiInt : Integrable phi.toH1Function.toFun
        (volumeMeasureOn (wholeSpaceCube d v)) :=
      phi.toH1Function.memL2.integrable (by norm_num)
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ 2 * D * |phi.toH1Function.toFun x|) (fun n ↦ ?_)
      (hphiInt.abs.const_mul (2 * D)) (fun n ↦ ?_) ?_
    · exact ((A.measurable_cubeLevelResidual (v + 1 + n) mu hf hfD).aestronglyMeasurable).mul
        phi.toH1Function.memL2.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (A.abs_cubeLevelResidual_le (v + 1 + n) mu hf hD hfD x) (abs_nonneg _)
    · filter_upwards with x
      have hshift : Tendsto (fun n : ℕ ↦ v + 1 + n) atTop atTop := by
        simpa only [Nat.add_comm] using tendsto_add_atTop_nat (v + 1)
      have hres : Tendsto (fun n : ℕ ↦ A.cubeLevelResidual (v + 1 + n) mu hf hfD x) atTop
          (𝓝 (A.wholeSpaceResidual mu hf hfD x)) := by
        have hpsi := (A.tendsto_analyticCubeResolvent_real mu hf hfD x).comp hshift
        exact tendsto_const_nhds.sub (hpsi.const_mul ((mu : ℝ)))
      exact hres.mul_const _
  have heq : ∀ n : ℕ, (∫ x in wholeSpaceCube d v, vecDot (matVecMul (A.a x)
      ((A.cubeApproxSolution v n mu hf hfD).grad x)) (phi.toH1Function.grad x) ∂volume) =
      ∫ x in wholeSpaceCube d v,
        A.cubeLevelResidual (v + 1 + n) mu hf hfD x * phi.toH1Function.toFun x ∂volume :=
    fun n ↦ (A.isScalarForcedWeakSolution_cubeApproxSolution v n mu hf hfD).2 phi
  exact tendsto_nhds_unique (hlhs.congr heq) hrhs

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
