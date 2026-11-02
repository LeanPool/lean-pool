/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.CaccioppoliPlain
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationCutoff
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationLevel
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PositiveC0Resolvent

/-!
# ExitMeanValueIdentificationCauchy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Caccioppoli Cauchy estimate for the exhaustion resolvents

The Dirichlet resolvents of a fixed bounded measurable datum on the cubes of the exhaustion
converge pointwise to the whole-space resolvent, and are uniformly bounded.  Their *gradients*
are controlled by the Caccioppoli inequality at level zero: on two consecutive cubes
`V ⊆ V'` the difference of two exhaustion levels solves the homogeneous shifted equation, whose
forcing is a negative multiple of the difference, so the forcing pairing in the Caccioppoli
estimate is nonpositive and
  `∫_V |grad (psi_k - psi_m)|² ≤ C ∫_{V'} (psi_k - psi_m)²`.

The right-hand side goes to zero by dominated convergence, so the gradients are Cauchy in `L²(V)`
and no weak-compactness argument is needed.

This file supplies the two halves: the `L²` convergence of the values on any cube, and the
Caccioppoli Cauchy estimate with a constant depending only on the cube index.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Two Hilbert-space identities -/

omit [NeZero d] in
/-- The Hilbert gradient class of a difference is the difference of the classes. -/
theorem gradToHilbertVectorL2_sub {U : Set (Vec d)} (u w : H1Function U) :
    (u - w).gradToHilbertVectorL2 = u.gradToHilbertVectorL2 - w.gradToHilbertVectorL2 := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [H1Function.coeFn_gradToHilbertVectorL2 (u - w),
    H1Function.coeFn_gradToHilbertVectorL2 u, H1Function.coeFn_gradToHilbertVectorL2 w,
    MeasureTheory.Lp.coeFn_sub u.gradToHilbertVectorL2 w.gradToHilbertVectorL2]
    with x h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3]
  simp only [hilbertifyVecField, H1Function.sub_grad]
  exact map_sub (HilbertVec.continuousLinearEquivVec d).symm (u.grad x) (w.grad x)

omit [NeZero d] in
/-- The squared `L²` norm of a gradient difference is the integral of the squared pointwise
difference. -/
theorem norm_gradToHilbertVectorL2_sub_sq {U : Set (Vec d)} (u w : H1Function U) :
    ‖u.gradToHilbertVectorL2 - w.gradToHilbertVectorL2‖ ^ 2 =
      ∫ x in U, vecNormSq (u.grad x - w.grad x) ∂volume := by
  rw [← gradToHilbertVectorL2_sub u w, ← real_inner_self_eq_norm_sq]
  have h : (u - w).gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField (u - w).grad_memVectorL2 := rfl
  rw [h, inner_toHilbertVectorL2OfVecField_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [H1Function.sub_grad]
  rfl

omit [NeZero d] in
/-- The squared `L²` norm of a value difference is the integral of the squared pointwise
difference. -/
theorem norm_toScalarL2_sub_sq {U : Set (Vec d)} (u : H1Function U) {g : Vec d → ℝ}
    (hg : MemL2On U g) :
    ‖u.toScalarL2 - toScalarL2 hg‖ ^ 2 = ∫ x in U, (u.toFun x - g x) ^ 2 ∂volume := by
  rw [← real_inner_self_eq_norm_sq, scalarInner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_sub u.toScalarL2 (toScalarL2 hg),
    u.coeFn_toScalarL2, coeFn_toScalarL2 hg] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, sq]

/-! ## Integrability of the cutoff energy density -/

omit [NeZero d] in
/-- A smooth compactly supported weight times the squared gradient of an `H¹` function is
integrable. -/
private theorem integrable_mul_vecNormSq_grad {U : Set (Vec d)} (u : H1Function U)
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hphiCompact : HasCompactSupport phi) :
    Integrable (fun x ↦ phi x * vecNormSq (u.grad x)) (volumeMeasureOn U) := by
  have hphiTop : MemLp phi ∞ (volumeMeasureOn U) :=
    (hphi.continuous.memLp_of_hasCompactSupport hphiCompact).restrict U
  have hq : MemVectorL2 U (fun x ↦ phi x • u.grad x) := by
    simpa only [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul, mul_comm] using!
      (MemLp.of_eval fun i : Fin d ↦
        (memScalarL2_coord_of_memVectorL2 u.grad_memVectorL2 i).fun_mul hphiTop)
  refine (integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hq).congr ?_
  filter_upwards with x
  simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

omit [NeZero d] in
private theorem isFiniteMeasure_cube (v : ℕ) :
    IsFiniteMeasure (volumeMeasureOn (wholeSpaceCube d v)) :=
  (isOpenBoundedConvexDomain_wholeSpaceCube d v).isBoundedDomain.isFiniteMeasure_restrict_volume

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The exhaustion-level solutions -/

/-- The exact `H¹` representative of the Dirichlet resolvent of the `m`-th exhaustion cube. -/
def cubeLevelSolution (m : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) : H1Function (wholeSpaceCube d m) :=
  Classical.choose (A.exists_cubeResolventH1 m mu hf hfD)

@[simp] theorem cubeLevelSolution_toFun (m : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    (A.cubeLevelSolution m mu hf hfD).toFun = A.analyticCubeResolvent mu f hf hfD m :=
  (Classical.choose_spec (A.exists_cubeResolventH1 m mu hf hfD)).1

theorem isScalarForcedWeakSolution_cubeLevelSolution (m : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    IsScalarForcedWeakSolution A.a (wholeSpaceCube d m) (A.cubeLevelResidual m mu hf hfD)
      (A.cubeLevelSolution m mu hf hfD) :=
  (Classical.choose_spec (A.exists_cubeResolventH1 m mu hf hfD)).2

/-! ## `L²` convergence of the values -/

/-- **The exhaustion resolvents converge to the whole-space resolvent in `L²` of every cube.**
The pointwise convergence is the exhaustion limit and the domination is the shift bound. -/
theorem tendsto_setIntegral_analyticCubeResolvent_sub_sq (v : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    Tendsto (fun n : ℕ ↦ ∫ x in wholeSpaceCube d v,
        (A.analyticCubeResolvent mu f hf hfD n x -
          A.analyticMinimalResolventReal mu f hf hfD x) ^ 2 ∂volume) atTop (𝓝 0) := by
  let := isFiniteMeasure_cube (d := d) v
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
  set B : ℝ := 2 * (D / (mu : ℝ)) with hB
  have hlimit : ∫ _x in wholeSpaceCube d v, (0 : ℝ) ∂volume = 0 := integral_zero _ _
  rw [← hlimit]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ B ^ 2) (fun n ↦ ?_)
    (integrable_const _) (fun n ↦ ?_) ?_
  · exact ((A.measurable_analyticCubeResolvent mu hf hfD n).sub
      (A.measurable_analyticMinimalResolventReal mu hf hfD)).pow_const 2 |>.aestronglyMeasurable
  · filter_upwards with x
    have h1 := A.abs_analyticCubeResolvent_le mu hf hD hfD n x
    have h2 := A.abs_analyticMinimalResolventReal_le mu hf hfD x
    have habs : |A.analyticCubeResolvent mu f hf hfD n x -
        A.analyticMinimalResolventReal mu f hf hfD x| ≤ B := by
      refine (abs_sub _ _).trans ?_
      rw [hB]
      linarith only [h1, h2]
    have hsq := pow_le_pow_left₀ (abs_nonneg (A.analyticCubeResolvent mu f hf hfD n x -
      A.analyticMinimalResolventReal mu f hf hfD x)) habs 2
    rw [sq_abs] at hsq
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq
  · filter_upwards with x
    have h := (A.tendsto_analyticCubeResolvent_real mu hf hfD x).sub
      (tendsto_const_nhds (x := A.analyticMinimalResolventReal mu f hf hfD x))
    rw [sub_self] at h
    have := h.pow 2
    rwa [show ((0 : ℝ) ^ 2) = 0 by norm_num] at this

/-! ## The Caccioppoli Cauchy estimate -/

/-- **The Caccioppoli Cauchy estimate.**  On the `v`-th exhaustion cube the gradients of the
exhaustion resolvents at two levels beyond `v` differ in `L²` by at most a fixed multiple of
their `L²` value difference on the next cube.  The constant depends only on the ellipticity
constants of the larger cube and on the cutoff between the two cubes. -/
theorem exists_cubeCauchyConstant (v : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k m : ℕ, v + 1 ≤ k → v + 1 ≤ m →
      ∫ x in wholeSpaceCube d v,
          vecNormSq ((A.cubeLevelSolution k mu hf hfD).grad x -
            (A.cubeLevelSolution m mu hf hfD).grad x) ∂volume ≤
        C * ∫ x in wholeSpaceCube d (v + 1),
          (A.analyticCubeResolvent mu f hf hfD k x -
            A.analyticCubeResolvent mu f hf hfD m x) ^ 2 ∂volume := by
  obtain ⟨eta, heta, hetaCompact, hetaSupport, hetaOne, K, hK, hKbound⟩ :=
    exists_wholeSpaceCubeCutoff d v
  set V : Set (Vec d) := wholeSpaceCube d v with hV
  set W : Set (Vec d) := wholeSpaceCube d (v + 1) with hW
  have hVW : V ⊆ W := wholeSpaceCube_subset_succ d v
  have hWdom := isOpenBoundedConvexDomain_wholeSpaceCube d (v + 1)
  have hEll := A.cubeEllipticity (v + 1)
  set Lam : ℝ := A.cubeEllipticityUpper (v + 1) with hLam
  have hnu : (0 : ℝ) < A.nu := A.hnu
  refine ⟨2 / A.nu * ((2 * Lam ^ 2 / A.nu) * K), by positivity, ?_⟩
  intro k m hk hm
  -- the two restricted level solutions and their difference
  set zk : H1Function W :=
    (A.cubeLevelSolution k mu hf hfD).restrict hWdom.isOpen (wholeSpaceCube_mono hk) with hzk
  set zm : H1Function W :=
    (A.cubeLevelSolution m mu hf hfD).restrict hWdom.isOpen (wholeSpaceCube_mono hm) with hzm
  set Z : H1Function W := zk - zm with hZ
  have hZfun : Z.toFun = fun x ↦ A.analyticCubeResolvent mu f hf hfD k x -
      A.analyticCubeResolvent mu f hf hfD m x := by
    rw [hZ, H1Function.sub_toFun]
    funext x
    change (A.cubeLevelSolution k mu hf hfD).toFun x - (A.cubeLevelSolution m mu hf hfD).toFun x = _
    rw [A.cubeLevelSolution_toFun, A.cubeLevelSolution_toFun]
  have hZgrad : Z.grad = fun x ↦ (A.cubeLevelSolution k mu hf hfD).grad x -
      (A.cubeLevelSolution m mu hf hfD).grad x := by
    rw [hZ, H1Function.sub_grad]
    funext x
    change (A.cubeLevelSolution k mu hf hfD).grad x -
      (A.cubeLevelSolution m mu hf hfD).grad x = _
    rfl
  -- the homogeneous shifted equation solved by the difference
  have hsolk := (A.isScalarForcedWeakSolution_cubeLevelSolution k mu hf hfD).restrictSubset
    hWdom.isOpen (wholeSpaceCube_mono hk)
  have hsolm := (A.isScalarForcedWeakSolution_cubeLevelSolution m mu hf hfD).restrictSubset
    hWdom.isOpen (wholeSpaceCube_mono hm)
  have hZsol : IsScalarForcedWeakSolution A.a W (fun x ↦ -(mu : ℝ) * Z.toFun x) Z := by
    have hsub := hsolk.sub hEll hsolm
    refine hsub.congr_datum ?_
    filter_upwards with x
    rw [hZfun]
    simp only [cubeLevelResidual]
    ring
  -- the Caccioppoli estimate at the cutoff
  have hcac := cutoff_energy_absorbed_plain hZsol hWdom hEll eta heta hetaCompact
    (hetaSupport.trans (subset_refl _))
  -- the forcing pairing is nonpositive
  have hforcing : (∫ x in W, (-(mu : ℝ) * Z.toFun x) * (eta x ^ 2 * Z.toFun x) ∂volume) ≤ 0 := by
    refine integral_nonpos ?_
    intro x
    have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
    have hsq : 0 ≤ eta x ^ 2 * Z.toFun x ^ 2 := by positivity
    change (-(mu : ℝ) * Z.toFun x) * (eta x ^ 2 * Z.toFun x) ≤ 0
    nlinarith only [hsq, hmu]
  -- the cutoff-gradient term
  have hZsqInt : Integrable (fun x ↦ Z.toFun x ^ 2) (volumeMeasureOn W) := by
    refine (Z.memL2.integrable_mul Z.memL2).congr ?_
    filter_upwards with x
    simp only [Pi.mul_apply, pow_two]
  have hcut : (∫ x in W, Z.toFun x ^ 2 *
      vecNormSq (fun i ↦ (fderiv ℝ eta x) (basisVec i)) ∂volume) ≤
      K * ∫ x in W, Z.toFun x ^ 2 ∂volume := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hZsqInt.const_mul K) ?_
    · filter_upwards with x
      have := vecNormSq_nonneg (fun i ↦ (fderiv ℝ eta x) (basisVec i))
      positivity
    · filter_upwards with x
      have h := mul_le_mul_of_nonneg_left (hKbound x) (sq_nonneg (Z.toFun x))
      rwa [mul_comm K (Z.toFun x ^ 2)]
  -- the inner energy is below the cutoff energy
  have hinnerInt : IntegrableOn (fun x ↦ eta x ^ 2 * vecNormSq (Z.grad x)) W volume := by
    have hsq : ContDiff ℝ (⊤ : ℕ∞) fun x ↦ eta x ^ 2 := by
      simpa only [pow_two] using heta.mul heta
    have hsqCompact : HasCompactSupport fun x ↦ eta x ^ 2 := by
      simpa only [pow_two] using! hetaCompact.mul_left (f := eta)
    exact integrable_mul_vecNormSq_grad Z hsq hsqCompact
  have hinner : (∫ x in V, vecNormSq (Z.grad x) ∂volume) ≤
      ∫ x in W, eta x ^ 2 * vecNormSq (Z.grad x) ∂volume := by
    have hcongr : ∫ x in V, vecNormSq (Z.grad x) ∂volume =
        ∫ x in V, eta x ^ 2 * vecNormSq (Z.grad x) ∂volume := by
      refine setIntegral_congr_fun
        (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen.measurableSet ?_
      intro x hx
      change vecNormSq (Z.grad x) = eta x ^ 2 * vecNormSq (Z.grad x)
      rw [hetaOne x hx, one_pow, one_mul]
    rw [hcongr]
    refine setIntegral_mono_set hinnerInt ?_ hVW.eventuallyLE
    filter_upwards with x
    have := vecNormSq_nonneg (Z.grad x)
    positivity
  -- assembling
  have hfinal : A.nu / 2 * ∫ x in V, vecNormSq (Z.grad x) ∂volume ≤
      (2 * Lam ^ 2 / A.nu) * (K * ∫ x in W, Z.toFun x ^ 2 ∂volume) := by
    have h1 : A.nu / 2 * ∫ x in V, vecNormSq (Z.grad x) ∂volume ≤
        A.nu / 2 * ∫ x in W, eta x ^ 2 * vecNormSq (Z.grad x) ∂volume :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    have h2 : (2 * Lam ^ 2 / A.nu) * (∫ x in W, Z.toFun x ^ 2 *
        vecNormSq (fun i ↦ (fderiv ℝ eta x) (basisVec i)) ∂volume) ≤
        (2 * Lam ^ 2 / A.nu) * (K * ∫ x in W, Z.toFun x ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left hcut (by positivity)
    linarith only [h1, h2, hcac, hforcing]
  have hZsqEq : (∫ x in W, Z.toFun x ^ 2 ∂volume) =
      ∫ x in W, (A.analyticCubeResolvent mu f hf hfD k x -
        A.analyticCubeResolvent mu f hf hfD m x) ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hZfun]
  rw [hZgrad] at hfinal
  rw [hZsqEq] at hfinal
  have hnu2 : (0 : ℝ) < A.nu / 2 := by positivity
  calc ∫ x in V, vecNormSq ((A.cubeLevelSolution k mu hf hfD).grad x -
        (A.cubeLevelSolution m mu hf hfD).grad x) ∂volume
      = (2 / A.nu) * (A.nu / 2 * ∫ x in V,
          vecNormSq ((A.cubeLevelSolution k mu hf hfD).grad x -
            (A.cubeLevelSolution m mu hf hfD).grad x) ∂volume) := by
        field_simp
    _ ≤ (2 / A.nu) * ((2 * Lam ^ 2 / A.nu) * (K * ∫ x in W,
          (A.analyticCubeResolvent mu f hf hfD k x -
            A.analyticCubeResolvent mu f hf hfD m x) ^ 2 ∂volume)) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = 2 / A.nu * ((2 * Lam ^ 2 / A.nu) * K) * ∫ x in W,
          (A.analyticCubeResolvent mu f hf hfD k x -
            A.analyticCubeResolvent mu f hf hfD m x) ^ 2 ∂volume := by ring

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
