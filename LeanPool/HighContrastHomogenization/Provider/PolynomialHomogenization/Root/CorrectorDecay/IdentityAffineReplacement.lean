/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.RoundedAffineReplacement
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityHarmonicComparison

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityAffineReplacement

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

private theorem affineBoundary_isIdentityForcedEquation
    {d : ℕ} (m : ℤ) (e : Vec d) :
    Book.Ch03.IsConstantCoeffForcedEquation (originCube d m)
      (identityConstantCoeffMatrix d) (finiteAffineBoundaryH1 m e)
      (0 : Vec d → Vec d) := by
  intro phi
  have hzero := integral_vecDot_const_zeroTraceGrad_eq_zero phi e
  simpa only [identityConstantCoeffMatrix_matrix,
    HCPolySupport.matVecMul_one, finiteAffineBoundaryH1_grad,
    Pi.zero_apply, vecDot_zero_left, integral_zero] using hzero

/-- The exact identity-harmonic replacement of a finite affine solution has
the prescribed affine gradient. -/
theorem identityHarmonicReplacementDatum_affine_grad_ae
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (e : Vec d) :
    let u := (finiteAffineSolution a m e).toH1
    let hu := isWeakSolutionOn_finiteAffineSolution a m e
    let W := identityHarmonicReplacementDatum a m u hu
    W.v.grad =ᵐ[volumeMeasureOn (cubeSet (originCube d m))]
      fun _ ↦ e := by
  let Q := originCube d m
  let U : Set (Vec d) := cubeSet Q
  let u := (finiteAffineSolution a m e).toH1
  let hu := isWeakSolutionOn_finiteAffineSolution a m e
  let W := identityHarmonicReplacementDatum a m u hu
  let a₀ := identityConstantCoeffMatrix d
  have hEll₀ : IsEllipticFieldOn a₀.lam a₀.Lam U
      (constantCoeffField a₀.matrix) :=
    Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField
      a₀ (measurableSet_cubeSet Q)
  have hWopen : IsH1DirichletRhsWeakSolutionOn
      (constantCoeffField a₀.matrix) (openCubeSet Q) W.v
        (0 : Vec d → Vec d) :=
    Book.Ch03.isH1DirichletRhsWeakSolutionOn_constantCoeff_of_isConstantCoeffForcedEquation
      W.vWeakSolution
  have hWweak : IsH1DirichletRhsWeakSolutionOn
      (constantCoeffField a₀.matrix) U W.v.toCubeSet
        (0 : Vec d → Vec d) :=
    Book.Ch03.isH1DirichletRhsWeakSolutionOn_cubeSet_of_openCubeSet hWopen
  have hBopen : IsH1DirichletRhsWeakSolutionOn
      (constantCoeffField a₀.matrix) (openCubeSet Q)
        (finiteAffineBoundaryH1 m e) (0 : Vec d → Vec d) :=
    Book.Ch03.isH1DirichletRhsWeakSolutionOn_constantCoeff_of_isConstantCoeffForcedEquation
      (affineBoundary_isIdentityForcedEquation m e)
  have hBweak : IsH1DirichletRhsWeakSolutionOn
      (constantCoeffField a₀.matrix) U (finiteAffineBoundaryH1 m e).toCubeSet
        (0 : Vec d → Vec d) :=
    Book.Ch03.isH1DirichletRhsWeakSolutionOn_cubeSet_of_openCubeSet hBopen
  have hWsol : IsSolenoidalOn U (fun x ↦ W.v.grad x) := by
    have h := hWweak.residual_solenoidal hEll₀ MeasureTheory.MemLp.zero
    simp only [U, Q, a₀, identityConstantCoeffMatrix_matrix,
      constantCoeffField,
      HCPolySupport.matVecMul_one, Pi.zero_apply, sub_zero] at h
    rwa [show W.v.toCubeSet.grad = W.v.grad from H1Function.grad_toCubeSet W.v] at h
  have hBsol : IsSolenoidalOn U (fun _x ↦ e) := by
    have h := hBweak.residual_solenoidal hEll₀ MeasureTheory.MemLp.zero
    simp only [U, Q, a₀, identityConstantCoeffMatrix_matrix,
      constantCoeffField, HCPolySupport.matVecMul_one,
      Pi.zero_apply, sub_zero] at h
    rwa [show (finiteAffineBoundaryH1 m e).toCubeSet.grad = fun _ ↦ e from
        (H1Function.grad_toCubeSet (finiteAffineBoundaryH1 m e)).trans
          (finiteAffineBoundaryH1_grad m e)] at h
  have hWmem : MemVectorL2 U (fun x ↦ W.v.grad x) := by
    have hg : W.v.toCubeSet.grad = W.v.grad := H1Function.grad_toCubeSet W.v
    simpa only [U, Q, hg] using W.v.toCubeSet.grad_memVectorL2
  have hBmem : MemVectorL2 U (fun _x ↦ e) := memVectorL2_const e
  have hsol : IsSolenoidalOn U (fun x ↦ W.v.grad x - e) := by
    have hsum := isSolenoidalOn_add_of_memVectorL2 hWmem
      (hBmem.const_smul (-1 : ℝ)) hWsol
      (isSolenoidalOn_smul hBsol (-1 : ℝ))
    have heq :
        (fun x ↦ W.v.grad x) + (-1 : ℝ) • (fun _x ↦ e) =
          fun x ↦ W.v.grad x - e := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply]
      module
    rw [← heq]
    exact hsum
  have hWpot : IsPotentialZeroTraceOn U
      (fun x ↦ u.grad x - W.v.grad x) := by
    have hpair := W.isHomogenizationComparisonPairOn_publicCoeffField_cubeSet
    have hWu : W.u = u := identityHarmonicReplacementDatum_u a m u hu
    rw [hWu] at hpair
    simpa only [Book.Ch03.publicH1ToCubeSet_grad] using hpair.2
  have hBpot : IsPotentialZeroTraceOn U (fun x ↦ u.grad x - e) := by
    exact isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet
      (by simpa only [u, Q, Book.Ch02.cubeDomain_coe] using
        (finiteAffineSolution_isAffineDirichletSolution a m e).2)
  have hpot : IsPotentialZeroTraceOn U (fun x ↦ W.v.grad x - e) := by
    have hsum := isPotentialZeroTraceOn_add hBpot
      (isPotentialZeroTraceOn_smul hWpot (-1 : ℝ))
    have heq :
        (fun x ↦ u.grad x - e) +
            (-1 : ℝ) • (fun x ↦ u.grad x - W.v.grad x) =
          fun x ↦ W.v.grad x - e := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply]
      module
    rw [← heq]
    exact hsum
  rcases hpot with ⟨z, hz⟩
  have hzweak : IsZeroTraceDirichletRhsWeakSolution
      (constantCoeffField a₀.matrix) U z (0 : Vec d → Vec d) := by
    intro phi
    have hzero := hsol phi
    simpa only [hz, a₀, identityConstantCoeffMatrix_matrix,
      constantCoeffField, HCPolySupport.matVecMul_one,
      Pi.zero_apply, vecDot_zero_left, integral_zero] using hzero
  have hzeroWeak : IsZeroTraceDirichletRhsWeakSolution
      (constantCoeffField a₀.matrix) U (0 : H10Function U)
        (0 : Vec d → Vec d) := by
    intro phi
    change
      (∫ x in U, vecDot (matVecMul (constantCoeffField a₀.matrix x)
        (0 : Vec d)) (phi.toH1Function.grad x) ∂volume) =
      ∫ x in U, vecDot (0 : Vec d) (phi.toH1Function.grad x) ∂volume
    simp only [matVecMul_zero, vecDot_zero_left, integral_zero]
  have hgradL2 :=
    IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (by
        refine ⟨cubeCenter Q, openCubeSet_subset_cubeSet Q ?_⟩
        rw [← ball_cubeCenter_eq_openCubeSet]
        simpa [Metric.mem_ball] using cubeRadius_pos Q)
      hzweak hzeroWeak hEll₀
  have hzzero : z.toH1Function.grad =ᵐ[volumeMeasureOn U]
      (0 : Vec d → Vec d) := by
    filter_upwards
        [H1Function.coeFn_gradToVectorL2 z.toH1Function,
          H1Function.coeFn_gradToVectorL2
            (0 : H10Function U).toH1Function]
      with x hx h0x
    rw [← hx, hgradL2, h0x]
    rfl
  have hdiff : (fun x ↦ W.v.grad x - e) =ᵐ[volumeMeasureOn U]
      (0 : Vec d → Vec d) := by
    simpa only [← hz] using hzzero
  filter_upwards [hdiff] with x hx
  exact sub_eq_zero.mp hx

/-- The exact identity-harmonic replacement also has the prescribed affine
value, not merely its gradient.  The shared Dirichlet trace puts the
difference in `H¹₀`, and the zero-gradient conclusion above then removes the
otherwise possible additive constant. -/
theorem identityHarmonicReplacementDatum_affine_toFun_ae
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (e : Vec d) :
    let u := (finiteAffineSolution a m e).toH1
    let hu := isWeakSolutionOn_finiteAffineSolution a m e
    let W := identityHarmonicReplacementDatum a m u hu
    W.v.toFun =ᵐ[volumeMeasureOn (cubeSet (originCube d m))]
      (finiteAffineBoundaryH1 m e).toFun := by
  let Q := originCube d m
  let U : Set (Vec d) := Book.Ch02.cubeDomain Q
  let u := (finiteAffineSolution a m e).toH1
  let hu := isWeakSolutionOn_finiteAffineSolution a m e
  let W := identityHarmonicReplacementDatum a m u hu
  have hWu : W.u = u := identityHarmonicReplacementDatum_u a m u hu
  obtain ⟨wW, hwW⟩ := W.zeroTraceDifference
  rw [hWu] at hwW
  obtain ⟨wB, hwB⟩ := finiteAffineSolution_zeroTraceDifference a m e
  let z := wB - wW
  have hwWgrad : wW.toH1Function.grad
      =ᵐ[volumeMeasureOn U] fun x ↦ u.grad x - W.v.grad x := by
    have hraw := Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (Book.Ch02.cubeDomain Q).isOpen
      (u := wW.toH1Function) (v := u - W.v) (by
        simpa only [H1Function.sub_toFun] using hwW)
    have hraw' : wW.toH1Function.grad =ᵐ[
        volume.restrict (Book.Ch02.cubeDomain Q : Set (Vec d))]
          fun x ↦ u.grad x - W.v.grad x := by
      simpa only [H1Function.sub_grad] using hraw
    simpa only [U, Q, volumeMeasureOn, Book.Ch02.cubeDomain_coe,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hraw'
  have hwBgrad : wB.toH1Function.grad
      =ᵐ[volumeMeasureOn U] fun x ↦ u.grad x - e := by
    have hraw := Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (Book.Ch02.cubeDomain Q).isOpen
      (u := wB.toH1Function) (v := u - finiteAffineBoundaryH1 m e) (by
        simpa only [H1Function.sub_toFun] using hwB)
    have hraw' : wB.toH1Function.grad =ᵐ[
        volume.restrict (Book.Ch02.cubeDomain Q : Set (Vec d))]
          fun x ↦ u.grad x - e := by
      simpa only [H1Function.sub_grad, finiteAffineBoundaryH1_grad] using hraw
    simpa only [U, Q, volumeMeasureOn, Book.Ch02.cubeDomain_coe,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hraw'
  have hWgrad : W.v.grad
      =ᵐ[volumeMeasureOn U] fun _ ↦ e := by
    simpa only [U, Q, u, hu, W, volumeMeasureOn,
      Book.Ch02.cubeDomain_coe,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      identityHarmonicReplacementDatum_affine_grad_ae a m e
  have hzgrad : z.toH1Function.grad
      =ᵐ[volumeMeasureOn U] (0 : Vec d → Vec d) := by
    change (wB.toH1Function - wW.toH1Function).grad
      =ᵐ[volumeMeasureOn U] (0 : Vec d → Vec d)
    rw [H1Function.sub_grad]
    filter_upwards [hwBgrad, hwWgrad, hWgrad] with x hBx hWx hgradx
    change wB.toH1Function.grad x - wW.toH1Function.grad x = 0
    rw [hBx, hWx, hgradx]
    module
  have hzgradL2 : z.toH1Function.gradToVectorL2 = 0 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [z.toH1Function.coeFn_gradToVectorL2,
        MeasureTheory.Lp.coeFn_zero
          (E := Vec d) (p := (2 : ENNReal)) (μ := volumeMeasureOn U),
        hzgrad] with x hx hzero hxgrad
    rw [hx, hzero, hxgrad]
  have hP := H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
    (by simpa only [U, Q, Book.Ch02.cubeDomain_coe] using
      isOpenBoundedConvexDomain_openCubeSet Q)
  have hzvalueL2 : z.toH1Function.toScalarL2 = 0 :=
    H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      hP z hzgradL2
  have hzvalue : z.toH1Function.toFun
      =ᵐ[volumeMeasureOn U] (0 : Vec d → ℝ) := by
    filter_upwards [z.toH1Function.coeFn_toScalarL2,
        MeasureTheory.Lp.coeFn_zero
          (E := ℝ) (p := (2 : ENNReal)) (μ := volumeMeasureOn U)]
      with x hx hzero
    rw [← hx, hzvalueL2, hzero]
  have hfinal : W.v.toFun
      =ᵐ[volumeMeasureOn U] (finiteAffineBoundaryH1 m e).toFun := by
    filter_upwards [hzvalue, hwB, hwW] with x hz hB hW
    have hzfun : wB.toH1Function.toFun x - wW.toH1Function.toFun x = 0 := by
      have hz' := hz
      change (wB.toH1Function - wW.toH1Function).toFun x = 0 at hz'
      simpa only [H1Function.sub_toFun, Pi.sub_apply] using hz'
    rw [hB, hW] at hzfun
    linarith only [hzfun]
  simpa only [U, Q, volumeMeasureOn, Book.Ch02.cubeDomain_coe,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hfinal

end

end HighContrast
end HCPolySupport
