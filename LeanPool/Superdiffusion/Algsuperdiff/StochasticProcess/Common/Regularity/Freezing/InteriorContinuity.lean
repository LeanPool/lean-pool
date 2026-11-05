/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.ShiftedResidualBound
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.LocalContrast
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.LocalRepresentativeGlue
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ScalarForcing

/-!
# InteriorContinuity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Interior continuity by freezing continuous skew coefficients

At each interior point we subtract the constant skew part at that point,
normalize by the positive scalar symmetric part, and apply the scale-free
small-contrast Schauder estimate on a sufficiently small Euclidean ball.
The resulting local representatives are glued by shrinking-ball averages.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open DivergenceFormProcess.Form

noncomputable section

variable {d : ℕ}

/-- Scaling a zeroth-order weak equation by a constant scales its datum. -/
theorem isMatrixDivFormWeakSolutionZerothOrderOn_const_smul_zero
    {W : Set (Vec d)} {c : ℝ} {a : CoeffField d}
    {u : H1Function W} {g : Vec d → ℝ}
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a W u g 0) :
    IsMatrixDivFormWeakSolutionZerothOrderOn
      (fun x ↦ c • a x) W u (fun x ↦ c * g x) 0 := by
  intro phi
  have h := hu phi
  have hleft :
      (∫ x in W, vecDot (matVecMul (c • a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume) =
        c * ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp [smul_matVecMul, vecDot_smul_left]
  have hright :
      (∫ x in W, (c * g x) * phi.toH1Function.toFun x ∂volume) =
        c * ∫ x in W, g x * phi.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hleft, hright]
  simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] at h ⊢
  exact congrArg (c * ·) h

private theorem isMatrixDivFormWeakSolutionZerothOrderOn_of_scalarForced
    {W : Set (Vec d)} {a : CoeffField d} {u : H1Function W}
    {g : Vec d → ℝ} (hu : IsScalarForcedWeakSolution a W g u) :
    IsMatrixDivFormWeakSolutionZerothOrderOn a W u g 0 := by
  intro phi
  simpa only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero]
    using hu.2 phi

/-- A constant multiple of an essentially bounded datum is essentially
bounded. -/
theorem memScalarLInfOn_const_mul
    {W : Set (Vec d)} {c : ℝ} {g : Vec d → ℝ}
    (hg : MemScalarLInfOn W g) :
    MemScalarLInfOn W (fun x ↦ c * g x) := by
  have h := hg.const_smul c
  simpa only [Pi.smul_apply, smul_eq_mul] using! h

/-- A scalar-forced weak solution with bounded forcing has a `C^{0,1/2}`
representative on a ball about each interior point. The coefficient may have
continuous skew part of arbitrary size. -/
theorem exists_local_holder_representative_of_weakSolution_continuousCoeff
    [NeZero d] (hd : 2 ≤ d) {U : Set (Vec d)} (hU : IsOpen U)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    {g : Vec d → ℝ} (hg : MemScalarLInfOn U g)
    {u : H1Function U} (hu : IsScalarForcedWeakSolution a U g u) :
    ∀ z ∈ U, ∃ r > 0, euclideanBall z r ⊆ U ∧
      ∃ v : Vec d → ℝ, ContinuousOn v (euclideanBall z r) ∧
        v =ᵐ[volume.restrict (euclideanBall z r)] u.toFun ∧
        ∃ C : ℝ, EuclideanHolderBoundOn (euclideanBall z r) (1 / 2 : ℝ) C v := by
  intro z hz
  let delta : ℝ := smallContrastThreshold d (1 / 2 : ℝ)
  have hdelta : 0 < delta := by
    unfold delta smallContrastThreshold
    positivity
  obtain ⟨R, hR, hRU, hsmall, hEllFrozen⟩ :=
    exists_ball_coefficientIdentityDistanceLE_normalizedFrozenCoeff
      hU hnu hsymm hcont hz hdelta
  let B : Set (Vec d) := euclideanBall z R
  let uB : H1Function B := u.restrict (isOpen_euclideanBall z R) hRU
  have hbase : IsMatrixDivFormWeakSolutionZerothOrderOn a B uB g 0 :=
    isMatrixDivFormWeakSolutionZerothOrderOn_restrict hU
      (isOpen_euclideanBall z R) hRU
      (isMatrixDivFormWeakSolutionZerothOrderOn_of_scalarForced hu)
  have hk : matTranspose (a z - nu • (1 : Mat d)) =
      -(a z - nu • (1 : Mat d)) :=
    sub_scalar_one_isSkew_of_symmPart_eq (hsymm z)
  have hfrozen : IsMatrixDivFormWeakSolutionZerothOrderOn
      (fun x ↦ a x - (a z - nu • (1 : Mat d))) B uB g 0 :=
    (isMatrixDivFormWeakSolutionZerothOrderOn_sub_skew_const_iff hk).2 hbase
  have hnormalized : IsMatrixDivFormWeakSolutionZerothOrderOn
      (normalizedFrozenCoeff nu a z) B uB (fun x ↦ nu⁻¹ * g x) 0 := by
    exact isMatrixDivFormWeakSolutionZerothOrderOn_const_smul_zero hfrozen
  have hgB : MemScalarLInfOn B (fun x ↦ nu⁻¹ * g x) :=
    memScalarLInfOn_const_mul
      (hg.mono_measure (Measure.restrict_mono hRU le_rfl))
  classical
  let aLocal : CoeffField d := fun x i j ↦
    if x ∈ B then normalizedFrozenCoeff nu a z x i j else 0
  have hmeas : Measurable aLocal := by
    simpa only [aLocal, B] using! hEllFrozen.1
  have hsmallLocal : CoefficientIdentityDistanceLE B aLocal delta := by
    filter_upwards [hsmall, ae_restrict_mem (isOpen_euclideanBall z R).measurableSet]
      with x hx hxb
    simpa only [aLocal, hxb, ite_true] using hx
  have hnormalizedLocal : IsMatrixDivFormWeakSolutionZerothOrderOn
      aLocal B uB (fun x ↦ nu⁻¹ * g x) 0 := by
    intro phi
    have h := hnormalized phi
    have hlhs :
        (∫ x in B, vecDot (matVecMul (aLocal x) (uB.grad x))
            (phi.toH1Function.grad x) ∂volume) =
          ∫ x in B, vecDot
            (matVecMul (normalizedFrozenCoeff nu a z x) (uB.grad x))
            (phi.toH1Function.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (isOpen_euclideanBall z R).measurableSet]
        with x hx
      simp only [aLocal, hx, ite_true]
    rw [hlhs]
    exact h
  obtain ⟨v, hvcont, hvae, hvholder⟩ :=
    schauder_holder_euclideanBall_zerothOrder z hR hd
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1)
      (smallContrastThreshold_nonneg d (by norm_num : (1 / 2 : ℝ) ≤ 1))
      le_rfl hmeas hsmallLocal hnormalizedLocal hgB
  refine ⟨R / 2, half_pos hR, ?_, v, ?_, ?_, ?_⟩
  · exact (euclideanBall_subset_euclideanBall
      (by positivity : 0 ≤ R / 2) (by linarith only [hR])).trans hRU
  · exact hvcont
  · exact ae_restrict_of_ae_restrict_of_subset
      (euclideanBall_subset_euclideanBall
        (by positivity : 0 ≤ R / 2) (by linarith only [hR])) hvae
  · exact ⟨_, hvholder⟩

/-- Interior continuity and local `C^{0,1/2}` regularity for scalar-forced
weak solutions with bounded forcing and continuous coefficients of arbitrary
skew size. -/
theorem continuousOn_of_weakSolution_continuousCoeff
    [NeZero d] (hd : 2 ≤ d) {U : Set (Vec d)} (hU : IsOpen U)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    {g : Vec d → ℝ} (hg : MemScalarLInfOn U g)
    {u : H1Function U} (hu : IsScalarForcedWeakSolution a U g u) :
    ∃ v : Vec d → ℝ, ContinuousOn v U ∧
      v =ᵐ[volume.restrict U] u.toFun ∧
      ∀ z ∈ U, ∃ r > 0, euclideanBall z r ⊆ U ∧
        ∃ C : ℝ, EuclideanHolderBoundOn (euclideanBall z r) (1 / 2 : ℝ) C v := by
  have hlocal := exists_local_holder_representative_of_weakSolution_continuousCoeff
    hd hU hnu hsymm hcont hg hu
  have hlocalCont : ∀ z ∈ U, ∃ r > 0, euclideanBall z r ⊆ U ∧
      ∃ w : Vec d → ℝ, ContinuousOn w (euclideanBall z r) ∧
        w =ᵐ[volume.restrict (euclideanBall z r)] u.toFun := by
    intro z hz
    obtain ⟨r, hr, hrU, w, hwcont, hwae, -⟩ := hlocal z hz
    exact ⟨r, hr, hrU, w, hwcont, hwae⟩
  obtain ⟨v, hvcont, hvae⟩ :=
    exists_continuousOn_representative_of_local hU u.toFun hlocalCont
  refine ⟨v, hvcont, hvae, ?_⟩
  intro z hz
  obtain ⟨r, hr, hrU, w, hwcont, hwae, C, hwC⟩ := hlocal z hz
  have hvaeB : v =ᵐ[volume.restrict (euclideanBall z r)] w := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hrU hvae, hwae]
      with x hvx hwx
    exact hvx.trans hwx.symm
  have heq : Set.EqOn v w (euclideanBall z r) :=
    eqOn_of_continuousOn_of_ae_eq (isOpen_euclideanBall z r)
      (hvcont.mono hrU) hwcont hvaeB
  refine ⟨r, hr, hrU, C, ?_⟩
  intro x hx y hy
  rw [heq hx, heq hy]
  exact hwC x hx y hy

/-- A bounded shifted resolvent for the same continuous coefficient has a
continuous, locally `C^{0,1/2}` representative. The bounded residual
`f - mu*u` supplies the zeroth-order datum. -/
theorem continuousOn_alphaShiftedResolvent_continuousCoeff
    [NeZero d] (hd : 2 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (a : CoeffField d)
    {nu : ℝ} (hnu : 0 < nu)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    {mu lam Lam M : ℝ} (hmu : 0 < mu) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (hM : 0 ≤ M) (hfM : ∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ M) :
    ∃ v : Vec d → ℝ, ContinuousOn v U ∧
      v =ᵐ[volumeMeasureOn U] alphaShiftedResolvent a hmu hlam hEll f ∧
      ∀ z ∈ U, ∃ r > 0, euclideanBall z r ⊆ U ∧
        ∃ C : ℝ, EuclideanHolderBoundOn (euclideanBall z r) (1 / 2 : ℝ) C v := by
  obtain ⟨u, hueq, -, hscalar, hresidual⟩ :=
    exists_h10Function_scalarForced_residual_bound hU a hmu hlam hEll f hM hfM
  let g : Vec d → ℝ := fun x ↦ f x - mu * u.toH1Function.toFun x
  have hg : MemScalarLInfOn U g := by
    apply memLp_top_of_bound hscalar.1.aestronglyMeasurable (2 * M)
    filter_upwards [hresidual] with x hx
    simpa only [g, Real.norm_eq_abs] using hx
  obtain ⟨v, hvcont, hvae, hvholder⟩ :=
    continuousOn_of_weakSolution_continuousCoeff hd hU.isOpen hnu hsymm hcont
      hg hscalar
  refine ⟨v, hvcont, ?_, hvholder⟩
  filter_upwards [hvae, u.toH1Function.coeFn_toScalarL2] with x hv hu
  have hvalue := congrArg (fun F : ScalarL2 U ↦ F x) hueq
  exact hv.trans (hu.symm.trans hvalue)

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
