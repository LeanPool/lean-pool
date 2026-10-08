/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.H10AffinePullbackAssembly
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.DomainDualityFromHodge
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakSolution
public import LeanPool.HighContrastHomogenization.Analytic.AffineNormalization
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewSolenoidal
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Duality.GaugeWitnessPremiseTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Transporting the two PDE premises to the gauge image

The Seam-2 consumer states the duality clause at the gauge image, but the two
PDE hypotheses of the printed lemma — `u − v ∈ H₀^{1−s}(U)` and
`∇·(a∇u − a₁∇v) = 0` — are supplied one level up, at the **physical** domain
(`ScheduledLocalizationRowSupply`).  This file carries both across the gauge.

* the zero-trace potential half moves covariantly, by the `H¹₀` affine
  pullback;
* the solenoidal half moves through the affine transport of the weak equation,
  after the constant skew part of the comparison matrix is annihilated: the
  gauge image of that skew part is again a constant skew matrix, and a constant
  skew matrix applied to a weak gradient is solenoidal.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Matrix preliminaries -/

/-- The matrix square root of a positive definite matrix is symmetric. -/
theorem matTranspose_matSqrt {A : Mat d} (hA : A.PosDef) :
    matTranspose (matSqrt A) = matSqrt A := by
  change Matrix.transpose (matSqrt A) = matSqrt A
  rw [← conjTranspose_eq_transpose']
  exact (matSqrt_spec hA.posSemidef).1.isHermitian

/-- The inverse of a symmetric invertible matrix is symmetric. -/
theorem matTranspose_inv_of_symm {L : Mat d} (hLsymm : matTranspose L = L) :
    matTranspose L⁻¹ = L⁻¹ := by
  have h : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
    simpa [matTranspose] using Matrix.transpose_nonsing_inv (A := L)
  rw [h, hLsymm]

private theorem matTranspose_mul' (A B : Mat d) :
    matTranspose (A * B) = matTranspose B * matTranspose A :=
  Matrix.transpose_mul A B

/-- A symmetric conjugation of a skew matrix is skew. -/
theorem isSkewMat_conj {M K : Mat d} (hMsymm : matTranspose M = M)
    (hK : IsSkewMat K) : IsSkewMat (M * K * M) := by
  change matTranspose (M * K * M) = -(M * K * M)
  rw [matTranspose_mul', matTranspose_mul', hMsymm, hK]
  noncomm_ring

/-- The matrix decomposition into symmetric and skew parts. -/
theorem symmPart_add_skewPart' (A : Mat d) :
    A = symmPart A + skewPart A := by
  funext i j
  simp only [symmPart, skewPart, Matrix.add_apply]
  ring

/-- The gauge conjugation normalizes the symmetric part to the identity. -/
theorem gaugeConj_symmPart_eq_one {abar : Mat d}
    (hS : (symmPart abar).PosDef) :
    (matSqrt (symmPart abar))⁻¹ * symmPart abar *
        matTranspose (matSqrt (symmPart abar))⁻¹ = 1 := by
  have h := affineCoefficient_matSqrt_symmPart_eq_one hS (0 : Vec d)
  simpa only [affineCoefficient_apply] using h

/-- The affine coefficient transform is additive on differences. -/
theorem affineCoefficient_sub (L : Mat d) (hL : IsUnit L.det)
    (a b : CoeffField d) (y : Vec d) :
    affineCoefficient L hL (fun x => a x - b x) y =
      affineCoefficient L hL a y - affineCoefficient L hL b y := by
  simp only [affineCoefficient_apply]
  noncomm_ring

/-! ## Solenoidal algebra -/

/-- Solenoidal fields are closed under differences. -/
theorem isSolenoidalOn_sub {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hfL2 : MemVectorL2 U f) (hgL2 : MemVectorL2 U g)
    (hf : IsSolenoidalOn U f) (hg : IsSolenoidalOn U g) :
    IsSolenoidalOn U (fun x => f x - g x) := by
  intro phi
  have hInt1 : IntegrableOn
      (fun x => vecDot (f x) (phi.toH1Function.grad x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 hfL2 phi.toH1Function.grad_memVectorL2
  have hInt2 : IntegrableOn
      (fun x => vecDot (g x) (phi.toH1Function.grad x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 hgL2 phi.toH1Function.grad_memVectorL2
  have hsplit : (fun x => vecDot (f x - g x) (phi.toH1Function.grad x)) =
      fun x => vecDot (f x) (phi.toH1Function.grad x) -
        vecDot (g x) (phi.toH1Function.grad x) := by
    funext x
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  rw [hsplit, integral_sub hInt1 hInt2, hf phi, hg phi, sub_zero]

/-- A compact-test weak equation upgrades to solenoidality of its flux once the
flux is square integrable. -/
theorem isSolenoidalOn_of_isWeakSolutionOn {U : Set (Vec d)}
    (hU : IsOpen U)
    (b : CoeffField d) {F : Vec d → Vec d}
    (hbF : MemVectorL2 U (fun x => matVecMul (b x) (F x)))
    (hweak : IsWeakSolutionOn b U F) :
    IsSolenoidalOn U (fun x => matVecMul (b x) (F x)) := by
  apply IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hbF hU
  intro psi hpsiSmooth hpsiCompact hpsiSupport
  have hlocal : IsLocalTest U psi :=
    { contDiff := hpsiSmooth
      hasCompactSupport := hpsiCompact
      tsupport_subset := hpsiSupport }
  have hzero := (hweak psi hlocal).2
  calc
    ∫ x in U, vecDot (matVecMul (b x) (F x))
        (fun i => (fderiv ℝ psi x) (basisVec i)) ∂volume =
        ∫ x in U, vecDot (fun i => (fderiv ℝ psi x) (basisVec i))
          (matVecMul (b x) (F x)) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact vecDot_comm _ _
    _ = 0 := by
      simpa only [smoothGrad] using! hzero

/-! ## The two transports -/

/-- **The zero-trace potential premise, transported to the gauge image.**  The
printed hypothesis `u − v ∈ H₀^{1−s}(U)` is supplied at the physical domain; its
gauge image is the zero-trace potential the duality reduction consumes. -/
theorem isPotentialZeroTraceOn_gaugeGradSub {L : Mat d} (hL : IsUnit L.det)
    (hLsymm : matTranspose L = L) {U : Set (Vec d)} (hU : MeasurableSet U)
    (u h : H1Function U) (haff : MemAffineH10 U h u)
    (uHat hHat : H1Function (matImage L⁻¹ U))
    (huHat : uHat.grad = fun y => matVecMul L (u.grad (matVecMul L y)))
    (hhHat : hHat.grad = fun y => matVecMul L (h.grad (matVecMul L y))) :
    IsPotentialZeroTraceOn (matImage L⁻¹ U)
      (fun y => uHat.grad y - hHat.grad y) := by
  have hpot : IsPotentialZeroTraceOn U (fun x => u.grad x - h.grad x) :=
    isPotentialZeroTraceOn_gradSub_of_memAffineH10 u h haff
  have hpull := isPotentialZeroTraceOn_affinePullback hL hU hpot
  have hfun : (fun y => matVecMul (matTranspose L)
      (u.grad (matVecMul L y) - h.grad (matVecMul L y))) =
      fun y => uHat.grad y - hHat.grad y := by
    funext y
    have hu : uHat.grad y = matVecMul L (u.grad (matVecMul L y)) := by rw [huHat]
    have hh : hHat.grad y = matVecMul L (h.grad (matVecMul L y)) := by rw [hhHat]
    rw [hu, hh, hLsymm, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
      ← sub_eq_add_neg]
  rw [hfun] at hpull
  exact hpull

/-- **The solenoidal premise, transported to the gauge image.**  The printed
hypothesis `∇·(a∇u − a₁∇v) = 0` is supplied at the physical domain as two weak
equations; after the constant skew part is annihilated, its gauge image is the
solenoidality the duality reduction consumes. -/
theorem isSolenoidalOn_gaugeFluxDefect {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} (hU : MeasurableSet U)
    (hVopen : IsOpen (matImage (matSqrt (symmPart abar))⁻¹ U))
    (aPhysical : CoeffField d) (u h : H1Function U)
    (huPhys : IsWeakSolutionOn aPhysical U u.grad)
    (hhPhys : IsWeakSolutionOn (fun _ => abar) U h.grad)
    (uHat hHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ U))
    (huHat : uHat.grad = fun y => matVecMul (matSqrt (symmPart abar))
      (u.grad (matVecMul (matSqrt (symmPart abar)) y)))
    (hhHat : hHat.grad = fun y => matVecMul (matSqrt (symmPart abar))
      (h.grad (matVecMul (matSqrt (symmPart abar)) y)))
    {aHat : CoeffField d}
    (haHat : aHat = affineCoefficient (matSqrt (symmPart abar))
      (isUnit_det_matSqrt hS) (fun x => aPhysical x - skewPart abar))
    (hFdefect : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul (aHat y - 1) (uHat.grad y))) :
    IsSolenoidalOn (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul (aHat y) (uHat.grad y) - hHat.grad y) := by
  have hM : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hMsymm : matTranspose (matSqrt (symmPart abar)) = matSqrt (symmPart abar) :=
    matTranspose_matSqrt hS
  set Khat : Mat d := (matSqrt (symmPart abar))⁻¹ * skewPart abar *
    matTranspose (matSqrt (symmPart abar))⁻¹ with hKhat
  have hKskew : IsSkewMat Khat := by
    have hskew : IsSkewMat (skewPart abar) := by
      change matTranspose (skewPart abar) = -skewPart abar
      funext i j
      simp only [matTranspose, Matrix.transpose_apply, skewPart,
        Matrix.neg_apply]
      ring
    have hinv : matTranspose (matSqrt (symmPart abar))⁻¹ =
        (matSqrt (symmPart abar))⁻¹ := matTranspose_inv_of_symm hMsymm
    rw [hKhat, hinv]
    exact isSkewMat_conj hinv hskew
  -- the two pulled-back weak equations
  have hu' : IsWeakSolutionOn
      (affineCoefficient (matSqrt (symmPart abar)) hM aPhysical)
      (matImage (matSqrt (symmPart abar))⁻¹ U) uHat.grad := by
    have h0 := (isWeakSolutionOn_affinePullback_iff hM hU aPhysical u.grad).1
      huPhys
    rw [hMsymm] at h0
    rw [huHat]
    exact h0
  have hbarEq : affineCoefficient (matSqrt (symmPart abar)) hM
      (fun _ => abar) = fun _ : Vec d => (1 : Mat d) + Khat := by
    funext y
    rw [affineCoefficient_apply, hKhat]
    calc (matSqrt (symmPart abar))⁻¹ * abar *
        matTranspose (matSqrt (symmPart abar))⁻¹ =
        (matSqrt (symmPart abar))⁻¹ * (symmPart abar + skewPart abar) *
          matTranspose (matSqrt (symmPart abar))⁻¹ := by
          rw [← symmPart_add_skewPart']
      _ = (matSqrt (symmPart abar))⁻¹ * symmPart abar *
            matTranspose (matSqrt (symmPart abar))⁻¹ +
          (matSqrt (symmPart abar))⁻¹ * skewPart abar *
            matTranspose (matSqrt (symmPart abar))⁻¹ := by noncomm_ring
      _ = 1 + (matSqrt (symmPart abar))⁻¹ * skewPart abar *
            matTranspose (matSqrt (symmPart abar))⁻¹ := by
          rw [gaugeConj_symmPart_eq_one hS]
  have hh' : IsWeakSolutionOn (fun _ : Vec d => (1 : Mat d) + Khat)
      (matImage (matSqrt (symmPart abar))⁻¹ U) hHat.grad := by
    have h0 := (isWeakSolutionOn_affinePullback_iff hM hU (fun _ => abar)
      h.grad).1 hhPhys
    rw [hMsymm, hbarEq] at h0
    rw [hhHat]
    exact h0
  have haEq : ∀ y : Vec d,
      affineCoefficient (matSqrt (symmPart abar)) hM aPhysical y =
        aHat y + Khat := by
    intro y
    have hsub := affineCoefficient_sub (matSqrt (symmPart abar)) hM aPhysical
      (fun _ => skewPart abar) y
    have hKy : affineCoefficient (matSqrt (symmPart abar)) hM
        (fun _ => skewPart abar) y = Khat := by
      rw [affineCoefficient_apply, hKhat]
    rw [haHat, hsub, hKy]
    abel
  -- the four solenoidal pieces
  have huGradL2 : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      uHat.grad := uHat.grad_memVectorL2
  have hhGradL2 : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      hHat.grad := hHat.grad_memVectorL2
  have hKuL2 : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul Khat (uHat.grad y)) :=
    memVectorL2_constMatrix_mul Khat huGradL2
  have hKhL2 : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul Khat (hHat.grad y)) :=
    memVectorL2_constMatrix_mul Khat hhGradL2
  have hX1L2 : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul
        (affineCoefficient (matSqrt (symmPart abar)) hM aPhysical y)
        (uHat.grad y)) := by
    have hfun : (fun y => matVecMul
        (affineCoefficient (matSqrt (symmPart abar)) hM aPhysical y)
        (uHat.grad y)) =
        fun y => (matVecMul (aHat y - 1) (uHat.grad y) + uHat.grad y) +
          matVecMul Khat (uHat.grad y) := by
      funext y
      rw [haEq y, add_matVecMul, sub_matVecMul, matVecMul_one]
      abel
    rw [hfun]
    exact (hFdefect.add huGradL2).add hKuL2
  have hX2L2 : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul ((1 : Mat d) + Khat) (hHat.grad y)) :=
    memVectorL2_constMatrix_mul _ hhGradL2
  have hX1 : IsSolenoidalOn (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul
        (affineCoefficient (matSqrt (symmPart abar)) hM aPhysical y)
        (uHat.grad y)) :=
    isSolenoidalOn_of_isWeakSolutionOn hVopen _ hX1L2 hu'
  have hX2 : IsSolenoidalOn (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul ((1 : Mat d) + Khat) (hHat.grad y)) :=
    isSolenoidalOn_of_isWeakSolutionOn hVopen _ hX2L2 hh'
  have hX3 : IsSolenoidalOn (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul Khat (uHat.grad y)) :=
    Response.isSolenoidalOn_constSkew_mul_gradient hVopen Khat hKskew uHat
  have hX4 : IsSolenoidalOn (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul Khat (hHat.grad y)) :=
    Response.isSolenoidalOn_constSkew_mul_gradient hVopen Khat hKskew hHat
  have hA := isSolenoidalOn_sub hX1L2 hKuL2 hX1 hX3
  have hB := isSolenoidalOn_sub hX2L2 hKhL2 hX2 hX4
  have hAL2 : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul
          (affineCoefficient (matSqrt (symmPart abar)) hM aPhysical y)
          (uHat.grad y) - matVecMul Khat (uHat.grad y)) := hX1L2.sub hKuL2
  have hBL2 : MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y => matVecMul ((1 : Mat d) + Khat) (hHat.grad y) -
        matVecMul Khat (hHat.grad y)) := hX2L2.sub hKhL2
  have hAB := isSolenoidalOn_sub hAL2 hBL2 hA hB
  have hfinal : (fun y => (matVecMul
        (affineCoefficient (matSqrt (symmPart abar)) hM aPhysical y)
        (uHat.grad y) - matVecMul Khat (uHat.grad y)) -
      (matVecMul ((1 : Mat d) + Khat) (hHat.grad y) -
        matVecMul Khat (hHat.grad y))) =
      fun y => matVecMul (aHat y) (uHat.grad y) - hHat.grad y := by
    funext y
    rw [haEq y, add_matVecMul, add_matVecMul, matVecMul_one]
    abel
  rw [hfinal] at hAB
  exact hAB

end

end RowSupply
end HighContrast
end HCPolySupport
