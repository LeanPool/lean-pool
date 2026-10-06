/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineChapter3Comparison
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceConstantMatrix
public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Realization

/-!
# High-contrast homogenization: Provider.Regularity.RoundedHarmonicReplacement

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Harmonic replacement for the rounded constant reference

This module constructs the same-trace constant-coefficient comparison used in
the rounded regularity development.  The comparison coefficient is the genuinely
rounded near-identity matrix, not the scalar identity.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A smooth-test high-contrast weak solution supplies the Chapter 3
zero-force weak equation on the same cube. -/
theorem isForcedEquation_zero_of_isWeakSolutionOn
    {Q : TriadicCube d} {a : Book.Ch03.CoeffFamily d}
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u.grad) :
    Book.Ch03.IsForcedEquation Q a u (0 : Vec d → Vec d) := by
  have hEll : IsAEEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (Book.Ch02.cubeDomain Q : Set (Vec d)) (a.coeffOn Q).toCoeffField :=
    ⟨(Book.Ch02.cubeDomain Q).measurableSet,
      (a.coeffOn Q).aeStronglyMeasurable, (a.coeffOn Q).aeElliptic⟩
  have hflux : MemVectorL2 (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) :=
    hEll.memVectorL2_matVecMul u.grad_memVectorL2
  have hsol : IsSolenoidalOn (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
    refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hflux
      (Book.Ch02.cubeDomain Q).isOpen ?_
    intro psi hpsi hsupp hsub
    have hzero := (hu psi ⟨hpsi, hsupp, hsub⟩).2
    have hfun :
        (fun x ↦ vecDot
          (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (fun i ↦ (fderiv ℝ psi x) (basisVec i))) =
        fun x ↦ vecDot (smoothGrad psi x)
          (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
      funext x
      rw [vecDot_comm]
      rfl
    rw [hfun]
    exact hzero
  have hweak : IsH1DirichletRhsWeakSolutionOn
      (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u (0 : Vec d → Vec d) :=
    Book.Ch03.IsH1DirichletRhsWeakSolutionOn.of_residual_solenoidal
      hflux MeasureTheory.MemLp.zero (by simpa using hsol)
  simpa only [Book.Ch03.IsForcedEquation] using! hweak

/-- Any symmetric uniformly elliptic constant matrix admits a same-trace
homogeneous comparison for a high-contrast weak solution on an open cube. -/
theorem exists_constantCoeffCoarseGrainingComparisonDatum_of_hcWeakSolution
    {Q : TriadicCube d} {a : Book.Ch03.CoeffFamily d}
    (a0 : Book.Ch03.ConstantCoeffMatrix d)
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u.grad) :
    ∃ W : Book.Ch03.CoarseGrainingComparisonDatum Q a a0
        (0 : Vec d → Vec d),
      W.u = u := by
  by_cases hd : d = 0
  · subst d
    let U : Set (Vec 0) := Book.Ch02.cubeDomain Q
    let v : H1Function U := u
    have hv : Book.Ch03.IsConstantCoeffForcedEquation Q a0 v
        (0 : Vec 0 → Vec 0) := by
      intro phi
      simp [vecDot, matVecMul]
    let W : Book.Ch03.CoarseGrainingComparisonDatum Q a a0
        (0 : Vec 0 → Vec 0) :=
      { u := u
        v := v
        uWeakSolution := isForcedEquation_zero_of_isWeakSolutionOn u hu
        vWeakSolution := hv
        zeroTraceDifference := by
          refine ⟨0, ?_⟩
          filter_upwards with x
          change (0 : ℝ) = u.toFun x - u.toFun x
          ring }
    exact ⟨W, rfl⟩
  · let : NeZero d := ⟨hd⟩
    let U : Set (Vec d) := Book.Ch02.cubeDomain Q
    let b0 : CoeffField d := constantCoeffField a0.matrix
    have hRealize :
        PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U :=
      PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
        (by simpa only [U] using (Book.Ch02.cubeDomain Q).isDomain)
    have hEll0 : IsEllipticFieldOn a0.lam a0.Lam U b0 := by
      simpa only [U, b0] using
        Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField
          a0 (Book.Ch02.cubeDomain Q).measurableSet
    let g0 : Vec d → Vec d := fun x ↦ matVecMul (b0 x) (u.grad x)
    have hg0 : MemVectorL2 U g0 := by
      exact memVectorL2_matVecMul_of_isEllipticFieldOn
        hEll0 u.grad_memVectorL2
    obtain ⟨w, hw⟩ :=
      exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
        (a := b0) (U := U) (g := g0) hg0 hRealize
        (by simpa only [U] using (Book.Ch02.cubeDomain Q).nonempty) hEll0
    let v : H1Function U := u - w.toH1Function
    have hv : Book.Ch03.IsConstantCoeffForcedEquation Q a0 v
        (0 : Vec d → Vec d) := by
      intro phi
      have huFlux : MemVectorL2 U
          (fun x ↦ matVecMul a0.matrix (u.grad x)) := by
        simpa only [b0, g0, constantCoeffField] using hg0
      have hwFlux : MemVectorL2 U
          (fun x ↦ matVecMul a0.matrix (w.toH1Function.grad x)) := by
        have h := memVectorL2_matVecMul_of_isEllipticFieldOn
          hEll0 w.toH1Function.grad_memVectorL2
        simpa only [b0, constantCoeffField] using h
      have huInt : IntegrableOn
          (fun x ↦ vecDot (matVecMul a0.matrix (u.grad x))
            (phi.toH1Function.grad x)) U :=
        integrableOn_vecDot_of_memVectorL2
          huFlux phi.toH1Function.grad_memVectorL2
      have hwInt : IntegrableOn
          (fun x ↦ vecDot (matVecMul a0.matrix (w.toH1Function.grad x))
            (phi.toH1Function.grad x)) U :=
        integrableOn_vecDot_of_memVectorL2
          hwFlux phi.toH1Function.grad_memVectorL2
      have hEq :
          ∫ x in U, vecDot (matVecMul a0.matrix (w.toH1Function.grad x))
              (phi.toH1Function.grad x) ∂volume =
            ∫ x in U, vecDot (matVecMul a0.matrix (u.grad x))
              (phi.toH1Function.grad x) ∂volume := by
        simpa only [b0, g0, constantCoeffField] using hw phi
      calc
        ∫ x in (Book.Ch02.cubeDomain Q : Set (Vec d)),
            vecDot (matVecMul a0.matrix (v.grad x))
              (phi.toH1Function.grad x) ∂volume =
          ∫ x in U,
            (vecDot (matVecMul a0.matrix (u.grad x))
                (phi.toH1Function.grad x) -
              vecDot (matVecMul a0.matrix (w.toH1Function.grad x))
                (phi.toH1Function.grad x)) ∂volume := by
            refine MeasureTheory.setIntegral_congr_fun
              (Book.Ch02.cubeDomain Q).measurableSet ?_
            intro x _hx
            change vecDot (matVecMul a0.matrix (v.grad x))
                (phi.toH1Function.grad x) =
              vecDot (matVecMul a0.matrix (u.grad x))
                  (phi.toH1Function.grad x) -
                vecDot (matVecMul a0.matrix (w.toH1Function.grad x))
                  (phi.toH1Function.grad x)
            rw [show v.grad x = u.grad x - w.toH1Function.grad x by
              exact congrFun (H1Function.sub_grad u w.toH1Function) x]
            simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg,
              vecDot_add_left, vecDot_neg_left]
        _ = (∫ x in U, vecDot (matVecMul a0.matrix (u.grad x))
                (phi.toH1Function.grad x) ∂volume) -
              ∫ x in U, vecDot (matVecMul a0.matrix (w.toH1Function.grad x))
                (phi.toH1Function.grad x) ∂volume :=
          MeasureTheory.integral_sub huInt hwInt
        _ = 0 := sub_eq_zero.mpr hEq.symm
        _ = ∫ x in (Book.Ch02.cubeDomain Q : Set (Vec d)),
            vecDot ((0 : Vec d → Vec d) x) (phi.toH1Function.grad x)
              ∂volume := by simp [vecDot]
    let W : Book.Ch03.CoarseGrainingComparisonDatum Q a a0
        (0 : Vec d → Vec d) :=
      { u := u
        v := v
        uWeakSolution := isForcedEquation_zero_of_isWeakSolutionOn u hu
        vWeakSolution := hv
        zeroTraceDifference := by
          refine ⟨w, ?_⟩
          filter_upwards with x
          change w.toH1Function.toFun x =
            u.toFun x - (u - w.toH1Function).toFun x
          rw [H1Function.sub_toFun]
          ring }
    exact ⟨W, rfl⟩

/-- The chosen same-trace replacement for the rounded near-identity
comparison matrix. -/
@[expose]
noncomputable def roundedHarmonicReplacementDatum [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :
    Book.Ch03.CoarseGrainingComparisonDatum (originCube d m) a
      (roundedReferenceConstantCoeffMatrix abar hS)
      (0 : Vec d → Vec d) :=
  Classical.choose
    (exists_constantCoeffCoarseGrainingComparisonDatum_of_hcWeakSolution
      (roundedReferenceConstantCoeffMatrix abar hS) u hu)

end

end HighContrast
end HCPolySupport
