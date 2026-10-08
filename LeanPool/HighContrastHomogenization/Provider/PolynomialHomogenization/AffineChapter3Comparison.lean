/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineCoeffFamily
public import LeanPool.HighContrastHomogenization.Analytic.AffineH10
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakSolution
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutions
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincareRHS.Regularity
public import LeanPool.HighContrastHomogenization.Support.Probability.LocalEllipticitySlices
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Recovery

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.AffineChapter3Comparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Chapter 3 comparison data from weak solutions

On an open cube, the smooth compact-test weak equation upgrades to the full
zero-trace weak equation once the coefficient flux is known to lie in `L²`.
This constructs the deterministic Chapter 3 comparison datum directly from
the high-contrast weak-solution predicate.

The zero-trace difference below is deliberately cube-local.  A zero-trace
difference on a larger domain does not in general remain zero trace after
restriction to an interior cube.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem isH1DirichletRhsWeakSolutionOn_zero_of_isWeakSolutionOn
    {U : Set (Vec d)}
    (hU : IsOpen U) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsAEEllipticFieldOn lam Lam U a) (u : H1Function U)
    (hweak : IsWeakSolutionOn a U u.grad) :
    IsH1DirichletRhsWeakSolutionOn a U u (0 : Vec d → Vec d) := by
  have hflux : MemVectorL2 U (fun x => matVecMul (a x) (u.grad x)) :=
    hEll.memVectorL2_matVecMul u.grad_memVectorL2
  have hsol : IsSolenoidalOn U (fun x => matVecMul (a x) (u.grad x)) := by
    refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hflux hU ?_
    intro psi hpsi hsupp hsub
    have hzero := (hweak psi ⟨hpsi, hsupp, hsub⟩).2
    have hfun :
        (fun x => vecDot (matVecMul (a x) (u.grad x))
          (fun i => (fderiv ℝ psi x) (basisVec i))) =
          fun x => vecDot (smoothGrad psi x) (matVecMul (a x) (u.grad x)) := by
      funext x
      rw [vecDot_comm]
      rfl
    rw [hfun]
    exact hzero
  refine Book.Ch03.IsH1DirichletRhsWeakSolutionOn.of_residual_solenoidal hflux
    MeasureTheory.MemLp.zero ?_
  simpa using hsol

/-- The zero vector field satisfies every Chapter 3 force-regularity exponent. -/
theorem forceBesovRegularity_zero (Q : TriadicCube d) (s : ℝ) :
    Book.Ch03.ForceBesovRegularity Q s (0 : Vec d → Vec d) := by
  exact ⟨MeasureTheory.MemLp.zero,
    cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove Q s⟩

/-- Two high-contrast weak solutions on the same open cube, with an actual
cube-level zero-trace difference, form the zero-force Chapter 3 comparison
datum. -/
theorem coarseGrainingComparisonDatum_zero_of_hcWeakSolutions
    {Q : TriadicCube d} {a : Book.Ch03.CoeffFamily d}
    {a0 : Book.Ch03.ConstantCoeffMatrix d}
    (u v : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u.grad)
    (hv : IsWeakSolutionOn (constantCoeffField a0.matrix)
      (Book.Ch02.cubeDomain Q : Set (Vec d)) v.grad)
    (w : H10Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hw : w.toH1Function.toFun =ᵐ[volumeMeasureOn (Book.Ch02.cubeDomain Q : Set (Vec d))]
        fun x => u.toFun x - v.toFun x) :
    ∃ W : Book.Ch03.CoarseGrainingComparisonDatum Q a a0
        (0 : Vec d → Vec d),
      W.u = u ∧ W.v = v := by
  have hEll : IsAEEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (Book.Ch02.cubeDomain Q : Set (Vec d)) (a.coeffOn Q).toCoeffField :=
    ⟨(Book.Ch02.cubeDomain Q).measurableSet,
      (a.coeffOn Q).aeStronglyMeasurable, (a.coeffOn Q).aeElliptic⟩
  have huDir : IsH1DirichletRhsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u (0 : Vec d → Vec d) :=
    isH1DirichletRhsWeakSolutionOn_zero_of_isWeakSolutionOn
      (Book.Ch02.cubeDomain Q).isOpen hEll u hu
  have hEll0 : IsAEEllipticFieldOn a0.lam a0.Lam
      (Book.Ch02.cubeDomain Q : Set (Vec d)) (constantCoeffField a0.matrix) :=
    IsAEEllipticFieldOn.of_isEllipticFieldOn
      (Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField
        a0 (Book.Ch02.cubeDomain Q).measurableSet)
  have hvDir : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0.matrix)
      (Book.Ch02.cubeDomain Q : Set (Vec d)) v (0 : Vec d → Vec d) :=
    isH1DirichletRhsWeakSolutionOn_zero_of_isWeakSolutionOn
      (Book.Ch02.cubeDomain Q).isOpen hEll0 v hv
  let W : Book.Ch03.CoarseGrainingComparisonDatum Q a a0
      (0 : Vec d → Vec d) :=
    { u := u
      v := v
      uWeakSolution := huDir
      vWeakSolution := by simpa [constantCoeffField] using! hvDir
      zeroTraceDifference := ⟨w, hw⟩ }
  exact ⟨W, rfl, rfl⟩

end

end HighContrast
end HCPolySupport
