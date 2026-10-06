/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCorrector
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.CoeffRestriction
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Algebra

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSuccessorDifference

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Successive finite affine solutions

This module restricts a selected affine solution from one centered cube to its
central child, transports the coefficient representative, and subtracts the
selected solution on the child cube.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

theorem originCube_mem_descendantsAtDepth_succ {d : ℕ} (m : ℤ) :
    originCube d m ∈ descendantsAtDepth (originCube d (m + 1)) 1 := by
  rw [descendantsAtDepth_one]
  simpa [originCube] using!
    (middleChild_mem_childCubes (originCube d (m + 1)))

/-- The scale-`m + 1` selected affine solution, restricted to the scale-`m`
centered cube and transported to its coefficient representative. -/
@[expose]
noncomputable def finiteAffineSuccessorRestriction {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    Book.Ch03.CubeSolution (originCube d m) a := by
  let Q : TriadicCube d := originCube d (m + 1)
  let R : TriadicCube d := originCube d m
  have hR : R ∈ descendantsAtDepth Q 1 := by
    simpa only [Q, R] using
      originCube_mem_descendantsAtDepth_succ (d := d) m
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  let uQ : Book.Ch03.CubeSolution Q a :=
    finiteAffineCubeSolution a (m + 1) e
  have hfluxQ :
      MemVectorL2 (openCubeSet Q)
        (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x) (uQ.toH1.grad x)) :=
    Book.Ch02.Solution.flux_memVectorL2 uQ
  have hfluxR :
      MemVectorL2 (openCubeSet R)
        (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x) (uQ.toH1.grad x)) := by
    have hmono := Measure.restrict_mono_set volume hsub
    simpa only [MemVectorL2, volumeMeasureOn] using
      hfluxQ.mono_measure hmono
  let uR :
      Book.Ch02.Solution (Book.Ch02.cubeDomain R)
        ((a.coeffOn Q).restrictToSubcube hsub) :=
    uQ.restrictOfMemVectorL2
      (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub hfluxR
  have hCoeff :
      Book.Ch02.CoeffOn.AEEq ((a.coeffOn Q).restrictToSubcube hsub)
        (a.coeffOn R) := by
    exact (a.restrictsTo_of_subset hsub).symm
  exact Book.Ch02.Solution.ofAEEq hCoeff uR

/-- Restriction preserves the selected outer solution's value representative. -/
@[simp] theorem finiteAffineSuccessorRestriction_toFun {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    (finiteAffineSuccessorRestriction a m e).toH1.toFun =
      (finiteAffineCubeSolution a (m + 1) e).toH1.toFun := by
  rfl

/-- Restriction preserves the selected outer solution's gradient representative. -/
@[simp] theorem finiteAffineSuccessorRestriction_grad {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    (finiteAffineSuccessorRestriction a m e).toH1.grad =
      (finiteAffineCubeSolution a (m + 1) e).toH1.grad := by
  rfl

theorem cubeSolution_weakFluxIntegrable_finiteAffineSuccessorDifference {d : ℕ}
    {Q : TriadicCube d} {a : Book.Ch02.TriadicCoeffFamily d}
    (u : Book.Ch03.CubeSolution Q a) :
    weakFluxIntegrable (Book.Ch02.cubeDomain Q).carrier
      (a.coeffOn Q).toCoeffField u := by
  intro φ
  exact integrableOn_vecDot_of_memVectorL2
    (Book.Ch02.Solution.flux_memVectorL2 u)
    φ.toH1Function.grad_memVectorL2

/-- The restricted scale-`m + 1` affine solution minus the scale-`m` affine
solution, as an actual harmonic solution on the scale-`m` centered cube. -/
@[expose]
noncomputable def finiteAffineSuccessorDifference {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    Book.Ch03.CubeSolution (originCube d m) a :=
  AHarmonicFunction.subOfIntegrable
    (finiteAffineSuccessorRestriction a m e)
    (finiteAffineCubeSolution a m e)
    (cubeSolution_weakFluxIntegrable_finiteAffineSuccessorDifference
      (finiteAffineSuccessorRestriction a m e))
    (cubeSolution_weakFluxIntegrable_finiteAffineSuccessorDifference (finiteAffineCubeSolution a m e))

/-- The successor difference has the literal outer-minus-inner value field. -/
@[simp] theorem finiteAffineSuccessorDifference_toFun {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    (finiteAffineSuccessorDifference a m e).toH1.toFun =
      fun x ↦ (finiteAffineCubeSolution a (m + 1) e).toH1.toFun x -
        (finiteAffineCubeSolution a m e).toH1.toFun x := by
  simp only [finiteAffineSuccessorDifference,
    AHarmonicFunction.toH1_subOfIntegrable, H1Function.sub_toFun,
    finiteAffineSuccessorRestriction_toFun]

/-- The successor difference has the literal outer-minus-inner gradient field. -/
@[simp] theorem finiteAffineSuccessorDifference_grad {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    (finiteAffineSuccessorDifference a m e).toH1.grad =
      fun x ↦ (finiteAffineCubeSolution a (m + 1) e).toH1.grad x -
        (finiteAffineCubeSolution a m e).toH1.grad x := by
  unfold finiteAffineSuccessorDifference
  rw [AHarmonicFunction.grad_subOfIntegrable,
    finiteAffineSuccessorRestriction_grad]
  funext x
  rfl

end

end HighContrast
end HCPolySupport
