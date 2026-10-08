/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.CoeffRestriction
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SolutionIntegrability
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry

/-!
# High-contrast homogenization: Provider.Regularity.FiniteCubeSolutionRestriction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Restriction of centered-cube solutions

This module restricts a coefficient-harmonic solution on one centered
triadic cube to any smaller centered triadic cube and transports the
coefficient representative supplied by the compatible coefficient family.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory CubeCalderonZygmund

noncomputable section

private theorem triadic_cube_ext {d : ℕ} {Q R : TriadicCube d}
    (hscale : Q.scale = R.scale) (hindex : Q.index = R.index) : Q = R := by
  cases Q
  cases R
  cases hscale
  cases hindex
  rfl

/-- A central descendant of a centered cube is the centered cube at the
corresponding lower scale. -/
theorem centralDescendant_originCube_eq_originCube_sub {d : ℕ}
    (m : ℤ) (j : ℕ) :
    centralDescendant (originCube d m) j = originCube d (m - (j : ℤ)) := by
  apply triadic_cube_ext
  · simpa [originCube] using centralDescendant_scale (originCube d m) j
  · funext i
    rw [centralDescendant_index]
    simp [originCube]

/-- The smaller centered cube is a descendant of the larger centered cube at
the integer scale gap. -/
theorem originCube_mem_descendantsAtDepth_of_le {d : ℕ} {n m : ℤ}
    (hnm : n ≤ m) :
    originCube d n ∈
      descendantsAtDepth (originCube d m) (Int.toNat (m - n)) := by
  have hnonneg : 0 ≤ m - n := sub_nonneg.mpr hnm
  have hdesc :=
    centralDescendant_mem_descendantsAtDepth
      (originCube d m) (Int.toNat (m - n))
  rw [centralDescendant_originCube_eq_originCube_sub] at hdesc
  simpa [Int.toNat_of_nonneg hnonneg] using hdesc

/-- Centered open cubes are nested in their scale parameter. -/
theorem openCubeSet_originCube_subset_of_le {d : ℕ} {n m : ℤ}
    (hnm : n ≤ m) :
    openCubeSet (originCube d n) ⊆ openCubeSet (originCube d m) :=
  openCubeSet_subset_of_mem_descendantsAtDepth
    (originCube_mem_descendantsAtDepth_of_le (d := d) hnm)

/-- Restrict a solution on `Q_m` to the centered subcube `Q_n`, retaining the
compatible coefficient representative on `Q_n`. -/
@[expose]
noncomputable def finiteCubeSolutionRestriction {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    Book.Ch03.CubeSolution (originCube d n) a := by
  let Q : TriadicCube d := originCube d m
  let R : TriadicCube d := originCube d n
  have hsub : openCubeSet R ⊆ openCubeSet Q := by
    simpa only [Q, R] using
      openCubeSet_originCube_subset_of_le (d := d) hnm
  have hfluxQ :
      MemVectorL2 (openCubeSet Q)
        (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x) (u.toH1.grad x)) :=
    Book.Ch02.Solution.flux_memVectorL2 u
  have hfluxR :
      MemVectorL2 (openCubeSet R)
        (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x) (u.toH1.grad x)) := by
    have hmono := Measure.restrict_mono_set volume hsub
    simpa only [MemVectorL2, volumeMeasureOn] using
      hfluxQ.mono_measure hmono
  let uR :
      Book.Ch02.Solution (Book.Ch02.cubeDomain R)
        ((a.coeffOn Q).restrictToSubcube hsub) :=
    u.restrictOfMemVectorL2
      (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub hfluxR
  have hCoeff :
      Book.Ch02.CoeffOn.AEEq ((a.coeffOn Q).restrictToSubcube hsub)
        (a.coeffOn R) := by
    exact (a.restrictsTo_of_subset hsub).symm
  exact Book.Ch02.Solution.ofAEEq hCoeff uR

/-- Restriction preserves the original value representative. -/
@[simp] theorem finiteCubeSolutionRestriction_toFun {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    (finiteCubeSolutionRestriction a hnm u).toH1.toFun = u.toH1.toFun := by
  rfl

/-- Restriction preserves the original gradient representative. -/
@[simp] theorem finiteCubeSolutionRestriction_grad {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    (finiteCubeSolutionRestriction a hnm u).toH1.grad = u.toH1.grad := by
  rfl

end

end HighContrast
end HCPolySupport
