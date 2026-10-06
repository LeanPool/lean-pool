/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HessianL2
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianKernelIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Assoc Pressure Helmholtz

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped Convolution
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

/-- The time-dependent Newtonian potential of a smooth compactly supported
space-time density, used in `lem:helmholtz-test`. -/
@[expose]
noncomputable def associatedPressureNewtonianPotential
    (h : Vec3 × ℝ → ℝ) : Vec3 × ℝ → ℝ := fun z =>
  CKN.pressureNewtonianPotential (fun y : Vec3 => h (y, z.2)) z.1

private theorem associatedPressureNewtonianPotential_eq_convolution
    (h : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) :
    associatedPressureNewtonianPotential h z =
      ((fun y : Vec3 => h (y, z.2)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ), (volume : Measure Vec3)]
        (-newtonianKernel)) z.1 := by
  rw [associatedPressureNewtonianPotential, CKN.pressureNewtonianPotential,
    convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.lsmul_apply]
  exact mul_comm _ _

/-- This potential is jointly smooth, as required for the test-field
Helmholtz decomposition in `lem:helmholtz-test`. -/
theorem associatedPressureNewtonianPotential_contDiff
    {h : Vec3 × ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) :
    ContDiff ℝ (⊤ : ℕ∞) (associatedPressureNewtonianPotential h) := by
  let K : Set Vec3 := (tsupport h).image (fun z : Vec3 × ℝ => z.1)
  have hproj : Continuous (fun z : Vec3 × ℝ => z.1) := continuous_fst
  have hK : IsCompact K := hc.isCompact.image hproj
  have hgzero : ∀ t : ℝ, ∀ y : Vec3, t ∈ (Set.univ : Set ℝ) →
      y ∉ K → h (y, t) = 0 := by
    intro t y _ hy
    have hy' : (y, t) ∉ tsupport h := by
      intro hm
      exact hy ⟨(y, t), hm, rfl⟩
    exact image_eq_zero_of_notMem_tsupport hy'
  have hparam : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun t : ℝ => fun y : Vec3 => h (y, t))) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec3 => (q.2, q.1)) :=
      contDiff_snd.prodMk contDiff_fst
    exact hh.comp hmap
  have hg : ContDiffOn ℝ (⊤ : ℕ∞)
      ↿(fun t : ℝ => fun y : Vec3 => h (y, t))
      ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set Vec3)) := hparam.contDiffOn
  have hconv := contDiffOn_convolution_left_with_param
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (s := (Set.univ : Set ℝ)) (k := K)
    isOpen_univ hK hgzero (locallyIntegrable_newtonianKernel.neg) hg
  have hconv' : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ((fun y : Vec3 => h (y, z.2)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ), (volume : Measure Vec3)]
        (-newtonianKernel)) z.1) := by
    have h : ContDiff ℝ (⊤ : ℕ∞)
       (fun q : ℝ × Vec3 => ((fun y : Vec3 => h (y, q.1)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ), (volume : Measure Vec3)]
        (-newtonianKernel)) q.2) := by
      exact contDiffOn_univ.mp (by simpa using hconv)
    exact h.comp (contDiff_snd.prodMk contDiff_fst)
  have heq := associatedPressureNewtonianPotential_eq_convolution h
  rw [funext heq]
  exact hconv'

/-- Each spatial slice of this potential solves its Poisson equation, as used
in `lem:helmholtz-test`. -/
theorem associatedPressureNewtonianPotential_laplacian
    {h : Vec3 × ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) (z : Vec3 × ℝ) :
    CKN.spatialLaplacian
      (fun x : Vec3 => associatedPressureNewtonianPotential h (x, z.2)) z.1 = h z := by
  let hSlice : Vec3 → ℝ := fun x => h (x, z.2)
  let K : Set Vec3 := (tsupport h).image (fun w : Vec3 × ℝ => w.1)
  have hproj : Continuous (fun w : Vec3 × ℝ => w.1) := continuous_fst
  have hK : IsCompact K := hc.isCompact.image hproj
  have hSliceSmooth : ContDiff ℝ (⊤ : ℕ∞) hSlice := by
    exact hh.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  have hSliceCompact : HasCompactSupport hSlice :=
    HasCompactSupport.of_support_subset_isCompact hK (by
      intro x hx
      change h (x, z.2) ≠ 0 at hx
      exact ⟨(x, z.2), subset_tsupport h hx, rfl⟩)
  have hLap := CKN.pressureNewtonianPotential_laplacian_eq
    hSliceSmooth hSliceCompact z.1
  simpa [hSlice, associatedPressureNewtonianPotential] using hLap

/-- Spatial differentiation commutes with this Newtonian potential on smooth
compactly supported data. -/
theorem associatedPressureNewtonianPotential_spatialPartial
    {h : Vec3 × ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (associatedPressureNewtonianPotential h) i z =
      associatedPressureNewtonianPotential (CKN.spatialPartialProd h i) z := by
  let hSlice : Vec3 → ℝ := fun x => h (x, z.2)
  let K : Set Vec3 := (tsupport h).image (fun w : Vec3 × ℝ => w.1)
  have hproj : Continuous (fun w : Vec3 × ℝ => w.1) := continuous_fst
  have hK : IsCompact K := hc.isCompact.image hproj
  have hSliceSmooth : ContDiff ℝ (⊤ : ℕ∞) hSlice := by
    exact hh.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  have hSliceCompact : HasCompactSupport hSlice :=
    HasCompactSupport.of_support_subset_isCompact hK (by
      intro x hx
      change h (x, z.2) ≠ 0 at hx
      exact ⟨(x, z.2), subset_tsupport h hx, rfl⟩)
  have hderiv := CKN.pressureNewtonianPotential_spatialDeriv_convolution
    hSliceSmooth hSliceCompact i z.1
  change CKN.spatialDeriv (fun x : Vec3 =>
      CKN.pressureNewtonianPotential hSlice x) i z.1 =
    CKN.pressureNewtonianPotential
      (fun x : Vec3 => CKN.spatialPartialProd h i (x, z.2)) z.1
  rw [hderiv]
  rw [CKN.pressureNewtonianPotential]
  apply integral_congr_ae
  filter_upwards [] with x
  have heq : CKN.spatialDeriv hSlice i x =
      CKN.spatialPartialProd h i (x, z.2) := by rfl
  rw [heq]
  ring

/-- The divergence of a compactly supported smooth vector test, used in
`lem:helmholtz-test`. -/
@[expose]
def associatedPressureTestDivergence (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → ℝ :=
  fun z : Vec3 × ℝ => ∑ i : Fin 3,
    CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) i z

/-- The three-dimensional curl of a compactly supported smooth vector test on
each time slice, used in `lem:helmholtz-test`. -/
@[expose]
def associatedPressureTestCurlComponent (φ : Vec3 × ℝ → Vec3) (j : Fin 3) :
    Vec3 × ℝ → ℝ := fun z : Vec3 × ℝ =>
  if j = 0 then
    CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w 2) 1 z -
      CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w 1) 2 z
  else if j = 1 then
    CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w 0) 2 z -
      CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w 2) 0 z
  else
    CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w 1) 0 z -
      CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w 0) 1 z

/-- The scalar Newtonian potential in the test-field Helmholtz decomposition.
-/
@[expose]
def associatedPressureHelmholtzScalarPotential
    (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → ℝ :=
  associatedPressureNewtonianPotential (associatedPressureTestDivergence φ)

/-- The vector Newtonian potential in the test-field Helmholtz decomposition.
-/
@[expose]
def associatedPressureHelmholtzVectorPotential
    (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → Vec3 := fun z j =>
  -associatedPressureNewtonianPotential (associatedPressureTestCurlComponent φ j) z

/-- The divergence of a smooth test is smooth, as used in `lem:helmholtz-test`. -/
theorem associatedPressureTestDivergence_contDiff
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T)) :
    ContDiff ℝ (⊤ : ℕ∞) (associatedPressureTestDivergence φ) := by
  apply ContDiff.sum
  intro i hi
  simpa [CKN.spatialPartialProd] using CKN.spatialPartial_contDiff
    (CKN.component_mem_spaceTimeTestFunction hφ i).1 i

/-- The divergence of a compactly supported test has compact support, as used
in `lem:helmholtz-test`. -/
theorem associatedPressureTestDivergence_hasCompactSupport
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T)) :
    HasCompactSupport (associatedPressureTestDivergence φ) := by
  have hi (i : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ =>
        CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) i z) := by
    simpa [CKN.spatialPartialProd] using CKN.hasCompactSupport_spatialPartial
      (CKN.component_mem_spaceTimeTestFunction hφ i).2.1 i
  change HasCompactSupport (fun z : Vec3 × ℝ =>
    ∑ i : Fin 3, CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) i z)
  have hsum := HasCompactSupport.finset_sum
    (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i : Fin 3 => fun z : Vec3 × ℝ =>
      CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) i z)
    (fun i _ => hi i)
  convert hsum using 1
  funext z
  simp only [Finset.sum_apply]

/-- Each component of the curl of a smooth test is smooth, as used in
`lem:helmholtz-test`. -/
theorem associatedPressureTestCurlComponent_contDiff
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T))
    (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (associatedPressureTestCurlComponent φ j) := by
  have hφi (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hφ i
  fin_cases j <;>
    exact (CKN.spatialPartial_contDiff (hφi _).1 _).sub
      (CKN.spatialPartial_contDiff (hφi _).1 _)

/-- Each component of the curl of a compactly supported test has compact
support, as used in `lem:helmholtz-test`. -/
theorem associatedPressureTestCurlComponent_hasCompactSupport
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T))
    (j : Fin 3) :
    HasCompactSupport (associatedPressureTestCurlComponent φ j) := by
  have hφi (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hφ i
  have hderiv (i k : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ =>
        CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) k z) := by
    simpa [CKN.spatialPartialProd] using CKN.hasCompactSupport_spatialPartial
      (hφi i).2.1 k
  fin_cases j <;>
    exact (hderiv _ _).sub (hderiv _ _)

/-- The scalar Helmholtz potential is jointly smooth, as required in
`lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzScalarPotential_contDiff
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T)) :
    ContDiff ℝ (⊤ : ℕ∞) (associatedPressureHelmholtzScalarPotential φ) :=
  associatedPressureNewtonianPotential_contDiff
    (associatedPressureTestDivergence_contDiff hφ)
    (associatedPressureTestDivergence_hasCompactSupport hφ)

/-- The vector Helmholtz potential is jointly smooth, as required in
`lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzVectorPotential_contDiff
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T)) :
    ContDiff ℝ (⊤ : ℕ∞) (associatedPressureHelmholtzVectorPotential φ) := by
  apply contDiff_pi.mpr
  intro j
  exact (associatedPressureNewtonianPotential_contDiff
    (associatedPressureTestCurlComponent_contDiff hφ j)
    (associatedPressureTestCurlComponent_hasCompactSupport hφ j)).neg

end CKN.Leray

end
