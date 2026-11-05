/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveBarrier
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.BoundaryClosedCubeRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepPartialReflection
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumZeroTrace
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# ExcessiveCubeData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The barrier data on an axis cube

The caller obligation of `WholeSpaceBarrierData` is the continuous
representative of the part solution which vanishes on the geometric boundary
of the part domain.  On an axis cube it is discharged: the shifted residual of
a bounded measurable datum is a bounded scalar source, so the closed-cube
boundary representative of the regularity layer applies, and a continuous
function on the closed cube vanishing on its geometric boundary extends by
zero to a continuous function on the whole space.

The resulting barrier data needs no input beyond the coefficient field and the
observable.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Topology
open Algsuperdiff.StochasticProcess.Common.Regularity
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup

noncomputable section

variable {d : ℕ}

private theorem isClosed_memAxisCubeClosure (z : Vec d) (L : ℝ) :
    IsClosed {x | MemAxisCubeClosure z L x} := by
  have hset : {x | MemAxisCubeClosure z L x} =
      ⋂ i : Fin d, (fun x : Vec d => x i) ⁻¹' Set.Icc (z i) (z i + L) := by
    ext x
    simp only [MemAxisCubeClosure, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_preimage, Set.mem_Icc]
  rw [hset]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)

/-- A continuous closed-cube function vanishing on the geometric boundary
extends by zero to a continuous function on the whole space. -/
theorem exists_continuous_zeroExtension_of_cube_boundary_zero
    (z : Vec d) (L : ℝ) (v : Vec d → ℝ)
    (hv : ContinuousOn v {x | MemAxisCubeClosure z L x})
    (hvzero : ∀ x, MemAxisCubeClosure z L x → x ∉ axisCube z L → v x = 0) :
    ∃ w : Vec d → ℝ, Continuous w ∧ (∀ x ∈ axisCube z L, w x = v x) ∧
      ∀ x, x ∉ axisCube z L → w x = 0 := by
  classical
  let C : Set (Vec d) := {x | MemAxisCubeClosure z L x}
  have hCclosed : IsClosed C := isClosed_memAxisCubeClosure z L
  have hQC : axisCube z L ⊆ C := axisCube_subset_closureSet z L
  let vc : C(C, ℝ) := ⟨fun x => v x, continuousOn_iff_continuous_domRestrict.mp hv⟩
  obtain ⟨e, he⟩ := ContinuousMap.exists_restrict_eq hCclosed vc
  have he_on_C : ∀ x, x ∈ C → e x = v x := fun x hx =>
    DFunLike.congr_fun he ⟨x, hx⟩
  have hfrontier : ∀ x ∈ frontier C, e x = 0 := by
    intro x hx
    have hxC : x ∈ C := by
      rw [frontier, hCclosed.closure_eq] at hx
      exact hx.1
    have hxNotQ : x ∉ axisCube z L := by
      intro hxQ
      have hxInt : x ∈ interior C :=
        (interior_maximal hQC (isOpen_axisCube z L)) hxQ
      rw [frontier, hCclosed.closure_eq] at hx
      exact hx.2 hxInt
    rw [he_on_C x hxC, hvzero x hxC hxNotQ]
  refine ⟨C.piecewise e 0, ?_, ?_, ?_⟩
  · exact continuous_piecewise hfrontier e.continuous.continuousOn
      continuous_const.continuousOn
  · intro x hx
    rw [Set.piecewise_eq_of_mem C e 0 (hQC hx)]
    exact he_on_C x (hQC hx)
  · intro x hx
    by_cases hxC : x ∈ C
    · rw [Set.piecewise_eq_of_mem C e 0 hxC, he_on_C x hxC, hvzero x hxC hx]
    · exact Set.piecewise_eq_of_notMem C e 0 hxC

variable [NeZero d]

/-- **The continuous zero extension of the part solution on an axis cube.**
The closed-cube boundary representative of the regularity layer applies to the
shifted residual of a bounded measurable datum, and its zero extension is
continuous on the whole space. -/
theorem exists_continuous_partSolution_zeroExtension
    (A : WholeSpaceAnalyticData d) (z : Vec d) {L : ℝ} (hL : 0 < L)
    {LamV : ℝ} (hEllV : IsEllipticFieldOn A.nu LamV (axisCube z L) A.a)
    (lam : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) :
    ∃ w : Vec d → ℝ, Continuous w ∧ (∀ x, x ∉ axisCube z L → w x = 0) ∧
      w =ᵐ[volumeMeasureOn (axisCube z L)]
        ZeroTraceSobolev.toL2
          (alphaShiftedSolution A.a lam.property A.hnu hEllV
            (partDatumL2 (isOpenBoundedConvexDomain_axisCube z L) hf hfD)) := by
  classical
  have hQ : IsOpenBoundedConvexDomain (axisCube z L) :=
    isOpenBoundedConvexDomain_axisCube z L
  have hD : 0 ≤ D := (abs_nonneg (f 0)).trans (hfD 0)
  set fL2 : ScalarL2 (axisCube z L) := partDatumL2 hQ hf hfD with hfL2
  have hfbound : ∀ᵐ x ∂volumeMeasureOn (axisCube z L), |fL2 x| ≤ D := by
    have hbd := abs_boundedMeasurableToScalarL2_le hQ
      (hf.comp measurable_subtype_coe) (fun y => hfD y)
    filter_upwards [hbd] with x hx
    rwa [abs_of_nonneg hD] at hx
  obtain ⟨u, huvalue, -, hscalar, hresidual⟩ :=
    exists_h10Function_scalarForced_residual_bound hQ A.a lam.property A.hnu
      hEllV fL2 hD hfbound
  set g : Vec d → ℝ := fun x => fL2 x - (lam : ℝ) * u.toH1Function.toFun x
    with hgdef
  have hgM : ∀ᵐ y ∂volume.restrict (axisCube z L), |g y| ≤ 2 * D := hresidual
  have hg : MemScalarLInfOn (axisCube z L) g := by
    refine memLp_top_of_bound hscalar.1.aestronglyMeasurable (2 * D) ?_
    filter_upwards [hgM] with x hx
    simpa only [Real.norm_eq_abs] using hx
  have hmatrix : IsMatrixDivFormWeakSolutionZerothOrderOn A.a (axisCube z L)
      u.toH1Function g 0 := by
    intro phi
    simpa only [hgdef, Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero]
      using hscalar.2 phi
  obtain ⟨W, hWcont, hWae, hWzero⟩ :=
    exists_closedCube_representative_continuousCoeff A.hd z hL A.hnu A.hameas
      A.hsymm (A.hskewContinuous.mono (Set.subset_univ _))
      (by linarith only [hD] : (0 : ℝ) ≤ 2 * D) hg hgM hmatrix
  obtain ⟨w, hwcont, hwon, hwoff⟩ :=
    exists_continuous_zeroExtension_of_cube_boundary_zero z L W hWcont hWzero
  refine ⟨w, hwcont, hwoff, ?_⟩
  filter_upwards [hWae, u.toH1Function.coeFn_toScalarL2,
    self_mem_ae_restrict hQ.isOpen.measurableSet] with x h1 h2 hx
  rw [hwon x hx, h1, ← h2, huvalue]
  rfl

/-- **The barrier data of the whole-space comparison on an axis cube.**  Every
field is discharged: the continuous zero extension of the part solution comes
from the closed-cube boundary representative. -/
def axisCubeBarrierData (A : WholeSpaceAnalyticData d) (z : Vec d) {L : ℝ}
    (hL : 0 < L) (lam : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (hfV : f =ᵐ[volume] (axisCube z L).indicator f) : WholeSpaceBarrierData A :=
  let hw := exists_continuous_partSolution_zeroExtension A z hL
    (partEllipticity A (isOpenBoundedConvexDomain_axisCube z L)) lam hf hfD
  { V := axisCube z L
    hV := isOpenBoundedConvexDomain_axisCube z L
    lam := lam
    f := f
    hf := hf
    hf0 := hf0
    D := D
    hfD := hfD
    hfV := hfV
    utilde := Classical.choose hw
    hutildeCont := (Classical.choose_spec hw).1
    hutildeOff := (Classical.choose_spec hw).2.1
    hutildeRep := (Classical.choose_spec hw).2.2 }

@[simp] theorem axisCubeBarrierData_V (A : WholeSpaceAnalyticData d) (z : Vec d)
    {L : ℝ} (hL : 0 < L) (lam : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (hfV : f =ᵐ[volume] (axisCube z L).indicator f) :
    (axisCubeBarrierData A z hL lam hf hf0 hfD hfV).V = axisCube z L := rfl

@[simp] theorem axisCubeBarrierData_lam (A : WholeSpaceAnalyticData d)
    (z : Vec d) {L : ℝ} (hL : 0 < L) (lam : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (hfV : f =ᵐ[volume] (axisCube z L).indicator f) :
    (axisCubeBarrierData A z hL lam hf hf0 hfD hfV).lam = lam := rfl

@[simp] theorem axisCubeBarrierData_f (A : WholeSpaceAnalyticData d)
    (z : Vec d) {L : ℝ} (hL : 0 < L) (lam : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (hfV : f =ᵐ[volume] (axisCube z L).indicator f) :
    (axisCubeBarrierData A z hL lam hf hf0 hfD hfV).f = f := rfl

end

end DivergenceFormProcess.Form
