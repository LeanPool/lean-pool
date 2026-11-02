/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveBarrier
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ResolventIdentity

/-!
# ExcessiveCubeRemainder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The cube remainder of the whole-space barrier

On an exhaustion cube containing the part domain, the difference between the
cube resolvent of the observable and the zero extension of the part solution
is a nonnegative weak supersolution of the shifted equation with zero
right-hand side.  This is the second analytic step of the comparison: the
resolvent solves the equation, the zero extension is a subsolution, and their
difference is therefore a supersolution.

The truncated barriers increase along the exhaustion and converge pointwise to
the whole-space barrier, which is therefore nonnegative everywhere.  The
truncated barrier vanishes off its own cube, because the observable and the
part solution both vanish there.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Topology
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d}

namespace WholeSpaceBarrierData

variable (P : WholeSpaceBarrierData A)

theorem bound_nonneg : 0 ≤ P.D := (abs_nonneg _).trans (P.hfD 0)

theorem measurable_utilde : Measurable P.utilde := P.hutildeCont.measurable

/-- The continuous part solution obeys the sharp resolvent bound. -/
theorem abs_utilde_le (x : Vec d) : |P.utilde x| ≤ P.D / (P.lam : ℝ) := by
  have hDlam : 0 ≤ P.D / (P.lam : ℝ) :=
    div_nonneg P.bound_nonneg P.lam.property.le
  by_cases hx : x ∈ P.V
  · have hae : ∀ᵐ y ∂volumeMeasureOn P.V, |P.utilde y| ≤ P.D / (P.lam : ℝ) := by
      have hbound := abs_alpha_mul_alphaShiftedResolvent_le_ae A.a P.hV
        P.lam.property A.hnu (partEllipticity A P.hV)
        (partDatumL2 P.hV P.hf P.hfD) |P.D|
        (abs_nonneg _)
        (abs_boundedMeasurableToScalarL2_le P.hV
          (P.hf.comp measurable_subtype_coe) (fun y => P.hfD y))
      filter_upwards [hbound, P.hutildeRep] with y hy hrep
      rw [hrep, ← alphaShiftedResolvent_apply A.a P.lam.property A.hnu
        (partEllipticity A P.hV) (partDatumL2 P.hV P.hf P.hfD)]
      rw [abs_mul, abs_of_pos P.lam.property] at hy
      rw [abs_of_nonneg P.bound_nonneg] at hy
      rw [le_div_iff₀ P.lam.property]
      linarith only [hy]
    exact le_of_ae_le_of_continuousOn P.hV.isOpen
      (continuous_abs.comp_continuousOn P.hutildeCont.continuousOn)
      continuousOn_const hae x hx
  · rw [P.hutildeOff x hx, abs_zero]
    exact hDlam

/-- The barrier truncated at one exhaustion cube. -/
def cubeBarrier (m : ℕ) : Vec d → ℝ := fun x =>
  A.analyticCubeResolvent P.lam P.f P.hf P.hfD m x - P.utilde x

/-- The whole-space barrier. -/
def barrier : Vec d → ℝ := fun x =>
  (A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x).toReal - P.utilde x

theorem measurable_cubeBarrier (m : ℕ) : Measurable (P.cubeBarrier m) :=
  (A.measurable_analyticCubeResolvent P.lam P.hf P.hfD m).sub P.measurable_utilde

theorem measurable_barrier : Measurable P.barrier :=
  (A.measurable_analyticMinimalResolvent P.lam P.hf P.hfD).ennreal_toReal.sub
    P.measurable_utilde

theorem abs_cubeBarrier_le (m : ℕ) (x : Vec d) :
    |P.cubeBarrier m x| ≤ 2 * (P.D / (P.lam : ℝ)) := by
  have h1 := A.abs_analyticCubeResolvent_le P.lam P.hf P.bound_nonneg P.hfD m x
  have h2 := P.abs_utilde_le x
  calc |P.cubeBarrier m x| ≤
      |A.analyticCubeResolvent P.lam P.f P.hf P.hfD m x| + |P.utilde x| :=
        abs_sub _ _
    _ ≤ 2 * (P.D / (P.lam : ℝ)) := by linarith only [h1, h2]

theorem abs_barrier_le (x : Vec d) :
    |P.barrier x| ≤ 2 * (P.D / (P.lam : ℝ)) := by
  have h1 : (A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x).toReal ≤
      P.D / (P.lam : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (div_nonneg P.bound_nonneg P.lam.property.le)
      (A.analyticMinimalResolvent_le P.lam P.hf P.hf0 P.bound_nonneg P.hfD x)
  have h0 : 0 ≤ (A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x).toReal :=
    ENNReal.toReal_nonneg
  have h2 := P.abs_utilde_le x
  have hb : P.barrier x =
      (A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x).toReal -
        P.utilde x := rfl
  rw [abs_le] at h2
  rw [hb, abs_le]
  exact ⟨by linarith only [h0, h1, h2.1, h2.2],
    by linarith only [h0, h1, h2.1, h2.2]⟩

theorem continuousOn_cubeBarrier (m : ℕ) :
    ContinuousOn (P.cubeBarrier m) (wholeSpaceCube d m) :=
  (A.continuousOn_analyticCubeResolvent P.lam P.hf P.hfD m).sub
    P.hutildeCont.continuousOn

theorem cubeBarrier_of_notMem (m : ℕ) (hVU : P.V ⊆ wholeSpaceCube d m)
    {x : Vec d} (hx : x ∉ wholeSpaceCube d m) : P.cubeBarrier m x = 0 := by
  have hxV : x ∉ P.V := fun h => hx (hVU h)
  rw [cubeBarrier, WholeSpaceAnalyticData.analyticCubeResolvent, dite_eq_right hx,
    P.hutildeOff x hxV, sub_zero]

/-- On an exhaustion cube containing the part domain, the continuous zero
extension represents the `L²` zero extension. -/
theorem utilde_ae_cube (m : ℕ) (hVU : P.V ⊆ wholeSpaceCube d m) :
    P.utilde =ᵐ[volumeMeasureOn (wholeSpaceCube d m)]
      ZeroTraceSobolev.toL2 (P.cubeZeroExtension m hVU) := by
  classical
  have hind := ZeroTraceSobolev.extendByZeroToPartSuperset_toL2 P.hV
    (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen hVU P.partSolution
  have hrep : ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d m),
      x ∈ P.V → P.utilde x = ZeroTraceSobolev.toL2 P.partSolution x :=
    ae_restrict_of_ae
      ((ae_restrict_iff' P.hV.isOpen.measurableSet).1 P.utilde_ae_eq_partSolution)
  filter_upwards [hind, hrep] with x h1 h2
  rw [cubeZeroExtension, h1, Set.indicator_apply]
  by_cases hxV : x ∈ P.V
  · rw [ite_eq_left hxV]
    exact h2 hxV
  · rw [ite_eq_right hxV]
    exact P.hutildeOff x hxV

/-- The remainder on one exhaustion cube: the cube resolvent minus the zero
extension of the part solution. -/
def cubeRemainder (m : ℕ) (hVU : P.V ⊆ wholeSpaceCube d m) :
    ZeroTraceSobolev (wholeSpaceCube d m) :=
  alphaShiftedSolution A.a P.lam.property A.hnu (A.cubeEllipticity m)
      (boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (P.hf.comp measurable_subtype_coe) (fun y => P.hfD y)) -
    P.cubeZeroExtension m hVU

theorem cubeRemainder_nonneg_ae (m : ℕ) (hVU : P.V ⊆ wholeSpaceCube d m) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d m),
      0 ≤ ZeroTraceSobolev.toL2 (P.cubeRemainder m hVU) x := by
  have h := partDomainRemainder_nonneg_ae A.a P.hV
    (isOpenBoundedConvexDomain_wholeSpaceCube d m) hVU P.lam.property A.hnu
    (A.cubeEllipticity m)
    (boundedMeasurableToScalarL2
      (isOpenBoundedConvexDomain_wholeSpaceCube d m)
      (P.hf.comp measurable_subtype_coe) (fun y => P.hfD y))
    (ae_nonneg_boundedMeasurableToScalarL2
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) P.hf P.hf0 P.hfD)
  rw [P.partSolution_eq_of_cube m hVU] at h
  exact h

/-- The truncated barrier represents the cube remainder. -/
theorem cubeBarrier_ae (m : ℕ) (hVU : P.V ⊆ wholeSpaceCube d m) :
    P.cubeBarrier m =ᵐ[volumeMeasureOn (wholeSpaceCube d m)]
      ZeroTraceSobolev.toL2 (P.cubeRemainder m hVU) := by
  have hres := A.analyticCubeResolvent_ae P.lam P.hf P.hfD m
  have hut := P.utilde_ae_cube m hVU
  have hsub := MeasureTheory.Lp.coeFn_sub
    (ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a P.lam.property A.hnu (A.cubeEllipticity m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (P.hf.comp measurable_subtype_coe) (fun y => P.hfD y))))
    (ZeroTraceSobolev.toL2 (P.cubeZeroExtension m hVU))
  filter_upwards [hres, hut, hsub] with x h1 h2 h3
  have hgoal : ZeroTraceSobolev.toL2 (P.cubeRemainder m hVU) x =
      ZeroTraceSobolev.toL2
          (alphaShiftedSolution A.a P.lam.property A.hnu (A.cubeEllipticity m)
            (boundedMeasurableToScalarL2
              (isOpenBoundedConvexDomain_wholeSpaceCube d m)
              (P.hf.comp measurable_subtype_coe) (fun y => P.hfD y))) x -
        ZeroTraceSobolev.toL2 (P.cubeZeroExtension m hVU) x := by
    rw [cubeRemainder, map_sub, h3, Pi.sub_apply]
  rw [hgoal, ← h2,
    ← alphaShiftedResolvent_apply A.a P.lam.property A.hnu (A.cubeEllipticity m)
      (boundedMeasurableToScalarL2 (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (P.hf.comp measurable_subtype_coe) (fun y => P.hfD y)),
    ← h1]
  rfl

/-- **The truncated barrier is nonnegative everywhere.** -/
theorem cubeBarrier_nonneg (m : ℕ) (hVU : P.V ⊆ wholeSpaceCube d m)
    (x : Vec d) : 0 ≤ P.cubeBarrier m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · refine le_of_ae_le_of_continuousOn
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen continuousOn_const
      (P.continuousOn_cubeBarrier m) ?_ x hx
    filter_upwards [P.cubeBarrier_ae m hVU, P.cubeRemainder_nonneg_ae m hVU]
      with y h1 h2
    rw [h1]
    exact h2
  · rw [P.cubeBarrier_of_notMem m hVU hx]

/-- The truncated barriers increase along the exhaustion. -/
theorem cubeBarrier_mono {m n : ℕ} (hmn : m ≤ n) (x : Vec d) :
    P.cubeBarrier m x ≤ P.cubeBarrier n x := by
  have h := A.monotone_analyticCubeResolvent P.lam P.hf P.hf0 P.hfD x hmn
  exact sub_le_sub_right h _

/-- The truncated barriers converge to the whole-space barrier. -/
theorem tendsto_cubeBarrier (x : Vec d) :
    Filter.Tendsto (fun m => P.cubeBarrier m x) Filter.atTop
      (nhds (P.barrier x)) :=
  (A.tendsto_analyticCubeResolvent P.lam P.hf P.hf0 P.bound_nonneg P.hfD
    x).sub tendsto_const_nhds

theorem cubeBarrier_le_barrier (m : ℕ) (x : Vec d) :
    P.cubeBarrier m x ≤ P.barrier x := by
  refine ge_of_tendsto (P.tendsto_cubeBarrier x) ?_
  filter_upwards [Filter.eventually_ge_atTop m] with n hn
  exact P.cubeBarrier_mono hn x

/-- **The whole-space barrier is nonnegative.** -/
theorem barrier_nonneg (x : Vec d) : 0 ≤ P.barrier x := by
  obtain ⟨m, hVU⟩ := exists_wholeSpaceCube_superset P.hV.isBoundedDomain.isBounded
  exact (P.cubeBarrier_nonneg m hVU x).trans (P.cubeBarrier_le_barrier m x)

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
