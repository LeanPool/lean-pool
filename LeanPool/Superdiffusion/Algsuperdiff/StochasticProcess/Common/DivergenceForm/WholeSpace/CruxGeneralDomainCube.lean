/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeAxisBridge
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEProcess

/-!
# CruxGeneralDomainCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The killed resolvent on a translated triadic cube

The localized Dirichlet problems of the field are indexed by the translated
triadic cube `cubeSetAt y n`, the open cube of side `3 ^ n` centred at `y`.
It is an axis cube, so the caller obligation of the whole-space barrier data —
a continuous zero extension of the part solution — is discharged there, and
the barrier data may be built with the triadic cube itself as its part domain.

The resulting identification is the one the localized exit-time estimates
consume: at every positive shift and every point of the cube, the resolvent of
the process killed on leaving the compactified image of the cube, applied to
the constant one, is the continuous representative of the Dirichlet resolvent
of the constant datum on the cube.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The continuous zero extension of the part solution on a domain which is
an axis cube.**  The obligation is discharged on the axis cube and read back
through the set equation. -/
theorem exists_continuous_partSolution_zeroExtension_of_eq_axisCube
    (A : WholeSpaceAnalyticData d) {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (z : Vec d) {L : ℝ} (hL : 0 < L)
    (hVeq : V = axisCube z L) (lam : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    ∃ w : Vec d → ℝ, Continuous w ∧ (∀ x, x ∉ V → w x = 0) ∧
      w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
        (alphaShiftedSolution A.a lam.property A.hnu (partEllipticity A hV)
          (partDatumL2 hV hf hfD)) := by
  subst hVeq
  exact exists_continuous_partSolution_zeroExtension A z hL
    (partEllipticity A hV) lam hf hfD

/-- **The barrier data on a domain which is an axis cube.**  Every field is
discharged, and the part domain of the data is the given set, not the axis
cube it is equal to. -/
def eqAxisCubeBarrierData (A : WholeSpaceAnalyticData d) {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (z : Vec d) {L : ℝ} (hL : 0 < L)
    (hVeq : V = axisCube z L) (lam : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (hfV : f =ᵐ[volume] V.indicator f) : WholeSpaceBarrierData A :=
  let hw := exists_continuous_partSolution_zeroExtension_of_eq_axisCube A hV z
    hL hVeq lam hf hfD
  { V := V
    hV := hV
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

@[simp] theorem eqAxisCubeBarrierData_V (A : WholeSpaceAnalyticData d)
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (z : Vec d) {L : ℝ}
    (hL : 0 < L) (hVeq : V = axisCube z L) (lam : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hfV : f =ᵐ[volume] V.indicator f) :
    (eqAxisCubeBarrierData A hV z hL hVeq lam hf hf0 hfD hfV).V = V := rfl

@[simp] theorem eqAxisCubeBarrierData_f (A : WholeSpaceAnalyticData d)
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (z : Vec d) {L : ℝ}
    (hL : 0 < L) (hVeq : V = axisCube z L) (lam : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hfV : f =ᵐ[volume] V.indicator f) :
    (eqAxisCubeBarrierData A hV z hL hVeq lam hf hf0 hfD hfV).f = f := rfl

@[simp] theorem eqAxisCubeBarrierData_lam (A : WholeSpaceAnalyticData d)
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (z : Vec d) {L : ℝ}
    (hL : 0 < L) (hVeq : V = axisCube z L) (lam : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hfV : f =ᵐ[volume] V.indicator f) :
    (eqAxisCubeBarrierData A hV z hL hVeq lam hf hf0 hfD hfV).lam = lam := rfl

/-! ## The constant datum on a translated triadic cube -/

/-- The datum of the exit-time problem on a translated triadic cube: the
constant one on the cube, extended by zero. -/
def cubeSetAtOneDatum (y : Vec d) (n : ℤ) : Vec d → ℝ :=
  (cubeSetAt y n).indicator fun _ => 1

omit [NeZero d] in
theorem measurable_cubeSetAtOneDatum (y : Vec d) (n : ℤ) :
    Measurable (cubeSetAtOneDatum y n) :=
  measurable_const.indicator (measurableSet_cubeSetAt y n)

omit [NeZero d] in
theorem cubeSetAtOneDatum_nonneg (y : Vec d) (n : ℤ) (x : Vec d) :
    0 ≤ cubeSetAtOneDatum y n x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

omit [NeZero d] in
theorem abs_cubeSetAtOneDatum_le (y : Vec d) (n : ℤ) (x : Vec d) :
    |cubeSetAtOneDatum y n x| ≤ 1 := by
  unfold cubeSetAtOneDatum
  by_cases hx : x ∈ cubeSetAt y n
  · rw [Set.indicator_of_mem hx]
    norm_num
  · rw [Set.indicator_of_notMem hx]
    norm_num

omit [NeZero d] in
theorem cubeSetAtOneDatum_of_mem {y : Vec d} {n : ℤ} {x : Vec d}
    (hx : x ∈ cubeSetAt y n) : cubeSetAtOneDatum y n x = 1 :=
  Set.indicator_of_mem hx _

omit [NeZero d] in
theorem cubeSetAtOneDatum_ae_indicator (y : Vec d) (n : ℤ) :
    cubeSetAtOneDatum y n =ᵐ[volume]
      (cubeSetAt y n).indicator (cubeSetAtOneDatum y n) := by
  refine Filter.Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ cubeSetAt y n
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, cubeSetAtOneDatum,
      Set.indicator_of_notMem hx]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- **The barrier data of the exit-time problem on a translated triadic
cube.**  The part domain is `cubeSetAt y n` itself and the observable is the
constant datum on it. -/
def cubeSetAtOneBarrierData (y : Vec d) (n : ℤ) (lam : PositiveShift) :
    WholeSpaceBarrierData A :=
  eqAxisCubeBarrierData A (isOpenBoundedConvexDomain_cubeSetAt y n)
    (fun i => y i - (3 : ℝ) ^ n / 2) (zpow_pos (by norm_num) n)
    (cubeSetAt_eq_axisCube y n) lam (measurable_cubeSetAtOneDatum y n)
    (cubeSetAtOneDatum_nonneg y n) (abs_cubeSetAtOneDatum_le y n)
    (cubeSetAtOneDatum_ae_indicator y n)

@[simp] theorem cubeSetAtOneBarrierData_V (y : Vec d) (n : ℤ)
    (lam : PositiveShift) :
    (A.cubeSetAtOneBarrierData y n lam).V = cubeSetAt y n := rfl

@[simp] theorem cubeSetAtOneBarrierData_f (y : Vec d) (n : ℤ)
    (lam : PositiveShift) :
    (A.cubeSetAtOneBarrierData y n lam).f = cubeSetAtOneDatum y n := rfl

@[simp] theorem cubeSetAtOneBarrierData_lam (y : Vec d) (n : ℤ)
    (lam : PositiveShift) :
    (A.cubeSetAtOneBarrierData y n lam).lam = lam := rfl

/-- **The Dirichlet resolvent of the constant datum on a translated triadic
cube**, in its continuous zero extension to the whole space. -/
def cubeSetAtOneResolvent (y : Vec d) (n : ℤ) (lam : PositiveShift) :
    Vec d → ℝ :=
  (A.cubeSetAtOneBarrierData y n lam).utilde

theorem continuous_cubeSetAtOneResolvent (y : Vec d) (n : ℤ)
    (lam : PositiveShift) : Continuous (A.cubeSetAtOneResolvent y n lam) :=
  (A.cubeSetAtOneBarrierData y n lam).hutildeCont

/-- **The Dirichlet resolvent of the constant datum on a translated triadic
cube represents the shifted part solution.**  This is the characterization the
continuous zero extension is named by. -/
theorem cubeSetAtOneResolvent_ae (y : Vec d) (n : ℤ) (lam : PositiveShift) :
    A.cubeSetAtOneResolvent y n lam =ᵐ[volumeMeasureOn (cubeSetAt y n)]
      ZeroTraceSobolev.toL2
        (alphaShiftedSolution A.a lam.property A.hnu
          (partEllipticity A (isOpenBoundedConvexDomain_cubeSetAt y n))
          (partDatumL2 (isOpenBoundedConvexDomain_cubeSetAt y n)
            (measurable_cubeSetAtOneDatum y n)
            (abs_cubeSetAtOneDatum_le y n))) :=
  (A.cubeSetAtOneBarrierData y n lam).hutildeRep

/-! ## The expected exit time from a translated triadic cube -/

/-- The Dirichlet resolvent of the constant datum on a translated triadic
cube, transported to the one-point compactification by zero extension.
Outside the positive shifts the value is zero; the identifications below are
stated at positive shifts only. -/
def cubeSetAtExitResolvent (y : Vec d) (n : ℤ) (lam : ℝ) :
    OnePoint (Vec d) → ℝ≥0∞ :=
  if h : 0 < lam then
    PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun w => ENNReal.ofReal (A.cubeSetAtOneResolvent y n ⟨lam, h⟩ w))
  else 0

theorem cubeSetAtExitResolvent_coe (y : Vec d) (n : ℤ) {lam : ℝ}
    (hlam : 0 < lam) (w : Vec d) :
    A.cubeSetAtExitResolvent y n lam (w : OnePoint (Vec d)) =
      ENNReal.ofReal (A.cubeSetAtOneResolvent y n ⟨lam, hlam⟩ w) := by
  rw [cubeSetAtExitResolvent, dite_eq_left hlam,
    PositiveC0ContractiveResolvent.onePointLiveExtension_coe]

/-- **The limit of the Dirichlet resolvents of the constant datum on a
translated triadic cube as the shift decreases to zero**, taken as the
supremum along the shifts `1 / (m + 1)`.  This is the shape in which the
expected exit time consumes the limit. -/
def cubeSetAtExitFunction (y : Vec d) (n : ℤ) : OnePoint (Vec d) → ℝ≥0∞ :=
  fun z => ⨆ m : ℕ, A.cubeSetAtExitResolvent y n ((m : ℝ) + 1)⁻¹ z

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
