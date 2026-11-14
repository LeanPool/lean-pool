/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamExitTime
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamGeneralDomain
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueCubeSetAtProcess

/-!
# CruxStreamMeanValueCubeSetAt

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The exit decomposition on a translated triadic cube for the stream field

The exit decomposition of `ExitMeanValueCubeSetAtProcess.lean` carries a global small-contrast
datum, because the crux equality it invokes does.  The stream field of the model supplies no such
datum, and the coefficient-generic `C₀` barrier comparison replaces it.  This file is the
small-contrast-free copy of that decomposition on `cubeSetAt y n`: the same four statements, with
the small-contrast datum removed from every hypothesis list and the analytic data fixed to the
stream field of the model.

The assumptions are those of the coefficient-generic comparison: the resolvent carrying the
process, its one-point regularity data, conservativity of the live kernel semigroup, the
bounded-measurable identification of the kernel resolvent with the analytic minimal resolvent,
and the operator identification against the `C₀` barrier resolvent of the stream field.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable {M : ABKModel d} {omega : FullSample d M.gamma}
  (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
  (hcons : R.kernelSemigroup.IsConservative)
  (hid : (streamWholeSpaceAnalyticData M omega).KernelResolventIdentifiesAnalyticMinimal R)
  (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
    R.toContractiveResolvent.operator mu g =
      ((streamWholeSpaceC0BarrierData M omega).resolvent).toContractiveResolvent.operator mu g)

include hcons hid hT in
/-- **The killed resolvent of a continuous datum on a translated triadic cube for the stream
field.**  No small-contrast datum appears. -/
theorem killedResolvent_eq_cubeSetAtC0Resolvent_stream (y : Vec d) (n : ℤ) {lam : ℝ}
    (hlam : 0 < lam) (g : C₀(Vec d, ℝ)) (hg0 : ∀ z, 0 ≤ g z) {x : Vec d}
    (hx : x ∈ cubeSetAt y n) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
        (OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n)) lam
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun z => ENNReal.ofReal (g z))) (x : OnePoint (Vec d)) =
      ENNReal.ofReal ((streamWholeSpaceAnalyticData M omega).cubeSetAtC0Resolvent y n g lam x) := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  set P : WholeSpaceBarrierData A := A.cubeSetAtC0BarrierData y n ⟨lam, hlam⟩ g hg0
    with hPdef
  have hcrux := P.killedResolvent_eq_partResolvent_stream_general R hreg hcons hid hT hx
  have hcrux' : IsConservative.killedResolvent R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      (OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n)) lam
      (PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun z => ENNReal.ofReal (P.f z))) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (P.utilde x) := by
    simpa only [P, cubeSetAtC0BarrierData_V, cubeSetAtC0BarrierData_lam] using hcrux
  have hobs : ∀ z ∈ ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n,
      PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun w => ENNReal.ofReal (g w)) z =
        PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun w => ENNReal.ofReal (P.f w)) z := by
    rintro _ ⟨w, hw, rfl⟩
    rw [PositiveC0ContractiveResolvent.onePointLiveExtension_coe,
      PositiveC0ContractiveResolvent.onePointLiveExtension_coe]
    exact congrArg ENNReal.ofReal (cubeSetAtC0Datum_of_mem g hw).symm
  refine ((killedResolvent_congr_of_eqOn _ _ _ _ lam hobs
    (x : OnePoint (Vec d))).trans hcrux').trans ?_
  exact congrArg ENNReal.ofReal
    ((A.eq_partC0Resolvent_of_isRepresentative (isOpenBoundedConvexDomain_cubeSetAt y n)
      ⟨lam, hlam⟩ (measurable_cubeSetAtC0Datum y n g) (abs_cubeSetAtC0Datum_le y n g)
      P.hutildeCont P.hutildeRep hx).trans
      (A.cubeSetAtC0Resolvent_of_pos y n g hlam x).symm)

include hcons hid hT in
/-- **The exit decomposition at a positive shift on a translated triadic cube for the stream
field.** -/
theorem operator_eq_cubeSetAtC0Resolvent_add_discountedExitAverage_stream
    (y : Vec d) (n : ℤ) {lam : ℝ} (hlam : 0 < lam) (g : C₀(Vec d, ℝ))
    (hg0 : ∀ z, 0 ≤ g z) {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    R.toContractiveResolvent.operator ⟨lam, hlam⟩ g x =
      (streamWholeSpaceAnalyticData M omega).cubeSetAtC0Resolvent y n g lam x +
        discountedExitAverage R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) lam
          (onePointRealExtension
            (fun z => R.toContractiveResolvent.operator ⟨lam, hlam⟩ g z))
          (x : OnePoint (Vec d)) := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  set U : Set (OnePoint (Vec d)) :=
    ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n with hUdef
  have hUopen : IsOpen U := OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n)
  set q : Vec d → ℝ := fun z => R.toContractiveResolvent.operator ⟨lam, hlam⟩ g z with hqdef
  have hq0 : ∀ z, 0 ≤ q z := fun z => R.isPositive ⟨lam, hlam⟩ g hg0 z
  have hqmeas : Measurable q :=
    (R.toContractiveResolvent.operator ⟨lam, hlam⟩ g).continuous.measurable
  have hqbd : ∀ z, |q z| ≤ ‖R.toContractiveResolvent.operator ⟨lam, hlam⟩ g‖ :=
    abs_apply_le_norm_zeroAtInfty _
  have hgmeas : Measurable fun z : Vec d => ENNReal.ofReal (g z) :=
    ENNReal.measurable_ofReal.comp g.continuous.measurable
  have hlive : Measurable (PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun z => ENNReal.ofReal (g z))) :=
    PositiveC0ContractiveResolvent.measurable_onePointLiveExtension hgmeas
  have hres : ∀ z : OnePoint (Vec d),
      (∫⁻ path, ContinuousPath.pathResolvent lam
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun w => ENNReal.ofReal (g w))) path
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup z)) =
        (fun z => ENNReal.ofReal (onePointRealExtension q z)) z := by
    intro z
    rw [ofReal_onePointRealExtension_eq_onePointLiveExtension q]
    exact lintegral_pathResolvent_c0 R hreg ⟨lam, hlam⟩ g hg0 z
  have hdecomp := eq_killedResolvent_add_lintegralDiscountedExit
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    R.isFellerKernelSemigroup_onePointKernelSemigroup hreg.kolmogorovRegular
    hUopen lam hlive hres (x : OnePoint (Vec d))
  have hkilled : IsConservative.killedResolvent R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup U hUopen lam
      (PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun z => ENNReal.ofReal (g z))) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (A.cubeSetAtC0Resolvent y n g lam x) :=
    killedResolvent_eq_cubeSetAtC0Resolvent_stream R hreg hcons hid hT y n hlam g hg0 hx
  have hfin : lintegralDiscountedExit R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup U lam
      (fun z => ENNReal.ofReal (onePointRealExtension q z)) (x : OnePoint (Vec d)) ≠ ⊤ := by
    refine lintegralDiscountedExit_ne_top R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup hlam.le
      (C := ENNReal.ofReal ‖R.toContractiveResolvent.operator ⟨lam, hlam⟩ g‖)
      ENNReal.ofReal_ne_top (fun z => ?_) _
    refine ENNReal.ofReal_le_ofReal ?_
    exact (le_abs_self _).trans (abs_onePointRealExtension_le (norm_nonneg _) hqbd z)
  have htoReal := congrArg ENNReal.toReal hdecomp
  rw [hkilled, ENNReal.toReal_add ENNReal.ofReal_ne_top hfin,
    ENNReal.toReal_ofReal (A.cubeSetAtC0Resolvent_nonneg y n hg0 lam x),
    toReal_lintegralDiscountedExit R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup hUopen lam
      (measurable_onePointRealExtension hqmeas)
      (onePointRealExtension_nonneg hq0),
    onePointRealExtension_coe, ENNReal.toReal_ofReal (hq0 x)] at htoReal
  exact htoReal

include hcons hid hT in
/-- **The discounted exit average of a resolvent datum on a translated triadic cube for the
stream field.** -/
theorem discountedExitAverage_eq_sub_add_cubeSetAt_stream
    (y : Vec d) (n : ℤ) (mu : PositiveShift) (g : C₀(Vec d, ℝ)) (hg0 : ∀ z, 0 ≤ g z)
    {lam : ℝ} (hlam : 0 < lam) {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    discountedExitAverage R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) lam
        (onePointRealExtension (fun z => R.toContractiveResolvent.operator mu g z))
        (x : OnePoint (Vec d)) =
      R.toContractiveResolvent.operator mu g x -
        (streamWholeSpaceAnalyticData M omega).cubeSetAtC0Resolvent y n g lam x +
        ((mu : ℝ) - lam) * (streamWholeSpaceAnalyticData M omega).cubeSetAtC0Resolvent y n
          (R.toContractiveResolvent.operator mu g) lam x := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  set U : Set (OnePoint (Vec d)) :=
    ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n with hUdef
  have hUopen : IsOpen U := OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n)
  set psi : C₀(Vec d, ℝ) := R.toContractiveResolvent.operator mu g with hpsidef
  have hpsi0 : ∀ z, 0 ≤ psi z := R.isPositive mu g hg0
  have hident : ∀ z, R.toContractiveResolvent.operator ⟨lam, hlam⟩ g z =
      psi z + ((mu : ℝ) - lam) * R.toContractiveResolvent.operator ⟨lam, hlam⟩ psi z := by
    intro z
    have h := DFunLike.congr_fun
      (R.toContractiveResolvent.resolvent_identity ⟨lam, hlam⟩ mu) g
    have hz := congrArg (fun f : C₀(Vec d, ℝ) => f z) h
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply,
      ZeroAtInftyContinuousMap.coe_sub, ZeroAtInftyContinuousMap.coe_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hz
    linarith only [hz]
  set p1 : OnePoint (Vec d) → ℝ := onePointRealExtension (fun z => psi z) with hp1def
  set p2 : OnePoint (Vec d) → ℝ := onePointRealExtension
    (fun z => R.toContractiveResolvent.operator ⟨lam, hlam⟩ psi z) with hp2def
  have hp1meas : Measurable p1 :=
    measurable_onePointRealExtension psi.continuous.measurable
  have hp2meas : Measurable p2 :=
    measurable_onePointRealExtension
      (R.toContractiveResolvent.operator ⟨lam, hlam⟩ psi).continuous.measurable
  have hp1bd : ∀ z, ‖p1 z‖ ≤ ‖psi‖ := fun z => by
    rw [Real.norm_eq_abs]
    exact abs_onePointRealExtension_le (norm_nonneg _) (abs_apply_le_norm_zeroAtInfty psi) z
  have hp2bd : ∀ z, ‖p2 z‖ ≤ ‖R.toContractiveResolvent.operator ⟨lam, hlam⟩ psi‖ := fun z => by
    rw [Real.norm_eq_abs]
    exact abs_onePointRealExtension_le (norm_nonneg _) (abs_apply_le_norm_zeroAtInfty _) z
  have hfun : onePointRealExtension
      (fun z => R.toContractiveResolvent.operator ⟨lam, hlam⟩ g z) =
      fun z => p1 z + ((mu : ℝ) - lam) * p2 z := by
    funext z
    rw [hp1def, hp2def]
    induction z using OnePoint.rec with
    | infty =>
      rw [onePointRealExtension_infty, onePointRealExtension_infty,
        onePointRealExtension_infty, mul_zero, add_zero]
    | coe w =>
      rw [onePointRealExtension_coe, onePointRealExtension_coe,
        onePointRealExtension_coe]
      exact hident w
  have hstep1 : R.toContractiveResolvent.operator ⟨lam, hlam⟩ g x =
      A.cubeSetAtC0Resolvent y n g lam x +
        discountedExitAverage R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup U lam
          (fun z => p1 z + ((mu : ℝ) - lam) * p2 z) (x : OnePoint (Vec d)) := by
    rw [← hfun]
    exact operator_eq_cubeSetAtC0Resolvent_add_discountedExitAverage_stream R hreg hcons hid
      hT y n hlam g hg0 hx
  have hstep2 : R.toContractiveResolvent.operator ⟨lam, hlam⟩ psi x =
      A.cubeSetAtC0Resolvent y n psi lam x +
        discountedExitAverage R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup U lam p2 (x : OnePoint (Vec d)) :=
    operator_eq_cubeSetAtC0Resolvent_add_discountedExitAverage_stream R hreg hcons hid hT
      y n hlam psi hpsi0 hx
  have hlin := discountedExitAverage_add_const_mul R.onePointKernelSemigroup
    R.isConservative_onePointKernelSemigroup hUopen lam hlam.le hp1meas hp2meas
    hp1bd hp2bd ((mu : ℝ) - lam) (x : OnePoint (Vec d))
  rw [hlin] at hstep1
  have hidentx := hident x
  have hkey : A.cubeSetAtC0Resolvent y n g lam x +
      (discountedExitAverage R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup U lam p1 (x : OnePoint (Vec d)) +
        ((mu : ℝ) - lam) * discountedExitAverage R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup U lam p2 (x : OnePoint (Vec d))) =
      psi x + ((mu : ℝ) - lam) * (A.cubeSetAtC0Resolvent y n psi lam x +
        discountedExitAverage R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup U lam p2 (x : OnePoint (Vec d))) := by
    rw [← hstep1, hidentx, hstep2]
  rw [mul_add] at hkey
  linarith only [hkey]

include hcons hid hT in
/-- **The harmonic part of a stream resolvent datum on a translated triadic cube is represented
by the exit distribution.** -/
theorem hasExitMeanValueOn_of_isCubeSetAtResolventHarmonicPart_stream
    (y : Vec d) (n : ℤ) (mu : PositiveShift) (g : C₀(Vec d, ℝ)) (hg0 : ∀ z, 0 ≤ g z)
    {h : Vec d → ℝ}
    (hh : (streamWholeSpaceAnalyticData M omega).IsCubeSetAtResolventHarmonicPart R y n mu g h)
    (hwfin : letI := hreg.metricSpace
      letI := hreg.completeSpace
      ∀ z ∈ cubeSetAt y n,
        expectedExitTime R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
          (z : OnePoint (Vec d)) ≠ ⊤) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    HasExitMeanValueOn R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      (onePointRealExtension h) := by
  let A := streamWholeSpaceAnalyticData M omega
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  set U : Set (OnePoint (Vec d)) :=
    ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n with hUdef
  have hUopen : IsOpen U := OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n)
  set psi : C₀(Vec d, ℝ) := R.toContractiveResolvent.operator mu g with hpsidef
  have hnotMem : ∀ z : Vec d, (z : OnePoint (Vec d)) ∉ U → z ∉ cubeSetAt y n := by
    intro z hz hmem
    exact hz (Set.mem_image_of_mem _ hmem)
  refine hasExitMeanValueOn_of_tendsto_discountedExitAverage
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    hreg.kolmogorovRegular hUopen
    (measurable_onePointRealExtension psi.continuous.measurable)
    (M := ‖psi‖) (fun z => by
      rw [Real.norm_eq_abs]
      exact abs_onePointRealExtension_le (norm_nonneg _)
        (abs_apply_le_norm_zeroAtInfty psi) z)
    ?_ mu.property
    (fun lam => onePointRealExtension (fun z => psi z - A.cubeSetAtC0Resolvent y n g lam z +
      ((mu : ℝ) - lam) * A.cubeSetAtC0Resolvent y n psi lam z)) ?_ ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hwfin z hz
  · rintro lam hlam _ ⟨z, hz, rfl⟩
    simp only [onePointRealExtension_coe]
    exact discountedExitAverage_eq_sub_add_cubeSetAt_stream R hreg hcons hid hT y n mu g hg0
      hlam.1 hz
  · intro z hz
    induction z using OnePoint.rec with
    | infty => rw [onePointRealExtension_infty, onePointRealExtension_infty]
    | coe w =>
      rw [onePointRealExtension_coe, onePointRealExtension_coe]
      exact hh.1 w (hnotMem w hz)
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [onePointRealExtension_coe] using hh.2 z hz

include hcons hid hT in
/-- **The expected exit time from a translated triadic cube is finite for the stream-field
process.** -/
theorem expectedExitTime_cubeSetAt_ne_top_stream (y : Vec d) (n : ℤ) {x : Vec d}
    (hx : x ∈ cubeSetAt y n) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    expectedExitTime R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (x : OnePoint (Vec d)) ≠ ⊤ := by
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  set v : ℕ := partCubeIndex (isOpenBoundedConvexDomain_cubeSetAt y n) with hvdef
  have hsub : cubeSetAt y n ⊆ wholeSpaceCube d v :=
    subset_wholeSpaceCube_partCubeIndex (isOpenBoundedConvexDomain_cubeSetAt y n)
  have himage : ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n ⊆
      ((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v := Set.image_mono hsub
  have hmono : expectedExitTime R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (x : OnePoint (Vec d)) ≤
      ∫⁻ path, ContinuousPath.exitTime
        (((↑) : Vec d → OnePoint (Vec d)) '' wholeSpaceCube d v) path
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint (Vec d))) := by
    refine lintegral_mono fun path => ?_
    exact ContinuousPath.exitTime_mono himage path
  exact ne_top_of_le_ne_top
    (lintegral_exitTime_lt_top_stream R hreg hcons hid hT v (hsub hx)).ne hmono

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
