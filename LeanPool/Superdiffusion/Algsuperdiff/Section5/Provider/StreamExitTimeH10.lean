/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.LocalizedTailData
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamCube
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEIdentificationCube
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PartGreenH10

/-!
# StreamExitTimeH10

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The expected exit time from a triadic cube as a zero-trace Sobolev function

The corrected observable of the stopped second-moment bound is the weakly harmonic observable
less a multiple of the expected exit time from the cube.  To compare it with the homogenized
datum through the renormalization estimate, the expected exit time has to be read as an `H¹`
function of the cube solving `-∇ · a ∇w = 1` weakly with zero trace, at every point.

The analytic object is the Green potential of the constant datum on the cube: the zero-shift
limit of the Dirichlet resolvents of one, which is bounded, continuous on the cube, vanishes off
it, and has an exact zero-trace representative solving the constant forcing.  The process object
is identified with it through the exit-time identity of the stream chain and the identification
of the exit-time function of the cube with any bounded continuous zero-trace solution of the
constant forcing.

## Main definitions

* `streamExitFunction` — the Green potential of the constant datum on `y + □_n` for the stream
  field.
* `streamExitH10` — its exact zero-trace `H¹` representative.

## Main results

* `isScalarForcedWeakSolution_streamExitH10` — the representative solves `-∇ · a ∇w = 1`.
* `toReal_expectedExitTime_cubeSetAt_eq_stream` — at every point of the compactified state
  space, the expected exit time of the stream process from the cube is the exit function, read
  through the one-point extension.

## References

* ABK26, the localized exit-time problem of Section 5.2 and Step 3 of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The exit function of a triadic cube -/

omit [NeZero d] in
/-- The constant datum of the exit-time problem is bounded by one. -/
theorem abs_one_datum_le (x : Vec d) : |(fun _ : Vec d => (1 : ℝ)) x| ≤ 1 := by
  simp

/-- **The exit function of `y + □_n` for the stream field**: the Green potential of the
constant datum, that is, the zero-shift limit of the Dirichlet resolvents of one on the cube. -/
def streamExitFunction (M : ABKModel d) (omega : FullSample d M.gamma) (y : Vec d) (n : ℤ) :
    Vec d → ℝ :=
  (streamWholeSpaceAnalyticData M omega).partGreenPotential
    (isOpenBoundedConvexDomain_cubeSetAt y n) (fun _ => (1 : ℝ)) measurable_const zero_le_one
    abs_one_datum_le

/-- **The exact zero-trace `H¹` representative of the exit function.** -/
def streamExitH10 (M : ABKModel d) (omega : FullSample d M.gamma) (y : Vec d) (n : ℤ) :
    H10Function (cubeSetAt y n) :=
  (streamWholeSpaceAnalyticData M omega).partGreenH10
    (isOpenBoundedConvexDomain_cubeSetAt y n) (f := fun _ => (1 : ℝ)) measurable_const
    zero_le_one abs_one_datum_le

/-- The coefficient field of the stream analytic data is the stream coefficient. -/
theorem streamWholeSpaceAnalyticData_a (M : ABKModel d) (omega : FullSample d M.gamma) :
    (streamWholeSpaceAnalyticData M omega).a = streamCoefficient M.nu omega := rfl

variable (M : ABKModel d) (omega : FullSample d M.gamma) (y : Vec d) (n : ℤ)

theorem streamExitH10_toFun :
    (streamExitH10 M omega y n).toH1Function.toFun = streamExitFunction M omega y n :=
  (streamWholeSpaceAnalyticData M omega).partGreenH10_toFun
    (isOpenBoundedConvexDomain_cubeSetAt y n) (f := fun _ => (1 : ℝ)) measurable_const
    zero_le_one abs_one_datum_le

/-- The representative solves `-∇ · a ∇w = 1` weakly on the cube. -/
theorem isScalarForcedWeakSolution_streamExitH10 :
    IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData M omega).a (cubeSetAt y n)
      (fun _ => (1 : ℝ)) (streamExitH10 M omega y n).toH1Function :=
  (streamWholeSpaceAnalyticData M omega).isScalarForcedWeakSolution_partGreenH10
    (isOpenBoundedConvexDomain_cubeSetAt y n) (f := fun _ => (1 : ℝ)) measurable_const
    zero_le_one abs_one_datum_le

theorem streamExitFunction_of_notMem {x : Vec d} (hx : x ∉ cubeSetAt y n) :
    streamExitFunction M omega y n x = 0 :=
  (streamWholeSpaceAnalyticData M omega).partGreenPotential_of_notMem
    (isOpenBoundedConvexDomain_cubeSetAt y n) (f := fun _ => (1 : ℝ)) measurable_const
    zero_le_one abs_one_datum_le hx

theorem streamExitFunction_nonneg (x : Vec d) : 0 ≤ streamExitFunction M omega y n x :=
  (streamWholeSpaceAnalyticData M omega).partGreenPotential_nonneg
    (isOpenBoundedConvexDomain_cubeSetAt y n) (f := fun _ => (1 : ℝ)) measurable_const
    (fun _ => zero_le_one) zero_le_one abs_one_datum_le x

theorem abs_streamExitFunction_le (x : Vec d) :
    |streamExitFunction M omega y n x| ≤
      1 * (streamWholeSpaceAnalyticData M omega).partTorsionBound
        (isOpenBoundedConvexDomain_cubeSetAt y n) :=
  (streamWholeSpaceAnalyticData M omega).abs_partGreenPotential_le
    (isOpenBoundedConvexDomain_cubeSetAt y n) (f := fun _ => (1 : ℝ)) measurable_const
    zero_le_one abs_one_datum_le x

theorem continuousOn_streamExitFunction :
    ContinuousOn (streamExitFunction M omega y n) (cubeSetAt y n) :=
  (streamWholeSpaceAnalyticData M omega).continuousOn_partGreenPotential
    (isOpenBoundedConvexDomain_cubeSetAt y n) (f := fun _ => (1 : ℝ)) measurable_const
    zero_le_one abs_one_datum_le

/-! ## 2. The identification with the expected exit time of the stream process -/

section Process

variable {M omega y n}
  (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
  (hcons : R.kernelSemigroup.IsConservative)
  (hid : (streamWholeSpaceAnalyticData M omega
    ).KernelResolventIdentifiesAnalyticMinimal R)
  (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
    R.toContractiveResolvent.operator mu g =
      ((streamWholeSpaceC0BarrierData M omega).resolvent
        ).toContractiveResolvent.operator mu g)

include hcons hid hT in
/-- **The expected exit time from the cube is the exit function**, at every point of the
cube. -/
theorem expectedExitTime_cubeSetAt_eq_streamExitFunction (y : Vec d) (n : ℤ) {x : Vec d}
    (hx : x ∈ cubeSetAt y n) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    expectedExitTime R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (streamExitFunction M omega y n x) := by
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  have hchain := WholeSpaceAnalyticData.lintegral_exitTime_eq_cubeSetAtExitFunction_stream
    (M := M) (omega := omega) R hreg hcons hid hT y n hx
  have hpde := (streamWholeSpaceAnalyticData M omega
    ).cubeSetAtExitFunction_coe_eq_of_isScalarForcedWeakSolution y n (streamExitH10 M omega y n)
    (isScalarForcedWeakSolution_streamExitH10 M omega y n)
    (wRep := streamExitFunction M omega y n)
    (by rw [streamExitH10_toFun])
    (continuousOn_streamExitFunction M omega y n)
    (mul_nonneg zero_le_one ((streamWholeSpaceAnalyticData M omega).partTorsionBound_nonneg _))
    (fun z _ => abs_streamExitFunction_le M omega y n z) hx
  change ∫⁻ path, ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) path
      ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint (Vec d))) = _
  rw [hchain, hpde]

include hcons hid hT in
/-- **The expected exit time from the cube, at every point of the compactified state space.**
At a point of the cube it is the exit function; off the cube, and at infinity, both vanish. -/
theorem toReal_expectedExitTime_cubeSetAt_eq_stream (y : Vec d) (n : ℤ) (z : OnePoint (Vec d)) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    (expectedExitTime R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) z).toReal =
      onePointRealExtension (streamExitFunction M omega y n) z := by
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  induction z using OnePoint.rec with
  | infty =>
    have hzero : expectedExitTime R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) OnePoint.infty = 0 :=
      expectedExitTime_eq_zero_of_notMem _ _ hreg.kolmogorovRegular
        OnePoint.infty_notMem_image_coe
    refine (congrArg ENNReal.toReal hzero).trans ?_
    simp
  | coe x =>
    by_cases hx : x ∈ cubeSetAt y n
    · rw [expectedExitTime_cubeSetAt_eq_streamExitFunction R hreg hcons hid hT y n hx,
        ENNReal.toReal_ofReal (streamExitFunction_nonneg M omega y n x),
        onePointRealExtension_coe]
    · have hx' : (x : OnePoint (Vec d)) ∉ ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n := by
        rintro ⟨w, hw, hwx⟩
        exact hx (OnePoint.coe_injective hwx ▸ hw)
      have hzero : expectedExitTime R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (x : OnePoint (Vec d)) = 0 :=
        expectedExitTime_eq_zero_of_notMem _ _ hreg.kolmogorovRegular hx'
      refine (congrArg ENNReal.toReal hzero).trans ?_
      rw [onePointRealExtension_coe, streamExitFunction_of_notMem M omega y n hx]
      simp

end Process

end

end Algsuperdiff.Section5.Provider
