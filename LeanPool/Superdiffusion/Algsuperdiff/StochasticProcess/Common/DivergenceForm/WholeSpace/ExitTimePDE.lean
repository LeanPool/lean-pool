/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveCubeData
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointKilled

/-!
# ExitTimePDE

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Dirichlet resolvent of the constant datum on an exhaustion cube

The exit-time problem on a bounded domain `V` is the Dirichlet problem with
constant forcing,
  `-div (a grad w) = 1` in `V`,  `w = 0` on the boundary of `V`,

and its shifted approximations are the Dirichlet resolvents `R^V_lam 1` at the
positive shifts `lam`.  This file assembles those approximations for the
exhaustion cubes `V = wholeSpaceCube d v` and records their behaviour as the
shift decreases to zero.

The Dirichlet resolvent of a nonnegative datum is antitone in the shift: a
larger shift discounts more, and the resolvent identity of the analytic layer
converts this into an inequality between the two values.  The transported
family `cubeExitResolvent` therefore increases as the shift decreases, and its
supremum along the shifts `1 / (n + 1)`, namely `cubeExitFunction`, is the
candidate for the exit-time function.

The regularity witness for the values used here is explicit: on its cube the
Dirichlet resolvent of the constant datum is continuous, which is what makes the pointwise
statements independent of the choice of representative.

Everything in this file is analytic; no process, and no hypothesis about one,
appears.  The identification of `cubeExitFunction` with an expected exit time
is proved separately.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The constant datum on an exhaustion cube -/

/-- The datum of the exit-time problem on an exhaustion cube: the constant one
on the cube, extended by zero. -/
def cubeOneDatum (d v : ℕ) : Vec d → ℝ :=
  (wholeSpaceCube d v).indicator (fun _ => 1)

theorem measurable_cubeOneDatum (d v : ℕ) : Measurable (cubeOneDatum d v) :=
  measurable_const.indicator
    (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen.measurableSet

theorem cubeOneDatum_nonneg (d v : ℕ) (x : Vec d) : 0 ≤ cubeOneDatum d v x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem abs_cubeOneDatum_le (d v : ℕ) (x : Vec d) : |cubeOneDatum d v x| ≤ 1 := by
  unfold cubeOneDatum
  by_cases hx : x ∈ wholeSpaceCube d v
  · rw [Set.indicator_of_mem hx]
    norm_num
  · rw [Set.indicator_of_notMem hx]
    norm_num

theorem cubeOneDatum_of_mem {d v : ℕ} {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    cubeOneDatum d v x = 1 :=
  Set.indicator_of_mem hx _

theorem cubeOneDatum_ae_indicator (d v : ℕ) :
    cubeOneDatum d v =ᵐ[volume] (wholeSpaceCube d v).indicator (cubeOneDatum d v) := by
  refine Filter.Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ wholeSpaceCube d v
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, cubeOneDatum, Set.indicator_of_notMem hx]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- **The barrier data of the exit-time problem.**  The part domain is an
exhaustion cube and the observable is the constant datum on it; every field is
discharged by the axis-cube construction. -/
def cubeOneBarrierData (v : ℕ) (lam : PositiveShift) : WholeSpaceBarrierData A :=
  axisCubeBarrierData A (fun _ => -((3 : ℝ) ^ v)) (by positivity) lam
    (measurable_cubeOneDatum d v) (cubeOneDatum_nonneg d v)
    (abs_cubeOneDatum_le d v) (cubeOneDatum_ae_indicator d v)

@[simp] theorem cubeOneBarrierData_V (v : ℕ) (lam : PositiveShift) :
    (A.cubeOneBarrierData v lam).V = wholeSpaceCube d v := rfl

@[simp] theorem cubeOneBarrierData_f (v : ℕ) (lam : PositiveShift) :
    (A.cubeOneBarrierData v lam).f = cubeOneDatum d v := rfl

@[simp] theorem cubeOneBarrierData_lam (v : ℕ) (lam : PositiveShift) :
    (A.cubeOneBarrierData v lam).lam = lam := rfl

/-! ## The shifted family on the compactification and its limit -/

/-- The Dirichlet resolvent of the constant datum on an exhaustion cube,
transported to the one-point compactification by zero extension.  Outside the
positive shifts the value is zero; the identifications below are stated at
positive shifts only. -/
def cubeExitResolvent (v : ℕ) (lam : ℝ) : OnePoint (Vec d) → ℝ≥0∞ :=
  if h : 0 < lam then
    PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun y => ENNReal.ofReal (A.analyticCubeResolvent ⟨lam, h⟩ (cubeOneDatum d v)
        (measurable_cubeOneDatum d v) (abs_cubeOneDatum_le d v) v y))
  else 0

theorem cubeExitResolvent_coe (v : ℕ) {lam : ℝ} (hlam : 0 < lam) (y : Vec d) :
    A.cubeExitResolvent v lam (y : OnePoint (Vec d)) =
      ENNReal.ofReal (A.analyticCubeResolvent ⟨lam, hlam⟩ (cubeOneDatum d v)
        (measurable_cubeOneDatum d v) (abs_cubeOneDatum_le d v) v y) := by
  rw [cubeExitResolvent, dite_eq_left hlam,
    PositiveC0ContractiveResolvent.onePointLiveExtension_coe]

/-- **The limit of the Dirichlet resolvents of the constant datum as the shift
decreases to zero**, taken as the supremum along the shifts `1 / (n + 1)`.
This is the shape in which the expected exit time consumes the limit. -/
def cubeExitFunction (v : ℕ) : OnePoint (Vec d) → ℝ≥0∞ :=
  fun z => ⨆ n : ℕ, A.cubeExitResolvent v ((n : ℝ) + 1)⁻¹ z

/-- The limit read on the live space: the supremum of the values of the
Dirichlet resolvents of the constant datum at the shifts `1 / (n + 1)`. -/
theorem cubeExitFunction_coe (v : ℕ) (y : Vec d) :
    A.cubeExitFunction v (y : OnePoint (Vec d)) =
      ⨆ n : ℕ, ENNReal.ofReal (A.analyticCubeResolvent
        ⟨((n : ℝ) + 1)⁻¹, Set.mem_Ioi.mpr (by positivity)⟩ (cubeOneDatum d v)
        (measurable_cubeOneDatum d v) (abs_cubeOneDatum_le d v) v y) :=
  iSup_congr fun n => A.cubeExitResolvent_coe v (by positivity) y

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
