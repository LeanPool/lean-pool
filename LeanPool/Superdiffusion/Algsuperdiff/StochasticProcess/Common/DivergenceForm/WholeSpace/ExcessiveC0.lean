/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveMinimalMaximum
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Vanishing

/-!
# ExcessiveC0

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The whole-space barrier as a `C₀` function

The observable is bounded, measurable and supported in the bounded part
domain, so it is square integrable and compactly supported.  Continuity of the
barrier then follows from the unconditional local Hölder estimate for the
analytic minimal resolvent, and vanishing at infinity from the analytic tail
estimate together with the compact support of the continuous part solution.

Continuity uses no contrast hypothesis.  Vanishing at infinity is stated under
the contrast datum carried by the tail estimate available for the minimal
resolvent.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Topology
open MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d}

namespace WholeSpaceBarrierData

variable (P : WholeSpaceBarrierData A)


/-- The observable restricted to the part domain is measurable. -/
theorem measurable_indicator_f : Measurable (P.V.indicator P.f) :=
  P.hf.indicator P.hV.isOpen.measurableSet

theorem indicator_f_nonneg (x : Vec d) : 0 ≤ P.V.indicator P.f x :=
  Set.indicator_nonneg (fun y _ => P.hf0 y) x

theorem abs_indicator_f_le (x : Vec d) : |P.V.indicator P.f x| ≤ P.D := by
  classical
  by_cases hx : x ∈ P.V
  · rw [Set.indicator_of_mem hx]
    exact P.hfD x
  · rw [Set.indicator_of_notMem hx, abs_zero]
    exact P.bound_nonneg

theorem memLp_f : MemLp P.f 2 volume := by
  have hind : MemLp (P.V.indicator P.f) 2 volume := by
    rw [memLp_indicator_iff_restrict P.hV.isOpen.measurableSet]
    let := P.hV.isFiniteMeasure_restrict_volume
    refine MemLp.of_bound P.hf.aestronglyMeasurable P.D ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact P.hfD x
  exact (memLp_congr_ae P.hfV).mpr hind

theorem hasCompactSupport_indicator_f : HasCompactSupport (P.V.indicator P.f) := by
  classical
  have hsub : tsupport (P.V.indicator P.f) ⊆ closure P.V :=
    closure_mono fun x hx => by
      by_contra h
      exact hx (Set.indicator_of_notMem h P.f)
  exact IsCompact.of_isClosed_subset
    P.hV.isBoundedDomain.isBounded.isCompact_closure isClosed_closure hsub

theorem hasCompactSupport_utilde : HasCompactSupport P.utilde := by
  have hsub : tsupport P.utilde ⊆ closure P.V :=
    closure_mono fun x hx => by
      by_contra h
      exact hx (P.hutildeOff x h)
  exact IsCompact.of_isClosed_subset
    P.hV.isBoundedDomain.isBounded.isCompact_closure isClosed_closure hsub

/-- **The whole-space barrier is continuous.**  No contrast hypothesis is
used. -/
theorem continuous_barrier : Continuous P.barrier := by
  have h := A.continuous_analyticMinimalResolventReal_of_memLp P.lam P.hf
    P.bound_nonneg P.hfD P.memLp_f
  have hcong : Continuous fun x =>
      (A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x).toReal :=
    h.congr fun x => A.analyticMinimalResolventReal_eq_toReal P.lam P.hf P.hf0
      P.hfD x
  exact hcong.sub P.hutildeCont

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
