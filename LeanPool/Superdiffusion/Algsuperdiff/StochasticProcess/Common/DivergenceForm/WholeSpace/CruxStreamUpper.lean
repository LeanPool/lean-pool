/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamInterchange
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxUpperProcess

/-!
# CruxStreamUpper

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Process upper comparison for the stream field

This module propagates the localized split-skew penalization interchange to
the process killed resolvent.  It is an S-free successor under distinct names;
the existing small-contrast declarations remain unchanged.
-/

namespace DivergenceFormProcess.Form

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field
open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup ProbabilityTheory
open MarkovProcess.SubMarkovKernelSemigroup WholeSpaceAnalyticData
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The stream penalization interchange read through an equality identifying
the part domain with an exhaustion cube. -/
theorem iInf_toReal_streamAnalyticPenalizedResolvent_le_analyticCubeResolvent
    (M : ABKModel d) (omega : FullSample d M.gamma)
    {V : Set (Vec d)} (hV : IsOpen V) (lam : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hD : 0 < D) (hfD : ∀ y, |f y| ≤ D)
    (v : ℕ) (hVcube : V = wholeSpaceCube d v)
    (hsupp : ∀ᵐ y ∂volume, y ∉ wholeSpaceCube d v → f y = 0)
    {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    (⨅ n : ℕ, ((streamWholeSpaceAnalyticData M omega).analyticPenalizedResolvent
      hV n lam f hf hfD x).toReal) ≤
      (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent
        lam f hf hfD v x := by
  subst hVcube
  exact iInf_toReal_streamAnalyticPenalizedResolvent_le_cube_of_bound
    M omega v lam hf hf0 hD hfD hsupp hx

namespace WholeSpaceBarrierData

variable {M : ABKModel d} {omega : FullSample d M.gamma}
  (P : WholeSpaceBarrierData (streamWholeSpaceAnalyticData M omega))

/-- The stream penalization limit is bounded by the continuous representative
of the part resolvent. -/
theorem iInf_toReal_streamAnalyticPenalizedResolvent_le_utilde
    {D : ℝ} (hD : 0 < D) (hfD : ∀ y, |P.f y| ≤ D)
    (v : ℕ) (hVcube : P.V = wholeSpaceCube d v)
    {x : Vec d} (hx : x ∈ P.V) :
    (⨅ n : ℕ, ((streamWholeSpaceAnalyticData M omega).analyticPenalizedResolvent
      P.hV.isOpen n P.lam P.f P.hf hfD x).toReal) ≤
      P.utilde x := by
  let A := streamWholeSpaceAnalyticData M omega
  have hutilde : P.utilde x = A.analyticCubeResolvent P.lam P.f P.hf hfD v x :=
    eq_analyticCubeResolvent_of_isRepresentative A P.hV P.lam P.hf hfD
      P.hutildeCont P.hutildeRep v hVcube hx
  rw [hutilde]
  have hsupp : ∀ᵐ y ∂volume, y ∉ wholeSpaceCube d v → P.f y = 0 := by
    filter_upwards [P.hfV] with y hy hynot
    rw [hVcube] at hy
    rw [hy, Set.indicator_of_notMem hynot]
  have hxcube : x ∈ wholeSpaceCube d v := hVcube ▸ hx
  exact iInf_toReal_streamAnalyticPenalizedResolvent_le_analyticCubeResolvent
    M omega P.hV.isOpen P.lam P.hf P.hf0 hD hfD v hVcube hsupp hxcube

/-- **S-free upper stream-process comparison.**  The killed resolvent of any
identified conservative C0 process is bounded by the part resolvent.  The
analytic input is the localized split-skew fixed-collar estimate. -/
theorem killedResolvent_le_partResolvent_stream
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : WholeSpaceAnalyticData.KernelResolventIdentifiesAnalyticMinimal
      (streamWholeSpaceAnalyticData M omega) R)
    (v : ℕ) (hVcube : P.V = wholeSpaceCube d v)
    {x : Vec d} (hx : x ∈ P.V) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
        (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) ≤
      ENNReal.ofReal (P.utilde x) := by
  have hD : (0 : ℝ) < max P.D 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hfD : ∀ y, |P.f y| ≤ max P.D 1 := fun y =>
    (P.hfD y).trans (le_max_left _ _)
  exact P.killedResolvent_le_ofReal_of_iInf_le R hreg hcons hid hD.le hfD
    (P.iInf_toReal_streamAnalyticPenalizedResolvent_le_utilde
      hD hfD v hVcube hx)

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
