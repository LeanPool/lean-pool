/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointKilled
public import LeanPool.Superdiffusion.Algsuperdiff.Process.Kernel.ResolventTail

/-!
# OnePointExhaustionTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Exhaustion-metric resolvent tails from amplified live tails

The resolvent tail decay a compactified semigroup needs is stated in the metric an exhaustion
function determines on the one-point compactification, while the analysis produces tail decay in
the metric of the live space.  This file converts the second into the first.

The conversion is a set inclusion.  The complement of the exhaustion-metric ball of radius `r`
about a live point `x` meets the live space in points that are simultaneously at live distance at
least `r` from `x` and at exhaustion level at least `r - rho x`
(`OnePoint.coe_preimage_compl_ball_subset`).  Both constraints are available at once, so the tail
set is contained in the complement of the live ball of any *amplified* radius `amp x r` the two
constraints force.  Where the exhaustion function is small the amplification is large: a starting
point deep in a tail of the space must be displaced far in the live metric before its exhaustion
level can rise.  Under conservativity the compactified potential of the tail set about a live
point is the live potential of its live preimage, and about the added point it vanishes, so the
amplified live tail estimate is exactly what the compactified tail decay asks for
(`PositiveC0ContractiveResolvent.hasResolventTail_onePoint_of_amplified`).

Taking `amp x r = r` recovers the plain transport of a live tail, since the exhaustion metric is
bounded by the live metric.  No analytic estimate is asserted here: the live tail bound and the
amplification are the consumer's hypotheses.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace Algsuperdiff.Process.OnePoint

open _root_.OnePoint

variable {X : Type*} [MetricSpace X]

/-- The live part of an exhaustion-metric tail about a live point is Euclidean-far and lies in a
compact superlevel set of the exhaustion function. -/
theorem coe_preimage_compl_ball_subset (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) (x : X) (r : ℝ) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    ((↑) : X → OnePoint X) ⁻¹' (Metric.ball (x : OnePoint X) r)ᶜ ⊆
      {z : X | r ≤ dist z x} ∩ {z : X | r - rho x ≤ rho z} := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  intro z hz
  have hdist : r ≤ min (dist z x) (rho z + rho x) := by
    have hz' : r ≤ dist (z : OnePoint X) (x : OnePoint X) := by
      simpa only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_ball, not_lt] using hz
    rwa [OnePoint.exhaustionMetricSpace_dist_coe_coe rho hrho_cont hrho_pos hrho_lipschitz
      hrho_compact z x] at hz'
  refine ⟨le_trans hdist (min_le_left _ _), ?_⟩
  show r - rho x ≤ rho z
  linarith only [le_trans hdist (min_le_right _ _)]

end Algsuperdiff.Process.OnePoint

open MarkovProcess

namespace Algsuperdiff.Process.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.PositiveC0ContractiveResolvent

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Exhaustion-metric resolvent tails from amplified Euclidean tails.**  Under conservativity the
compactified potential of an exhaustion tail of radius `r` about a live point is dominated by the
live potential of the Euclidean tail of the amplified radius `amp x r`; about the added point it
vanishes. -/
theorem hasResolventTail_onePoint_of_amplified (R : PositiveC0ContractiveResolvent X)
    (hcons : R.kernelSemigroup.IsConservative)
    (rho : X → ℝ) (hrho_cont : Continuous rho) (hrho_pos : ∀ x, 0 < rho x)
    (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    {lam : ℝ} {phi : ℝ → ℝ}
    (amp : X → ℝ → ℝ)
    (hamp_le : ∀ (x : X) (r : ℝ), ∀ z : X,
      r ≤ dist z x → r - rho x ≤ rho z → amp x r ≤ dist z x)
    (hlive : ∀ (x : X) (r : ℝ), 0 < r →
      ENNReal.ofReal lam *
          R.kernelSemigroup.resolventPotential lam x (Metric.ball x (amp x r))ᶜ ≤
        ENNReal.ofReal (phi (Real.sqrt lam * r))) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    Algsuperdiff.Process.SubMarkovKernelSemigroup.HasResolventTail R.onePointKernelSemigroup lam phi := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  intro z r hr
  induction z using OnePoint.rec with
  | infty =>
      -- the added point is absorbing, so the tail carries no potential mass at all
      let tail := (Metric.ball (OnePoint.infty : OnePoint X) r)ᶜ
      have htail : MeasurableSet tail := Metric.isOpen_ball.measurableSet.compl
      have hinfty : OnePoint.infty ∉ tail := fun hz ↦ hz (Metric.mem_ball_self hr)
      have hset : R.onePointKernelSemigroup.kernelResolvent lam
          (tail.indicator 1) OnePoint.infty =
          R.onePointKernelSemigroup.resolventPotential lam OnePoint.infty tail := by
        rw [← R.onePointKernelSemigroup.lintegral_resolventPotential
          lam (measurable_one.indicator htail) OnePoint.infty,
          lintegral_indicator_one htail]
      rw [← hset, SubMarkovKernelSemigroup.kernelResolvent]
      simp only [R.onePointKernelSemigroup_absorbing, lintegral_dirac,
        Set.indicator_of_notMem hinfty, mul_zero, lintegral_zero, zero_le]
  | coe x =>
      let tailOne := (Metric.ball (x : OnePoint X) r)ᶜ
      let tailLive := (Metric.ball x (amp x r))ᶜ
      have htailOne : MeasurableSet tailOne := Metric.isOpen_ball.measurableSet.compl
      have htailLive : MeasurableSet tailLive := Metric.isOpen_ball.measurableSet.compl
      -- the live part of the compactified tail lies beyond the amplified radius
      have hsubset : ((↑) : X → OnePoint X) ⁻¹' tailOne ⊆ tailLive := by
        intro y hy
        obtain ⟨hfar, hlevel⟩ :=
          OnePoint.coe_preimage_compl_ball_subset rho hrho_cont hrho_pos hrho_lipschitz
            hrho_compact x r hy
        simpa only [tailLive, Set.mem_compl_iff, Metric.mem_ball, not_lt] using
          hamp_le x r y hfar hlevel
      have htransition : ∀ t : ℝ,
          R.onePointKernelSemigroup (Real.toNNReal t) (x : OnePoint X) tailOne ≤
            R.kernelSemigroup (Real.toNNReal t) x tailLive := by
        intro t
        rw [R.onePointKernelSemigroup_apply_coe, hcons, tsub_self, zero_smul,
          add_zero, Measure.map_apply OnePoint.continuous_coe.measurable htailOne]
        exact measure_mono hsubset
      have hkernel : R.onePointKernelSemigroup.kernelResolvent lam
          (tailOne.indicator 1) (x : OnePoint X) ≤
          R.kernelSemigroup.kernelResolvent lam (tailLive.indicator 1) x := by
        unfold SubMarkovKernelSemigroup.kernelResolvent
        refine setLIntegral_mono' measurableSet_Ioi fun t _ht ↦ ?_
        apply mul_le_mul' le_rfl
        rw [lintegral_indicator_one htailOne, lintegral_indicator_one htailLive]
        exact htransition t
      have hsetOne : R.onePointKernelSemigroup.kernelResolvent lam
          (tailOne.indicator 1) (x : OnePoint X) =
          R.onePointKernelSemigroup.resolventPotential lam (x : OnePoint X) tailOne := by
        rw [← R.onePointKernelSemigroup.lintegral_resolventPotential
          lam (measurable_one.indicator htailOne) (x : OnePoint X),
          lintegral_indicator_one htailOne]
      have hsetLive : R.kernelSemigroup.kernelResolvent lam (tailLive.indicator 1) x =
          R.kernelSemigroup.resolventPotential lam x tailLive := by
        rw [← R.kernelSemigroup.lintegral_resolventPotential
          lam (measurable_one.indicator htailLive) x,
          lintegral_indicator_one htailLive]
      calc
        ENNReal.ofReal lam *
            R.onePointKernelSemigroup.resolventPotential lam (x : OnePoint X) tailOne =
          ENNReal.ofReal lam *
            R.onePointKernelSemigroup.kernelResolvent lam
              (tailOne.indicator 1) (x : OnePoint X) :=
            congrArg (ENNReal.ofReal lam * ·) hsetOne.symm
        _ ≤ ENNReal.ofReal lam *
            R.kernelSemigroup.kernelResolvent lam (tailLive.indicator 1) x :=
              mul_le_mul' le_rfl hkernel
        _ = ENNReal.ofReal lam * R.kernelSemigroup.resolventPotential lam x tailLive :=
              congrArg (ENNReal.ofReal lam * ·) hsetLive
        _ ≤ ENNReal.ofReal (phi (Real.sqrt lam * r)) := hlive x r hr

end Algsuperdiff.Process.PositiveC0ContractiveResolvent
