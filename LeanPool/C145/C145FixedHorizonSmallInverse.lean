/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145ObservedKernelRecovery
public import LeanPool.C145.C145TimeKernelContinuation

/-!
Fixed-positive-horizon ordinary response jets determine the retained small
finite spectral model under its explicit calibration and positivity hypotheses.
Modal matching and vertex relabelling remain distinct. No general graph
spectral reduction, noisy inverse, or continuum conclusion is asserted.
-/

@[expose] public section

noncomputable section
namespace C145.FixedHorizonSmallInverse
open C145.ActualResponse C145.ObservedKernelRecovery
open scoped BigOperators Topology ContDiff
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

theorem ordinary_C2_jets_determine_small_spectral_model {m n : ℕ} {T : ℝ}
    (hT : 0 < T)
    (μ c0 c1 : ℝ) (hμ : 0 < μ)
    (Q0 : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates0 b0 : Fin (m + 1) → ℝ)
    (rates1 b1 : Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hGround0 : ∀ v, Q0 v 0 = c0)
    (hGround1 : ∀ v, Q1 v 0 = c1)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hRateGround0 : rates0 0 = μ)
    (hRateGround1 : rates1 0 = μ)
    (hAbove0 : ∀ i : Fin m, μ < rates0 i.succ)
    (hAbove1 : ∀ j : Fin n, μ < rates1 j.succ)
    (ha0 : ∀ i, 0 < C145.Pulse.modalOverlap Q0 b0 i)
    (ha1 : ∀ j, 0 < C145.Pulse.modalOverlap Q1 b1 j)
    (hm : m ≤ 4)
    (R0 : Input T → Path m T) (R1 : Input T → Path n T)
    (hR0 : IsActualResponse hT Q0 rates0 b0 R0)
    (hR1 : IsActualResponse hT Q1 rates1 b1 R1)
    (hcR0 : ContDiffAt ℝ 2 R0 0) (hcR1 : ContDiffAt ℝ 2 R1 0)
    (hFirst : ∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
      rawFirst b0 R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT))
    (hMixed : ∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
      rawMixed b0 R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT)) :
    ∃ e : Fin (m + 1) ≃ Fin (n + 1),
      m = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, C145.Pulse.modalOverlap Q1 b1 (e i) =
        C145.Pulse.modalOverlap Q0 b0 i) ∧
      c0 = c1 ∧ (∑ v, b0 v) = (∑ w, b1 w) ∧
      ∃ π : Fin (m + 1) ≃ Fin (n + 1),
        (∀ (w : Fin (n + 1)) (v : Fin (m + 1)),
          (∑ i : Fin (m + 1), Q1 w (e i) * Q0 v i) =
            if w = π v then 1 else 0) ∧
        (∀ (v i : Fin (m + 1)), Q1 (π v) (e i) = Q0 v i) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.spectralGenerator rates0 Q0 v u) ∧
        (∀ v : Fin (m + 1), b1 (π v) = b0 v) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.decayLaplacian μ rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.decayLaplacian μ rates0 Q0 v u) := by
  have hObserved := ordinary_C2_jets_recover_observed_time_kernels hT
    Q0 rates0 b0 Q1 rates1 b1 hQ0 hQ1 R0 R1 hR0 hR1 hcR0 hcR1 hFirst hMixed
  have hAll := C145.TimeKernelContinuation.observed_time_kernels_determine_all_nonnegative_delays
    hT Q0 rates0 b0 Q1 rates1 b1 hObserved.1 hObserved.2
  exact C145.DelayKernel.actual_time_kernel_vertex_identification
    μ c0 c1 hμ Q0 Q1 rates0 b0 rates1 b1 hQ0 hQ1 hGround0 hGround1
    hRates0 hRates1 hRateGround0 hRateGround1 hAbove0 hAbove1 ha0 ha1 hm hAll.1 hAll.2

end C145.FixedHorizonSmallInverse
end

end
