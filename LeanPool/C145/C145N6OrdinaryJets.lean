/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145N6TimeKernels
public import LeanPool.C145.C145ObservedKernelRecovery
public import LeanPool.C145.C145TimeKernelContinuation

/-!
# Ordinary terminal response derivatives for the six-vertex identification.
-/

@[expose] public section
noncomputable section
namespace C145N6Frame
open C145.ActualResponse C145.ObservedKernelRecovery
open scoped BigOperators Topology ContDiff
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

theorem literal_source_actual_C2_response {T : ℝ} (hT : 0 < T) :
    ∃ R : Input T → C145.ActualResponse.Path 5 T,
      IsActualResponse hT frame literalRates port R ∧ ContDiffAt ℝ 2 R 0 :=
  exists_actual_C2_response hT frame literalRates port frame_orthonormal

theorem literal_N6_ordinary_C2_jets_identification {n : ℕ} {T : ℝ}
    (hT : 0 < T)
    (c1 : ℝ) (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates1 b1 : Fin (n + 1) → ℝ)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hGround1 : ∀ v, Q1 v 0 = c1)
    (hRates1 : Function.Injective rates1)
    (hRateGround1 : rates1 0 = 1)
    (hAbove1 : ∀ j : Fin n, 1 < rates1 j.succ)
    (ha1 : ∀ j, 0 < C145.Pulse.modalOverlap Q1 b1 j)
    (R0 : Input T → C145.ActualResponse.Path 5 T) (R1 : Input T → C145.ActualResponse.Path n T)
    (hR0 : IsActualResponse hT frame literalRates port R0)
    (hR1 : IsActualResponse hT Q1 rates1 b1 R1)
    (hcR0 : ContDiffAt ℝ 2 R0 0) (hcR1 : ContDiffAt ℝ 2 R1 0)
    (hFirst : ∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
      rawFirst port R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT))
    (hMixed : ∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
      rawMixed port R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT)) :
    ∃ e : Fin (5 + 1) ≃ Fin (n + 1),
      5 = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = literalRates i) ∧
      (∀ i, C145.Pulse.modalOverlap Q1 b1 (e i) =
        C145.Pulse.modalOverlap frame port i) ∧
      (1 / Real.sqrt 6) = c1 ∧ (∑ v, port v) = (∑ w, b1 w) ∧
      ∃ π : Fin (5 + 1) ≃ Fin (n + 1),
        (∀ (w : Fin (n + 1)) (v : Fin (5 + 1)),
          (∑ i : Fin (5 + 1), Q1 w (e i) * frame v i) =
            if w = π v then 1 else 0) ∧
        (∀ (v i : Fin (5 + 1)), Q1 (π v) (e i) = frame v i) ∧
        (∀ (v u : Fin (5 + 1)),
          C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.spectralGenerator literalRates frame v u) ∧
        (∀ v : Fin (5 + 1), b1 (π v) = port v) ∧
        (∀ (v u : Fin (5 + 1)),
          C145CoordinatePermutation.decayLaplacian 1 rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.decayLaplacian 1 literalRates frame v u) := by
  have hObserved := ordinary_C2_jets_recover_observed_time_kernels hT
    frame literalRates port Q1 rates1 b1 frame_orthonormal hQ1 R0 R1 hR0 hR1 hcR0 hcR1 hFirst hMixed
  have hAll := C145.TimeKernelContinuation.observed_time_kernels_determine_all_nonnegative_delays
    hT frame literalRates port Q1 rates1 b1 hObserved.1 hObserved.2
  exact literal_N6_time_kernels_identification c1 Q1 rates1 b1 hQ1 hGround1 hRates1
    hRateGround1 hAbove1 ha1 hAll.1 hAll.2

end C145N6Frame

end
