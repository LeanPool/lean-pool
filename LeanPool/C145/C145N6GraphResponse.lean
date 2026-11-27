/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145N6OrdinaryJets
public import LeanPool.C145.C145GraphSpectralRealization

/-!
# Local responses for the explicit six-vertex graph.
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

/-- An actual response germ continuous at zero inherits C2 from local uniqueness. -/
theorem actual_response_C2_of_continuous {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (R : Input T → C145.ActualResponse.Path n T)
    (hR : IsActualResponse hT Q rates b R) (hc : ContinuousAt R 0) :
    ContDiffAt ℝ 2 R 0 := by
  obtain ⟨S,hS,hCS⟩ := exists_actual_C2_response hT Q rates b hQ
  exact hCS.congr_of_eventuallyEq (actual_response_germ_unique hT Q rates b hQ R S hR hS hc
    hCS.continuousAt)

theorem literal_graph_generator : C145.GraphSpectralRealization.generator 1 edgeWeight = generator
  := by
  have h := actual_generator_laplacian
  simpa only [C145.GraphSpectralRealization.generator, neg_smul, one_smul] using h.symm

theorem literal_graph_vectorField : vectorField frame literalRates port =
    C145.GraphSpectralRealization.graphVectorField 1 edgeWeight port := by
  unfold vectorField C145.GraphSpectralRealization.graphVectorField
  rw [actual_spectral_generator, literal_graph_generator]

theorem literal_graph_response_iff {T : ℝ} (hT : 0 < T)
    (R : Input T → C145.ActualResponse.Path 5 T) :
    C145.GraphSpectralRealization.IsGraphResponse hT 1 edgeWeight port R ↔
      IsActualResponse hT frame literalRates port R := by
  unfold C145.GraphSpectralRealization.IsGraphResponse IsActualResponse
  rw [literal_graph_vectorField]

theorem literal_graph_response_exists {T : ℝ} (hT : 0 < T) :
    ∃ R : Input T → C145.ActualResponse.Path 5 T,
      C145.GraphSpectralRealization.IsGraphResponse hT 1 edgeWeight port R ∧ ContDiffAt ℝ 2 R 0 :=
        by
  obtain ⟨R,hR,hC⟩ := literal_source_actual_C2_response hT
  exact ⟨R,(literal_graph_response_iff hT R).mpr hR,hC⟩
end C145N6Frame

end
