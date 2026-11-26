/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145N6GraphResponse

/-!
# Identification of the explicit six-vertex graph in vertex coordinates.
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

theorem zero_diagonal_weights_of_laplacian_transport {n : ℕ}
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (π : Fin 6 ≃ Fin (n + 1))
    (hdiag : ∀ v, W v v = 0)
    (hL : ∀ v u, C145.WeightedGraph.laplacian W (π v) (π u) =
      C145.WeightedGraph.laplacian edgeWeight v u) :
    ∀ v u, W (π v) (π u) = edgeWeight v u := by
  intro v u
  by_cases h : v = u
  · subst u; rw [hdiag, edgeWeight_diagonal]
  · have he := hL v u
    have hp : π v ≠ π u := fun h' => h (π.injective h')
    simp only [C145.WeightedGraph.laplacian, Matrix.sub_apply, Matrix.diagonal_apply,
      ite_eq_right h, ite_eq_right hp, zero_sub] at he
    exact neg_injective he

/-- Original graph identification for the literal N6 source. Spectral frames,
simple rates, positive-oriented overlaps and C2 regularity are derived, not supplied.
Diagonal self-loop weights require the separately explicit zero-diagonal condition. -/
theorem literal_N6_original_graph_identification {n : ℕ} {T : ℝ}
    (hT : 0 < T)
    (W1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hs1 : W1.IsSymm) (hn1 : ∀ v u, 0 ≤ W1 v u)
    (hconnected1 : (C145.WeightedGraph.supportGraph W1 hs1).Connected)
    (b1 : State n)
    (hcyclic1 : C145.CyclicSpectral.KrylovCyclic (C145.GraphSpectralRealization.generator 1 W1) b1)
    (R0 : Input T → C145.ActualResponse.Path 5 T)
    (R1 : Input T → C145.ActualResponse.Path n T)
    (hR0 : C145.GraphSpectralRealization.IsGraphResponse hT 1 edgeWeight port R0)
    (hR1 : C145.GraphSpectralRealization.IsGraphResponse hT 1 W1 b1 R1)
    (hc0 : ContinuousAt R0 0) (hc1 : ContinuousAt R1 0)
    (hFirst : ∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
      rawFirst port R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT))
    (hMixed : ∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
      rawMixed port R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT)) :
    5 = n ∧ ∃ π : Fin 6 ≃ Fin (n + 1),
      (∀ v u, C145.GraphSpectralRealization.generator 1 W1 (π v) (π u) =
        C145.GraphSpectralRealization.generator 1 edgeWeight v u) ∧
      (∀ v, b1 (π v) = port v) ∧
      (∀ v u, C145.WeightedGraph.laplacian W1 (π v) (π u) =
        C145.WeightedGraph.laplacian edgeWeight v u) ∧
      ((∀ v, W1 v v = 0) → ∀ v u, W1 (π v) (π u) = edgeWeight v u) := by
  obtain ⟨S1⟩ :=
    C145.GraphSpectralRealization.connected_cyclic_graph_has_oriented_spectral_realization
      1 (by norm_num) W1 hs1 hn1 hconnected1 b1 hcyclic1
  have hActual0 := (literal_graph_response_iff hT R0).mp hR0
  have hActual1 := S1.actualResponse hT R1 hR1
  have hC0 := actual_response_C2_of_continuous hT frame literalRates port frame_orthonormal R0
    hActual0 hc0
  have hC1 := actual_response_C2_of_continuous hT S1.Q S1.rates b1 S1.orthonormal R1 hActual1 hc1
  obtain ⟨e,hn,_,_,_,_,_,π,_,_,hG,hP,hL⟩ := literal_N6_ordinary_C2_jets_identification hT
    S1.c S1.Q S1.rates b1 S1.orthonormal S1.ground S1.simple S1.ground_rate S1.higher
    S1.positive_overlap R0 R1 hActual0 hActual1 hC0 hC1 hFirst hMixed
  have hLap : ∀ v u, C145.WeightedGraph.laplacian W1 (π v) (π u) =
      C145.WeightedGraph.laplacian edgeWeight v u := by
    simpa only [S1.original_laplacian, actual_decay_laplacian] using hL
  refine ⟨hn,π,?_,hP,hLap,fun hd => zero_diagonal_weights_of_laplacian_transport W1 π hd hLap⟩
  simpa only [S1.original_generator, actual_spectral_generator, literal_graph_generator] using hG
end C145N6Frame

end
