/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145N6CalibratedTransport
public import LeanPool.C145.C145WeightedGraph

/-!
# Positive weights and connectedness of the explicit six-vertex graph.
-/

@[expose] public section
noncomputable section
namespace C145N6Frame
open scoped BigOperators
open C145CoordinatePermutation

/-- The six exact decay rates for the explicit graph, including the ground rate one. -/
def literalRates : Fin 6 → ℝ := ![1,20,21,22,23,24]
/-- The generator reconstructed from the Helmert array and the six exact rates. -/
def generator : Matrix (Fin 6) (Fin 6) ℝ :=
  fun v u => -(∑ i, literalRates i * helmert v i * helmert u i / gramWeight i)
/-- The off-diagonal part of the generator, giving the graph's edge weights. -/
def edgeWeight : Matrix (Fin 6) (Fin 6) ℝ := generator - Matrix.diagonal (fun v => generator v v)

theorem literalRates_full : literalRates = C145.H2.fullRates 1 C145N6.rates := by
  funext i; fin_cases i <;> rfl
theorem frame_pair_product (v u i : Fin 6) :
    frame v i * frame u i = helmert v i * helmert u i / gramWeight i := by
  unfold frame
  field_simp [sqrtWeight_ne i, ne_of_gt (gramWeight_pos i)]
  rw [sqrtWeight_sq]
  ring

theorem actual_spectral_generator : spectralGenerator literalRates frame = generator := by
  funext v u
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, frame_pair_product]
  ring

theorem generator_symmetric : generator.IsSymm := by
  apply Matrix.IsSymm.ext
  intro v u
  dsimp [generator]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem generator_row_sum (v : Fin 6) : (∑ u, generator v u) = -1 := by
  fin_cases v <;> norm_num [generator, literalRates, helmert, gramWeight, Fin.sum_univ_succ]
theorem generator_offdiagonal_lower (v u : Fin 6) (h : v ≠ u) : 51 / 20 ≤ generator v u := by
  fin_cases v <;> fin_cases u <;> norm_num [generator, literalRates, helmert, gramWeight,
    Fin.sum_univ_succ] at *
theorem generator_minimum_attained : generator 0 1 = 51 / 20 := by
  norm_num [generator, literalRates, helmert, gramWeight, Fin.sum_univ_succ]

theorem edgeWeight_symmetric : edgeWeight.IsSymm :=
  generator_symmetric.sub (Matrix.isSymm_diagonal _)
theorem edgeWeight_diagonal (v : Fin 6) : edgeWeight v v = 0 := by
  simp [edgeWeight]
theorem edgeWeight_offdiagonal (v u : Fin 6) (h : v ≠ u) : edgeWeight v u = generator v u := by
  simp [edgeWeight, h]
theorem edgeWeight_nonnegative (v u : Fin 6) : 0 ≤ edgeWeight v u := by
  by_cases h : v = u
  · subst u; rw [edgeWeight_diagonal]
  · rw [edgeWeight_offdiagonal v u h]
    have hh := generator_offdiagonal_lower v u h
    linarith

theorem edgeWeight_row_sum (v : Fin 6) : (∑ u, edgeWeight v u) = -1-generator v v := by
  simp only [edgeWeight, Matrix.sub_apply, Finset.sum_sub_distrib, generator_row_sum]
  congr 1
  simp [Matrix.diagonal_apply]

theorem actual_generator_laplacian : generator = -1 - C145.WeightedGraph.laplacian edgeWeight := by
  ext v u
  simp only [C145.WeightedGraph.laplacian, Matrix.sub_apply,
    Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply, edgeWeight]
  by_cases h : v = u
  · subst u; simp [generator_row_sum]
  · simp [h]

theorem actual_decay_laplacian : decayLaplacian 1 literalRates frame =
  C145.WeightedGraph.laplacian edgeWeight := by
  funext v u
  rw [decayLaplacian, actual_spectral_generator]
  have h := congrFun (congrFun actual_generator_laplacian v) u
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply] at h
  linarith
theorem edgeWeight_positive (v u : Fin 6) (h : v ≠ u) : 0 < edgeWeight v u := by
  rw [edgeWeight_offdiagonal v u h]
  have hh := generator_offdiagonal_lower v u h
  linarith

theorem literal_graph_connected : (C145.WeightedGraph.supportGraph edgeWeight
  edgeWeight_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  by_cases h : (0 : Fin 6) = v
  · subst v; exact SimpleGraph.Reachable.refl _
  · exact (show (C145.WeightedGraph.supportGraph edgeWeight edgeWeight_symmetric).Adj 0 v from
      ⟨h,edgeWeight_positive 0 v h⟩).reachable

/-- Calibrated rational H2 data transports the literal positive graph generator,
its reconstructed vertex port and its Laplacian by the same permutation.
No time-domain or unknown-calibration statement is made. -/
theorem calibrated_literal_graph_transport (Q : Fin 6 → Fin 6 → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (hground : ∀ v, Q v 0 = 1 / Real.sqrt 6)
    (hresponse : C145.H2.SamePositive literalRates
      (C145PhysicalFrame.T frame overlap) (C145PhysicalFrame.T Q overlap)) :
    ∃ π : Equiv.Perm (Fin 6),
      (∀ v i, Q (π v) i = frame v i) ∧
      (∀ v u, spectralGenerator literalRates Q (π v) (π u) = generator v u) ∧
      (∀ v, spectralPort overlap Q (π v) = port v) ∧
      (∀ v u, decayLaplacian 1 literalRates Q (π v) (π u) =
        C145.WeightedGraph.laplacian edgeWeight v u) := by
  rw [literalRates_full] at hresponse
  obtain ⟨π,_,hframe,hgen,hport,hlap⟩ := calibrated_response_spectral_transport 1 Q hQ hground
    hresponse
  refine ⟨π,hframe,?_,hport,?_⟩
  · simpa only [← literalRates_full, actual_spectral_generator] using hgen
  · simpa only [← literalRates_full, actual_decay_laplacian] using hlap
end C145N6Frame

end
