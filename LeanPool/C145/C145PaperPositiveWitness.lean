/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8OriginalGraphInverse

/-! A nonvacuity control for the original-graph hypotheses of Theorem A.
The source is the three-vertex unit-weight path, with decay shift ten and
the Euclidean-normalized real port (1,2,4)/sqrt(21). No numerical test is used.
This is an application check, with no claim of new science or novelty. -/

@[expose] public section

noncomputable section
namespace C145.PaperPositiveWitness
open scoped BigOperators
open Matrix C145.WeightedGraph C145.CyclicSpectral C145.GraphSpectralRealization

/-- The unit weights on the edges of the three-vertex path. -/
def weights : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0; 1,0,1; 0,1,0]
/-- The unnormalized separated port of the three-vertex witness. -/
def rawPort : Fin 3 → ℝ := ![1,2,4]
/-- The Euclidean normalization of the three-vertex witness port. -/
def port : Fin 3 → ℝ := (Real.sqrt 21)⁻¹ • rawPort
/-- The chosen port separation bound after normalization. -/
def delta : ℝ := (Real.sqrt 21)⁻¹
/-- The generator of the three-vertex witness with common decay ten. -/
def A : Matrix (Fin 3) (Fin 3) ℝ := generator 10 weights

theorem weights_symmetric : weights.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [weights]

theorem weights_nonnegative : ∀ i j, 0 ≤ weights i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [weights]

theorem support_connected : (supportGraph weights weights_symmetric).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨1, ?_⟩
  intro v
  fin_cases v
  · apply SimpleGraph.Adj.reachable
    norm_num [supportGraph, weights]
  · exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    norm_num [supportGraph, weights]

theorem generator_explicit : A = !![-11,1,0; 1,-12,1; 0,1,-11] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, generator, laplacian, weights, Fin.sum_univ_succ]

theorem raw_first_krylov : A *ᵥ rawPort = ![-9,-19,-42] := by
  rw [generator_explicit]
  ext i
  fin_cases i <;> norm_num [rawPort, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem raw_second_krylov : A ^ 2 *ᵥ rawPort = ![80,177,443] := by
  rw [pow_two, ← Matrix.mulVec_mulVec, raw_first_krylov, generator_explicit]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem raw_port_cyclic : KrylovCyclic A rawPort := by
  let S := Submodule.span ℝ (Set.range (fun k : ℕ => A ^ k *ᵥ rawPort))
  have h0 : rawPort ∈ S := by
    simpa using (Submodule.subset_span (Set.mem_range_self 0) : A ^ 0 *ᵥ rawPort ∈ S)
  have h1 : ![-9,-19,-42] ∈ S := by
    simpa [pow_one, raw_first_krylov] using
      (Submodule.subset_span (Set.mem_range_self 1) : A ^ 1 *ᵥ rawPort ∈ S)
  have h2 : ![80,177,443] ∈ S := by
    simpa [raw_second_krylov] using
      (Submodule.subset_span (Set.mem_range_self 2) : A ^ 2 *ᵥ rawPort ∈ S)
  apply top_unique
  intro x _
  have hx : x =
      ((983 * x 0-627 * x 1 + 73 * x 2) / 21) • rawPort +
      ((178 * x 0-123 * x 1 + 17 * x 2) / 21) • ![-9,-19,-42] +
      ((8 * x 0-6 * x 1 + x 2) / 21) • ![80,177,443] := by
    ext i
    fin_cases i <;> simp [rawPort] <;> ring
  rw [hx]
  exact S.add_mem (S.add_mem (S.smul_mem _ h0) (S.smul_mem _ h1)) (S.smul_mem _ h2)

theorem sqrt_pos : 0 < Real.sqrt (21 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem port_cyclic : KrylovCyclic (generator 10 weights) port := by
  have hs : Real.sqrt (21 : ℝ) ≠ 0 := ne_of_gt sqrt_pos
  change Submodule.span ℝ (Set.range (fun k : ℕ => A ^ k *ᵥ port)) = ⊤
  apply top_unique
  rw [← raw_port_cyclic]
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  have hk : A ^ k *ᵥ rawPort = Real.sqrt 21 • (A ^ k *ᵥ port) := by
    simp [port, Matrix.mulVec_smul, smul_smul, hs]
  change A ^ k *ᵥ rawPort ∈ _
  rw [hk]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

theorem delta_pos : 0 < delta := inv_pos.2 sqrt_pos

theorem delta_sq : delta ^ 2 = (1 : ℝ) / 21 := by
  unfold delta
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]
  norm_num

theorem port_normalized : (∑ i, (port i) ^ 2) = 1 := by
  have hd := delta_sq
  change (∑ i, (delta * rawPort i) ^ 2) = 1
  norm_num [rawPort, Fin.sum_univ_succ] at *
  nlinarith

theorem port_separation : ∀ j k : Fin 3, j ≠ k →
    delta ^ 2 ≤ (port j-port k) ^ 2 := by
  intro j k hjk
  change delta ^ 2 ≤ (delta * rawPort j-delta * rawPort k) ^ 2
  fin_cases j <;> fin_cases k <;> norm_num [rawPort] at * <;> nlinarith [sq_nonneg delta]

theorem source_q_exact : C145DRE8.sourceQChebyshevSq port 11 13 delta =
    (35 : ℝ) / 12754584 := by
  have hn : delta ≠ 0 := ne_of_gt delta_pos
  have hp : ∀ v, port v = delta * rawPort v := fun _ => rfl
  unfold C145DRE8.sourceQChebyshevSq C145DRE8.centeredPort
  simp_rw [hp]
  norm_num [rawPort, Fin.sum_univ_succ]
  field_simp [hn]; ring

theorem source_q_lt_one : C145DRE8.sourceQChebyshevSq port 11 13 delta < 1 := by
  rw [source_q_exact]
  norm_num

/-- Exact original-matrix nonground spectral band, derived from all eigenvectors. -/
theorem nonground_decay_band : C145DRE8.NonGroundDecayBand 10 weights 11 13 := by
  intro r x hx he hr
  change A *ᵥ x = (-r) • x at he
  rw [generator_explicit] at he
  have h0 : (r-11) * x 0 + x 1 = 0 := by
    have hh := congrFun he 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hh
    linarith
  have h1 : x 0 + (r-12) * x 1 + x 2 = 0 := by
    have hh := congrFun he 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hh
    linarith
  have h2 : x 1 + (r-11) * x 2 = 0 := by
    have hh := congrFun he 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hh
    linarith
  have hx0 : x 0 ≠ 0 := by
    intro hz
    have hz1 : x 1 = 0 := by simpa [hz] using h0
    have hz2 : x 2 = 0 := by simpa [hz, hz1] using h1
    apply hx
    ext i
    fin_cases i <;> simp_all
  have hp : (r-10) * (r-11) * (r-13) * x 0 = 0 := by
    linear_combination ((r-11) * (r-12)-1) * h0 - (r-11) * h1 + h2
  have hp' : (r-10) * (r-11) * (r-13) = 0 := (mul_eq_zero.mp hp).resolve_right hx0
  rcases mul_eq_zero.mp hp' with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hr (sub_eq_zero.mp h)).elim
    · have : r = 11 := sub_eq_zero.mp h
      subst r
      norm_num
  · have : r = 13 := sub_eq_zero.mp h
    subst r
    norm_num

/-- The concrete graph meets every graph-side structural/criterion premise of
Theorem A; the equal-response premise still refers to actual response jets. -/
theorem theoremA_source_witness :
    weights.IsSymm ∧ (∀ i j, 0 ≤ weights i j) ∧
    (supportGraph weights weights_symmetric).Connected ∧
    KrylovCyclic (generator 10 weights) port ∧
    (∑ i, (port i) ^ 2) = 1 ∧
    (11 : ℝ) < 13 ∧ (13 : ℝ) < 2 * 11 ∧
    C145DRE8.NonGroundDecayBand 10 weights 11 13 ∧
    0 < delta ∧ (∀ j k : Fin 3, j ≠ k → delta ^ 2 ≤ (port j-port k) ^ 2) ∧
    C145DRE8.sourceQChebyshevSq port 11 13 delta < 1 := by
  exact ⟨weights_symmetric, weights_nonnegative, support_connected, port_cyclic,
    port_normalized, by norm_num, by norm_num, nonground_decay_band,
    delta_pos, port_separation, source_q_lt_one⟩

end C145.PaperPositiveWitness

end
