/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CommutantVectorDomination
public import LeanPool.VacuumBellSeparation.Bell.SeparatingCommutantCyclic

/-!
# Norm approximation of vector states by dominated commutant-orbit states

Separation makes the commutant orbit norm dense in the original full Hilbert
space. Normalizing its nonzero vectors and using the uniform dual estimate
gives domination and approximation simultaneously. The conclusion covers
actual vector states, not all normal states in this representation.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite.SW88

open scoped Topology InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An actual normalized commutant operator gives a nearby normal vector state
which is dominated by a positive multiple of the reference vector state. -/
theorem exists_dominated_commutant_vectorState_near (M : VonNeumannAlgebra H)
    (Ω : H) (hsep : IsSeparatingForAlgebra M Ω) (χ : H) (hχ : ‖χ‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : H →L[ℂ] H, S ∈ M.commutant ∧ ‖S Ω‖ = 1 ∧
      ‖vectorDual M χ - vectorDual M (S Ω)‖ < ε ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ T : M.toStarSubalgebra,
        0 ≤ T → t • vectorDual M (S Ω) T ≤ vectorDual M Ω T := by
  have hcyc := commutant_cyclic_of_separating M Ω hsep
  have hclosure : χ ∈ closure (operatorOrbit M.commutant.toStarSubalgebra Ω : Set H) := by
    change χ ∈ (operatorOrbit M.commutant.toStarSubalgebra Ω).topologicalClosure
    rw [(cyclicForAlgebra_iff_closedOperatorOrbit M.commutant Ω).mp hcyc]
    trivial
  let δ : ℝ := min (1 / 2) (ε / 8)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.mp hclosure δ hδ
  obtain ⟨R, hR, rfl⟩ := hx
  have hd : ‖χ - R Ω‖ < δ := by simpa only [dist_eq_norm] using hdist
  have hdhalf : ‖χ - R Ω‖ < 1 / 2 := hd.trans_le (min_le_left _ _)
  have hde : ‖χ - R Ω‖ < ε / 8 := hd.trans_le (min_le_right _ _)
  have hne : R Ω ≠ 0 := by
    intro hz
    rw [hz, sub_zero, hχ] at hdhalf
    norm_num at hdhalf
  let S : H →L[ℂ] H := (‖R Ω‖ : ℂ)⁻¹ • R
  have hS : S ∈ M.commutant := M.commutant.toStarSubalgebra.smul_mem hR _
  have he : S Ω = reehSchliederUnitVector (R Ω) := rfl
  have hSn : ‖S Ω‖ = 1 := by
    rw [he]
    exact reehSchliederUnitVector_norm hne
  have hvector : ‖χ - S Ω‖ ≤ 2 * ‖χ - R Ω‖ := by
    rw [he]
    exact unitVector_distance_le hne hχ
  have hdual : ‖vectorDual M χ - vectorDual M (S Ω)‖ ≤ 2 * ‖χ - S Ω‖ := by
    simpa only [hχ, hSn, one_add_one_eq_two] using vectorDual_difference_norm_le M χ (S Ω)
  refine ⟨S, hS, hSn, ?_, exists_small_vector_domination M Ω hS⟩
  nlinarith

/-- Every represented unit-vector state lies in the norm closure of normal
states dominated by the reference state. There is no implicit assertion that
every normal state is a vector state in H. -/
theorem vectorNormalState_mem_closure_dominated (M : VonNeumannAlgebra H)
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hsep : IsSeparatingForAlgebra M Ω)
    (χ : H) (hχ : ‖χ‖ = 1) :
    vectorNormalState M χ hχ ∈ closure {φ : HC00.NormalStateSpace M |
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ T : M.toStarSubalgebra,
        0 ≤ T → t • φ.1 T ≤ (vectorNormalState M Ω hΩ).1 T} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨S, hS, hn, hd, t, ht, ht1, hdom⟩ :=
    exists_dominated_commutant_vectorState_near M Ω hsep χ hχ hε
  refine ⟨vectorNormalState M (S Ω) hn, ⟨t, ht, ht1, hdom⟩, ?_⟩
  change dist (vectorDual M χ) (vectorDual M (S Ω)) < ε
  simpa only [dist_eq_norm] using hd

end VacuumBellSeparation.Bipartite.SW88
