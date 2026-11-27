/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalFunctionalFiniteVectorApproximation
public import LeanPool.VacuumBellSeparation.Bell.CommutantVectorDomination
public import LeanPool.VacuumBellSeparation.Bell.SeparatingCommutantCyclic
public import LeanPool.VacuumBellSeparation.Bell.NormalPositiveConeClosure
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Topology.Algebra.Monoid

/-!
# Full normal-positive density from a separating reference vector

The cone of positive dual functionals dominated by a finite multiple of the
reference is an actual additive submonoid. Its norm closure contains every
original-H vector functional by commutant orbit density, and hence every
normal positive functional by finite-vector approximation. No single-vector
representation of an arbitrary normal functional is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open SW88
open scoped Topology ComplexOrder InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance separatingDensity_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- Domination is tested on every positive element of the original algebra. -/
def dominatedPositiveDualMonoid (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) : AddSubmonoid (StrongDual ℂ M.toStarSubalgebra) where
  carrier := {f | (∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : M.toStarSubalgebra, 0 ≤ X → f X ≤ C • φ X}
  zero_mem' := ⟨fun X _ => by simp, 0, le_rfl, fun X _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf, C, hC, hCf⟩ ⟨hg, D, hD, hDg⟩
    refine ⟨fun X hX => add_nonneg (hf X hX) (hg X hX),
      C + D, add_nonneg hC hD, ?_⟩
    intro X hX
    simpa only [add_apply, add_smul] using
      add_le_add (hCf X hX) (hDg X hX)

/-- No normalization is used, including for the zero vector and zero H. -/
theorem vectorDual_mem_closure_dominated_of_separating (M : VonNeumannAlgebra H)
    (Ω : H) (hsep : IsSeparatingForAlgebra M Ω) (χ : H) :
    vectorDual M χ ∈ (dominatedPositiveDualMonoid M
      (vectorPositiveLinearMap M Ω)).topologicalClosure := by
  change vectorDual M χ ∈ closure (dominatedPositiveDualMonoid M
    (vectorPositiveLinearMap M Ω) : Set (StrongDual ℂ M.toStarSubalgebra))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt hε (2 * ‖χ‖ + 1)
  have hcyc := commutant_cyclic_of_separating M Ω hsep
  have hclosure : χ ∈ closure (operatorOrbit M.commutant.toStarSubalgebra Ω : Set H) := by
    change χ ∈ (operatorOrbit M.commutant.toStarSubalgebra Ω).topologicalClosure
    rw [(cyclicForAlgebra_iff_closedOperatorOrbit M.commutant Ω).mp hcyc]
    trivial
  obtain ⟨x, ⟨S, hS, rfl⟩, hd⟩ :=
    Metric.mem_closure_iff.mp hclosure (min 1 δ) (lt_min zero_lt_one hδ)
  have hdist : ‖χ - S Ω‖ < min 1 δ := by simpa only [dist_eq_norm] using hd
  have hd1 : ‖χ - S Ω‖ < 1 := hdist.trans_le (min_le_left _ _)
  have hdd : ‖χ - S Ω‖ < δ := hdist.trans_le (min_le_right _ _)
  have hn : ‖S Ω‖ ≤ ‖χ‖ + 1 := by
    have h := norm_sub_norm_le (S Ω) χ
    rw [norm_sub_rev] at h
    linarith
  refine ⟨vectorDual M (S Ω), ?_, ?_⟩
  · exact ⟨fun X hX => (vectorPositiveLinearMap M (S Ω)).map_nonneg hX,
      ‖S‖ ^ 2, sq_nonneg _, fun X hX => vectorDual_commutant_le M Ω hS X hX⟩
  · rw [dist_eq_norm]
    calc
      ‖vectorDual M χ - vectorDual M (S Ω)‖ ≤ (‖χ‖ + ‖S Ω‖) * ‖χ - S Ω‖ :=
        vectorDual_difference_norm_le M χ (S Ω)
      _ ≤ (2 * ‖χ‖ + 1) * ‖χ - S Ω‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ (2 * ‖χ‖ + 1) * δ :=
        mul_le_mul_of_nonneg_left hdd.le (by positivity)
      _ < ε := hδε

/-- Equality in the genuine continuous dual, including an empty family. -/
theorem finiteVectorFunctional_dual_eq_sum (M : VonNeumannAlgebra H)
    {ι : Type*} [Fintype ι] (ξ : ι → H) :
    (PositiveContinuousLinearMap.ofClass (finiteVectorFunctional M ξ)).toContinuousLinearMap =
      ∑ i, vectorDual M (ξ i) := by
  apply ContinuousLinearMap.ext
  intro a
  change finiteVectorFunctional M ξ a = (∑ i, vectorDual M (ξ i)) a
  rw [sum_apply, finiteVectorFunctional_apply]
  rfl

theorem finiteVectorDual_mem_closure_dominated_of_separating (M : VonNeumannAlgebra H)
    (Ω : H) (hsep : IsSeparatingForAlgebra M Ω)
    {ι : Type*} [Fintype ι] (ξ : ι → H) :
    (PositiveContinuousLinearMap.ofClass (finiteVectorFunctional M ξ)).toContinuousLinearMap ∈
      (dominatedPositiveDualMonoid M (vectorPositiveLinearMap M Ω)).topologicalClosure := by
  rw [finiteVectorFunctional_dual_eq_sum]
  exact AddSubmonoid.sum_mem _ fun i _ =>
    vectorDual_mem_closure_dominated_of_separating M Ω hsep (ξ i)

/-- Every positive order-normal functional is approximated in full dual norm
by actual positive functionals dominated by the separating reference. -/
theorem normalFunctional_mem_closure_dominated_of_separating (M : VonNeumannAlgebra H)
    (Ω : H) (hsep : IsSeparatingForAlgebra M Ω)
    (ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M ψ) :
    (PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap ∈
      (dominatedPositiveDualMonoid M (vectorPositiveLinearMap M Ω)).topologicalClosure := by
  have h := normalFunctional_mem_closure_finite_vector_sums M ψ hn
  apply closure_minimal ?_
    (dominatedPositiveDualMonoid M (vectorPositiveLinearMap M Ω)).isClosed_topologicalClosure h
  rintro f ⟨n, ξ, rfl⟩
  exact finiteVectorDual_mem_closure_dominated_of_separating M Ω hsep ξ

/-- Exact cone equality; positivity and order normality are literal predicates
on the original continuous dual. This is not a statement only about vectors. -/
theorem closure_dominated_eq_positive_normal_of_separating (M : VonNeumannAlgebra H)
    (Ω : H) (hsep : IsSeparatingForAlgebra M Ω) :
    ((dominatedPositiveDualMonoid M (vectorPositiveLinearMap M Ω)).topologicalClosure :
      Set (StrongDual ℂ M.toStarSubalgebra)) =
      {f : StrongDual ℂ M.toStarSubalgebra |
        (∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X) ∧ IsNormalFunctional M f} := by
  apply Set.ext
  intro f
  constructor
  · exact fun hf => closure_dominated_positive_subset_normal M
      (vectorPositiveLinearMap M Ω) (vectorFunctional_isNormal M Ω) hf
  · rintro ⟨hf, hn⟩
    let ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ f.toLinearMap hf
    exact normalFunctional_mem_closure_dominated_of_separating M Ω hsep ψ hn

end VacuumBellSeparation.Bipartite
