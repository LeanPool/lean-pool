/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! Coordinatewise Lagrange interpolation on a finite grid. The degree
depends on the side length of the grid rather than its number of points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def gridPointSeparator {K σ : Type*} [Field K] [Fintype σ] [DecidableEq K]
    (S : Finset K) (a : σ → K) : MvPolynomial σ K :=
  ∏ j, ∏ t ∈ S.erase (a j),
    C ((a j - t)⁻¹) * (X j - C t)

private lemma gridPointSeparator_eval {K σ : Type*} [Field K] [Fintype σ]
    [DecidableEq K]
    (S : Finset K) (a x : σ → K) (hx : ∀ j, x j ∈ S) :
    eval x (gridPointSeparator S a) = if x = a then 1 else 0 := by
  classical
  rw [gridPointSeparator, eval_prod]
  by_cases h : x = a
  · subst x
    rw [ite_eq_left rfl]
    apply Finset.prod_eq_one
    intro j _
    rw [eval_prod]
    apply Finset.prod_eq_one
    intro t ht
    simp only [eval_mul, eval_C, eval_sub, eval_X]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (Finset.mem_erase.mp ht).1.symm)
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, hx j⟩)
    simp

private lemma gridPointSeparator_degree {K σ : Type*} [Field K] [Fintype σ]
    [DecidableEq K]
    (S : Finset K) (a : σ → K) (ha : ∀ j, a j ∈ S) :
    (gridPointSeparator S a).totalDegree ≤ Fintype.card σ * (S.card - 1) := by
  classical
  unfold gridPointSeparator
  calc
    _ ≤ ∑ j : σ, (∏ t ∈ S.erase (a j),
        C ((a j - t)⁻¹) * (X j - C t)).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _j : σ, (S.card - 1) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ t ∈ S.erase (a j),
            (C ((a j - t)⁻¹) * (X j - C t)).totalDegree := totalDegree_finsetProd _ _
        _ ≤ ∑ _t ∈ S.erase (a j), 1 := by
          apply Finset.sum_le_sum
          intro t _
          apply (totalDegree_mul _ _).trans
          rw [totalDegree_C, Nat.zero_add]
          exact (totalDegree_sub _ _).trans (by simp)
        _ = _ := by simp [Finset.card_erase_of_mem (ha j)]
    _ = _ := by simp

/-- Distinct points of a fixed coordinate grid give independent filtered
coordinate classes at the grid-interpolation degree. -/
theorem grid_points_filtered_lower {K σ ι : Type*} [Field K]
    [Fintype σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (S : Finset K)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzS : ∀ i j, z i j ∈ S)
    (hzI : ∀ i f, f ∈ I → eval (z i) f = 0) {N : ℕ}
    (hN : Fintype.card σ * (S.card - 1) ≤ N) :
    Fintype.card ι ≤ Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let ψ : ι → (MvPolynomial σ K ⧸ I) →ₐ[K] K := fun i =>
    Ideal.Quotient.liftₐ I (aeval (z i)) (by
      intro f hf
      simpa only [aeval_eq_eval] using hzI i f hf)
  have hψ (i : ι) (f : MvPolynomial σ K) : ψ i (q f) = eval (z i) f := rfl
  let v : ι → filteredCoordinateSpace I N := fun j =>
    ⟨q (gridPointSeparator S (z j)), Submodule.mem_map.mpr
      ⟨gridPointSeparator S (z j),
        (mem_restrictTotalDegree _ _ _).mpr
          ((gridPointSeparator_degree S (z j) (hzS j)).trans hN), rfl⟩⟩
  have hlin : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have he := congrArg (fun w : filteredCoordinateSpace I N => ψ i w.val) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
      ZeroMemClass.coe_zero, map_zero] at he
    change (∑ j, c j • ψ i (q (gridPointSeparator S (z j)))) = 0 at he
    simp only [hψ, gridPointSeparator_eval S _ _ (hzS i), hz.eq_iff, smul_eq_mul] at he
    simpa using he
  exact hlin.fintype_card_le_finrank

end
end CCDN
