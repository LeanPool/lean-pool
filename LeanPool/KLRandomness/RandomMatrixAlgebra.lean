/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Affine
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The algebraic obstruction to full row rank

A matrix is represented by its finite family of columns. Its row rank is
full exactly when no nonzero linear functional annihilates all the columns.
The evaluation map for a fixed nonzero functional is surjective on every
set of columns. These facts supply the algebraic part of the random-matrix
estimate used in the finite candidate construction.
-/

@[expose] public section

namespace Klr.RandomMatrix

open scoped BigOperators

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι]

/-- The linear map whose columns are the vectors `B i`. -/
noncomputable def columnMap (B : ι → V) : (ι → K) →ₗ[K] V where
  toFun x := ∑ i, x i • B i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul, Finset.smul_sum]

@[simp] theorem columnMap_apply (B : ι → V) (x : ι → K) :
    columnMap B x = ∑ i, x i • B i := rfl

theorem columnMap_single [DecidableEq ι] (B : ι → V) (i : ι) :
    columnMap B (Pi.single i (1 : K)) = B i := by
  simp [columnMap, Pi.single_apply]

theorem column_mem_range (B : ι → V) (i : ι) :
    B i ∈ LinearMap.range (columnMap B (K := K)) := by
  classical
  exact ⟨Pi.single i 1, columnMap_single B i⟩

/-- Failure of full row rank is witnessed by a nonzero row functional. -/
theorem not_surjective_iff_exists_annihilator (B : ι → V) :
    ¬ Function.Surjective (columnMap B (K := K)) ↔
      ∃ φ : Module.Dual K V, φ ≠ 0 ∧ ∀ i, φ (B i) = 0 := by
  constructor
  · intro hB
    have hr : LinearMap.range (columnMap B (K := K)) < ⊤ := by
      exact lt_top_iff_ne_top.mpr (fun h => hB (LinearMap.range_eq_top.mp h))
    obtain ⟨φ, hφ, hrφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top hr inferInstance
    refine ⟨φ, hφ, fun i => ?_⟩
    have hi : φ (B i) ∈ (LinearMap.range (columnMap B (K := K))).map φ :=
      ⟨B i, column_mem_range B i, rfl⟩
    rwa [hrφ, Submodule.mem_bot] at hi
  · rintro ⟨φ, hφ, hB⟩ hs
    apply hφ
    ext v
    obtain ⟨x, rfl⟩ := hs v
    simp [columnMap, map_sum, hB]

/-- Apply one row functional to each column in a fixed finite set. -/
noncomputable def evaluationMap (φ : Module.Dual K V) (T : Finset ι) :
    (ι → V) →ₗ[K] (T → K) where
  toFun B t := φ (B t.val)
  map_add' B C := by ext t; simp
  map_smul' a B := by ext t; simp

omit [Fintype ι] in
@[simp] theorem evaluationMap_apply (φ : Module.Dual K V) (T : Finset ι)
    (B : ι → V) (t : T) : evaluationMap φ T B t = φ (B t.val) := rfl

omit [Fintype ι] in
/-- A nonzero scalar-valued functional produces every requested pattern of
values on the selected columns. -/
theorem evaluationMap_surjective {φ : Module.Dual K V} (hφ : φ ≠ 0)
    (T : Finset ι) : Function.Surjective (evaluationMap φ T) := by
  classical
  obtain ⟨u, hu⟩ := (LinearMap.surjective hφ) 1
  intro y
  refine ⟨fun i => if hi : i ∈ T then y ⟨i, hi⟩ • u else 0, ?_⟩
  ext t
  simp [evaluationMap, t.property, hu]

/-- The restriction of a matrix to the columns in `T`. -/
noncomputable def restrictedMap (B : ι → V) (T : Finset ι) : (T → K) →ₗ[K] V :=
  columnMap (fun t : T => B t.val)

omit [Fintype ι] in
theorem restricted_not_surjective_iff (B : ι → V) (T : Finset ι) :
    ¬ Function.Surjective (restrictedMap B T (K := K)) ↔
      ∃ φ : Module.Dual K V, φ ≠ 0 ∧ evaluationMap φ T B = 0 := by
  rw [restrictedMap, not_surjective_iff_exists_annihilator]
  constructor
  · rintro ⟨φ, hφ, hB⟩
    exact ⟨φ, hφ, funext hB⟩
  · rintro ⟨φ, hφ, hB⟩
    exact ⟨φ, hφ, fun t => congrFun hB t⟩

theorem restricted_univ_surjective_iff (B : ι → V) :
    Function.Surjective (restrictedMap B Finset.univ (K := K)) ↔
      Function.Surjective (columnMap B (K := K)) := by
  rw [← not_iff_not, restricted_not_surjective_iff,
    not_surjective_iff_exists_annihilator]
  simp [evaluationMap, funext_iff]

end Klr.RandomMatrix
