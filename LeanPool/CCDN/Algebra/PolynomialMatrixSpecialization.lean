/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import LeanPool.CCDN.Algebra.BoundedLinearSeparation

/-! An injective polynomial matrix over K(t) remains injective at some integer
specialization. Clearing a left inverse's denominators gives the assertion
without selecting minors or assuming a generic-rank principle. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix Polynomial

/-- Clear all entries of a rational-function matrix with one nonzero
polynomial denominator. -/
lemma ratFunc_matrix_common_denominator {K ι κ : Type*} [Field K]
    [Finite ι] [Finite κ] (B : Matrix ι κ (RatFunc K)) :
    ∃ q : Polynomial K, ∃ C : Matrix ι κ (Polynomial K), q ≠ 0 ∧
      ∀ i j, algebraMap (Polynomial K) (RatFunc K) (C i j) =
        algebraMap (Polynomial K) (RatFunc K) q * B i j := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun t : ι × κ => B t.1 t.2)
  choose C hC using hq
  refine ⟨q.val, fun i j => C (i,j), mem_nonZeroDivisors_iff_ne_zero.mp q.property, ?_⟩
  intro i j
  exact (hC (i,j)).trans (Algebra.smul_def _ _)

/-- An injective polynomial matrix has a polynomial left inverse up to one
nonzero scalar polynomial. -/
private theorem polynomial_matrix_scaled_left_inverse {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : Function.Injective (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin) :
    ∃ q : Polynomial K, ∃ C : Matrix κ ι (Polynomial K), q ≠ 0 ∧ C * A = q • 1 := by
  classical
  let f := algebraMap (Polynomial K) (RatFunc K)
  let M := A.map f
  obtain ⟨T, hT⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hA)
  let B := LinearMap.toMatrix' T
  have hBA : B * M = 1 := by
    have hh := congrArg LinearMap.toMatrix' hT
    simpa only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using hh
  obtain ⟨q, C, hq, hC⟩ := ratFunc_matrix_common_denominator B
  refine ⟨q, C, hq, ?_⟩
  have hCm : C.map f = f q • B := by ext i j; exact hC i j
  have hh : (C * A).map f = f q • (1 : Matrix κ κ (RatFunc K)) := by
    rw [Matrix.map_mul, hCm, Matrix.smul_mul, hBA]
  apply Matrix.ext
  intro i j
  apply RatFunc.algebraMap_injective K
  change f ((C * A) i j) = f ((q • (1 : Matrix κ κ (Polynomial K))) i j)
  have he := congrArg (fun D : Matrix κ κ (RatFunc K) => D i j) hh
  simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Matrix.one_apply, apply_ite f, map_one, map_zero] using he

/-- Full column rank over K(t) occurs at an integer specialization. -/
theorem polynomial_matrix_injective_specialization {K ι κ : Type*} [Field K] [CharZero K]
    [Finite ι] [Fintype κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : Function.Injective (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin) :
    ∃ k : ℕ, Function.Injective (A.map (Polynomial.evalRingHom (k : K))).mulVecLin := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨q, C, hq, hCA⟩ := polynomial_matrix_scaled_left_inverse A hA
  obtain ⟨k, _, hk⟩ := polynomial_exists_small_nat_eval_ne_zero q hq
  refine ⟨k, ?_⟩
  let e := Polynomial.evalRingHom (k : K)
  have he : C.map e * A.map e = e q • (1 : Matrix κ κ K) := by
    rw [← Matrix.map_mul, hCA]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      Matrix.one_apply, apply_ite e, map_one, map_zero]
  intro x y hxy
  have hh := congrArg (fun v => (C.map e) *ᵥ v) hxy
  change (C.map e) *ᵥ ((A.map e) *ᵥ x) = (C.map e) *ᵥ ((A.map e) *ᵥ y) at hh
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, he, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at hh
  exact (smul_right_injective _ hk) hh

end
end CCDN
