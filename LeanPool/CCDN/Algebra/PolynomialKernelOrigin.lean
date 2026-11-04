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
import LeanPool.CCDN.Algebra.PolynomialMatrixSpecialization

/-! A polynomial matrix with dependent columns at every integer value has a
polynomial kernel vector that remains nonzero at zero. A common power of X is
removed from a kernel vector after its rational denominators are cleared. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Remove the common order of vanishing of a nonzero polynomial vector. -/
private lemma polynomial_vector_remove_common_X {K ι : Type*} [Field K]
    (w : ι → Polynomial K) (hw : w ≠ 0) :
    ∃ N : ℕ, ∃ v : ι → Polynomial K,
      (∀ i, w i = X ^ N * v i) ∧ ∃ i, (v i).eval 0 ≠ 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ i, (w i).coeff N ≠ 0 := by
    by_contra! h
    apply hw
    funext i
    ext N
    exact h N i
  let N := Nat.find hex
  have hdiv (i : ι) : X ^ N ∣ w i := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro m hm
    by_contra hn
    exact Nat.find_min hex hm ⟨i, hn⟩
  choose v hv using hdiv
  refine ⟨N, v, hv, ?_⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  refine ⟨i, ?_⟩
  have hh : (w i).coeff N = (v i).coeff 0 := by
    rw [hv i]
    simpa only [zero_add] using Polynomial.coeff_X_pow_mul (v i) N 0
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact hh ▸ hi

/-- Rational-function dependence of columns gives a nonzero polynomial
kernel vector by clearing one common denominator. -/
private theorem polynomial_matrix_kernel_of_not_injective {K ι κ : Type*} [Field K]
    [Finite ι] [Fintype κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : ¬ Function.Injective (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin) :
    ∃ w : κ → Polynomial K, w ≠ 0 ∧ A *ᵥ w = 0 := by
  classical
  let := Fintype.ofFinite ι
  let f := algebraMap (Polynomial K) (RatFunc K)
  let M := A.map f
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hA
  let v := x - y
  have hv : v ≠ 0 := sub_ne_zero.mpr hne
  have hMv : M *ᵥ v = 0 := by
    change M.mulVecLin (x - y) = 0
    rw [map_sub, hxy, sub_self]
  obtain ⟨q, C, hq, hC⟩ := ratFunc_matrix_common_denominator
    (fun i (_ : Unit) => v i)
  let w := fun i => C i ()
  have hw (i : κ) : f (w i) = f q * v i := hC i ()
  have hqf : f q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  refine ⟨w, ?_, ?_⟩
  · intro hw0
    apply hv
    funext i
    have hh := hw i
    rw [hw0, Pi.zero_apply, map_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hqf
  · funext i
    apply RatFunc.algebraMap_injective K
    change f (∑ j, A i j * w j) = f 0
    rw [map_sum, map_zero]
    simp only [map_mul, hw]
    calc
      ∑ j, f (A i j) * (f q * v j) = f q * ∑ j, f (A i j) * v j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by
        have hh := congrFun hMv i
        change ∑ j, f (A i j) * v j = 0 at hh
        rw [hh, mul_zero]

/-- If every integer specialization has dependent columns, there is a
polynomial relation whose constant coefficient vector is nonzero. -/
theorem polynomial_matrix_kernel_nonzero_at_zero {K ι κ : Type*} [Field K] [CharZero K]
    [Finite ι] [Fintype κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : ∀ k : ℕ, ¬ Function.Injective (A.map (Polynomial.evalRingHom (k : K))).mulVecLin) :
    ∃ v : κ → Polynomial K, A *ᵥ v = 0 ∧ ∃ j, (v j).eval 0 ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  have hgen : ¬ Function.Injective
      (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin := by
    intro hi
    obtain ⟨k, hk⟩ := polynomial_matrix_injective_specialization A hi
    exact hA k hk
  obtain ⟨w, hw, hAw⟩ := polynomial_matrix_kernel_of_not_injective A hgen
  obtain ⟨N, v, hv, hv0⟩ := polynomial_vector_remove_common_X w hw
  refine ⟨v, ?_, hv0⟩
  funext i
  apply mul_left_cancel₀ (pow_ne_zero N (Polynomial.X_ne_zero : (X : Polynomial K) ≠ 0))
  simp only [Pi.zero_apply, mul_zero]
  change X ^ N * (∑ j, A i j * v j) = 0
  rw [Finset.mul_sum]
  have hh := congrFun hAw i
  change ∑ j, A i j * w j = 0 at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro j _
  rw [hv j]
  ring

end
end CCDN
