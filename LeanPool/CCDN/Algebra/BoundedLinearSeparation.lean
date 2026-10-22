/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots

/-! A finite family of distinct coordinate vectors is separated by a bounded
integer linear form on the moment curve (1,t,...,t^(n-1)). The proof avoids
an unquantified genericity argument. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- In characteristic zero, a nonzero polynomial `P` does not vanish at some natural number
`k ≤ P.natDegree`. -/
lemma polynomial_exists_small_nat_eval_ne_zero {K : Type*} [Field K] [CharZero K]
    (P : Polynomial K) (hP : P ≠ 0) :
    ∃ k : ℕ, k ≤ P.natDegree ∧ P.eval (k : K) ≠ 0 := by
  by_contra! hn
  apply hP
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun k : Fin (P.natDegree + 1) => (k.val : K))
    (fun i j h => Fin.ext (Nat.cast_injective h))
  · intro i
    exact hn i.val (by omega)
  · simp only [Fintype.card_fin]
    omega

/-- A moment form with parameter at most n times the number of directions
is nonzero on all those directions. -/
theorem exists_bounded_moment_nonvanishing {K ι : Type*} [Field K] [CharZero K]
    [Fintype ι] {n : ℕ} (v : ι → Fin n → K) (hv : ∀ i, v i ≠ 0) :
    ∃ k : ℕ, k ≤ n * Fintype.card ι ∧
      ∀ i, ∑ j : Fin n, v i j * (k : K) ^ j.val ≠ 0 := by
  classical
  let P (i : ι) : Polynomial K := Polynomial.ofFn n (v i)
  have hPn (i : ι) : P i ≠ 0 := by
    intro he
    apply hv i
    funext j
    have hc := congrArg (fun q : Polynomial K => q.coeff j.val) he
    simpa only [P, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
      Pi.zero_apply] using hc
  have hPd (i : ι) : (P i).natDegree ≤ n := by
    cases n with
    | zero => simp [P]
    | succ n => exact Nat.le_of_lt (Polynomial.ofFn_natDegree_lt (by omega) _)
  let Q := ∏ i, P i
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hPn i)
  have hd : Q.natDegree ≤ n * Fintype.card ι := by
    calc
      _ ≤ ∑ _i : ι, n := (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum (fun i _ => hPd i))
      _ = _ := by simp [Nat.mul_comm]
  obtain ⟨k, hk, hval⟩ := polynomial_exists_small_nat_eval_ne_zero Q hQ
  refine ⟨k, hk.trans hd, ?_⟩
  intro i
  have hp : (∏ i, (P i).eval (k : K)) ≠ 0 := by
    simpa only [Q, Polynomial.eval_prod] using hval
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  simpa only [P, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial] using hi

/-- Bounded integer moment-curve coefficients separate every pair of a finite
family of distinct vectors. -/
theorem exists_bounded_moment_separation {K ι : Type*} [Field K] [CharZero K]
    [Fintype ι] {n : ℕ}
    (v : ι → Fin n → K) (hv : Function.Injective v) :
    ∃ k : ℕ, k ≤ n * (Fintype.card ι) ^ 2 ∧
      Function.Injective (fun i => ∑ j : Fin n, v i j * (k : K) ^ j.val) := by
  classical
  let T := {t : ι × ι // t.1 ≠ t.2}
  have hne (t : T) : v t.val.1 - v t.val.2 ≠ 0 :=
    sub_ne_zero.mpr (fun he => t.property (hv he))
  obtain ⟨k, hk, hnonzero⟩ := exists_bounded_moment_nonvanishing
    (fun t : T => v t.val.1 - v t.val.2) hne
  have hcard : Fintype.card T ≤ (Fintype.card ι) ^ 2 := by
    have hh := Fintype.card_subtype_le (fun t : ι × ι => t.1 ≠ t.2)
    simpa only [Fintype.card_prod, pow_two] using hh
  refine ⟨k, hk.trans (Nat.mul_le_mul_left n hcard), ?_⟩
  intro i j he
  by_contra hij
  apply hnonzero ⟨(i, j), hij⟩
  simpa only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using he

end
end CCDN
