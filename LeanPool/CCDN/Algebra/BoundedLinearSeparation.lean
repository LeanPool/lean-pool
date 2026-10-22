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

/-- Bounded integer moment-curve coefficients separate every pair of a finite
family of distinct vectors. -/
theorem exists_bounded_moment_separation {K ι : Type*} [Field K] [CharZero K]
    [Fintype ι] {n : ℕ}
    (v : ι → Fin n → K) (hv : Function.Injective v) :
    ∃ k : ℕ, k ≤ n * (Fintype.card ι) ^ 2 ∧
      Function.Injective (fun i => ∑ j : Fin n, v i j * (k : K) ^ j.val) := by
  classical
  let T := {t : ι × ι // t.1 ≠ t.2}
  let P (t : T) : Polynomial K := Polynomial.ofFn n (fun j => v t.val.1 j - v t.val.2 j)
  have hPn (t : T) : P t ≠ 0 := by
    intro he
    apply t.property
    apply hv
    funext j
    have hc := congrArg (fun q : Polynomial K => q.coeff j.val) he
    simpa only [P, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
      sub_eq_zero] using hc
  have hPd (t : T) : (P t).natDegree ≤ n := by
    cases n with
    | zero => simp [P]
    | succ n => exact Nat.le_of_lt (Polynomial.ofFn_natDegree_lt (by omega) _)
  let Q := ∏ t : T, P t
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun t _ => hPn t)
  have hd : Q.natDegree ≤ n * (Fintype.card ι) ^ 2 := by
    calc
      _ ≤ ∑ _t : T, n := (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum (fun t _ => hPd t))
      _ = Fintype.card T * n := by simp
      _ ≤ (Fintype.card ι) ^ 2 * n := Nat.mul_le_mul_right n (by
        have hh := Fintype.card_subtype_le (fun t : ι × ι => t.1 ≠ t.2)
        simpa only [Fintype.card_prod, pow_two] using hh)
      _ = _ := Nat.mul_comm _ _
  obtain ⟨k, hk, hval⟩ := polynomial_exists_small_nat_eval_ne_zero Q hQ
  refine ⟨k, hk.trans hd, ?_⟩
  intro i j he
  by_contra hij
  let t : T := ⟨(i,j), hij⟩
  have hv : (P t).eval (k : K) ≠ 0 := by
    have hp : (∏ t : T, (P t).eval (k : K)) ≠ 0 := by
      simpa only [Q, Polynomial.eval_prod] using hval
    exact (Finset.prod_ne_zero_iff.mp hp) t (Finset.mem_univ t)
  apply hv
  simp only [P, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, t]
  simpa only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using he

end
end CCDN
