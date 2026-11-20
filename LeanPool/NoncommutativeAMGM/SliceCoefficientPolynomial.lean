/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.SlicePositivity

/-! # Polynomial dependence of the harmonic replacement on the slice parameter -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

/-- A harmonic replacement coefficient as an explicit polynomial in `s`. -/
noncomputable def sliceCoefficientPolynomial {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d k : ℕ) (S : HomogeneousIndex n k) :
    Polynomial ℝ :=
  ∑ r ∈ Finset.range (d + 1), if k ≤ r then
    C (h r k S) * (descPochhammer ℝ (r - k)).comp (X - C (k : ℝ)) else 0

theorem sliceCoefficientPolynomial_eval {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d k : ℕ) (S : HomogeneousIndex n k) (s : ℝ) :
    (sliceCoefficientPolynomial h d k S).eval s = harmonicSliceComponent h d s k S := by
  classical
  simp only [sliceCoefficientPolynomial, eval_finsetSum, harmonicSliceComponent, WithLp.ofLp_sum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hkr : k ≤ r
  · simp only [hkr, ite_true, eval_mul, eval_C, eval_comp, eval_sub, eval_X,
      ← falling_eq_descPochhammer, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp [hkr]

theorem sliceCoefficientPolynomial_natDegree {n : ℕ}
    (h : (r k : ℕ) → HomogeneousSpace n k) (d k : ℕ) (S : HomogeneousIndex n k) :
    (sliceCoefficientPolynomial h d k S).natDegree ≤ d - k := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro r hr
  by_cases hkr : k ≤ r
  · rw [ite_eq_left hkr]
    calc
      _ ≤ (C (h r k S) : Polynomial ℝ).natDegree +
          ((descPochhammer ℝ (r - k)).comp (X - C (k : ℝ))).natDegree := natDegree_mul_le
      _ = r - k := by simp only [natDegree_C, natDegree_comp, descPochhammer_natDegree,
          natDegree_X_sub_C, mul_one, zero_add]
      _ ≤ d - k := by have := Finset.mem_range.mp hr; omega
  · simp [hkr]

/-- Equation (28) with the coefficient polynomials and their precise degree bounds. -/
theorem exists_harmonic_norm_polynomials {n d : ℕ} (f : BooleanPolynomial n)
    (hn : 0 < n) (hd : 2 * d ≤ n) (hf : BooleanDegreeLE f d) :
    ∃ p : (k : ℕ) → HomogeneousIndex n k → Polynomial ℝ,
      (∀ k S, (p k S).natDegree ≤ d - k) ∧
      ∀ s : ℝ, sliceFunctional n s (f ^ 2) =
        ∑ k ∈ Finset.range (d + 1),
          (falling s k * falling ((n : ℝ) - s) k / falling n (2 * k)) *
            ∑ S : HomogeneousIndex n k, ((p k S).eval s) ^ 2 := by
  obtain ⟨h, _, he⟩ := boolean_harmonic_norm_formula f hn hd hf
  refine ⟨sliceCoefficientPolynomial h d, sliceCoefficientPolynomial_natDegree h d, ?_⟩
  intro s
  simpa only [sliceCoefficientPolynomial_eval] using he s

end NoncommutativeAMGM
