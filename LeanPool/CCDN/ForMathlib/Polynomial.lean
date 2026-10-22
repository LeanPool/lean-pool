/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Finite differences, derivatives and resultants of univariate polynomials

## Main results

* `Polynomial.natDegree_comp_X_add_C_sub_self` and
  `Polynomial.leadingCoeff_comp_X_add_C_sub_self`: in characteristic zero, the finite difference
  `P(X + s) - P(X)` of a polynomial of degree `m + 1` with step `s ≠ 0` has degree `m` and
  leading coefficient `P.leadingCoeff * (m + 1) * s`.
* `Polynomial.derivative_ne_zero_of_natCast_natDegree_ne_zero`: a polynomial whose degree is
  nonzero in the coefficient ring has nonzero derivative.
* `Polynomial.exists_divided_difference`: the divided difference `(f(y) - f(z)) / (y - z)` exists
  and is congruent to `f'(z)` modulo `y - z`.
* `Matrix.natDegree_det_le`, `Polynomial.natDegree_resultant_le`: degree bounds for determinants
  and Sylvester resultants of polynomials in a coefficient parameter, independent of the
  eliminated variable.
* `Polynomial.resultant_ne_zero_of_irreducible_of_natDegree_lt`: padding the second Sylvester
  degree preserves nonvanishing when the first polynomial is irreducible.
-/

@[expose] public section

namespace Polynomial

section FiniteDifference

variable {K : Type*} [Field K] [CharZero K]

private theorem natDegree_and_leadingCoeff_comp_X_add_C_sub_self
    (P : K[X]) {m : ℕ} (hm : P.natDegree = m + 1) (s : K) (hs : s ≠ 0) :
    (P.comp (X + C s) - P).natDegree = m ∧
      (P.comp (X + C s) - P).leadingCoeff = P.leadingCoeff * (m + 1) * s := by
  have hP : P ≠ 0 := by
    intro h
    simp [h] at hm
  have hhasse : (hasseDeriv m P).natDegree ≤ 1 := by
    have h := natDegree_hasseDeriv_le P m
    omega
  have hform := eq_X_add_C_of_natDegree_le_one hhasse
  have hcoeff : (P.comp (X + C s) - P).coeff m =
      P.leadingCoeff * (m + 1) * s := by
    rw [coeff_sub, ← taylor_apply, taylor_coeff, hform]
    simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
      zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    rw [show 1 + m = m + 1 by omega, Nat.choose_succ_self_right, ← hm,
      coeff_natDegree]
    rw [hm, Nat.cast_add, Nat.cast_one]
    ring
  have hcoeff0 : (P.comp (X + C s) - P).coeff m ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
      (Nat.cast_add_one_ne_zero m)) hs
  have hdiff0 : P.comp (X + C s) - P ≠ 0 := by
    intro h
    simp [h] at hcoeff0
  have hdeg : (P.comp (X + C s) - P).natDegree = m := by
    apply le_antisymm
    · have hlt := degree_sub_lt_right (degree_taylor P s) hP (leadingCoeff_taylor s P)
      change (P.comp (X + C s) - P).degree < P.degree at hlt
      rw [degree_eq_natDegree hdiff0, degree_eq_natDegree hP, Nat.cast_lt] at hlt
      omega
    · exact le_natDegree_of_ne_zero hcoeff0
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]⟩

/-- In characteristic zero, the finite difference `P(X + s) - P(X)` with step `s ≠ 0` lowers
the degree by exactly one. -/
theorem natDegree_comp_X_add_C_sub_self (P : K[X]) {m : ℕ} (hm : P.natDegree = m + 1)
    (s : K) (hs : s ≠ 0) : (P.comp (X + C s) - P).natDegree = m :=
  (natDegree_and_leadingCoeff_comp_X_add_C_sub_self P hm s hs).1

/-- In characteristic zero, the finite difference `P(X + s) - P(X)` with step `s ≠ 0` of a
polynomial of degree `m + 1` has leading coefficient `P.leadingCoeff * (m + 1) * s`. -/
theorem leadingCoeff_comp_X_add_C_sub_self (P : K[X]) {m : ℕ} (hm : P.natDegree = m + 1)
    (s : K) (hs : s ≠ 0) :
    (P.comp (X + C s) - P).leadingCoeff = P.leadingCoeff * (m + 1) * s :=
  (natDegree_and_leadingCoeff_comp_X_add_C_sub_self P hm s hs).2

end FiniteDifference

/-- A polynomial whose degree `n` satisfies `(n : R) ≠ 0` has nonzero derivative. -/
theorem derivative_ne_zero_of_natCast_natDegree_ne_zero {R : Type*} [Semiring R]
    [NoZeroDivisors R] {f : R[X]} (hn : (f.natDegree : R) ≠ 0) : derivative f ≠ 0 := by
  have hpos : 0 < f.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    rintro h
    simp [h] at hn
  have hf : f ≠ 0 := by intro h; simp [h] at hpos
  intro hz
  have hc := congrArg (fun g : R[X] => g.coeff (f.natDegree - 1)) hz
  rw [coeff_derivative, show f.natDegree - 1 + 1 = f.natDegree by omega, coeff_zero] at hc
  have he : ((f.natDegree - 1 : ℕ) : R) + 1 = (f.natDegree : R) := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hpos]
  rw [he] at hc
  exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hf) hn) hc

/-- Divided differences agree with the derivative modulo the argument difference. -/
theorem exists_divided_difference {R : Type*} [CommRing R]
    (f : R[X]) (y z : R) :
    ∃ q : R, f.eval y - f.eval z = (y - z) * q ∧
      y - z ∣ q - f.derivative.eval z := by
  have hd : X - C z ∣ f - C (f.eval z) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot]
  obtain ⟨g, hg⟩ := hd
  have he := congrArg (Polynomial.eval y) hg
  simp only [eval_sub, eval_C, eval_mul, eval_X] at he
  have hder := congrArg (fun p : R[X] => p.derivative.eval z) hg
  simp only [derivative_sub, derivative_C, sub_zero, derivative_mul,
    derivative_X, derivative_sub, eval_add, eval_mul, eval_sub,
    eval_X, eval_C, sub_self, zero_mul, one_mul, add_zero] at hder
  refine ⟨g.eval y, he, ?_⟩
  rw [hder]
  exact Polynomial.sub_dvd_eval_sub y z g

end Polynomial

namespace Matrix

open Polynomial

/-- The degree of a determinant of polynomials is at most the size times an entrywise degree
bound. -/
theorem natDegree_det_le {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R[X]) (D : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, D := Finset.sum_le_sum fun i _ => hM (σ i) i
    _ = _ := by simp

end Matrix

namespace Polynomial

/-- The degree in the coefficient parameter of a Sylvester resultant is at most the Sylvester
size times a coefficientwise degree bound. -/
theorem natDegree_resultant_le {R : Type*} [CommRing R]
    (f g : R[X][X]) (m n D : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (f.resultant g m n).natDegree ≤ (m + n) * D := by
  have hM : ∀ i j, (f.sylvester g m n i j).natDegree ≤ D := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hg _
      · simp
    | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hf _
      · simp
  simpa only [Fintype.card_fin, resultant] using Matrix.natDegree_det_le (f.sylvester g m n) D hM

/-- Padding the second Sylvester degree preserves nonvanishing when the
first polynomial is irreducible and the second is nonzero of smaller degree. -/
theorem resultant_ne_zero_of_irreducible_of_natDegree_lt
    {K : Type*} [Field K] (f g : K[X]) (hf : Irreducible f) (hg : g ≠ 0)
    (hdeg : g.natDegree < f.natDegree) (n : ℕ) (hn : g.natDegree ≤ n) :
    f.resultant g f.natDegree n ≠ 0 := by
  have hcop : IsCoprime f g := hf.coprime_iff_not_dvd.mpr fun h =>
    (not_le_of_gt hdeg) (natDegree_le_of_dvd h hg)
  have he : n = g.natDegree + (n - g.natDegree) := by omega
  rw [he, resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf.ne_zero))
    (resultant_ne_zero f g hcop)

end Polynomial
