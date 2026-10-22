/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Partial derivatives: the chain rule and vanishing derivatives

Partial derivatives commute with homomorphisms of polynomial algebras by the chain rule.
If `∂f/∂xᵢ = 0`, then each exponent of `xᵢ` occurring in `f` is zero in the coefficient ring.
Below the characteristic this means that `xᵢ` does not occur in `f`.

## Main results

* `MvPolynomial.pderiv_algHom`: the chain rule for a homomorphism of polynomial algebras.
* `CharP.natCast_ne_zero_of_lt`: a positive natural number below the characteristic is nonzero.
* `MvPolynomial.coeff_mul_natCast_eq_zero_of_pderiv_eq_zero`: the coefficient of `m` is
  annihilated by the exponent `m i`.
* `MvPolynomial.notMem_vars_of_pderiv_eq_zero`: a variable with vanishing partial derivative does
  not occur, when its exponents are nonzero in the coefficient ring.
* `MvPolynomial.exists_pderiv_ne_zero`: a nonconstant polynomial of total degree below the
  characteristic has a nonzero partial derivative.
-/

@[expose] public section

namespace CharP

/-- A positive natural number below the characteristic is nonzero. -/
theorem natCast_ne_zero_of_lt (R : Type*) [AddMonoidWithOne R] {p : ℕ} [CharP R p] {n : ℕ}
    (hn : n ≠ 0) (hnp : n < p) : (n : R) ≠ 0 := fun h =>
  Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) hnp ((cast_eq_zero_iff R p n).mp h)

end CharP

namespace MvPolynomial

/-- The polynomial chain rule for a homomorphism of polynomial algebras. -/
theorem pderiv_algHom {K σ τ : Type*} [CommRing K] [Fintype σ]
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (f : MvPolynomial σ K) (k : τ) :
    pderiv k (φ f) = ∑ i, φ (pderiv i f) * pderiv k (φ (X i)) := by
  classical
  have hC (a : K) : φ (C a) = C a := φ.commutes a
  induction f using MvPolynomial.induction_on with
  | C a => simp [hC]
  | add f g hf hg => simp only [map_add, hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f j hf =>
    rw [map_mul, pderiv_mul, hf]
    calc
      _ = ∑ i, (φ (pderiv i f) * φ (X j) * pderiv k (φ (X i)) +
          if j = i then φ f * pderiv k (φ (X i)) else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : j = i <;>
          simp [pderiv_X, hi, add_mul, mul_comm, add_comm]

variable {R σ : Type*}

/-- If `∂f/∂xᵢ = 0`, then the coefficient of `f` at `m` is annihilated by the exponent `m i`. -/
theorem coeff_mul_natCast_eq_zero_of_pderiv_eq_zero [CommSemiring R] {f : MvPolynomial σ R}
    {i : σ} (h : pderiv i f = 0) (m : σ →₀ ℕ) : f.coeff m * (m i : R) = 0 := by
  classical
  rcases Nat.eq_zero_or_pos (m i) with hmi | hmi
  · simp [hmi]
  have hu : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    refine tsub_add_cancel_of_le fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hji
    · simpa using Nat.one_le_iff_ne_zero.mpr hmi.ne'
    · simp [Finsupp.single_eq_of_ne hji]
  have hc : (pderiv i f).coeff (m - Finsupp.single i 1) = 0 := by simp [h]
  rw [coeff_pderiv, hu, Finsupp.tsub_apply, Finsupp.single_eq_same,
    ← Nat.cast_add_one, Nat.sub_add_cancel hmi] at hc
  exact hc

/-- A variable with vanishing partial derivative does not occur in `f`, provided the positive
natural numbers up to its degree are nonzero in `R`. -/
theorem notMem_vars_of_pderiv_eq_zero [CommSemiring R] [NoZeroDivisors R]
    {f : MvPolynomial σ R} {i : σ} (h : pderiv i f = 0)
    (hchar : ∀ n : ℕ, 0 < n → n ≤ f.degreeOf i → (n : R) ≠ 0) : i ∉ f.vars := by
  classical
  intro hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  exact mul_ne_zero (mem_support_iff.mp hm)
    (hchar _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmi)) (monomial_le_degreeOf i hm))
    (coeff_mul_natCast_eq_zero_of_pderiv_eq_zero h m)

/-- A polynomial of positive total degree has a nonzero partial derivative, provided the
positive natural numbers up to its total degree are nonzero in `R`. -/
theorem exists_pderiv_ne_zero [CommSemiring R] [NoZeroDivisors R] {f : MvPolynomial σ R}
    (hpos : 0 < f.totalDegree)
    (hchar : ∀ n : ℕ, 0 < n → n ≤ f.totalDegree → (n : R) ≠ 0) :
    ∃ i, pderiv i f ≠ 0 := by
  classical
  obtain ⟨m, hm, i, hi⟩ : ∃ m ∈ f.support, ∃ i, m i ≠ 0 := by
    by_contra! h
    exact hpos.ne' ((totalDegree_eq_zero_iff (p := f)).mpr h)
  refine ⟨i, fun hz ↦ notMem_vars_of_pderiv_eq_zero hz
    (fun n hn hle ↦ hchar n hn (hle.trans (degreeOf_le_totalDegree f i))) ?_⟩
  exact (mem_vars_iff_mem_support i).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hi⟩

end MvPolynomial
