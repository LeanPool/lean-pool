/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Height.Box
import LeanPool.CCDN.LowerBound.GridMultivariate
import LeanPool.CCDN.Noether.ShearNormalization
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Section 6, Lemma 6.1: an absolutely irreducible rational equation
of prescribed degree vanishes on the entire stated integer box. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For `d > 0` and `n ≥ 2`, there is a polynomial over `K` in `n` variables of total degree `d`
that stays irreducible over `L` along `φ : K →+* L` and vanishes at both `0` and `(1, …, 1)`. -/
lemma exists_irreducible_zero_one_equation
    {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    ∃ f : MvPolynomial (Fin n) K,
      f.totalDegree = d ∧ Irreducible (map φ f) ∧
        eval (0 : Fin n → K) f = 0 ∧ eval (fun _ => (1 : K)) f = 0 := by
  classical
  let f : MvPolynomial (Fin 2) K := X 0 - X 1 ^ d
  have hfdeg : f.totalDegree = d := by
    apply le_antisymm
    · exact (totalDegree_sub _ _).trans (by simp [max_eq_right (show 1 ≤ d by omega)])
    · have he : bivariatePolynomialEquiv K f =
          Polynomial.X - Polynomial.C (Polynomial.X ^ d) := by
        simp [f, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
      have hc : (((bivariatePolynomialEquiv K f).coeff 0).coeff d : K) ≠ 0 := by
        rw [he]
        simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
          Polynomial.coeff_neg, Polynomial.coeff_X_pow, ite_true, zero_sub, neg_ne_zero]
        exact _root_.one_ne_zero
      have hh := bivariateTotalDegree_coeff_le (bivariatePolynomialEquiv K f) 0 d hc
      simpa [bivariateTotalDegree] using hh
  have hfir : Irreducible (map φ f) := by
    apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)).mp
    simp only [f, map_sub, map_pow, map_X, bivariatePolynomialEquiv_X_zero,
      bivariatePolynomialEquiv_X_one]
    rw [← Polynomial.C_pow]
    exact Polynomial.irreducible_X_sub_C (Polynomial.X ^ d : Polynomial L)
  let i : Fin 2 → Fin n := Fin.castLE hn
  have hi : Function.Injective i := Fin.castLE_injective hn
  let r : Fin n → Fin 2 := fun j => if j.val = 0 then 0 else 1
  have hr : Function.LeftInverse r i := by
    intro j
    fin_cases j <;> simp [r, i]
  refine ⟨rename i f, ?_, ?_, ?_, ?_⟩
  · rw [totalDegree_rename_of_leftInverse i r hr, hfdeg]
  · rw [map_rename]
    exact irreducible_rename_of_injective i hi _ hfir
  · simp [f, ne_of_gt hd]
  · simp [f]

/-- For `d > 0` and `n ≥ 2`, there is a polynomial over `K` in `n` variables of total degree `d`
that stays irreducible over `L` along `φ : K →+* L` and vanishes at the origin; this supplies the
degree-`d` examples in every positive degree of CCDN Section 6. -/
lemma exists_irreducible_origin_equation
    {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    ∃ f : MvPolynomial (Fin n) K,
      f.totalDegree = d ∧ Irreducible (map φ f) ∧ eval (0 : Fin n → K) f = 0 := by
  obtain ⟨f, hfdeg, hfir, hfzero, _⟩ := exists_irreducible_zero_one_equation φ d n hd hn
  exact ⟨f, hfdeg, hfir, hfzero⟩

/-- CCDN Lemma 6.1. The radius is exactly floor((d−1)/(2n)). -/
theorem exists_absolutely_irreducible_integer_grid (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    ∃ f : MvPolynomial (Fin n) ℚ,
      f.totalDegree = d ∧ AbsolutelyIrreducibleRat f ∧
        ∀ z : IntPoint n, (∀ i, |z i| ≤ ((d - 1) / (2 * n) : ℕ)) →
          eval (rationalPoint z) f = 0 := by
  classical
  let r := (d - 1) / (2 * n)
  have hr : 4 * r ≤ d - 1 := by
    have hdiv := Nat.mul_div_le (d - 1) (2 * n)
    change 2 * n * r ≤ d - 1 at hdiv
    nlinarith
  by_cases hsmall : d ≤ 2
  · have hr0 : r = 0 := by omega
    obtain ⟨f, hfdeg, hfir, hfzero⟩ := exists_irreducible_origin_equation
      (algebraMap ℚ (AlgebraicClosure ℚ)) d n (by omega) hn
    refine ⟨f, hfdeg, hfir, ?_⟩
    intro z hz
    have hzero : rationalPoint z = 0 := by
      funext i
      have hi := hz i
      change |z i| ≤ (r : ℤ) at hi
      rw [hr0, Nat.cast_zero] at hi
      have hz0 : z i = 0 := abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
      simp [rationalPoint, hz0]
    rwa [hzero]
  · let s : Finset ℚ := (Finset.Icc (-(r : ℤ)) (r : ℤ)).image (Int.castRingHom ℚ)
    have hcard : s.card = 2 * r + 1 := by
      change ((Finset.Icc (-(r : ℤ)) (r : ℤ)).image (fun x : ℤ => (x : ℚ))).card = _
      rw [Finset.card_image_of_injective _ Int.cast_injective, Int.card_Icc]
      omega
    have hsd : s.card + 2 ≤ d := by
      rw [hcard]
      by_cases hzero : r = 0
      · omega
      · omega
    have hssize : 2 * s.card ≤ d + 1 := by rw [hcard]; omega
    obtain ⟨f, hfdeg, hfir, hfzero⟩ := exists_absolutely_irreducible_grid
      (algebraMap ℚ (AlgebraicClosure ℚ)) s (by rw [hcard]; omega) d n hn hsd hssize
    refine ⟨f, hfdeg, hfir, ?_⟩
    intro z hz
    apply hfzero
    intro i
    apply Finset.mem_image.mpr
    refine ⟨z i, ?_, rfl⟩
    exact Finset.mem_Icc.mpr (abs_le.mp (hz i))

end
end CCDN
