/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.BlockKeys
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring

/-!
# Polynomial expansion at one level

The multinomial expansion of the two generators gives the higher digits.
Multiplication by the low - degree polynomial attaches the units digit.
Mathlib's `Finset.sum_pow_eq_sum_piAntidiag` enumerates the multiplicity vectors.
-/

@[expose] public section

open Finset Polynomial
open scoped BigOperators

namespace Autoconvolutions.Blocks

/-- A set of digit positions, with the units position reserved. The index
`i = 0` corresponds to the first position above the units digit. -/
noncomputable def gen {m : ℕ} (D : ℕ) (I : Finset (Fin m)) : Polynomial ℝ :=
  ∑ i ∈ I, X ^ (D * D ^ i.val)

@[simp] theorem eval_gen_one {m : ℕ} (D : ℕ) (I : Finset (Fin m)) :
    (gen D I).eval 1 = (I.card : ℝ) := by
  simp [gen, Polynomial.eval_finsetSum]

/-- Expand the `u` independent selections of a position in `I` by their multiplicities. -/
theorem gen_pow {m : ℕ} (D : ℕ) (I : Finset (Fin m)) (u : ℕ) :
    (gen D I) ^ u = ∑ a ∈ I.piAntidiag u,
      monomial (D * code D a) (Nat.multinomial I a : ℝ) := by
  classical
  rw [gen, Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_congr rfl
  intro a ha
  have he : (∑ i ∈ I, a i * D ^ i.val) = code D a := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [(not_imp_comm.mp ((Finset.mem_piAntidiag.mp ha).2 i)) hi]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ i ∈ I, (D * D ^ i.val) * a i) = D * code D a := by
    rw [← he, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsum, ← Polynomial.C_eq_natCast, Polynomial.C_mul_X_pow_eq_monomial]

/-- Expand a polynomial whose coefficients vanish from `D` onward, including when `D=0`. -/
private theorem sum_monomials_below (B : Polynomial ℝ) (D : ℕ)
    (hB : ∀ h, D ≤ h → B.coeff h = 0) :
    B = ∑ h ∈ range D, monomial h (B.coeff h) := by
  classical
  calc
    B = ∑ h ∈ B.support, monomial h (B.coeff h) := B.as_sum_support
    _ = _ := by
      apply Finset.sum_subset
      · intro h hh
        exact mem_range.mpr (by_contra fun hn =>
          (Polynomial.mem_support_iff.mp hh) (hB h (Nat.le_of_not_gt hn)))
      · intro h _ hh
        simp [Polynomial.notMem_support_iff.mp hh]

/-- The paper's `W_s B_s` written as monomials indexed by two multiplicity
vectors and a low digit. Independently of injectivity this polynomial identity
counts each selection with its exact multinomial weight. -/
theorem expand_level {m : ℕ} (D : ℕ) (I J : Finset (Fin m)) (u v : ℕ)
    (B : Polynomial ℝ) (hB : ∀ h, D ≤ h → B.coeff h = 0) :
    (gen D I) ^ u * (gen D J) ^ v * B =
      ∑ t ∈ rows I J u v D, monomial (rowKey D t)
        ((Nat.multinomial I t.1.1 : ℝ) * (Nat.multinomial J t.1.2 : ℝ) * B.coeff t.2) := by
  classical
  rw [gen_pow, gen_pow]
  conv_lhs => rhs; rw [sum_monomials_below B D hB]
  simp only [rows, Finset.sum_product, Finset.sum_mul, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, rowKey, key, Nat.mul_add]
  conv_lhs =>
    enter [2, h]
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro h _
  rw [add_comm (D * code D a + D * code D b) h]

end Autoconvolutions.Blocks
