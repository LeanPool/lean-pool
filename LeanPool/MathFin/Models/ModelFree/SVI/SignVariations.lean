/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Matrix.Spectrum

/-! # Descartes' rule of signs when every root is real

Part of the SVI polynomial-sign certificate (#174).

For a real polynomial that splits, the number of sign variations equals the number of positive
roots with multiplicity (`signVariations_eq_pos_roots`). For a real symmetric matrix this gives the
number of positive minus the number of negative characteristic roots as the difference of the sign
variations of `charpoly` and `charpoly.comp (-X)` (`signatureTest_eq_root_counts`).

## Main results

* `signVariations_pair_bound`:
  `P.signVariations + (P.comp (-X)).signVariations + P.natTrailingDegree ≤ P.natDegree`.
* `signVariations_eq_pos_roots`: if `P.Splits`, `P.signVariations` equals the number of positive
  roots counted with multiplicity.
* `signatureTest_eq_root_counts`: for a symmetric real matrix, the sign variations of `charpoly`
  minus those of `charpoly.comp (-X)` equal the number of positive minus the number of negative
  characteristic roots.

## Tags

Descartes rule of signs, sign variations, positive roots, real-rooted polynomial, SVI, MSC 91G20,
JEL G13
-/

@[expose] public section


namespace MathFin
namespace SVI
open Polynomial

/-- Substituting `-X` into a monomial multiplies its coefficient by `(-1)^n`. -/
theorem monomial_comp_neg (n : ℕ) (a : ℝ) :
    (monomial n a).comp (-X) = monomial n (a * (-1)^n) := by
  rw [monomial_comp, ← C_mul_X_pow_eq_monomial]
  rw [C_mul, C_pow]
  simp only [C_neg, C_1]
  rw [neg_pow]
  ring

/-- Erasing the leading term commutes with the substitution `X ↦ -X`. -/
theorem eraseLead_comp_neg (P : ℝ[X]) :
    (P.comp (-X)).eraseLead = P.eraseLead.comp (-X) := by
  rw [← self_sub_monomial_natDegree_leadingCoeff,
    ← self_sub_monomial_natDegree_leadingCoeff P, sub_comp, monomial_comp_neg]
  simp only [natDegree_comp, natDegree_neg, natDegree_X, one_mul,
    comp_neg_X_leadingCoeff_eq, mul_comm]

/-- Erasing the leading term of a polynomial with nonzero remainder keeps its trailing degree. -/
theorem natTrailingDegree_eraseLead (P : ℝ[X]) (h : P.eraseLead ≠ 0) :
    P.eraseLead.natTrailingDegree = P.natTrailingDegree := by
  have hd : P.eraseLead.natDegree < P.natDegree :=
    P.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right h
  have hcoef := coeff_natTrailingDegree_ne_zero.mpr h
  have hle : P.natTrailingDegree ≤ P.eraseLead.natTrailingDegree := by
    apply natTrailingDegree_le_of_ne_zero
    rw [← eraseLead_coeff_of_ne _ (ne_of_lt
      ((natTrailingDegree_le_natDegree P.eraseLead).trans_lt hd))]
    exact hcoef
  apply le_antisymm _ hle
  apply natTrailingDegree_le_of_ne_zero
  rw [eraseLead_coeff_of_ne _ (ne_of_lt (hle.trans_lt
    ((natTrailingDegree_le_natDegree P.eraseLead).trans_lt hd)))]
  apply coeff_natTrailingDegree_ne_zero.mpr
  intro hp
  simp [hp] at h

/-- For nonzero `x`, `y`, `u`, exactly one of the sign-change tests for `(x, y)` and
`(-u*x, u*y)` holds. -/
theorem sign_pair_step (x y u : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hu : u ≠ 0) :
    (if SignType.sign x = -SignType.sign y then 1 else 0) +
      (if SignType.sign (-u*x) = -SignType.sign (u*y) then 1 else 0) = (1 : ℕ) := by
  have hsx : SignType.sign x ≠ 0 := by simpa using hx
  have hsy : SignType.sign y ≠ 0 := by simpa using hy
  have hsu : SignType.sign u ≠ 0 := by simpa using hu
  simp only [sign_mul, Left.sign_neg]
  cases hxx : SignType.sign x <;> cases hyy : SignType.sign y <;>
    cases huu : SignType.sign u <;> simp_all

/-- The two Descartes counts cannot exceed the number of nonzero roots
available in a completely split polynomial. This bound itself needs no split
hypothesis. -/
theorem signVariations_pair_bound (P : ℝ[X]) :
    P.signVariations + (P.comp (-X)).signVariations + P.natTrailingDegree ≤ P.natDegree := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | ind n ih =>
    by_cases hp : P = 0
    · simp [hp]
    by_cases he : P.eraseLead = 0
    · have hm := P.eraseLead_add_monomial_natDegree_leadingCoeff
      rw [he, zero_add] at hm
      rw [← hm]
      simp only [monomial_comp_neg, signVariations_monomial,
        natTrailingDegree_monomial (leadingCoeff_ne_zero.mpr hp), zero_add]
      exact hn.le
    have hd : P.eraseLead.natDegree < P.natDegree :=
      P.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right he
    have hind := ih _ (hn ▸ hd) P.eraseLead rfl
    rw [natTrailingDegree_eraseLead P he] at hind
    have hpn : P.comp (-X) ≠ 0 := by simpa using hp
    rw [signVariations_eq_eraseLead_add_ite hp,
      signVariations_eq_eraseLead_add_ite hpn, eraseLead_comp_neg]
    by_cases hgap : P.natDegree = P.eraseLead.natDegree + 1
    · have hstep := sign_pair_step P.leadingCoeff P.eraseLead.leadingCoeff
        ((-1 : ℝ)^P.eraseLead.natDegree) (leadingCoeff_ne_zero.mpr hp)
        (leadingCoeff_ne_zero.mpr he) (pow_ne_zero _ (by norm_num))
      simp only [comp_neg_X_leadingCoeff_eq]
      rw [hgap, pow_succ]
      have hh : (-1 : ℝ)^P.eraseLead.natDegree * -1 * P.leadingCoeff =
          -((-1 : ℝ)^P.eraseLead.natDegree) * P.leadingCoeff := by ring
      rw [hh]
      omega
    · have h1 : (if SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff
          then 1 else 0) ≤ (1 : ℕ) := by split <;> omega
      have h2 : (if SignType.sign (P.comp (-X)).leadingCoeff =
          -SignType.sign (P.eraseLead.comp (-X)).leadingCoeff then 1 else 0) ≤ (1 : ℕ) :=
        by split <;> omega
      omega

/-- A real multiset splits into its positive, negative and zero elements. -/
theorem countP_pos_add_countP_neg_add_count_zero (s : Multiset ℝ) :
    s.countP (0 < ·) + s.countP (· < 0) + s.count 0 = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rcases lt_trichotomy a 0 with ha | rfl | ha
    · simp [ha, not_lt_of_ge ha.le, Ne.symm (ne_of_lt ha)]
      omega
    · simp
      omega
    · simp [ha, not_lt_of_ge ha.le, Ne.symm (ne_of_gt ha)]
      omega

/-- Descartes' rule is exact when all roots are real, with multiplicities and
zero roots handled without nondegeneracy assumptions. -/
theorem signVariations_eq_pos_roots (P : ℝ[X]) (hs : P.Splits) :
    P.signVariations = P.roots.countP (0 < ·) := by
  have hpos := P.roots_countP_pos_le_signVariations
  have hneg := (P.comp (-X)).roots_countP_pos_le_signVariations
  simp only
      [roots_comp_neg_X, Multiset.countP_map, neg_pos, ← Multiset.countP_eq_card_filter] at hneg
  have hbound := signVariations_pair_bound P
  have hsum := countP_pos_add_countP_neg_add_count_zero P.roots
  rw [count_roots, rootMultiplicity_eq_natTrailingDegree', ← hs.natDegree_eq_card_roots] at hsum
  omega

/-- The exact characteristic-coefficient rule for any real symmetric matrix. -/
theorem signatureTest_eq_root_counts {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) :
    ((M.charpoly.signVariations : ℤ) - ((M.charpoly.comp (-X)).signVariations : ℤ)) =
    (M.charpoly.roots.countP (0 < ·) : ℤ) - (M.charpoly.roots.countP (· < 0) : ℤ) := by
  have hh : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  have hs := hh.splits_charpoly
  rw [signVariations_eq_pos_roots _ hs, signVariations_eq_pos_roots _ hs.comp_neg_X]
  simp only [roots_comp_neg_X, Multiset.countP_map, neg_pos, ← Multiset.countP_eq_card_filter]

end SVI
end MathFin
