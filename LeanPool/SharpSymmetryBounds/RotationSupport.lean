/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic

/-!
# Polynomial support under a high-order rotation

This file concerns polynomials, not their real zero sets. In particular, a
polynomial transformation identity is a hypothesis, not a consequence assumed
from a geometric symmetry without proof.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Complex plane polynomials in the coordinates `X = z`, `Y = conj z`. -/
abbrev BPoly := MvPolynomial (Fin 2) ℂ
/-- Exponents of monomials in two variables. -/
abbrev Exponent := Fin 2 →₀ ℕ

/-- Rotation by `ζ` in complex coordinates: `X ↦ ζ X`, `Y ↦ ζ⁻¹ Y`. -/
noncomputable def rotate (ζ : ℂ) : BPoly →+* BPoly :=
  eval₂Hom C (fun i => C (if i = 0 then ζ else ζ⁻¹) * X i)

lemma exponent_decompose (s : Exponent) :
    s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) := by
  ext i
  fin_cases i <;> simp

lemma exponent_degree (s : Exponent) : s.sum (fun _ e => e) = s 0 + s 1 := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

lemma rotate_monomial (ζ : ℂ) (s : Exponent) (c : ℂ) :
    rotate ζ (monomial s c) = monomial s (c * (ζ ^ s 0 * (ζ⁻¹) ^ s 1)) := by
  simp only [rotate, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, mul_pow,
    ← map_pow C, X_pow_eq_monomial]
  rw [show s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) from exponent_decompose s]
  simp only [C_mul_monomial, monomial_mul_monomial, mul_one]
  simp

lemma coeff_rotate (ζ : ℂ) (P : BPoly) (s : Exponent) :
    (rotate ζ P).coeff s = P.coeff s * (ζ ^ s 0 * (ζ⁻¹) ^ s 1) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial t c =>
      rw [rotate_monomial]
      by_cases h : t = s
      · subst t; simp
      · simp [coeff_monomial, h]
  | add P Q hP hQ => simp [map_add, hP, hQ, add_mul]

lemma primitive_half_turn {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) : ζ ^ m = -1 := by
  have hs : (ζ ^ m) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 2]
    exact hζ.pow_eq_one
  rcases (sq_eq_one_iff).mp hs with h | h
  · exact (hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega) h).elim
  · exact h

/-- Below degree `2m`, an anti-invariant monomial has weight `m` or `-m`. -/
theorem anti_weight {m a b : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) (hdeg : a + b < 2 * m)
    (hanti : ζ ^ a * (ζ⁻¹) ^ b = -1) : a = b + m ∨ b = a + m := by
  have hz : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hhalf := primitive_half_turn hm hζ
  have hp : ζ ^ a = -(ζ ^ b) := by
    rw [inv_pow, ← div_eq_mul_inv] at hanti
    simpa using (div_eq_iff (pow_ne_zero b hz)).mp hanti
  by_cases hb : b < m
  · left
    apply hζ.pow_inj (by omega) (by omega)
    simpa [pow_add, hhalf] using hp
  · right
    apply hζ.pow_inj (by omega) (by omega)
    simp [pow_add, hhalf, hp]

lemma support_degree {P : BPoly} {s : Exponent} (hs : s ∈ P.support) :
    s 0 + s 1 ≤ P.totalDegree := by
  simpa [exponent_degree] using le_totalDegree hs

/-- The weight restriction follows from an actual polynomial substitution identity. -/
theorem anti_support {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P)
    {s : Exponent} (hs : s ∈ P.support) : s 0 = s 1 + m ∨ s 1 = s 0 + m := by
  have hc : P.coeff s ≠ 0 := mem_support_iff.mp hs
  have heq := congrArg (fun Q : BPoly => Q.coeff s) hanti
  rw [coeff_rotate, coeff_neg] at heq
  have hchar : ζ ^ s 0 * (ζ⁻¹) ^ s 1 = -1 := by
    apply mul_left_cancel₀ hc
    simpa using heq
  exact anti_weight hm hζ (lt_of_le_of_lt (support_degree hs) hdeg) hchar

/-- The degree gap in the rotation bound, without any geometric hypotheses. -/
theorem anti_degree_gap {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P)
    (hnot : ¬ P.IsHomogeneous m) : m + 2 ≤ P.totalDegree := by
  by_contra hgap
  apply hnot
  intro s hs
  have hd := support_degree (mem_support_iff.mpr hs)
  have hw := anti_support hm hζ hdeg hanti (mem_support_iff.mpr hs)
  have he : s 0 + s 1 = m := by omega
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
  exact (exponent_degree s).trans he

/-- The exponent of the monomial `X^a Y^b`. -/
noncomputable def exponent (a b : ℕ) : Exponent :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma exponent_zero (a b : ℕ) : exponent a b 0 = a := by simp [exponent]
@[simp] lemma exponent_one (a b : ℕ) : exponent a b 1 = b := by simp [exponent]

lemma exponent_eq_iff {s : Exponent} {a b : ℕ} :
    s = exponent a b ↔ s 0 = a ∧ s 1 = b := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1⟩
    rw [exponent_decompose s, h0, h1]
    rfl

/-- At degree at most `m+2`, there are only four possible monomials. -/
theorem anti_four_support {m : ℕ} (hm : 3 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree ≤ m + 2) (hanti : rotate ζ P = -P)
    {s : Exponent} (hs : s ∈ P.support) :
    s = exponent m 0 ∨ s = exponent (m + 1) 1 ∨
      s = exponent 0 m ∨ s = exponent 1 (m + 1) := by
  have hd := support_degree hs
  have hw := anti_support (by omega) hζ (by omega) hanti hs
  simp only [exponent_eq_iff]
  omega

/-- The four-term normal form, with its coefficients extracted from `P`. -/
theorem anti_four_normal_form {m : ℕ} (hm : 3 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree ≤ m + 2) (hanti : rotate ζ P = -P) :
    P = monomial (exponent m 0) (P.coeff (exponent m 0)) +
      monomial (exponent (m + 1) 1) (P.coeff (exponent (m + 1) 1)) +
      monomial (exponent 0 m) (P.coeff (exponent 0 m)) +
      monomial (exponent 1 (m + 1)) (P.coeff (exponent 1 (m + 1))) := by
  classical
  have h01 : exponent m 0 ≠ exponent (m + 1) 1 := by
    simp [exponent_eq_iff]
  have h02 : exponent m 0 ≠ exponent 0 m := by
    simp [exponent_eq_iff]; omega
  have h03 : exponent m 0 ≠ exponent 1 (m + 1) := by
    simp [exponent_eq_iff]
  have h12 : exponent (m + 1) 1 ≠ exponent 0 m := by
    simp [exponent_eq_iff]
  have h13 : exponent (m + 1) 1 ≠ exponent 1 (m + 1) := by
    simp [exponent_eq_iff]; omega
  have h23 : exponent 0 m ≠ exponent 1 (m + 1) := by
    simp [exponent_eq_iff]
  ext s
  by_cases hs : s ∈ P.support
  · rcases anti_four_support hm hζ hdeg hanti hs with rfl | rfl | rfl | rfl <;>
      simp [coeff_monomial, h01, h02, h03, h12, h13, h23,
        Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]
  · have hc : P.coeff s = 0 := notMem_support_iff.mp hs
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, coeff_monomial]
    split_ifs <;> simp_all

lemma monomial_exponent (a b : ℕ) (c : ℂ) :
    monomial (exponent a b) c = C c * (X 0 : BPoly) ^ a * X 1 ^ b := by
  simp [X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial, exponent]

/-- Conjugate-symmetric coefficients give the two-parameter form used in the paper. -/
theorem anti_real_normal_form {m : ℕ} (hm : 3 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree ≤ m + 2) (hanti : rotate ζ P = -P)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    ∃ a b : ℂ, P = (X 0 : BPoly) ^ m * (C a + C b * X 0 * X 1) +
      X 1 ^ m * (C (star a) + C (star b) * X 0 * X 1) := by
  refine ⟨P.coeff (exponent m 0), P.coeff (exponent (m + 1) 1), ?_⟩
  calc
    P = monomial (exponent m 0) (P.coeff (exponent m 0)) +
        monomial (exponent (m + 1) 1) (P.coeff (exponent (m + 1) 1)) +
        monomial (exponent 0 m) (star (P.coeff (exponent m 0))) +
        monomial (exponent 1 (m + 1)) (star (P.coeff (exponent (m + 1) 1))) := by
          conv_lhs => rw [anti_four_normal_form hm hζ hdeg hanti]
          rw [hreal m 0, hreal (m + 1) 1]
    _ = _ := by simp only [monomial_exponent, pow_zero, pow_succ]; ring

/-- A polynomial fixed by a rotation of order greater than its degree is radial. -/
theorem fixed_support {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {P : BPoly}
    (hdeg : P.totalDegree < N) (hfixed : rotate ζ P = P)
    {s : Exponent} (hs : s ∈ P.support) : s 0 = s 1 := by
  have hc : P.coeff s ≠ 0 := mem_support_iff.mp hs
  have hd := support_degree hs
  have hz : ζ ≠ 0 := hζ.ne_zero (by omega)
  have heq := congrArg (fun Q : BPoly => Q.coeff s) hfixed
  rw [coeff_rotate] at heq
  have hchar : ζ ^ s 0 * (ζ⁻¹) ^ s 1 = 1 := by
    apply mul_left_cancel₀ hc
    simpa using heq
  rw [inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hz)] at hchar
  exact hζ.pow_inj (by omega) (by omega) hchar

/-- A nonzero polynomial can transform by the sign `-1` only at even order. -/
theorem anti_even_order {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {P : BPoly}
    (hP : P ≠ 0) (hanti : rotate ζ P = -P) : Even N := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP
  have heq := congrArg (fun Q : BPoly => Q.coeff s) hanti
  rw [coeff_rotate, coeff_neg] at heq
  have hchar : ζ ^ s 0 * (ζ⁻¹) ^ s 1 = -1 := by
    apply mul_left_cancel₀ hs
    simpa using heq
  have hpow : (-1 : ℂ) ^ N = 1 := by
    rw [← hchar, mul_pow, ← pow_mul, Nat.mul_comm (s 0) N, pow_mul, hζ.pow_eq_one]
    rw [← pow_mul, Nat.mul_comm (s 1) N, pow_mul, inv_pow, hζ.pow_eq_one]
    simp
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp hpow

/-- The polynomial core of the sharp rotation bound.

Non-radiality and exclusion of homogeneous binary forms are explicit hypotheses.
The later modules derive these exclusions from irreducibility and the
non-circle hypothesis; this lemma isolates the coefficient argument.
-/
theorem polynomial_rotation_bound {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) {P : BPoly} (hd : 2 ≤ P.totalDegree)
    (hnonradial : ∃ s ∈ P.support, s 0 ≠ s 1)
    (hhom : ∀ m : ℕ, 2 ≤ m → ¬ P.IsHomogeneous m)
    (hsign : rotate ζ P = P ∨ rotate ζ P = -P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  by_cases hsmall : N ≤ P.totalDegree
  · exact le_trans hsmall (le_max_left _ _)
  have hlarge : P.totalDegree < N := by omega
  rcases hsign with hfixed | hanti
  · obtain ⟨s, hs, hne⟩ := hnonradial
    exact (hne (fixed_support hζ hlarge hfixed hs)).elim
  · have hP : P ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨m, hN⟩ := anti_even_order hζ hP hanti
    have horder : N = 2 * m := by omega
    have hm : 2 ≤ m := by omega
    have hgap := anti_degree_gap (by omega) (horder ▸ hζ)
      (by omega) hanti (hhom m hm)
    exact le_trans (by omega : N ≤ 2 * P.totalDegree - 4) (le_max_right _ _)

end CurveSymmetry
