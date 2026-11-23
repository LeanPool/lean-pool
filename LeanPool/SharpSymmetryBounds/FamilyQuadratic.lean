/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.ReflectionBound
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# The quadratic strict transform

The strict transform of the extremal family after `X = t Y`, and its irreducibility by Eisenstein's
criterion after reversing the quadratic variable.
-/

@[expose] public section

namespace CurveSymmetry

open Polynomial

lemma unit_of_reverse_unit {R : Type*} [CommRing R] [IsDomain R]
    {p : Polynomial R} (hp : p.coeff 0 ≠ 0) (hu : IsUnit p.reverse) : IsUnit p := by
  have hd := natDegree_eq_zero_of_isUnit hu
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hp), Nat.sub_zero] at hd
  rw [eq_C_of_natDegree_eq_zero hd] at hu ⊢
  simpa using hu

lemma irreducible_of_reverse {R : Type*} [CommRing R] [IsDomain R]
    {p : Polynomial R} (hp : p.coeff 0 ≠ 0) (hi : Irreducible p.reverse) : Irreducible p := by
  refine ⟨?_, ?_⟩
  · intro hu
    obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp hu
    apply hi.not_isUnit
    rw [← he, reverse_C]
    exact hc.map C
  · intro a b he
    have hcoeff : a.coeff 0 * b.coeff 0 ≠ 0 := by simpa [he] using hp
    have hrev : p.reverse = a.reverse * b.reverse := by rw [he, reverse_mul_of_domain]
    rcases hi.isUnit_or_isUnit hrev with ha | hb
    · exact Or.inl (unit_of_reverse_unit (mul_ne_zero_iff.mp hcoeff).1 ha)
    · exact Or.inr (unit_of_reverse_unit (mul_ne_zero_iff.mp hcoeff).2 hb)

/-- The coefficient `α t^m + conj α` of the strict transform of the extremal family. -/
noncomputable def familyA (m : ℕ) (α : ℂ) : UPoly := C α * X ^ m + C (star α)
/-- The coefficient `t (t^m + 1)` of the strict transform of the extremal family. -/
noncomputable def familyB (m : ℕ) : UPoly := X * (X ^ m + 1)

/-- The strict-transform equation after the substitution `X = tY`. -/
noncomputable def familyQuadratic (m : ℕ) (α : ℂ) : NPoly :=
  C (familyA m α) + C (familyB m) * X ^ 2

/-- The strict-transform equation with the quadratic variable reversed. -/
noncomputable def familyReciprocal (m : ℕ) (α : ℂ) : NPoly :=
  C (familyB m) + C (familyA m α) * X ^ 2

lemma familyA_zero (m : ℕ) (hm : 0 < m) (α : ℂ) : (familyA m α).coeff 0 = star α := by
  simp [familyA, hm.ne]

lemma familyB_coeff_one (m : ℕ) (hm : 0 < m) : (familyB m).coeff 1 = 1 := by
  simp [familyB, hm.ne]

lemma familyB_ne_zero (m : ℕ) (hm : 0 < m) : familyB m ≠ 0 := by
  intro h
  have he := familyB_coeff_one m hm
  simp [h] at he

lemma family_coefficients_no_common_root {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (z : ℂ) :
    ¬ ((familyA m α).eval z = 0 ∧ (familyB m).eval z = 0) := by
  rintro ⟨hA, hB⟩
  simp only [familyA, familyB, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one] at hA hB
  rcases mul_eq_zero.mp hB with hz | hz
  · rw [hz, zero_pow hm.ne', mul_zero, zero_add] at hA
    apply ha
    have hα : α = 0 := star_eq_zero.mp hA
    simp [hα]
  · apply ha
    linear_combination α * hz - hA

lemma familyReciprocal_primitive {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    (familyReciprocal m α).IsPrimitive := by
  intro q hq
  by_contra hu
  have hd : q.degree ≠ 0 := by
    intro hd
    exact hu (isUnit_iff_degree_eq_zero.mpr hd)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root q hd
  have hdiv := (C_dvd_iff_dvd_coeff q _).mp hq
  have hA : q ∣ familyA m α := by simpa [familyReciprocal] using hdiv 2
  have hB : q ∣ familyB m := by simpa [familyReciprocal] using hdiv 0
  apply family_coefficients_no_common_root hm ha z
  constructor
  · exact dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hz).trans hA)
  · exact dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hz).trans hB)

/-- Eisenstein at `t = 0` applies after reversing the quadratic variable. -/
theorem familyReciprocal_irreducible {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Irreducible (familyReciprocal m α) := by
  have hα : α ≠ 0 := by intro hz; apply ha; simp [hz]
  have hA : familyA m α ≠ 0 := by
    intro h
    have he := familyA_zero m hm α
    rw [h, coeff_zero] at he
    exact (star_ne_zero.mpr hα) he.symm
  have hd : (familyReciprocal m α).natDegree = 2 := by
    simp [familyReciprocal, natDegree_C_mul hA]
  have hl : (familyReciprocal m α).leadingCoeff = familyA m α := by
    rw [leadingCoeff, hd]
    simp [familyReciprocal]
  apply irreducible_of_eisenstein_criterion
    ((Ideal.span_singleton_prime (X_ne_zero : (X : UPoly) ≠ 0)).mpr prime_X)
  · rw [hl, Ideal.mem_span_singleton, X_dvd_iff, familyA_zero m hm α]
    exact star_ne_zero.mpr hα
  · intro n hn
    have hn' : n < 2 := by simpa [hd] using (coe_lt_degree.mp hn)
    interval_cases n
    · rw [Ideal.mem_span_singleton]
      simp [familyReciprocal, familyB]
    · simp [familyReciprocal]
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have hc := X_pow_dvd_iff.mp h 1 (by decide : 1 < 2)
    simp [familyReciprocal, familyB_coeff_one m hm] at hc
  · exact familyReciprocal_primitive hm ha

/-- The quadratic strict transform of every nonreal-parameter family member is irreducible.
The blowup-to-original-curve transfer is a separate proof obligation. -/
theorem familyQuadratic_irreducible {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Irreducible (familyQuadratic m α) := by
  have hα : α ≠ 0 := by intro hz; apply ha; simp [hz]
  have hA : familyA m α ≠ 0 := by
    intro h
    have he := familyA_zero m hm α
    rw [h, coeff_zero] at he
    exact (star_ne_zero.mpr hα) he.symm
  have h0 : (familyQuadratic m α).coeff 0 ≠ 0 := by simpa [familyQuadratic] using hA
  have hrev : (familyQuadratic m α).reverse = familyReciprocal m α := by
    have hX : ((X : NPoly) ^ 2).reverse = 1 := by
      have hone : (1 : NPoly).reverse = 1 := by
        change (C (1 : UPoly)).reverse = C 1
        rw [reverse_C]
      simpa [hone] using (reverse_mul_X_pow (1 : NPoly) 2)
    simp [familyQuadratic, familyReciprocal, reverse_C_add,
      natDegree_C_mul (familyB_ne_zero m hm), hX, add_comm]
  exact irreducible_of_reverse h0 (hrev ▸ familyReciprocal_irreducible hm ha)

end CurveSymmetry
