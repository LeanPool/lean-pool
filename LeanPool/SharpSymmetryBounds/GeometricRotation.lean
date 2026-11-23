/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Elimination
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Rotations of the real zero set

A rotation preserving the real zero set acts on the irreducible equation by a sign, and the
zero-set rotation bound with no support or sign hypotheses.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Conjugate the coefficients and swap the two variables `X`, `Y`. -/
noncomputable def conjugateSwap : BPoly →+* BPoly :=
  (MvPolynomial.map (starRingEnd ℂ)).comp
    (rename (Equiv.swap (0 : Fin 2) 1)).toRingHom

lemma coeff_conjugateSwap (P : BPoly) (a b : ℕ) :
    (conjugateSwap P).coeff (exponent b a) = star (P.coeff (exponent a b)) := by
  have he : (exponent a b).mapDomain (Equiv.swap (0 : Fin 2) 1) = exponent b a := by
    simp [exponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single, add_comm]
  simp only [conjugateSwap, RingHom.comp_apply, coeff_map]
  change star ((rename (Equiv.swap (0 : Fin 2) 1) P).coeff (exponent b a)) = _
  rw [← he, coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 2) 1).injective]

lemma conjugateSwap_ne_zero {P : BPoly} (hP : P ≠ 0) : conjugateSwap P ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  intro hzero
  have h := coeff_conjugateSwap P (s 0) (s 1)
  rw [hzero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
  apply hs
  rw [he]
  exact star_eq_zero.mp h.symm

lemma conjugateSwap_degree_le (P : BPoly) : (conjugateSwap P).totalDegree ≤ P.totalDegree := by
  exact (totalDegree_le_of_support_subset (support_map_subset _ _)).trans
    (totalDegree_rename_le _ _)

lemma eval_conjugateSwap (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (conjugateSwap P) =
      star (eval (fun i : Fin 2 => if i = 0 then z else star z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [conjugateSwap]
  | add P Q hP hQ => simp only [map_add, hP, hQ, star_add]
  | mul_X P i hP =>
      simp only [map_mul, hP, star_mul]
      fin_cases i <;> simp [conjugateSwap, mul_comm]

/-- Infinite real locus forces symmetric monomial support, without a reality assumption. -/
lemma realLocus_support_symmetric {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) {a b : ℕ}
    (hc : P.coeff (exponent a b) ≠ 0) : P.coeff (exponent b a) ≠ 0 := by
  have hsub : realLocus P ⊆ realLocus (conjugateSwap P) := by
    intro z hz
    change eval _ (conjugateSwap P) = 0
    rw [eval_conjugateSwap, hz, star_zero]
  obtain ⟨c, _, hprop⟩ := proportional_of_realLocus_subset hP
    (conjugateSwap_ne_zero hP.ne_zero) hinf hsub (conjugateSwap_degree_le P)
  have he := congrArg (fun Q : BPoly => Q.coeff (exponent b a)) hprop
  rw [coeff_conjugateSwap, coeff_C_mul] at he
  intro hzero
  rw [hzero, mul_zero] at he
  exact hc (star_eq_zero.mp he)

lemma rotate_degree_le (ζ : ℂ) (P : BPoly) : (rotate ζ P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_le_of_support_subset
  intro s hs
  rw [mem_support_iff, coeff_rotate] at hs
  exact mem_support_iff.mpr (mul_ne_zero_iff.mp hs).1

lemma rotate_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) {P : BPoly} (hP : P ≠ 0) : rotate ζ P ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP
  intro hzero
  have he := coeff_rotate ζ P s
  rw [hzero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at he
  exact (mul_ne_zero hs (mul_ne_zero (pow_ne_zero _ hζ)
    (pow_ne_zero _ (inv_ne_zero hζ)))) he.symm

lemma eval_rotate (ζ : ℂ) (hnorm : ‖ζ‖ = 1) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (rotate ζ P) =
      eval (fun i : Fin 2 => if i = 0 then ζ * z else star (ζ * z)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rotate]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [rotate, Complex.inv_eq_conj hnorm, star_mul, mul_comm]

/-- A rotation of the real zero set acts on the irreducible equation by a sign. -/
theorem rotation_sign_of_realLocus {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) {ζ : ℂ} (hnorm : ‖ζ‖ = 1)
    (hsym : ∀ z ∈ realLocus P, ζ * z ∈ realLocus P) :
    rotate ζ P = P ∨ rotate ζ P = -P := by
  have hz : ζ ≠ 0 := by intro h; simp [h] at hnorm
  have hsub : realLocus P ⊆ realLocus (rotate ζ P) := by
    intro z hz
    change eval _ (rotate ζ P) = 0
    rw [eval_rotate ζ hnorm]
    exact hsym z hz
  obtain ⟨c, _, hprop⟩ := proportional_of_realLocus_subset hP
    (rotate_ne_zero hz hP.ne_zero) hinf hsub (rotate_degree_le ζ P)
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP.ne_zero
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  have hs' : P.coeff (exponent (s 0) (s 1)) ≠ 0 := by simpa [← he] using hs
  have ht := realLocus_support_symmetric hP hinf hs'
  have hchar : ∀ a b, P.coeff (exponent a b) ≠ 0 → ζ ^ a * (ζ⁻¹) ^ b = c := by
    intro a b hc
    have h := congrArg (fun Q : BPoly => Q.coeff (exponent a b)) hprop
    rw [coeff_rotate, coeff_C_mul] at h
    simp only [exponent_zero, exponent_one] at h
    apply mul_left_cancel₀ hc
    simpa [mul_comm] using h
  have h1 := hchar (s 0) (s 1) hs'
  have h2 := hchar (s 1) (s 0) ht
  have hc : c ^ 2 = 1 := by
    calc
      c ^ 2 = (ζ ^ s 0 * (ζ⁻¹) ^ s 1) * (ζ ^ s 1 * (ζ⁻¹) ^ s 0) := by rw [h1, h2]; ring
      _ = 1 := by rw [inv_pow, inv_pow]; field_simp
  rcases sq_eq_one_iff.mp hc with hc | hc
  · left; simpa [hc] using hprop
  · right; simpa [hc] using hprop

/-- A genuine zero-set rotation bound: no polynomial sign or support hypotheses remain. -/
theorem geometric_rotation_order_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    {N : ℕ} (hN : N ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hsym : ∀ z ∈ realLocus P, ζ * z ∈ realLocus P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) :=
  realLocus_rotation_bound hζ hP hd hinf hcircle
    (rotation_sign_of_realLocus hP hinf (hζ.norm'_eq_one hN) hsym)

end CurveSymmetry
