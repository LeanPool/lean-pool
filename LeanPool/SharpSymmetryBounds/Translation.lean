/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.RotationGroup
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Translations

A nontrivial translation cannot preserve an irreducible real plane curve of degree at least two.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Restriction of a plane polynomial to the line `t ↦ z + t v`. -/
noncomputable def lineRestriction (z v : ℂ) : BPoly →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (fun i : Fin 2 =>
    Polynomial.C (if i = 0 then z else star z) +
      Polynomial.C (if i = 0 then v else star v) * Polynomial.X)

lemma eval_lineRestriction (P : BPoly) (z v t : ℂ) :
    (lineRestriction z v P).eval t =
      eval (fun i : Fin 2 => if i = 0 then z + v * t else star z + star v * t) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineRestriction]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, Polynomial.eval_mul, hP]
      fin_cases i <;> simp [lineRestriction]

/-- An equation of the real line through `z` with direction `v`. -/
noncomputable def lineEquation (z v : ℂ) : BPoly :=
  C (star v) * X 0 - C v * X 1 - C (star v * z - v * star z)

lemma eval_lineEquation (z v w : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then w else star w) (lineEquation z v) =
      star v * w - v * star w - (star v * z - v * star z) := by
  simp [lineEquation]

lemma lineEquation_degree (z v : ℂ) (hv : v ≠ 0) : (lineEquation z v).totalDegree = 1 := by
  have h0 := totalDegree_mul (C (star v) : BPoly) (X 0)
  have h1 := totalDegree_mul (C v : BPoly) (X 1)
  have h2 := totalDegree_sub (C (star v) * X 0 : BPoly) (C v * X 1)
  have h3 := totalDegree_sub_C_le (C (star v) * X 0 - C v * X 1 : BPoly)
    (star v * z - v * star z)
  simp only [totalDegree_C, totalDegree_X, zero_add] at h0 h1
  have hne : (Finsupp.single (1 : Fin 2) 1 : Exponent) ≠ Finsupp.single 0 1 := by
    intro h
    have := congrArg (fun s : Exponent => s 0) h
    simp at this
  have hn0 : (0 : Exponent) ≠ Finsupp.single 0 1 := by
    intro h
    have := congrArg (fun s : Exponent => s 0) h
    simp at this
  have hc : (lineEquation z v).coeff (exponent 1 0) = star v := by
    simp [lineEquation, exponent, coeff_C_mul, coeff_X, hne, hn0]
  have hs : exponent 1 0 ∈ (lineEquation z v).support := by
    rw [mem_support_iff, hc]
    exact star_ne_zero.mpr hv
  have h4 := support_degree hs
  simp only [exponent_zero, exponent_one, add_zero] at h4
  change (C (star v) * X 0 - C v * X 1 - C (star v * z - v * star z) : BPoly).totalDegree = 1
  change 1 ≤ (C (star v) * X 0 - C v * X 1 - C (star v * z - v * star z) : BPoly).totalDegree at h4
  omega

lemma lineEquation_irreducible (z v : ℂ) (hv : v ≠ 0) : Irreducible (lineEquation z v) := by
  have hd := lineEquation_degree z v hv
  apply irreducible_of_totalDegree_eq_one hd
  intro a ha
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hzero : lineEquation z v = 0 := by
    ext s
    have h := ha s
    simpa [hz] using h
  simp [hzero] at hd

lemma lineEquation_realLocus_infinite (z v : ℂ) (hv : v ≠ 0) :
    (realLocus (lineEquation z v)).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => z + v * (n : ℂ)) := by
    intro n m h
    have hnm : (n : ℂ) = m := mul_left_cancel₀ hv (add_left_cancel h)
    exact_mod_cast hnm
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  change eval _ (lineEquation z v) = 0
  rw [eval_lineEquation]
  simp only [star_add, star_mul, star_natCast]
  ring

/-- A nontrivial translation cannot preserve an irreducible real plane curve of degree at least
two. -/
theorem no_translation_symmetry {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {v : ℂ}
    (htrans : ∀ z ∈ realLocus P, z + v ∈ realLocus P) : v = 0 := by
  by_contra hv
  obtain ⟨z, hz⟩ := hne
  have horbit : ∀ n : ℕ, z + v * (n : ℂ) ∈ realLocus P := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
        convert htrans (z + v * (n : ℂ)) ih using 1
        push_cast
        ring
  have hrestriction : lineRestriction z v P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hninj : Function.Injective (fun n : ℕ => (n : ℂ)) := Nat.cast_injective
    apply (Set.infinite_range_of_injective hninj).mono
    rintro _ ⟨n, rfl⟩
    change (lineRestriction z v P).eval (n : ℂ) = 0
    rw [eval_lineRestriction]
    have h := horbit n
    simpa only [realLocus, Set.mem_ofPred_eq, star_add, star_mul, star_natCast, mul_comm] using h
  have hsub : realLocus (lineEquation z v) ⊆ realLocus P := by
    intro w hw
    change eval _ (lineEquation z v) = 0 at hw
    rw [eval_lineEquation] at hw
    have hx : z + v * ((w - z) / v) = w := by field_simp; ring
    have hy : star z + star v * ((w - z) / v) = star w := by
      field_simp
      linear_combination hw
    have he := eval_lineRestriction P z v ((w - z) / v)
    rw [hrestriction, Polynomial.eval_zero, hx, hy] at he
    exact he.symm
  have hL := lineEquation_irreducible z v hv
  have hdiv := dvd_of_realLocus_subset hL (lineEquation_realLocus_infinite z v hv) hsub
  have hb := degree_le_of_nonunit_dvd hP hL.not_isUnit hdiv
  rw [lineEquation_degree z v hv] at hb
  omega

end CurveSymmetry
