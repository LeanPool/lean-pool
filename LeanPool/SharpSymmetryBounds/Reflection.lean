/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.DirectBound

/-!
# Reflections

Pullback by a reflection `z ↦ a conj z` with `‖a‖ = 1`; a reflection cannot negate or rescale an
irreducible equation of degree at least two.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

lemma mul_star_eq_one_of_norm {a : ℂ} (ha : ‖a‖ = 1) : a * star a = 1 := by
  have hn : a ≠ 0 := by intro h; simp [h] at ha
  change a * (starRingEnd ℂ) a = 1
  rw [← Complex.inv_eq_conj ha, mul_inv_cancel₀ hn]

/-- Pullback by the reflection `z ↦ a conjugate(z)` when `‖a‖ = 1`. -/
noncomputable def reflect (a : ℂ) : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => if i = 0 then C a * X 1 else C (star a) * X 0)

lemma reflect_involutive {a : ℂ} (ha : ‖a‖ = 1) (P : BPoly) :
    reflect a (reflect a P) = P := by
  have hc := mul_star_eq_one_of_norm ha
  have h0 : reflect a (X 0) = C a * X 1 := by simp [reflect]
  have h1 : reflect a (X 1) = C (star a) * X 0 := by simp [reflect]
  have hC : ∀ c : ℂ, reflect a (C c) = C c := by intro c; simp [reflect]
  induction P using MvPolynomial.induction_on with
  | C c => simp [reflect]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i
      · change P * reflect a (reflect a (X 0)) = P * X 0
        rw [h0, map_mul, hC, h1, ← mul_assoc (C a), ← C_mul, hc, C_1, one_mul]
      · change P * reflect a (reflect a (X 1)) = P * X 1
        rw [h1, map_mul, hC, h0, ← mul_assoc (C (star a)), ← C_mul,
          mul_comm (star a) a, hc, C_1, one_mul]

lemma reflect_ne_zero {a : ℂ} (ha : ‖a‖ = 1) {P : BPoly} (hP : P ≠ 0) :
    reflect a P ≠ 0 := by
  intro h
  have he := reflect_involutive ha P
  rw [h, map_zero] at he
  exact hP he.symm

lemma reflect_degree_le {a : ℂ} (ha : ‖a‖ = 1) (P : BPoly) :
    (reflect a P).totalDegree ≤ P.totalDegree := by
  have he : reflect a P = rename (Equiv.swap (0 : Fin 2) 1) (rotate a P) := by
    induction P using MvPolynomial.induction_on with
    | C c => simp [reflect, rotate]
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P i hP =>
        simp only [map_mul, hP]
        fin_cases i <;> simp [reflect, rotate, Complex.inv_eq_conj ha]
  rw [he]
  exact (totalDegree_rename_le _ _).trans (rotate_degree_le a P)

lemma eval_reflect (a : ℂ) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (reflect a P) =
      eval (fun i : Fin 2 => if i = 0 then a * star z else star (a * star z)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [reflect]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [reflect, star_mul, mul_comm]

lemma reflection_fixed_direction {a : ℂ} (ha : ‖a‖ = 1) :
    ∃ v : ℂ, v ≠ 0 ∧ a * star v = v := by
  have hc := mul_star_eq_one_of_norm ha
  by_cases h : a = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    simp [h]
  · refine ⟨1 + a, by intro hz; apply h; linear_combination hz, ?_⟩
    simp only [star_add, star_one, mul_add, mul_one, hc]
    ring

/-- A reflection cannot negate (or rescale) an irreducible curve equation of degree ≥ 2:
otherwise its fixed line is a component. -/
theorem reflection_fixes_equation {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) {a : ℂ}
    (ha : ‖a‖ = 1) (hsym : ∀ z ∈ realLocus P, a * star z ∈ realLocus P) :
    reflect a P = P := by
  have hsub : realLocus P ⊆ realLocus (reflect a P) := by
    intro z hz
    change eval _ (reflect a P) = 0
    rw [eval_reflect]
    exact hsym z hz
  obtain ⟨c, _, hp⟩ := proportional_of_realLocus_subset hP
    (reflect_ne_zero ha hP.ne_zero) hinf hsub (reflect_degree_le ha P)
  by_cases hc : c = 1
  · simpa [hc] using hp
  obtain ⟨v, hv, hfix⟩ := reflection_fixed_direction ha
  have hline : realLocus (lineEquation 0 v) ⊆ realLocus P := by
    intro z hz
    change eval _ (lineEquation 0 v) = 0 at hz
    rw [eval_lineEquation] at hz
    simp only [mul_zero, star_zero, sub_zero] at hz
    have hf : a * star z = z := by
      apply mul_left_cancel₀ (star_ne_zero.mpr hv)
      linear_combination -hz + star z * hfix
    have he := congrArg (eval (fun i : Fin 2 => if i = 0 then z else star z)) hp
    rw [eval_reflect, hf, map_mul, eval_C] at he
    have hh : (1 - c) * eval (fun i : Fin 2 => if i = 0 then z else star z) P = 0 := by
      linear_combination he
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  have hL := lineEquation_irreducible 0 v hv
  have hdiv := dvd_of_realLocus_subset hL (lineEquation_realLocus_infinite 0 v hv) hline
  have hb := degree_le_of_nonunit_dvd hP hL.not_isUnit hdiv
  rw [lineEquation_degree 0 v hv] at hb
  omega

end CurveSymmetry
