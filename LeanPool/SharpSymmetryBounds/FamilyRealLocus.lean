/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.FamilyIrreducibility

/-!
# The real locus of the extremal family

The real locus of each family member meets every circle about the origin, so it is infinite.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

lemma star_real_cast (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r

lemma mul_star_norm_sq (z : ℂ) : z * star z = (‖z‖ : ℂ) ^ 2 := by
  change z * (starRingEnd ℂ) z = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

lemma eval_familyPolynomial (m : ℕ) (α z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (familyPolynomial m α) =
      z ^ m * (α + z * star z) + star (z ^ m * (α + z * star z)) := by
  simp only [familyPolynomial, map_add, map_mul, map_pow, eval_C, eval_X,
    Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide,
    star_mul, star_pow, star_add, star_star]
  ring

/-- The real locus of the family meets every circle about the origin. -/
theorem family_point_of_norm {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α)
    {r : ℝ} (hr : 0 ≤ r) : ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = r := by
  let b : ℂ := α + (r : ℂ) ^ 2
  have hb : b ≠ 0 := by
    intro h
    have hs := congrArg star h
    simp only [b, star_add, star_pow, star_real_cast, star_zero] at hs
    apply ha
    dsimp [b] at h
    linear_combination h - hs
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hnc : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hnb
  let q : ℂ := Complex.I * star b / (‖b‖ : ℂ)
  have hq : ‖q‖ = 1 := by simp [q, hnb]
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq q hm
  have hvn : ‖v‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg v) hm.ne').mp
    rw [← norm_pow, hv, hq]
  have hvb : v ^ m * b = Complex.I * (‖b‖ : ℂ) := by
    rw [hv]
    dsimp [q]
    have he := mul_star_norm_sq b
    field_simp
    simp only [Complex.star_def] at he ⊢
    linear_combination he
  refine ⟨(r : ℂ) * v, ?_, by simp [hvn, abs_of_nonneg hr]⟩
  change eval _ (familyPolynomial m α) = 0
  rw [eval_familyPolynomial]
  have hz : ((r : ℂ) * v) * star ((r : ℂ) * v) = (r : ℂ) ^ 2 := by
    simp only [star_mul, star_real_cast]
    have he := mul_star_eq_one_of_norm hvn
    linear_combination (r : ℂ) ^ 2 * he
  have hw : ((r : ℂ) * v) ^ m * (α + ((r : ℂ) * v) * star ((r : ℂ) * v)) =
      (r : ℂ) ^ m * (Complex.I * (‖b‖ : ℂ)) := by
    rw [hz, mul_pow, mul_assoc]
    exact congrArg (fun x : ℂ => (r : ℂ) ^ m * x) hvb
  rw [hw]
  simp [star_mul, star_pow]
  ring

theorem family_realLocus_infinite {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    (realLocus (familyPolynomial m α)).Infinite := by
  have hex : ∀ n : ℕ, ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = (n : ℝ) + 1 := by
    intro n
    exact family_point_of_norm hm ha (by positivity)
  choose f hf hnorm using hex
  have hinj : Function.Injective f := by
    intro n k h
    have he := congrArg norm h
    rw [hnorm, hnorm] at he
    exact_mod_cast (add_right_cancel he)
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨n, rfl⟩; exact hf n)

theorem family_not_circle {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    NotCircle (familyPolynomial m α) := by
  rintro ⟨c, R, hR, he⟩
  obtain ⟨z, hz, hn⟩ := family_point_of_norm hm ha
    (show 0 ≤ ‖c‖ + R + 1 by positivity)
  rw [he, Metric.mem_sphere, dist_eq_norm] at hz
  have hb := norm_add_le (z - c) c
  rw [sub_add_cancel, hz, hn] at hb
  linarith

end CurveSymmetry
