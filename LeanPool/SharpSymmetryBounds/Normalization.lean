/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.EqualityForm

/-!
# Normalization by a similarity

Pullback by `z ↦ c z` and normalization of the modulus and phase of the parameter by a direct
similarity.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Pullback by the direct similarity `z ↦ cz`, allowing arbitrary nonzero scale. -/
noncomputable def dilate (c : ℂ) : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => C (if i = 0 then c else star c) * X i)

lemma eval_dilate (c : ℂ) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (dilate c P) =
      eval (fun i : Fin 2 => if i = 0 then c * z else star (c * z)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [dilate]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [dilate, star_mul, mul_comm]

lemma dilate_twoParameter (m : ℕ) (a b c : ℂ) :
    dilate c (twoParameter m a b) =
      twoParameter m (c ^ m * a) (c ^ m * b * (c * star c)) := by
  simp only [twoParameter, map_add, map_mul, map_pow]
  have h0 : dilate c (X 0) = C c * X 0 := by simp [dilate]
  have h1 : dilate c (X 1) = C (star c) * X 1 := by simp [dilate]
  have hC : ∀ a : ℂ, dilate c (C a) = C a := by intro a; simp [dilate]
  rw [h0, h1, hC, hC, hC, hC]
  simp only [star_mul, star_pow, star_star, map_mul, map_pow, mul_pow]
  ring

lemma twoParameter_real_scalar (m : ℕ) (α : ℂ) (k : ℝ) :
    twoParameter m ((k : ℂ) * α) (k : ℂ) = C (k : ℂ) * familyPolynomial m α := by
  simp only [twoParameter, familyPolynomial, star_mul, star_real_cast, map_mul]
  ring

/-- Normalize the modulus and phase by an actual nonzero complex similarity. -/
theorem normalize_twoParameter {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (hb : b ≠ 0) (hreal : a / b ≠ star (a / b)) :
    ∃ c α : ℂ, ∃ k : ℝ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧ 0 < k ∧
      dilate c (twoParameter m a b) = C (k : ℂ) * familyPolynomial m α := by
  let q : ℂ := a / b
  have hq : q ≠ 0 := by intro h; apply hreal; change q = star q; simp [h]
  have hnq : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hncq : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast hnq
  let r : ℝ := Real.sqrt ‖q‖
  have hr : 0 < r := Real.sqrt_pos.mpr (norm_pos_iff.mpr hq)
  have hrs : r ^ 2 = ‖q‖ := Real.sq_sqrt (norm_nonneg q)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq ((‖b‖ : ℂ) / b) hm
  have hun : ‖u‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg u) hm.ne').mp
    have he := congrArg norm hu
    simpa [hnb] using he
  have hu0 : u ≠ 0 := by intro h; simp [h] at hun
  let c : ℂ := (r : ℂ) * u
  let α : ℂ := q / (‖q‖ : ℂ)
  let k : ℝ := r ^ m * ‖b‖ * ‖q‖
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne') hu0
  have hαn : ‖α‖ = 1 := by simp [α, hnq]
  have hαr : α ≠ star α := by
    intro h
    have he : (‖q‖ : ℂ) * α = q := mul_div_cancel₀ _ hncq
    have hs := congrArg star he
    simp only [star_mul, star_real_cast, ← h] at hs
    apply hreal
    change q = star q
    linear_combination hs - he
  have hk : 0 < k := by dsimp [k]; positivity
  have hcc : c * star c = (‖q‖ : ℂ) := by
    have he := mul_star_eq_one_of_norm hun
    have hrs' : (r : ℂ) ^ 2 = (‖q‖ : ℂ) := by exact_mod_cast hrs
    change ((r : ℂ) * u) * star ((r : ℂ) * u) = (‖q‖ : ℂ)
    simp only [star_mul, star_real_cast]
    linear_combination (r : ℂ) ^ 2 * he + hrs'
  have hcb : c ^ m * b = (r : ℂ) ^ m * (‖b‖ : ℂ) := by
    dsimp [c]
    rw [mul_pow, hu]
    field_simp
  have hA : c ^ m * a = (k : ℂ) * α := by
    calc
      c ^ m * a = (c ^ m * b) * q := by dsimp [q]; field_simp
      _ = ((r : ℂ) ^ m * (‖b‖ : ℂ)) * q := by rw [hcb]
      _ = (k : ℂ) * α := by dsimp [k, α]; push_cast; field_simp
  have hB : c ^ m * b * (c * star c) = (k : ℂ) := by
    rw [hcb, hcc]
    simp [k]
  refine ⟨c, α, k, hc, hαn, hαr, hk, ?_⟩
  rw [dilate_twoParameter, hA, hB, twoParameter_real_scalar]

end CurveSymmetry
