/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.FamilyRealLocus

/-!
# Rotations of the extremal family

Sharpness of the rotation bound in every degree at least four, and the absence of opposite
symmetries above degree four.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

lemma family_monomial_form (m : ℕ) (α : ℂ) :
    familyPolynomial m α = monomial (exponent m 0) α + monomial (exponent (m + 1) 1) 1 +
      monomial (exponent 0 m) (star α) + monomial (exponent 1 (m + 1)) 1 := by
  simp only [familyPolynomial, monomial_exponent, pow_zero, C_1, pow_succ]
  ring

theorem family_degree {m : ℕ} (hm : 0 < m) (α : ℂ) :
    (familyPolynomial m α).totalDegree = m + 2 := by
  have hc : (familyPolynomial m α).coeff (exponent (m + 1) 1) = 1 := by
    rw [family_monomial_form]
    have h0 : exponent m 0 ≠ exponent (m + 1) 1 := by simp [exponent_eq_iff]
    have h1 : exponent 0 m ≠ exponent (m + 1) 1 := by simp [exponent_eq_iff]
    have h2 : exponent 1 (m + 1) ≠ exponent (m + 1) 1 := by simp [exponent_eq_iff]; omega
    simp [coeff_monomial, h0, h1, h2]
  have hlo := support_degree (mem_support_iff.mpr (by rw [hc]; exact one_ne_zero))
  simp only [exponent_zero, exponent_one] at hlo
  let A : BPoly := monomial (exponent m 0) α
  let B : BPoly := monomial (exponent (m + 1) 1) 1
  let D : BPoly := monomial (exponent 0 m) (star α)
  let E : BPoly := monomial (exponent 1 (m + 1)) 1
  have hA : A.totalDegree ≤ m := by
    simpa [A, Function.id_def, exponent_degree] using totalDegree_monomial_le (exponent m 0) α
  have hB : B.totalDegree ≤ m + 2 := by
    simp [B, totalDegree_monomial, exponent_degree, Nat.add_assoc]
  have hD : D.totalDegree ≤ m := by
    simpa [D, Function.id_def, exponent_degree] using
      totalDegree_monomial_le (exponent 0 m) (star α)
  have hE : E.totalDegree ≤ m + 2 := by
    simp [E, totalDegree_monomial, exponent_degree, Nat.add_left_comm]
  have hab := totalDegree_add A B
  have habd := totalDegree_add (A + B) D
  have habde := totalDegree_add (A + B + D) E
  have he : familyPolynomial m α = A + B + D + E := family_monomial_form m α
  rw [he] at hlo ⊢
  omega

lemma family_rotate {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) (hroot : ζ ^ (2 * m) = 1) (α : ℂ) :
    rotate ζ (familyPolynomial m α) = C (ζ ^ m) * familyPolynomial m α := by
  have hs : ζ ^ m * ζ ^ m = 1 := by rw [← pow_add, ← two_mul]; exact hroot
  have hi : (ζ⁻¹) ^ m = ζ ^ m := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_left hs
  have h0 : rotate ζ (X 0) = C ζ * X 0 := by simp [rotate]
  have h1 : rotate ζ (X 1) = C (ζ⁻¹) * X 1 := by simp [rotate]
  have hC : ∀ c : ℂ, rotate ζ (C c) = C c := by intro c; simp [rotate]
  have hxy : (C ζ * X 0 : BPoly) * (C (ζ⁻¹) * X 1) = X 0 * X 1 := by
    have he : (C ζ : BPoly) * C (ζ⁻¹) = 1 := by rw [← C_mul, mul_inv_cancel₀ hζ, C_1]
    linear_combination (X 0 : BPoly) * X 1 * he
  simp only [familyPolynomial, map_add, map_mul, map_pow]
  rw [h0, h1, hC, hC, hxy, mul_pow, mul_pow, ← map_pow, ← map_pow, hi]
  ring

lemma family_root_symmetry {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hroot : ζ ^ (2 * m) = 1) (α : ℂ) : DirectSymmetry (realLocus (familyPolynomial m α)) ζ 0 := by
  have hζ : ζ ≠ 0 := by intro h; simp [h, hm.ne'] at hroot
  have hn : ‖ζ‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) (by omega : 2 * m ≠ 0)).mp
    have h := congrArg norm hroot
    simpa using h
  refine ⟨hn, ?_⟩
  intro z
  simp only [add_zero]
  change eval _ (familyPolynomial m α) = 0 ↔ eval _ (familyPolynomial m α) = 0
  rw [← eval_rotate ζ hn, family_rotate hζ hroot α, map_mul, eval_C]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ hζ))

/-- Sharpness of the rotation bound for every degree at least four. -/
theorem family_direct_card {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    Nat.card (DirectSymmetries (familyPolynomial m α)) = 2 * m := by
  have hm' : 0 < m := by omega
  obtain ⟨hf, hb⟩ := direct_euclidean_bound (familyPolynomial_irreducible hm' ha)
    (by rw [family_degree hm']; omega) (family_realLocus_infinite hm' ha) (family_not_circle hm' ha)
  let := hf
  let : NeZero (2 * m) := ⟨by omega⟩
  let f : rootsOfUnity (2 * m) ℂ → DirectSymmetries (familyPolynomial m α) := fun u =>
    ⟨((u.val : ℂ), 0), family_root_symmetry hm' ((mem_rootsOfUnity' _ _).mp u.prop) α⟩
  have hi : Function.Injective f := by
    intro u v h
    exact rootsOfUnity.coe_injective (congrArg (fun w => w.val.1) h)
  have hlo := Nat.card_le_card_of_injective f hi
  rw [Complex.card_rootsOfUnity] at hlo
  rw [family_degree hm'] at hb
  omega

/-- Above degree four the extremal family cannot have an opposite Euclidean symmetry. -/
theorem family_no_opposite {m : ℕ} (hm : 3 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    IsEmpty (OppositeSymmetries (familyPolynomial m α)) := by
  refine ⟨fun g => ?_⟩
  have hm' : 0 < m := by omega
  have hb := direct_bound_with_opposite (familyPolynomial_irreducible hm' ha)
    (by rw [family_degree hm']; omega) (family_realLocus_infinite hm' ha)
    (family_not_circle hm' ha) g
  rw [family_direct_card (by omega) ha, family_degree hm'] at hb
  omega

end CurveSymmetry
