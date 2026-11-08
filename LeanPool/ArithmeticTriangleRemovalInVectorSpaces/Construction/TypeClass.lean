/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# The size of a type class

The type class of `a : Fin n → ℕ` is the set of the vectors `a ∘ σ` obtained by permuting its
entries. If the value `k` appears `D k` times in `a`, the type class has
`n.factorial / ∏ k, (D k).factorial` elements. This file bounds the logarithm of this number from
below by `∑ k, D k * log (ψ k)⁻¹`, up to an error controlled by
`∑ k, (D k - n * ψ k) ^ 2 / (n * ψ k)`, for every positive probability vector `ψ`. This is Lemma 3.1
of Kleinberg, Sawin and Speyer, together with the comparison between entropy and cross entropy.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.typeClass a`: the vectors obtained by permuting the
  entries of `a`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_typeClass_mul_prod_factorial`: the type class of
  `a` has `n.factorial / ∏ k, (D k).factorial` elements.
* `ArithmeticTriangleRemovalInVectorSpaces.le_log_card_typeClass`: the lower bound on its
  logarithm.
-/

public section

open Finset Real

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {n N : ℕ} {a b b' : Fin n → ℕ}

/-- The type class of `a`: the vectors `a ∘ σ` obtained by permuting the entries of `a`. -/
@[expose] def typeClass (a : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  univ.image fun σ : Equiv.Perm (Fin n) ↦ a ∘ σ

private lemma mem_typeClass : b ∈ typeClass a ↔ ∃ σ : Equiv.Perm (Fin n), a ∘ σ = b := by
  simp [typeClass]

lemma self_mem_typeClass (a : Fin n → ℕ) : a ∈ typeClass a :=
  mem_typeClass.2 ⟨1, rfl⟩

@[simp]
lemma typeClass_nonempty (a : Fin n → ℕ) : (typeClass a).Nonempty :=
  ⟨a, self_mem_typeClass a⟩

lemma comp_mem_typeClass (hb : b ∈ typeClass a) (σ : Equiv.Perm (Fin n)) :
    b ∘ σ ∈ typeClass a := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  exact mem_typeClass.2 ⟨τ * σ, rfl⟩

lemma exists_eq_comp_of_mem_typeClass (hb : b ∈ typeClass a) (hb' : b' ∈ typeClass a) :
    ∃ σ : Equiv.Perm (Fin n), b' = b ∘ σ := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  obtain ⟨τ', rfl⟩ := mem_typeClass.1 hb'
  refine ⟨τ⁻¹ * τ', ?_⟩
  ext r
  simp

lemma sum_eq_of_mem_typeClass (hb : b ∈ typeClass a) : ∑ r, b r = ∑ r, a r := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  exact Equiv.sum_comp τ a

lemma card_typeClass_le {p : ℕ} (ha : ∀ r, a r < p) : #(typeClass a) ≤ p ^ n := by
  have hsub : typeClass a ⊆ Fintype.piFinset fun _ ↦ range p := by
    intro b hb
    obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
    simp [ha]
  grw [card_le_card hsub]
  simp

/-- The values `k ≤ N` of `a` appear `n` times in total. -/
lemma sum_card_filter_eq (ha : ∀ r, a r ≤ N) : ∑ k ∈ range (N + 1), #{r | a r = k} = n := by
  rw [← card_eq_sum_card_fiberwise (fun r _ ↦ mem_range.2 (by grind [ha r])), card_univ,
    Fintype.card_fin]

/-- The permutations `σ` with `a ∘ σ = a ∘ τ` are as many as those with `a ∘ σ = a`. -/
private lemma card_filter_comp_eq_comp (a : Fin n → ℕ) (τ : Equiv.Perm (Fin n)) :
    #{σ : Equiv.Perm (Fin n) | a ∘ σ = a ∘ τ} =
      Fintype.card {σ : Equiv.Perm (Fin n) // a ∘ σ = a} := by
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ((Equiv.mulRight τ⁻¹).subtypeEquiv ?_)
  intro σ
  simp [Equiv.Perm.coe_mul, ← Function.comp_assoc, Equiv.Perm.inv_def, Equiv.comp_symm_eq]

/-- **Orbit-stabilizer for type classes.** The type class of `a` times `∏ k, (D k).factorial` is
`n.factorial`. -/
private lemma card_typeClass_mul_prod_factorial (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) :
    #(typeClass a) * ∏ k ∈ range (N + 1), (#{r | a r = k}).factorial = n.factorial := by
  have hprod : ∏ k ∈ range (N + 1), (#{r | a r = k}).factorial =
      ∏ k ∈ univ.image a, (Fintype.card {r // a r = k}).factorial := by
    simp_rw [Fintype.card_subtype]
    refine (prod_subset ?_ ?_).symm
    · intro k
      simp only [mem_image, mem_univ, true_and, mem_range]
      grind
    · intro k _ hk
      simp_all
  rw [hprod, ← DomMulAct.stabilizer_card',
    (by simp [Fintype.card_perm] : n.factorial = #(univ : Finset (Equiv.Perm (Fin n)))),
    card_eq_sum_card_image fun σ : Equiv.Perm (Fin n) ↦ a ∘ σ, typeClass, sum_const_nat]
  simp only [mem_image, mem_univ, true_and]
  rintro _ ⟨τ, rfl⟩
  exact card_filter_comp_eq_comp a τ

private lemma log_card_typeClass (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) :
    log #(typeClass a) =
      log n.factorial - ∑ k ∈ range (N + 1), log (#{r | a r = k}).factorial := by
  rw [eq_sub_iff_add_eq, ← log_prod fun k _ ↦ by positivity,
    ← log_mul (by simpa using (typeClass_nonempty a).ne_empty) (by positivity),
    ← card_typeClass_mul_prod_factorial a ha]
  push_cast
  rfl

/-- For `D ≤ n`, `D * log (n / D) - (1 + log (n + 1)) ≤ D * log n - D - log D.factorial`, from the
bound `log D.factorial ≤ D * log D - D + log D + 1`. -/
private lemma mul_log_div_sub_le {D : ℕ} (hD : D ≤ n) :
    D * log (n / D) - (1 + log (n + 1)) ≤ D * log n - D - log D.factorial := by
  rcases D.eq_zero_or_pos with rfl | hD₀
  · simpa using (by linarith [log_nonneg (by simp : (1 : ℝ) ≤ n + 1)] : -log (n + 1 : ℝ) ≤ 1)
  have h := sum_log_le (x := D) (by exact_mod_cast hD₀)
  rw [Nat.floor_natCast, sum_log_eq_log_factorial] at h
  rw [log_div (by norm_cast; grind) (by positivity)]
  linarith [log_le_log (by positivity) (by norm_cast; grind : (D : ℝ) ≤ n + 1)]

/-- The logarithm of a multinomial coefficient is at least the entropy term
`∑ k, D k * log (n / D k)` minus `#s * (1 + log (n + 1))`. -/
private lemma sum_mul_log_div_sub_le_log {s : Finset ℕ} (D : ℕ → ℕ) (hD : ∑ k ∈ s, D k = n) :
    ∑ k ∈ s, D k * log (n / D k) - #s * (1 + log (n + 1)) ≤
      log n.factorial - ∑ k ∈ s, log (D k).factorial := by
  have h : ∑ k ∈ s, (D k * log (n / D k) - (1 + log (n + 1))) ≤
      ∑ k ∈ s, (D k * log n - D k - log (D k).factorial) := by
    apply sum_le_sum
    intro k hk
    exact mul_log_div_sub_le (hD ▸ single_le_sum (by simp) hk)
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_mul,
    (by exact_mod_cast hD : ∑ k ∈ s, (D k : ℝ) = n)] at h
  linarith [le_sum_log_nat n, sum_log_eq_log_factorial n]

/-- For `0 ≤ D ≤ x` and `ψ > 0`,
`D * log ψ⁻¹ - (D - x * ψ) ^ 2 / (x * ψ) - (D - x * ψ) ≤ D * log (x / D)`, from the bound
`1 - y⁻¹ ≤ log y`. -/
private lemma mul_log_inv_sub_sq_div_sub_le {D x ψ : ℝ} (hD : 0 ≤ D) (hDx : D ≤ x) (hψ : 0 < ψ) :
    D * log ψ⁻¹ - (D - x * ψ) ^ 2 / (x * ψ) - (D - x * ψ) ≤ D * log (x / D) := by
  rcases hD.eq_or_lt with rfl | hD
  · simp [sq]
  have hx : 0 < x := hD.trans_le hDx
  have hxψ : 0 < x * ψ := by positivity
  have hlog := one_sub_inv_le_log_of_pos (div_pos hxψ hD)
  rw [inv_div, log_div hxψ.ne' hD.ne', log_mul (by positivity) hψ.ne'] at hlog
  rw [log_div (by positivity) hD.ne', log_inv]
  have hid : D * (1 - D / (x * ψ)) = -((D - x * ψ) ^ 2 / (x * ψ)) - (D - x * ψ) := by
    field_simp
    ring
  linarith [mul_le_mul_of_nonneg_left hlog hD.le]

/-- **Entropy and cross entropy.** For a positive probability vector `ψ` and counts `D` summing to
`n`, `∑ k, D k * log (n / D k)` is at least
`∑ k, D k * log (ψ k)⁻¹ - ∑ k, (D k - n * ψ k) ^ 2 / (n * ψ k)`. -/
private lemma sum_mul_log_inv_sub_le {s : Finset ℕ} (D : ℕ → ℕ) (hD : ∑ k ∈ s, D k = n) {ψ : ℕ → ℝ}
    (hψ : ∀ k ∈ s, 0 < ψ k) (hψ₁ : ∑ k ∈ s, ψ k = 1) :
    ∑ k ∈ s, D k * log (ψ k)⁻¹ - ∑ k ∈ s, (D k - n * ψ k) ^ 2 / (n * ψ k) ≤
      ∑ k ∈ s, D k * log (n / D k) := by
  have hY : ∑ k ∈ s, ((D k : ℝ) - n * ψ k) = 0 := by
    rw [sum_sub_distrib, ← mul_sum, hψ₁, mul_one, sub_eq_zero]
    exact_mod_cast hD
  have h : ∑ k ∈ s, (D k * log (ψ k)⁻¹ - (D k - n * ψ k) ^ 2 / (n * ψ k) - (D k - n * ψ k)) ≤
      ∑ k ∈ s, D k * log (n / D k) := by
    apply sum_le_sum
    intro k hk
    exact mul_log_inv_sub_sq_div_sub_le (by positivity)
      (by exact_mod_cast hD ▸ single_le_sum (by simp) hk) (hψ k hk)
  rwa [sum_sub_distrib, hY, sub_zero, sum_sub_distrib] at h

/-- **Lower bound for the size of a type class.** If the value `k ≤ N` appears `D k` times in
`a : Fin n → ℕ` and `ψ` is a positive probability vector on `range (N + 1)`, then
`log #(typeClass a)` is at least
`∑ k, D k * log (ψ k)⁻¹ - ∑ k, (D k - n * ψ k) ^ 2 / (n * ψ k) - (N + 1) * (1 + log (n + 1))`. -/
lemma le_log_card_typeClass (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) {ψ : ℕ → ℝ}
    (hψ : ∀ k ∈ range (N + 1), 0 < ψ k) (hψ₁ : ∑ k ∈ range (N + 1), ψ k = 1) :
    ∑ k ∈ range (N + 1), #{r | a r = k} * log (ψ k)⁻¹ -
        ∑ k ∈ range (N + 1), (#{r | a r = k} - n * ψ k) ^ 2 / (n * ψ k) -
        (N + 1) * (1 + log (n + 1)) ≤ log #(typeClass a) := by
  have h := sum_mul_log_div_sub_le_log _ (sum_card_filter_eq ha)
  rw [card_range, Nat.cast_add_one] at h
  rw [log_card_typeClass a ha]
  linarith [sum_mul_log_inv_sub_le _ (sum_card_filter_eq ha) hψ hψ₁]

end ArithmeticTriangleRemovalInVectorSpaces
