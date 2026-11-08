/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Coupling.Basic
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Coupling.Decomposition
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pebody's theorem

Three decreasing mass functions on `[0, N]` with equal masses whose means sum to `N` are compatible.
This is Theorem 4 of Pebody, *Proof of a conjecture of Kleinberg, Sawin and Speyer*. Kleinberg,
Sawin and Speyer apply it to the truncated geometric distribution with mean `N / 3`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.geom N ρ`: the function `k ↦ ρ ^ k` on `[0, N]`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.compatible_of_isDecreasingOn`: Pebody's theorem.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_compatible_geom`: for `N > 0` there is
  `ρ ∈ [1 / 2, 1)` such that `geom N ρ` has mean `N / 3` and three copies of it are compatible.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {N : ℕ} {π π₁ π₂ π₃ : ℕ → ℝ}

private lemma IsDecreasingOn.isWeight (h : IsDecreasingOn N π) :
    IsWeight N fun k ↦ (k + 1) * (π k - π (k + 1)) :=
  ⟨h.weight_nonneg, fun _ hk ↦ h.weight_eq_zero hk⟩

private lemma IsDecreasingOn.mass_eq (h : IsDecreasingOn N π) :
    mass N π = mass N fun k ↦ (k + 1) * (π k - π (k + 1)) := by
  nth_rw 1 [h.eq_hat]
  exact mass_hat _

private lemma IsDecreasingOn.moment_eq (h : IsDecreasingOn N π) :
    moment N π = moment N (fun k ↦ (k + 1) * (π k - π (k + 1))) / 2 := by
  nth_rw 1 [h.eq_hat]
  exact moment_hat _

/-- Pebody's theorem at every level. -/
private lemma decreasingCompatible (N : ℕ) : DecreasingCompatible N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro π₁ π₂ π₃ h₁ h₂ h₃ hm₂ hm₃ hmom
  rw [h₁.eq_hat, h₂.eq_hat, h₃.eq_hat]
  refine IsBalanced.compatible_hat ih ⟨h₁.isWeight, h₂.isWeight, h₃.isWeight, ?_, ?_, ?_⟩
  · rw [← h₁.mass_eq, ← h₂.mass_eq, hm₂]
  · rw [← h₁.mass_eq, ← h₃.mass_eq, hm₃]
  · rw [← h₁.mass_eq]
    linarith [h₁.moment_eq, h₂.moment_eq, h₃.moment_eq]

/-- **Pebody's theorem.** Three decreasing mass functions on `[0, N]` with equal masses whose means
sum to `N` are compatible. -/
private lemma compatible_of_isDecreasingOn (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂)
    (h₃ : IsDecreasingOn N π₃) (hm₂ : mass N π₂ = mass N π₁) (hm₃ : mass N π₃ = mass N π₁)
    (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁) :
    Compatible N π₁ π₂ π₃ :=
  decreasingCompatible N π₁ π₂ π₃ h₁ h₂ h₃ hm₂ hm₃ hmom

/-- The function `k ↦ ρ ^ k` on `[0, N]`, extended by zero. -/
@[expose] noncomputable def geom (N : ℕ) (ρ : ℝ) (k : ℕ) : ℝ :=
  if k ≤ N then ρ ^ k else 0

private lemma mass_geom (ρ : ℝ) : mass N (geom N ρ) = ∑ k ∈ range (N + 1), ρ ^ k := by
  rw [mass]
  congr! 1 with k hk
  simp [geom, Nat.le_of_lt_succ (mem_range.1 hk)]

private lemma moment_geom (ρ : ℝ) : moment N (geom N ρ) = ∑ k ∈ range (N + 1), k * ρ ^ k := by
  rw [moment]
  congr! 1 with k hk
  simp [geom, Nat.le_of_lt_succ (mem_range.1 hk)]

private lemma isDecreasingOn_geom {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    IsDecreasingOn N (geom N ρ) := by
  refine ⟨?_, ?_, by simp [geom]⟩
  · intro k
    unfold geom
    positivity
  · intro a b hab
    unfold geom
    grind [pow_le_pow_of_le_one, pow_nonneg]

/-- `∑ k ≤ M, (3 * k - N) / 2 ^ k = 6 - 2 * N - (3 * M + 6 - N) / 2 ^ M`. -/
private lemma sum_mul_half_pow (N M : ℕ) :
    ∑ k ∈ range (M + 1), (3 * k - N : ℝ) * (1 / 2) ^ k = 6 - 2 * N - (3 * M + 6 - N) / 2 ^ M := by
  induction M with
  | zero =>
    norm_num
    ring
  | succ M ih =>
    rw [sum_range_succ, ih, one_div_pow]
    push_cast
    field_simp
    ring

/-- For `N > 0`, the polynomial `∑ k ≤ N, (3 k - N) ρ ^ k` is nonpositive at `ρ = 1 / 2`. -/
private lemma sum_mul_half_pow_nonpos (hN : 0 < N) :
    ∑ k ∈ range (N + 1), (3 * k - N : ℝ) * (1 / 2) ^ k ≤ 0 := by
  rw [sum_mul_half_pow]
  obtain rfl | rfl | hN := (by grind : N = 1 ∨ N = 2 ∨ 3 ≤ N)
  · norm_num
  · norm_num
  · have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [div_nonneg (by linarith : (0 : ℝ) ≤ 3 * N + 6 - N) (by positivity : (0 : ℝ) ≤ 2 ^ N)]

/-- The polynomial `∑ k ≤ N, (3 k - N) ρ ^ k` has a root in `[1 / 2, 1)`. -/
private lemma exists_sum_mul_pow_eq_zero (hN : 0 < N) :
    ∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ < 1 ∧ ∑ k ∈ range (N + 1), (3 * k - N) * ρ ^ k = 0 := by
  set f : ℝ → ℝ := fun ρ ↦ ∑ k ∈ range (N + 1), (3 * k - N) * ρ ^ k
  have hf₁ : f 1 = N * (N + 1) / 2 := by
    simp only [f, one_pow, mul_one, sum_sub_distrib, ← mul_sum, sum_const, card_range,
      nsmul_eq_mul, sum_range_succ_cast]
    push_cast
    ring
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨ρ, ⟨hρ₀, hρ₁⟩, hρ⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (by fun_prop : Continuous f).continuousOn
    (⟨sum_mul_half_pow_nonpos hN, by nlinarith⟩ : (0 : ℝ) ∈ Set.Icc (f (1 / 2)) (f 1))
  refine ⟨ρ, hρ₀, lt_of_le_of_ne hρ₁ ?_, hρ⟩
  rintro rfl
  nlinarith

/-- **The distribution of Kleinberg, Sawin and Speyer.** For `N > 0` there is `ρ ∈ [1 / 2, 1)` such
that `geom N ρ` has mean `N / 3` and three copies of it are compatible. -/
lemma exists_compatible_geom (hN : 0 < N) :
    ∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ < 1 ∧
      3 * ∑ k ∈ range (N + 1), k * ρ ^ k = N * ∑ k ∈ range (N + 1), ρ ^ k ∧
      Compatible N (geom N ρ) (geom N ρ) (geom N ρ) := by
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ := exists_sum_mul_pow_eq_zero hN
  have hmean : 3 * ∑ k ∈ range (N + 1), k * ρ ^ k = N * ∑ k ∈ range (N + 1), ρ ^ k := by
    simp only [sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum] at hρ
    linarith
  have hd := isDecreasingOn_geom (N := N) (by linarith) hρ₁.le
  refine ⟨ρ, hρ₀, hρ₁, hmean, compatible_of_isDecreasingOn hd hd hd rfl rfl ?_⟩
  rw [moment_geom, mass_geom]
  linarith

end ArithmeticTriangleRemovalInVectorSpaces
