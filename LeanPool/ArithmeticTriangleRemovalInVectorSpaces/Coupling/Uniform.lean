/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Coupling.Peeling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform distributions and their mixtures

Every decreasing mass function on `[0, N]` is a nonnegative combination of the uniform distributions
`unif k` on `[0, k]`, `k ≤ N`. This file proves that `unif k₁`, `unif k₂` and a mixture of `unif y`
and `unif z` are compatible when their means sum to `N`, assuming Pebody's theorem at lower levels.
This is the case analysis of Section 5 of Pebody.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.unif k`: the uniform distribution on `[0, k]`.
* `ArithmeticTriangleRemovalInVectorSpaces.hat N w`: the combination
  `∑ k ∈ range (N + 1), w k • unif k`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.eq_hat`: a decreasing mass function is a
  nonnegative combination of uniform distributions.
* `ArithmeticTriangleRemovalInVectorSpaces.compatible_lastcase`: Corollary 5.2 of Pebody.
* `ArithmeticTriangleRemovalInVectorSpaces.compatible_unif_mix`: `unif k₁`, `unif k₂` and
  `α • unif y + (1 - α) • unif z` are compatible when their means sum to `N`.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The uniform distribution on `[0, k]`. -/
@[expose] noncomputable def unif (k j : ℕ) : ℝ :=
  if j ≤ k then ((k : ℝ) + 1)⁻¹ else 0

/-- The combination `∑ k ∈ range (N + 1), w k • unif k` of uniform distributions. -/
@[expose] noncomputable def hat (N : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), w k * unif k j

variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}

lemma IsDecreasingOn.add (h : IsDecreasingOn N π) (h' : IsDecreasingOn N π') :
    IsDecreasingOn N (π + π') := by
  obtain ⟨hπ₀, hπ, hπN⟩ := h
  obtain ⟨hπ₀', hπ', hπN'⟩ := h'
  exact ⟨fun k ↦ add_nonneg (hπ₀ k) (hπ₀' k), hπ.add hπ', by simp [hπN, hπN']⟩

lemma IsDecreasingOn.smul (h : IsDecreasingOn N π) {r : ℝ} (hr : 0 ≤ r) :
    IsDecreasingOn N (r • π) := by
  obtain ⟨hπ₀, hπ, hπN⟩ := h
  exact ⟨fun k ↦ mul_nonneg hr (hπ₀ k), fun _ _ hab ↦ mul_le_mul_of_nonneg_left (hπ hab) hr,
    by simp [hπN]⟩

private lemma isDecreasingOn_unif (hk : k ≤ N) : IsDecreasingOn N (unif k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    unfold unif
    positivity
  · intro a b hab
    unfold unif
    grind [(by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹)]
  · simp only [unif, ite_eq_right_iff]
    grind

private lemma unif_eq_zero (hk : k < N) : unif k N = 0 := by
  simp only [unif, ite_eq_right_iff]
  grind

private lemma sum_mul_unif (hk : k ≤ N) (f : ℕ → ℝ) :
    ∑ j ∈ range (N + 1), f j * unif k j = (∑ j ∈ range (k + 1), f j) / (k + 1) := by
  rw [← sum_range_add_sum_Ico _ (by grind : k + 1 ≤ N + 1), sum_eq_zero (s := Ico _ _),
    add_zero, div_eq_mul_inv, sum_mul]
  · rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    congr with j
    simp [unif, j.is_le]
  · intro j hj
    simp only [mem_Ico] at hj
    simp [unif, (by grind : ¬j ≤ k)]

private lemma mass_unif (hk : k ≤ N) : mass N (unif k) = 1 := by
  have h := sum_mul_unif hk fun _ ↦ 1
  simp only [one_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  rw [mass, h]
  push_cast
  field_simp

lemma sum_range_succ_cast (k : ℕ) : ∑ j ∈ range (k + 1), (j : ℝ) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

private lemma moment_unif (hk : k ≤ N) : moment N (unif k) = k / 2 := by
  rw [moment, sum_mul_unif hk, sum_range_succ_cast]
  field_simp

private lemma isDecreasingOn_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) : IsDecreasingOn N (α • unif y + (1 - α) • unif z) :=
  ((isDecreasingOn_unif hy).smul hα₀).add ((isDecreasingOn_unif hz).smul (by linarith))

private lemma mass_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) (α : ℝ) :
    mass N (α • unif y + (1 - α) • unif z) = 1 := by
  rw [mass_add, mass_smul, mass_smul, mass_unif hy, mass_unif hz]
  ring

private lemma moment_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) (α : ℝ) :
    moment N (α • unif y + (1 - α) • unif z) = (α * y + (1 - α) * z) / 2 := by
  rw [moment_add, moment_smul, moment_smul, moment_unif hy, moment_unif hz]
  ring

private lemma mix_eq_zero {y z : ℕ} {α : ℝ} (hy : y < N ∨ α = 0) (hz : z < N ∨ α = 1) :
    (α • unif y + (1 - α) • unif z) N = 0 := by
  rcases hy with hy | rfl <;> rcases hz with hz | hz <;> simp_all [unif_eq_zero]

/-- A mixture of uniform distributions with mean `0` is the point mass at `0`. -/
private lemma mix_eq_unif_zero {y z : ℕ} {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (h : α * y + (1 - α) * z = 0) : α • unif y + (1 - α) • unif z = unif 0 := by
  obtain ⟨hy, hz⟩ := (add_eq_zero_iff_of_nonneg (by positivity)
    (mul_nonneg (sub_nonneg.2 hα₁) z.cast_nonneg)).1 h
  rcases mul_eq_zero.1 hy with rfl | hy <;> rcases mul_eq_zero.1 hz with hz | hz
  · norm_num at hz
  · simp_all
  · rw [(by linarith : α = 1)]
    simp_all
  · simp_all [← add_smul]

lemma hat_add (w w' : ℕ → ℝ) : hat N (w + w') = hat N w + hat N w' := by
  ext j
  simp [hat, add_mul, sum_add_distrib]

lemma hat_smul (r : ℝ) (w : ℕ → ℝ) : hat N (r • w) = r • hat N w := by
  ext j
  simp [hat, mul_sum, mul_assoc]

private lemma hat_zero : hat N 0 = 0 := by
  ext j
  simp [hat]

lemma hat_single (hk : k ≤ N) : hat N (Pi.single k 1) = unif k := by
  ext j
  rw [hat, sum_eq_single_of_mem k (mem_range.2 (by grind)) fun b _ hb ↦ by simp [hb]]
  simp

lemma mass_hat (w : ℕ → ℝ) : mass N (hat N w) = ∑ k ∈ range (N + 1), w k := by
  simp only [mass, hat]
  rw [sum_comm, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  congr with k
  rw [← mul_sum, ← mass, mass_unif k.is_le, mul_one]

lemma moment_hat (w : ℕ → ℝ) :
    moment N (hat N w) = (∑ k ∈ range (N + 1), (k : ℝ) * w k) / 2 := by
  simp only [moment, hat, mul_sum]
  rw [sum_comm, div_eq_mul_inv, sum_mul, ← Fin.sum_univ_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  congr with k
  simp_rw [mul_left_comm _ (w k), ← mul_sum]
  rw [← moment, moment_unif k.is_le]
  ring

/-- **A decreasing mass function is a combination of uniform distributions**, with the nonnegative
weights `(k + 1) * (π k - π (k + 1))`. -/
lemma IsDecreasingOn.eq_hat (h : IsDecreasingOn N π) :
    π = hat N fun k ↦ (k + 1) * (π k - π (k + 1)) := by
  ext j
  have hterm (k : ℕ) : (k + 1 : ℝ) * (π k - π (k + 1)) * unif k j =
      if j ≤ k then π k - π (k + 1) else 0 := by
    unfold unif
    grind
  simp only [hat, hterm]
  by_cases hj : j ≤ N
  · rw [← sum_range_add_sum_Ico _ (by grind : j ≤ N + 1), sum_eq_zero fun k hk ↦ by grind,
      zero_add, sum_Ico_eq_sum_range]
    simp only [le_add_iff_nonneg_right, zero_le, ite_true, add_assoc j]
    rw [sum_range_sub' (fun k ↦ π (j + k)), add_zero, (by grind : j + (N + 1 - j) = N + 1),
      h.eq_zero_of_lt (Nat.lt_succ_self N), sub_zero]
  · rw [h.eq_zero_of_lt (by grind)]
    symm
    apply sum_eq_zero
    grind

lemma IsDecreasingOn.weight_nonneg (h : IsDecreasingOn N π) (k : ℕ) :
    0 ≤ (k + 1 : ℝ) * (π k - π (k + 1)) := by
  obtain ⟨-, hπ, -⟩ := h
  exact mul_nonneg (by positivity) (sub_nonneg.2 (hπ (Nat.le_succ k)))

lemma IsDecreasingOn.weight_eq_zero (h : IsDecreasingOn N π) {k : ℕ} (hk : N < k) :
    (k + 1 : ℝ) * (π k - π (k + 1)) = 0 := by
  rw [h.eq_zero_of_lt hk, h.eq_zero_of_lt (by grind), sub_zero, mul_zero]

/-- The triples `(0, b, N - b)` with `b` uniform on `[0, N]`. -/
private lemma compatible_unif_zero : Compatible N (unif 0) (unif N) (unif N) := by
  convert compatible_layer (N := N) (f := fun _ ↦ ((N : ℝ) + 1)⁻¹) (fun _ ↦ by positivity)
    using 1
  · ext a
    simp only [unif, nonpos_iff_eq_zero, CharP.cast_eq_zero, zero_add, inv_one, sum_const,
      card_range, nsmul_eq_mul]
    push_cast
    grind
  · ext b
    rfl
  · ext c
    rfl

/-- Three uniform distributions whose means sum to the level `a + b` are compatible, given Pebody's
theorem at that level. -/
private lemma compatible_unif_triple {a b : ℕ} (h : DecreasingCompatible (a + b)) :
    Compatible (a + b) (unif a) (unif b) (unif (a + b)) := by
  refine h _ _ _ (isDecreasingOn_unif (by grind)) (isDecreasingOn_unif (by grind))
    (isDecreasingOn_unif le_rfl) ?_ ?_ ?_
  · rw [mass_unif (by grind), mass_unif (by grind)]
  · rw [mass_unif le_rfl, mass_unif (by grind)]
  · rw [moment_unif (by grind), moment_unif (by grind), moment_unif le_rfl, mass_unif (by grind)]
    push_cast
    ring

/-- **Corollary 3.2 of Pebody** for three mass functions of mass one. -/
private lemma compatible_of_eq_zero_of_eq_zero_of_mass_eq_one (ih : ∀ m < N, DecreasingCompatible m)
    (hN : N ≠ 0) (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂) (h₃ : IsDecreasingOn N π₃)
    (h₂N : π₂ N = 0) (h₃N : π₃ N = 0) (hm₁ : mass N π₁ = 1) (hm₂ : mass N π₂ = 1)
    (hm₃ : mass N π₃ = 1) (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N) :
    Compatible N π₁ π₂ π₃ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  refine compatible_of_eq_zero_of_eq_zero (ih n (by grind)) h₁ h₂ h₃ h₂N h₃N
    (hm₂.trans hm₁.symm) (hm₃.trans hm₁.symm) ?_
  rw [hm₁, mul_one, hmom]

/-- **Corollary 5.2 of Pebody.** For `i > 0`, the distributions `unif i`, `unif N` and the mixture
of `unif j` and `unif N` with mean `(N - i) / 2` are compatible, where `N = i + j + r + 1`. -/
private lemma compatible_lastcase {i j r : ℕ} (hij : DecreasingCompatible (i + j))
    (hir : DecreasingCompatible (i + r)) :
    Compatible (i + j + r + 1) (unif i) (unif (i + j + r + 1))
      (((i : ℝ) / (i + r + 1)) • unif j + (1 - (i : ℝ) / (i + r + 1)) • unif (i + j + r + 1)) := by
  have hw₁ : (0 : ℝ) ≤ 1 - (i + j + 1) / (i + j + r + 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have h₁ := ((compatible_unif_triple hij).shift (r + 1)).comm₂₃.smul
    (by positivity : (0 : ℝ) ≤ (i + j + 1) / (i + j + r + 2))
  have h₂ := ((compatible_unif_triple hir).shift (j + 1)).smul hw₁
  rw [(by grind : i + r + (j + 1) = i + j + (r + 1))] at h₂
  rw [(by grind : i + j + r + 1 = i + j + (r + 1))]
  convert h₁.add h₂ using 1
  · ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext k
    simp only [unif, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    grind
  · ext k
    simp only [unif, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    grind

/-- The case of Section 5 of Pebody where the first distribution is `unif N` and the mixture is one
of `unif j` and `unif N`, with weight `α < 1` on `unif j`. -/
private lemma compatible_top (ih : ∀ m < N, DecreasingCompatible m) {i j : ℕ} (hi : i ≤ N)
    (hj : j ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hsum : (i : ℝ) + α * j + (1 - α) * N = N) :
    Compatible N (unif N) (unif i) (α • unif j + (1 - α) • unif N) := by
  have hieq : (i : ℝ) = α * (N - j) := by linarith
  obtain rfl | hi₀ := Nat.eq_zero_or_pos i
  · rcases mul_eq_zero.1 (by simpa using hieq.symm : α * (N - j : ℝ) = 0) with rfl | hjN
    · simpa using compatible_unif_zero.comm₁₂
    obtain rfl : j = N := by exact_mod_cast (by linarith : (j : ℝ) = N)
    rw [← add_smul]
    simpa using compatible_unif_zero.comm₁₂
  have hij : i + j < N := by
    have : (0 : ℝ) < i := by exact_mod_cast hi₀
    exact_mod_cast (by nlinarith : (i + j : ℝ) < N)
  obtain ⟨r, rfl⟩ : ∃ r, N = i + j + r + 1 := ⟨N - i - j - 1, by grind⟩
  have hα : α = i / (i + r + 1) := by
    rw [eq_div_iff (by positivity)]
    push_cast at hieq
    linarith
  rw [hα]
  exact (compatible_lastcase (ih _ (by grind)) (ih _ (by grind))).comm₁₂

/-- The case of Section 5 of Pebody where the first distribution is `unif N` and the mixture has
mass at `N`. -/
private lemma compatible_unif_top_mix (ih : ∀ m < N, DecreasingCompatible m) {i y z : ℕ}
    (hi : i ≤ N) (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hyz : y = N ∧ α ≠ 0 ∨ z = N ∧ α ≠ 1) (hsum : (i + N + α * y + (1 - α) * z : ℝ) = 2 * N) :
    Compatible N (unif N) (unif i) (α • unif y + (1 - α) • unif z) := by
  rcases hyz with ⟨rfl, hα0⟩ | ⟨rfl, hα1⟩
  · have h := compatible_top ih hi hz (α := 1 - α) (by linarith)
      (by linarith [lt_of_le_of_ne hα₀ (Ne.symm hα0)]) (by linarith)
    rwa [sub_sub_cancel, add_comm ((1 - α) • unif z)] at h
  · exact compatible_top ih hi hy hα₀ (lt_of_le_of_ne hα₁ hα1) (by linarith)

/-- `unif k₁`, `unif k₂` and `α • unif y + (1 - α) • unif z` are compatible at level `N` when their
means sum to `N`, given Pebody's theorem at lower levels. -/
lemma compatible_unif_mix (ih : ∀ m < N, DecreasingCompatible m) {k₁ k₂ y z : ℕ} (hk₁ : k₁ ≤ N)
    (hk₂ : k₂ ≤ N) (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hsum : (k₁ + k₂ + α * y + (1 - α) * z : ℝ) = 2 * N) :
    Compatible N (unif k₁) (unif k₂) (α • unif y + (1 - α) • unif z) := by
  obtain rfl | hN := eq_or_ne N 0
  · obtain ⟨rfl, rfl, rfl, rfl⟩ : k₁ = 0 ∧ k₂ = 0 ∧ y = 0 ∧ z = 0 := by grind
    rw [← add_smul, add_sub_cancel, one_smul]
    exact compatible_unif_zero
  have hd := isDecreasingOn_mix hy hz hα₀ hα₁
  have hm := mass_mix hy hz α
  have hmom : moment N (unif k₁) + moment N (unif k₂) +
      moment N (α • unif y + (1 - α) • unif z) = N := by
    rw [moment_unif hk₁, moment_unif hk₂, moment_mix hy hz]
    linarith
  by_cases hA : k₁ < N ∧ k₂ < N
  · obtain ⟨hA₁, hA₂⟩ := hA
    exact (compatible_of_eq_zero_of_eq_zero_of_mass_eq_one ih hN hd (isDecreasingOn_unif hk₁)
      (isDecreasingOn_unif hk₂) (unif_eq_zero hA₁) (unif_eq_zero hA₂) hm (mass_unif hk₁)
      (mass_unif hk₂) (by linarith)).comm₁₂.comm₂₃
  by_cases hQ : (y < N ∨ α = 0) ∧ (z < N ∨ α = 1)
  · obtain ⟨hQy, hQz⟩ := hQ
    obtain hk₂N | rfl := hk₂.lt_or_eq
    · exact compatible_of_eq_zero_of_eq_zero_of_mass_eq_one ih hN (isDecreasingOn_unif hk₁)
        (isDecreasingOn_unif hk₂) hd (unif_eq_zero hk₂N) (mix_eq_zero hQy hQz) (mass_unif hk₁)
        (mass_unif hk₂) hm hmom
    obtain hk₁N | rfl := hk₁.lt_or_eq
    · exact (compatible_of_eq_zero_of_eq_zero_of_mass_eq_one ih hN (isDecreasingOn_unif hk₂)
        (isDecreasingOn_unif hk₁) hd (unif_eq_zero hk₁N) (mix_eq_zero hQy hQz) (mass_unif hk₂)
        (mass_unif hk₁) hm (by linarith)).comm₁₂
    rw [mix_eq_unif_zero hα₀ hα₁ (by linarith)]
    exact compatible_unif_zero.comm₁₃
  rcases (by grind : k₁ = N ∨ k₂ = N) with rfl | rfl
  · exact compatible_unif_top_mix ih hk₂ hy hz hα₀ hα₁ (by grind) (by linarith)
  · exact (compatible_unif_top_mix ih hk₁ hy hz hα₀ hα₁ (by grind) (by linarith)).comm₁₂

end ArithmeticTriangleRemovalInVectorSpaces
