/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Coupling.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Peeling off the layer where the first variable vanishes

This file contains the induction step of Pebody's proof that decreasing mass functions on `[0, N]`
whose means sum to `N` are compatible. If the second and the third mass functions vanish at `N`,
then the mass of the first one at `0` can be matched with pairs `(k, N - k)` so that what remains is
again decreasing, at level `N - 1`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn N π`: `π` is a nonnegative, antitone mass
  function vanishing beyond `N`.
* `ArithmeticTriangleRemovalInVectorSpaces.mass N π` and
  `ArithmeticTriangleRemovalInVectorSpaces.moment N π`: the total mass and the first moment.
* `ArithmeticTriangleRemovalInVectorSpaces.DecreasingCompatible N`: the statement of Pebody's
  theorem at level `N`.
* `ArithmeticTriangleRemovalInVectorSpaces.peelWeight N π₂ π₃ x`: the overlap of `π₂` and the
  reflection of `π₃`, cut at height `x`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.le_sum_min`: Lemma 3.1 of Pebody.
* `ArithmeticTriangleRemovalInVectorSpaces.compatible_of_eq_zero_of_eq_zero`: Corollary 3.2 of
  Pebody.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- A mass function on `ℕ` is decreasing on `[0, N]` if it is nonnegative, antitone and vanishes at
`N + 1`. -/
@[expose] def IsDecreasingOn (N : ℕ) (π : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ π k) ∧ Antitone π ∧ π (N + 1) = 0

/-- The total mass of `π` on `[0, N]`. -/
@[expose] def mass (N : ℕ) (π : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), π k

/-- The first moment of `π` on `[0, N]`. -/
@[expose] def moment (N : ℕ) (π : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), k * π k

/-- Pebody's theorem at level `N`: decreasing mass functions on `[0, N]` with equal masses whose
means sum to `N` are compatible. -/
@[expose] def DecreasingCompatible (N : ℕ) : Prop :=
  ∀ π₁ π₂ π₃ : ℕ → ℝ, IsDecreasingOn N π₁ → IsDecreasingOn N π₂ → IsDecreasingOn N π₃ →
    mass N π₂ = mass N π₁ → mass N π₃ = mass N π₁ →
    moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁ → Compatible N π₁ π₂ π₃

variable {N : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}

lemma mass_add : mass N (π + π') = mass N π + mass N π' := by
  simp [mass, sum_add_distrib]

lemma mass_sub : mass N (π - π') = mass N π - mass N π' := by
  simp [mass, sum_sub_distrib]

lemma mass_smul (r : ℝ) : mass N (r • π) = r * mass N π := by
  simp [mass, mul_sum]

lemma moment_add : moment N (π + π') = moment N π + moment N π' := by
  simp [moment, mul_add, sum_add_distrib]

lemma moment_sub : moment N (π - π') = moment N π - moment N π' := by
  simp [moment, mul_sub, sum_sub_distrib]

lemma moment_smul (r : ℝ) : moment N (r • π) = r * moment N π := by
  simp only [moment, Pi.smul_apply, smul_eq_mul, mul_sum]
  congr with k
  ring

private lemma mass_succ : mass (N + 1) π = mass N π + π (N + 1) :=
  sum_range_succ _ _

private lemma moment_succ : moment (N + 1) π = moment N π + (N + 1) * π (N + 1) := by
  rw [moment, sum_range_succ, ← moment]
  push_cast
  ring

private lemma mass_shift : mass N (fun k ↦ π (k + 1)) = mass (N + 1) π - π 0 := by
  rw [mass, mass, sum_range_succ' _ (N + 1)]
  ring

private lemma moment_shift :
    moment N (fun k ↦ π (k + 1)) = moment (N + 1) π - mass (N + 1) π + π 0 := by
  rw [moment, moment, mass, sum_range_succ' _ (N + 1), sum_range_succ' _ (N + 1)]
  push_cast
  simp only [add_mul, one_mul, sum_add_distrib]
  ring

private lemma mass_reflect : mass N (fun k ↦ π (N - k)) = mass N π := by
  simpa [mass] using sum_range_reflect π (N + 1)

private lemma moment_reflect : moment N (fun k ↦ π (N - k)) = N * mass N π - moment N π := by
  rw [moment, ← sum_range_reflect, mass, moment, mul_sum, ← sum_sub_distrib]
  congr! 1 with k hk
  rw [mem_range] at hk
  rw [Nat.add_sub_cancel, Nat.sub_sub_self (by grind), Nat.cast_sub (by grind)]
  ring

lemma IsDecreasingOn.eq_zero_of_lt (h : IsDecreasingOn N π) {k : ℕ} (hk : N < k) : π k = 0 := by
  obtain ⟨hπ₀, hπ, hπN⟩ := h
  exact le_antisymm (hπN ▸ hπ hk) (hπ₀ k)

private lemma IsDecreasingOn.le_mass (h : IsDecreasingOn N π) (k : ℕ) : π k ≤ mass N π := by
  have ⟨hπ₀, _, _⟩ := h
  by_cases hk : k ≤ N
  · refine single_le_sum ?_ (mem_range.2 (by grind))
    intro i _
    exact hπ₀ i
  · rw [h.eq_zero_of_lt (by grind)]
    apply sum_nonneg
    intro i _
    exact hπ₀ i

private lemma IsDecreasingOn.of_succ (h : IsDecreasingOn (N + 1) π) (hN : π (N + 1) = 0) :
    IsDecreasingOn N π := by
  obtain ⟨hπ₀, hπ, -⟩ := h
  exact ⟨hπ₀, hπ, hN⟩

/-- The first mass function after peeling: `π` shifted down by one. -/
lemma IsDecreasingOn.shift (h : IsDecreasingOn (N + 1) π) :
    IsDecreasingOn N fun k ↦ π (k + 1) := by
  obtain ⟨hπ₀, hπ, hπN⟩ := h
  exact ⟨fun k ↦ hπ₀ _, fun _ _ hab ↦ hπ (by grind), hπN⟩

/-- Decreasing weights on `[s, e]` have mean at most `(s + e) / 2`. -/
private lemma two_mul_sum_Icc_le (hπ : Antitone π) (s e : ℕ) :
    2 * ∑ k ∈ Icc s e, (k : ℝ) * π k ≤ (s + e) * ∑ k ∈ Icc s e, π k := by
  have hrefl : ∑ k ∈ Icc s e, (s + e - 2 * k : ℝ) * π k =
      ∑ k ∈ Icc s e, (2 * k - (s + e) : ℝ) * π (s + e - k) := by
    refine sum_nbij' (fun k ↦ s + e - k) (fun k ↦ s + e - k) ?_ ?_ ?_ ?_ ?_
    any_goals intro k hk; simp only [mem_Icc] at hk ⊢; grind
    intro k hk
    rw [mem_Icc] at hk
    rw [Nat.sub_sub_self (by grind), Nat.cast_sub (by grind)]
    push_cast
    ring
  have hterm (k) (_ : k ∈ Icc s e) : (2 * k - (s + e) : ℝ) * (π k - π (s + e - k)) ≤ 0 := by
    rcases le_total (2 * k) (s + e) with h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (by exact_mod_cast h))
        (sub_nonneg.2 (hπ (by grind)))
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (by exact_mod_cast h))
        (sub_nonpos.2 (hπ (by grind)))
  have hsum := sum_nonpos hterm
  simp only [mul_sub, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum] at hrefl hsum
  linarith

/-- For a decreasing mass function `π` on `[0, N]` and `t ≤ N`, the bound
`2 * moment N π ≤ t * mass N π + (N + 1) * (mass N π - ∑ k ∈ range (t + 1), π k)`. -/
private lemma IsDecreasingOn.two_mul_moment_le (h : IsDecreasingOn N π) {t : ℕ} (ht : t ≤ N) :
    2 * moment N π ≤ t * mass N π + (N + 1) * (mass N π - ∑ k ∈ range (t + 1), π k) := by
  obtain ⟨-, hπ, -⟩ := h
  have h₁ := two_mul_sum_Icc_le hπ 0 t
  have h₂ := two_mul_sum_Icc_le hπ (t + 1) N
  rw [← Ico_add_one_right_eq_Icc, ← range_eq_Ico] at h₁
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by grind), sum_Ico_eq_sub _ (by grind)] at h₂
  rw [moment, mass]
  push_cast at h₁ h₂
  linarith

/-- **Lemma 3.1 of Pebody**, for a cut after `t + 1 ≤ N` terms. -/
private lemma le_sum_range_add_sum_Ico (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂)
    (h₃ : IsDecreasingOn N π₃) (hm₂ : mass N π₂ = mass N π₁) (hm₃ : mass N π₃ = mass N π₁)
    (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁) {t : ℕ} (ht : t + 1 ≤ N) :
    π₁ 0 ≤ ∑ k ∈ range (t + 1), π₃ (N - k) + ∑ k ∈ Ico (t + 1) (N + 1), π₂ k := by
  have e₁ := h₁.two_mul_moment_le (Nat.zero_le N)
  have e₂ := h₂.two_mul_moment_le (by grind : t ≤ N)
  have e₃ := h₃.two_mul_moment_le (t := N - 1 - t) (by grind)
  rw [zero_add, sum_range_one, Nat.cast_zero, zero_mul, zero_add] at e₁
  rw [(by grind : N - 1 - t + 1 = N - t), Nat.cast_sub (by grind), Nat.cast_sub (by grind)] at e₃
  rw [range_eq_Ico, sum_Ico_reflect _ _ (by grind), Nat.add_sub_add_right, Nat.sub_zero,
    sum_Ico_eq_sub _ (by grind), sum_Ico_eq_sub _ (by grind), ← mass, ← mass]
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < N + 1)
  push_cast at e₃
  nlinarith

/-- If `a` is antitone and `b` is monotone, then `∑ k ∈ range n, min (a k) (b k)` splits at the
first point where `b` exceeds `a`. -/
private lemma exists_sum_min_eq {a b : ℕ → ℝ} (ha : Antitone a) (hb : Monotone b) (n : ℕ) :
    ∃ t ≤ n, ∑ k ∈ range n, min (a k) (b k) = ∑ k ∈ range t, b k + ∑ k ∈ Ico t n, a k := by
  classical
  have hex : ∃ t, n ≤ t ∨ a t < b t := ⟨n, .inl le_rfl⟩
  have ht := Nat.find_min' hex (.inl le_rfl)
  refine ⟨Nat.find hex, ht, ?_⟩
  rw [← sum_range_add_sum_Ico _ ht]
  congr 1
  · congr! 1 with k hk
    have := Nat.find_min hex (mem_range.1 hk)
    exact min_eq_right (by grind)
  · congr! 1 with k hk
    rw [mem_Ico] at hk
    obtain ⟨hk₁, hk₂⟩ := hk
    rcases Nat.find_spec hex with h | h
    · grind
    · exact min_eq_left ((ha hk₁).trans (h.le.trans (hb hk₁)))

/-- **Lemma 3.1 of Pebody.** The mass of `π₁` at `0` is at most the overlap
`∑ k ∈ range (N + 1), min (π₂ k) (π₃ (N - k))`. -/
private lemma le_sum_min (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂)
    (h₃ : IsDecreasingOn N π₃) (hm₂ : mass N π₂ = mass N π₁) (hm₃ : mass N π₃ = mass N π₁)
    (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁) :
    π₁ 0 ≤ ∑ k ∈ range (N + 1), min (π₂ k) (π₃ (N - k)) := by
  have ⟨_, hπ₂, _⟩ := h₂
  have ⟨_, hπ₃, _⟩ := h₃
  obtain ⟨t, ht, heq⟩ :=
    exists_sum_min_eq (b := fun k ↦ π₃ (N - k)) hπ₂ (hπ₃.comp antitone_const_tsub) (N + 1)
  rw [heq]
  rcases Nat.eq_zero_or_pos t with rfl | ht₀
  · rw [range_zero, sum_empty, zero_add, ← range_eq_Ico, ← mass, hm₂]
    exact h₁.le_mass 0
  obtain rfl | htN := ht.eq_or_lt
  · rw [Ico_self, sum_empty, add_zero]
    exact (h₁.le_mass 0).trans_eq (mass_reflect.trans hm₃).symm
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by grind⟩
  exact le_sum_range_add_sum_Ico h₁ h₂ h₃ hm₂ hm₃ hmom (by grind)

/-- The overlap of `π₂` and the reflection of `π₃`, cut at height `x`. Peeling it off removes the
layer where the first variable vanishes. -/
private noncomputable def peelWeight (N : ℕ) (π₂ π₃ : ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  min (min (π₂ k) (π₃ (N - k))) x

private lemma continuous_mass_peelWeight (N : ℕ) (π₂ π₃ : ℕ → ℝ) :
    Continuous fun x ↦ mass N (peelWeight N π₂ π₃ x) := by
  unfold mass peelWeight
  fun_prop

/-- There is a height `x ≥ 0` at which the overlap of `π₂` and `π₃` has mass `π₁ 0`. -/
private lemma exists_mass_peelWeight_eq (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂)
    (h₃ : IsDecreasingOn N π₃) (hm₂ : mass N π₂ = mass N π₁) (hm₃ : mass N π₃ = mass N π₁)
    (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁) :
    ∃ x, 0 ≤ x ∧ mass N (peelWeight N π₂ π₃ x) = π₁ 0 := by
  have ⟨hπ₁, _, _⟩ := h₁
  have ⟨hπ₂, _, _⟩ := h₂
  have ⟨hπ₃, _, _⟩ := h₃
  have h0 : mass N (peelWeight N π₂ π₃ 0) = 0 := by
    apply sum_eq_zero
    intro k _
    exact min_eq_right (le_min (hπ₂ k) (hπ₃ _))
  have hM : mass N (peelWeight N π₂ π₃ (mass N π₁)) =
      ∑ k ∈ range (N + 1), min (π₂ k) (π₃ (N - k)) := by
    congr with k
    exact min_eq_left ((min_le_left _ _).trans (hm₂ ▸ h₂.le_mass k))
  obtain ⟨x, ⟨hx, -⟩, hxeq⟩ := intermediate_value_Icc ((hπ₁ 0).trans (h₁.le_mass 0))
    (continuous_mass_peelWeight N π₂ π₃).continuousOn
    ⟨h0 ▸ hπ₁ 0, hM ▸ le_sum_min h₁ h₂ h₃ hm₂ hm₃ hmom⟩
  exact ⟨x, hx, hxeq⟩

section Peel

variable {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (h₂ : IsDecreasingOn n π₂) (h₃ : IsDecreasingOn n π₃)
include hx h₂ h₃

private lemma peelWeight_nonneg (k : ℕ) : 0 ≤ peelWeight (n + 1) π₂ π₃ x k := by
  obtain ⟨hπ₂, -, -⟩ := h₂
  obtain ⟨hπ₃, -, -⟩ := h₃
  exact le_min (le_min (hπ₂ k) (hπ₃ _)) hx

private lemma peelWeight_eq_zero_of_lt {k : ℕ} (hk : n < k) : peelWeight (n + 1) π₂ π₃ x k = 0 := by
  refine le_antisymm ?_ (peelWeight_nonneg hx h₂ h₃ k)
  exact ((min_le_left _ _).trans (min_le_left _ _)).trans (h₂.eq_zero_of_lt hk).le

private lemma peelWeight_zero : peelWeight (n + 1) π₂ π₃ x 0 = 0 := by
  refine le_antisymm ?_ (peelWeight_nonneg hx h₂ h₃ 0)
  exact ((min_le_left _ _).trans (min_le_right _ _)).trans (h₃.eq_zero_of_lt (by grind)).le

private lemma isDecreasingOn_sub_peelWeight :
    IsDecreasingOn n (π₂ - peelWeight (n + 1) π₂ π₃ x) := by
  have hN := peelWeight_eq_zero_of_lt hx h₂ h₃ (Nat.lt_succ_self n)
  obtain ⟨hπ₂₀, hπ₂, hπ₂N⟩ := h₂
  obtain ⟨-, hπ₃, -⟩ := h₃
  refine ⟨fun k ↦ sub_nonneg.2 ((min_le_left _ _).trans (min_le_left _ _)), ?_, by simp [hπ₂N, hN]⟩
  apply antitone_nat_of_succ_le
  intro k
  simp only [Pi.sub_apply, peelWeight]
  grind [hπ₂ (Nat.le_succ k), hπ₃ (by grind : n + 1 - (k + 1) ≤ n + 1 - k)]

private lemma isDecreasingOn_sub_peelWeight_reflect :
    IsDecreasingOn n (π₃ - fun c ↦ peelWeight (n + 1) π₂ π₃ x (n + 1 - c)) := by
  have h₀ := peelWeight_zero hx h₂ h₃
  obtain ⟨hπ₂₀, hπ₂, hπ₂N⟩ := h₂
  obtain ⟨hπ₃₀, hπ₃, hπ₃N⟩ := h₃
  have hle (c : ℕ) : peelWeight (n + 1) π₂ π₃ x (n + 1 - c) ≤ π₃ c := by
    by_cases hc : c ≤ n + 1
    · rw [peelWeight, Nat.sub_sub_self hc]
      grw [min_le_left, min_le_right]
    · rw [(by grind : n + 1 - c = 0), h₀]
      exact hπ₃₀ c
  refine ⟨fun c ↦ sub_nonneg.2 (hle c), ?_, by simp [hπ₃N, h₀]⟩
  apply antitone_nat_of_succ_le
  intro c
  simp only [Pi.sub_apply, peelWeight]
  grind [hπ₃ (Nat.le_succ c), hπ₂ (by grind : n + 1 - (c + 1) ≤ n + 1 - c)]

end Peel

/-- **Corollary 3.2 of Pebody.** If Pebody's theorem holds at level `n`, then decreasing mass
functions at level `n + 1` whose second and third members vanish at `n + 1` are compatible. -/
lemma compatible_of_eq_zero_of_eq_zero {n : ℕ} (ih : DecreasingCompatible n)
    (h₁ : IsDecreasingOn (n + 1) π₁) (h₂ : IsDecreasingOn (n + 1) π₂)
    (h₃ : IsDecreasingOn (n + 1) π₃) (h₂N : π₂ (n + 1) = 0) (h₃N : π₃ (n + 1) = 0)
    (hm₂ : mass (n + 1) π₂ = mass (n + 1) π₁) (hm₃ : mass (n + 1) π₃ = mass (n + 1) π₁)
    (hmom : moment (n + 1) π₁ + moment (n + 1) π₂ + moment (n + 1) π₃ =
      (n + 1 : ℕ) * mass (n + 1) π₁) :
    Compatible (n + 1) π₁ π₂ π₃ := by
  obtain ⟨x, hx, hsum⟩ := exists_mass_peelWeight_eq h₁ h₂ h₃ hm₂ hm₃ hmom
  replace h₂ := h₂.of_succ h₂N
  replace h₃ := h₃.of_succ h₃N
  have hf₀ := peelWeight_zero hx h₂ h₃
  have hfN := peelWeight_eq_zero_of_lt hx h₂ h₃ (Nat.lt_succ_self n)
  have hcomp := ih _ _ _ h₁.shift (isDecreasingOn_sub_peelWeight hx h₂ h₃)
    (isDecreasingOn_sub_peelWeight_reflect hx h₂ h₃) ?_ ?_ ?_
  · convert (hcomp.comm₁₃.shift 1).comm₁₃.add (compatible_layer (peelWeight_nonneg hx h₂ h₃))
      using 1
    · ext a
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simpa [mass] using hsum.symm
      · simp [(by grind : 1 ≤ a), (by grind : a ≠ 0), Nat.sub_add_cancel ha]
    · ext b
      by_cases hb : b ≤ n + 1
      · simp [hb]
      · simp [hb, peelWeight_eq_zero_of_lt hx h₂ h₃ (by grind : n < b)]
    · ext c
      by_cases hc : c ≤ n + 1
      · simp [hc]
      · simp [hc, (by grind : n + 1 - c = 0), hf₀]
  · rw [mass_sub, mass_shift, ← hm₂, ← hsum]
    simp [mass_succ, h₂N, hfN]
  · rw [mass_sub, mass_shift, ← hm₃, ← hsum, ← mass_reflect (π := peelWeight (n + 1) π₂ π₃ x)]
    simp [mass_succ, h₃N, hf₀]
  · have hrefl := moment_reflect (N := n + 1) (π := peelWeight (n + 1) π₂ π₃ x)
    rw [moment_succ, Nat.sub_self, hf₀, mul_zero, add_zero] at hrefl
    rw [moment_shift, mass_shift, moment_sub, moment_sub, hrefl, hsum]
    simp only [moment_succ, h₂N, h₃N, hfN, mul_zero, add_zero] at hmom ⊢
    push_cast at hmom ⊢
    linarith

end ArithmeticTriangleRemovalInVectorSpaces
