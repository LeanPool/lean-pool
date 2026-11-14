/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Intervals cut out by finitely many affine inequalities

The elementary one-dimensional geometry used in the cell divergence theorem.
Artificial outer endpoints allow a compactly supported field to be integrated
without improper endpoint bookkeeping.
-/

public section

open Set

namespace LiebThirring

/-- A transverse genuine facet has points of the open intersection beside it. -/
theorem exists_strict_halfspace_of_face {ι : Type*} [Finite ι]
    (a b : ι → ℝ) (i : ι) (hi : a i ≠ 0)
    (hface : ∀ j, j ≠ i → (b i / a i) * a j < b j) :
    ∃ t : ℝ, ∀ j, t * a j < b j := by
  let O : Set ℝ := {t | ∀ j : {j : ι // j ≠ i}, t * a j.val < b j.val}
  have hO : IsOpen O := by
    have he : O = ⋂ j : {j : ι // j ≠ i}, {t : ℝ | t * a j.val < b j.val} := by
      ext t
      simp only [O, mem_ofPred_eq, mem_iInter]
    rw [he]
    apply isOpen_iInter_of_finite
    intro j
    have hc : Continuous (fun t : ℝ => t * a j.val) := continuous_id.mul continuous_const
    exact isOpen_lt hc continuous_const
  have hm : b i / a i ∈ O := fun j => hface j.val j.property
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (b i / a i) hm
  rcases hi.lt_or_gt with hi | hi
  · refine ⟨b i / a i + ε / 2, ?_⟩
    have ht : b i / a i + ε / 2 ∈ O := hball (by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      exact half_lt_self hε)
    intro j
    by_cases hj : j = i
    · rw [hj, add_mul, div_mul_cancel₀ _ hi.ne]
      exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg (half_pos hε) hi)
    · exact ht ⟨j, hj⟩
  · refine ⟨b i / a i - ε / 2, ?_⟩
    have ht : b i / a i - ε / 2 ∈ O := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg,
        abs_of_pos (half_pos hε)]
      exact half_lt_self hε)
    intro j
    by_cases hj : j = i
    · rw [hj, sub_mul, div_mul_cancel₀ _ hi.ne']
      exact sub_lt_self _ (mul_pos (half_pos hε) hi)
    · exact ht ⟨j, hj⟩

/-- A nonempty slice of finitely many strict affine halfspaces, truncated to
an interval containing a point of the slice, is itself an open interval. -/
theorem exists_truncated_halfspace_interval {ι : Type*} [Finite ι]
    (a b : ι → ℝ) {A B t₀ : ℝ} (hA : A < t₀) (hB : t₀ < B)
    (h₀ : ∀ i, t₀ * a i < b i) :
    ∃ L U : ℝ, A ≤ L ∧ L < t₀ ∧ t₀ < U ∧ U ≤ B ∧
      (∀ i, 0 < a i → U ≤ b i / a i) ∧
      (∀ i, a i < 0 → b i / a i ≤ L) ∧
      (U = B ∨ ∃ i, 0 < a i ∧ U = b i / a i) ∧
      (L = A ∨ ∃ i, a i < 0 ∧ L = b i / a i) ∧
      (∀ t, ((∀ i, t * a i < b i) ∧ A < t ∧ t < B) ↔ L < t ∧ t < U) := by
  classical
  let := Fintype.ofFinite ι
  let P : Finset (Option ι) := insert none ((Finset.univ.filter (fun i => 0 < a i)).image some)
  let N : Finset (Option ι) := insert none ((Finset.univ.filter (fun i => a i < 0)).image some)
  let up : Option ι → ℝ := fun i => i.elim B (fun i => b i / a i)
  let lo : Option ι → ℝ := fun i => i.elim A (fun i => b i / a i)
  have hPn : P.Nonempty := ⟨none, Finset.mem_insert_self _ _⟩
  have hNn : N.Nonempty := ⟨none, Finset.mem_insert_self _ _⟩
  obtain ⟨ip, hip, hmin⟩ := Finset.exists_min_image P up hPn
  obtain ⟨im, him, hmax⟩ := Finset.exists_max_image N lo hNn
  have hsomeP (i : ι) : some i ∈ P ↔ 0 < a i := by simp [P]
  have hsomeN (i : ι) : some i ∈ N ↔ a i < 0 := by simp [N]
  have hUpper : up ip ≤ B := hmin none (Finset.mem_insert_self _ _)
  have hLower : A ≤ lo im := hmax none (Finset.mem_insert_self _ _)
  have hUpper₀ : t₀ < up ip := by
    cases ip with
    | none => exact hB
    | some i => exact (lt_div_iff₀ (hsomeP i |>.mp hip)).mpr (h₀ i)
  have hLower₀ : lo im < t₀ := by
    cases im with
    | none => exact hA
    | some i => exact (div_lt_iff_of_neg (hsomeN i |>.mp him)).mpr (h₀ i)
  have hp (i : ι) (hi : 0 < a i) : up ip ≤ b i / a i :=
    hmin (some i) ((hsomeP i).mpr hi)
  have hm (i : ι) (hi : a i < 0) : b i / a i ≤ lo im :=
    hmax (some i) ((hsomeN i).mpr hi)
  have hup : up ip = B ∨ ∃ i, 0 < a i ∧ up ip = b i / a i := by
    cases ip with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, (hsomeP i).mp hip, rfl⟩
  have hlo : lo im = A ∨ ∃ i, a i < 0 ∧ lo im = b i / a i := by
    cases im with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, (hsomeN i).mp him, rfl⟩
  refine ⟨lo im, up ip, hLower, hLower₀, hUpper₀, hUpper, hp, hm, hup, hlo, ?_⟩
  intro t
  constructor
  · rintro ⟨ht, htA, htB⟩
    constructor
    · rcases hlo with he | ⟨i, hi, he⟩
      · exact he ▸ htA
      · rw [he]
        exact (div_lt_iff_of_neg hi).mpr (ht i)
    · rcases hup with he | ⟨i, hi, he⟩
      · exact he ▸ htB
      · rw [he]
        exact (lt_div_iff₀ hi).mpr (ht i)
  · rintro ⟨htL, htU⟩
    refine ⟨?_, hLower.trans_lt htL, htU.trans_le hUpper⟩
    intro i
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · have ht := (hm i hi).trans_lt htL
      exact (div_lt_iff_of_neg hi).mp ht
    · simpa only [hi, mul_zero] using h₀ i
    · have ht := htU.trans_le (hp i hi)
      exact (lt_div_iff₀ hi).mp ht

end LiebThirring

end
