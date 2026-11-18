/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/Recurrence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Data.Rat.Encodable
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Recurrence
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

/-- Read the Boolean test at a real state as the real number zero or one. -/
def choiceBit (test : ℝ → Bool) (s : ℝ) : ℝ := if test s then 1 else 0

/-- The state recursion with increment `δ * (t - choiceBit test currentState)`. -/
def state (test : ℝ → Bool) (δ t : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => state test δ t n + δ * (t - choiceBit test (state test δ t n))

/-- The real-valued Boolean choice made at the specified state-recursion stage. -/
def branch (test : ℝ → Bool) (δ t : ℝ) (n : ℕ) : ℝ :=
  choiceBit test (state test δ t n)

theorem choiceBit_eq_zero_or_one (test : ℝ → Bool) (s : ℝ) :
    choiceBit test s = 0 ∨ choiceBit test s = 1 := by
  simp only [choiceBit]
  split <;> simp

theorem state_mem_Icc (test : ℝ → Bool) (δ t lo hi : ℝ)
    (hδ : 0 < δ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (left : ∀ s ∈ Set.Icc lo (lo + δ), test s = false)
    (right : ∀ s ∈ Set.Icc (hi - δ) hi, test s = true) :
    ∀ n, state test δ t n ∈ Set.Icc lo hi := by
  intro n
  induction n with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
    rcases ih with ⟨hslo, hshi⟩
    have hdt₀ : 0 < δ * t := mul_pos hδ ht₀
    have hdt₁ : δ * t < δ := by nlinarith
    have hneg : δ * (t - 1) < 0 := mul_neg_of_pos_of_neg hδ (by linarith)
    cases hb : test (state test δ t n) with
    | false =>
      have hs : state test δ t n < hi - δ := by
        by_contra h
        have := right _ ⟨le_of_not_gt h, hshi⟩
        simp [hb] at this
      simp only [state, choiceBit, hb, Bool.false_eq_true, ↓reduceIte, sub_zero]
      constructor <;> linarith
    | true =>
      have hs : lo + δ < state test δ t n := by
        by_contra h
        have := left _ ⟨hslo, le_of_not_gt h⟩
        simp [hb] at this
      simp only [state, choiceBit, hb, ↓reduceIte]
      constructor <;> nlinarith

theorem state_eq_sum (test : ℝ → Bool) (δ t : ℝ) (n : ℕ) :
    state test δ t n = δ * ((n : ℝ) * t - ∑ k ∈ Finset.range n, branch test δ t k) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    simp only [state, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    change state test δ t n + δ * (t - branch test δ t n) = _
    rw [ih]
    ring

theorem frequency_error (test : ℝ → Bool) (δ t : ℝ) (n : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hs : |state test δ t n| < 1) :
    |t - (∑ k ∈ Finset.range n, branch test δ t k) / (n : ℝ)| <
      1 / ((n : ℝ) * δ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * δ := mul_pos hn' hδ
  have heq : t - (∑ k ∈ Finset.range n, branch test δ t k) / (n : ℝ) =
      state test δ t n / ((n : ℝ) * δ) := by
    rw [state_eq_sum]
    field_simp
  rw [heq, abs_div, abs_of_pos hden]
  exact (div_lt_div_iff_of_pos_right hden).mpr hs

/-- The rational affine span consisting of numbers of the form `a + b * t`. -/
def rationalSpan (t : ℝ) : Set ℝ := {s | ∃ a b : ℚ, s = a + b * t}

theorem rationalSpan_countable (t : ℝ) : (rationalSpan t).Countable := by
  have hr : rationalSpan t = Set.range (fun p : ℚ × ℚ => (p.1 : ℝ) + p.2 * t) := by
    ext s
    simp only [rationalSpan, Set.mem_ofPred_eq, Set.mem_range, Prod.exists]
    exact ⟨fun ⟨a,b,h⟩ => ⟨a,b,h.symm⟩, fun ⟨a,b,h⟩ => ⟨a,b,h.symm⟩⟩
  rw [hr]
  exact Set.countable_range _

theorem state_mem_rationalSpan (test : ℝ → Bool) (δ : ℚ) (t : ℝ) :
    ∀ n, state test (δ : ℝ) t n ∈ rationalSpan t := by
  intro n
  induction n with
  | zero => exact ⟨0,0, by simp [state]⟩
  | succ n ih =>
    rcases ih with ⟨a,b,hab⟩
    cases hb : test (state test (δ : ℝ) t n) with
    | false =>
      refine ⟨a,b+δ, ?_⟩
      simp only [state, choiceBit, hb, Bool.false_eq_true, ↓reduceIte, sub_zero]
      rw [hab]
      push_cast
      ring
    | true =>
      refine ⟨a-δ,b+δ, ?_⟩
      simp only [state, choiceBit, hb, ↓reduceIte]
      rw [hab]
      push_cast
      ring

theorem state_mem_Icc_on_span (test : ℝ → Bool) (δ : ℚ) (t lo hi : ℝ)
    (hδ : (0 : ℝ) < δ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (left : ∀ s ∈ rationalSpan t, s ∈ Set.Icc lo (lo + δ) → test s = false)
    (right : ∀ s ∈ rationalSpan t, s ∈ Set.Icc (hi - δ) hi → test s = true) :
    ∀ n, state test (δ : ℝ) t n ∈ Set.Icc lo hi := by
  intro n
  induction n with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
    rcases ih with ⟨hslo, hshi⟩
    have hdt₀ : 0 < (δ : ℝ) * t := mul_pos hδ ht₀
    have hdt₁ : (δ : ℝ) * t < δ := by nlinarith
    have hneg : (δ : ℝ) * (t - 1) < 0 :=
      mul_neg_of_pos_of_neg hδ (by linarith)
    cases hb : test (state test (δ : ℝ) t n) with
    | false =>
      have hs : state test (δ : ℝ) t n < hi - δ := by
        by_contra h
        have := right _ (state_mem_rationalSpan test δ t n) ⟨le_of_not_gt h, hshi⟩
        simp [hb] at this
      simp only [state, choiceBit, hb, Bool.false_eq_true, ↓reduceIte, sub_zero]
      constructor <;> linarith
    | true =>
      have hs : lo + δ < state test (δ : ℝ) t n := by
        by_contra h
        have := left _ (state_mem_rationalSpan test δ t n) ⟨hslo, le_of_not_gt h⟩
        simp [hb] at this
      simp only [state, choiceBit, hb, ↓reduceIte]
      constructor <;> nlinarith

theorem exists_radius_lt (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ 1 / ((n : ℝ) * δ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (δ * ε))
  have hpos : 0 < 1 / (δ * ε) := one_div_pos.mpr (mul_pos hδ hε)
  have hn' : (0 : ℝ) < n := lt_trans hpos hn
  refine ⟨n, by exact_mod_cast hn', ?_⟩
  have hh : 1 < (n : ℝ) * (δ * ε) := (div_lt_iff₀ (mul_pos hδ hε)).mp hn
  apply (div_lt_iff₀ (mul_pos hn' hδ)).mpr
  nlinarith

theorem comparison_search (t δ : ℝ) (a : ℕ → ℝ) (hδ : 0 < δ)
    (herr : ∀ n : ℕ, 0 < n → |t - a n| < 1 / ((n : ℝ) * δ))
    (q : ℝ) (hqt : q ≠ t) :
    (∃ n : ℕ, 0 < n ∧
      (q < a n - 1 / ((n : ℝ) * δ) ∨ a n + 1 / ((n : ℝ) * δ) < q)) ∧
    (∀ n : ℕ, 0 < n →
      (q < a n - 1 / ((n : ℝ) * δ) → q < t) ∧
      (a n + 1 / ((n : ℝ) * δ) < q → t < q)) := by
  constructor
  · rcases lt_or_gt_of_ne hqt with hlt | hgt
    · obtain ⟨n, hn, hrad⟩ := exists_radius_lt δ ((t-q)/2) hδ (by linarith)
      refine ⟨n, hn, Or.inl ?_⟩
      have he := (abs_lt.mp (herr n hn)).2
      linarith
    · obtain ⟨n, hn, hrad⟩ := exists_radius_lt δ ((q-t)/2) hδ (by linarith)
      refine ⟨n, hn, Or.inr ?_⟩
      have he := (abs_lt.mp (herr n hn)).1
      linarith
  · intro n hn
    rcases abs_lt.mp (herr n hn) with ⟨hl,hu⟩
    constructor <;> intro h <;> linarith

theorem irrational_cut_iff_search (t δ : ℝ) (a : ℕ → ℝ) (ht : Irrational t)
    (hδ : 0 < δ)
    (herr : ∀ n : ℕ, 0 < n → |t - a n| < 1 / ((n : ℝ) * δ)) (q : ℚ) :
    (q : ℝ) < t ↔ ∃ n : ℕ, 0 < n ∧ (q : ℝ) < a n - 1 / ((n : ℝ) * δ) := by
  have hne : (q : ℝ) ≠ t := fun h => ht ⟨q, h⟩
  obtain ⟨⟨n, hn, hs⟩, sound⟩ := comparison_search t δ a hδ herr q hne
  constructor
  · intro hqt
    rcases hs with hs | hs
    · exact ⟨n, hn, hs⟩
    · exact False.elim ((not_lt_of_gt hqt) ((sound n hn).2 hs))
  · rintro ⟨m, hm, hcmp⟩
    exact (sound m hm).1 hcmp

end TuringRigidity

end OAI
