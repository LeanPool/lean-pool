/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Card
public import LeanPool.ShellsortMean.Actual214Arithmetic
public import Mathlib.Tactic.NormNum

/-! Concrete cardinality and order of the integer menu implemented by the
2.14 ten-gap generator. No random generator or real-valued energy assumed. -/
@[expose] public section

namespace Shellsort.Actual214
open Finset

def window (c d : ℕ) : Finset ℕ :=
  (Icc (c - c / 100) (c + c / 100)).filter (fun h => Nat.Coprime h d)

theorem window_card (c d : ℕ) (hd : 0 < d) (hu : d ≤ 94) (hc : 9400 ≤ c) :
    c / 9400 ≤ (window c d).card := by
  let f (t : ℕ) := (c / d + t) * d + 1
  have inj : Function.Injective f := by
    intro x y e
    dsimp [f] at e
    exact Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_right hd (Nat.add_right_cancel e))
  have sub : (range (c / 9400)).image f ⊆ window c d := by
    intro h hh
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hh
    have ht' := mem_range.mp ht
    have top := Nat.div_mul_le_self c d
    have low := Nat.mod_add_div c d
    have rem := Nat.mod_lt c hd
    have inc : t * d ≤ t * 94 := Nat.mul_le_mul_left t hu
    have rad : t * 94 + 1 ≤ c / 100 := by omega
    have mul : d * (c / d) = c / d * d := Nat.mul_comm _ _
    have e : f t = c / d * d + t * d + 1 := by simp [f, Nat.add_mul]
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · exact (Nat.coprime_mul_right_add_left 1 d (c / d + t)).mpr (Nat.coprime_one_left _)
  simpa [card_image_of_injective _ inj] using card_le_card sub

theorem gap_pos (j : ℕ) : 0 < gap j := by
  cases j with
  | zero => decide
  | succ k => change 0 < nextGap (gap k); unfold nextGap; omega

/-- j indexes the unperturbed center; j+1 and j+2 are the retained gaps. -/
theorem actual_window_card (j : ℕ) (hc : 9400 ≤ gap j) :
    gap j / 9400 ≤ (window (gap j) (Nat.gcd (gap (j + 2)) (gap (j + 1)))).card := by
  apply window_card _ _ (Nat.gcd_pos_of_pos_left _ (gap_pos _)) _ hc
  rw [Nat.gcd_comm]; exact adjacent_gap_gcd_le (j + 1)

/-- A perturbation centered at the middle gap stays strictly between its neighbors. -/
theorem actual_window_order {x h d : ℕ} (hh : h ∈ window (nextGap x) d) :
    x < h ∧ h < nextGap (nextGap x) := by
  obtain ⟨lo, hi⟩ := mem_Icc.mp (mem_filter.mp hh).1
  have a := scaled_next_bounds x
  have b := scaled_next_bounds (nextGap x)
  omega

/-- A uniform draw from the actual menu has atom mass O(1/center), with
explicit constant. The threshold below is independent of the total input size. -/
theorem actual_atom_le (j : ℕ) (hc : 9400 ≤ gap j) :
    (1 : ℝ) / (window (gap j) (Nat.gcd (gap (j + 2)) (gap (j + 1)))).card ≤
      18800 / (gap j : ℝ) := by
  let G := window (gap j) (Nat.gcd (gap (j + 2)) (gap (j + 1)))
  have b : gap j / 9400 ≤ G.card := actual_window_card j hc
  have k : gap j ≤ 18800 * G.card := by omega
  have p : (0 : ℝ) < G.card := by exact_mod_cast (show 0 < G.card by omega)
  have q : (0 : ℝ) < gap j := by exact_mod_cast gap_pos j
  change 1 / (G.card : ℝ) ≤ _
  apply (div_le_div_iff₀ p q).mpr
  simpa using (show (gap j : ℝ) ≤ 18800 * (G.card : ℝ) by exact_mod_cast k)

/-- A nontrivial denominator dividing a selected gap is broken by at least
one of the two retained passes. No restriction that the denominator be prime. -/
theorem retained_breaks_divisor {c g₁ g₂ h d : ℕ}
    (hh : h ∈ window c (Nat.gcd g₁ g₂)) (hdh : d ∣ h) (hd : 1 < d) :
    ¬ d ∣ g₁ ∨ ¬ d ∣ g₂ := by
  by_contra! hboth
  have gcdOne := (mem_filter.mp hh).2
  have div := Nat.dvd_gcd hdh (Nat.dvd_gcd hboth.1 hboth.2)
  rw [show Nat.gcd h (Nat.gcd g₁ g₂) = 1 from gcdOne] at div
  have := Nat.le_of_dvd (by decide : 0 < 1) div
  omega

end Shellsort.Actual214
