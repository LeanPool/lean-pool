/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.IdealVonMangoldtBounds
public import LeanPool.NairTenenbaum.NumberFields.IrreduciblePrimeIdealMatch
public import LeanPool.NairTenenbaum.Smooth.SmoothLogHigherPowers

/-! # Comparison of the weighted prime-root sum with ideal von Mangoldt sums

Eventual agreement of prime counts leaves a fixed finite exceptional-prime
contribution. Nonnegativity then permits enlarging the ideal-prime sum to all
positive integers.
-/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Polynomial

variable (K : Type*) [Field K] [NumberField K]

/-- The reciprocal sum weighted by the ideal von Mangoldt function. -/
noncomputable def idealMangoldtReciprocalSum (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, idealVonMangoldt K n / n

theorem primeRootLogSum_le_idealMangoldt_add {Q : ℤ[X]} (N : ℕ)
    (hmatch : ∀ p : ℕ, p.Prime → N < p → rootCount Q p = idealNormCount K p)
    (x : ℝ) :
    primeRootLogSum Q x ≤ idealMangoldtReciprocalSum K x + primeRootLogSum Q N := by
  classical
  let S := (range (⌊x⌋₊ + 1)).filter Nat.Prime
  let f := fun p : ℕ => (rootCount Q p : ℝ) / p * Real.log p
  have hf (p : ℕ) (hp : p.Prime) : 0 ≤ f p :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.log_nonneg (by exact_mod_cast hp.one_le))
  have hsmall : (∑ p ∈ S.filter (fun p => p ≤ N), f p) ≤ primeRootLogSum Q N := by
    unfold primeRootLogSum
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpS, hpN⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨by simpa using hpN, (mem_filter.mp hpS).2⟩
    · intro p hp _
      exact hf p (mem_filter.mp hp).2
  have hlarge : (∑ p ∈ S.filter (fun p => ¬p ≤ N), f p) ≤ idealMangoldtReciprocalSum K x := by
    calc
      _ = ∑ p ∈ S.filter (fun p => ¬p ≤ N), idealVonMangoldt K p / p := by
        apply sum_congr rfl
        intro p hp
        obtain ⟨hpS, hpN⟩ := mem_filter.mp hp
        have hpp := (mem_filter.mp hpS).2
        rw [idealVonMangoldt_prime K hpp, ← hmatch p hpp (by omega)]
        dsimp [f]
        ring
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hpS := (mem_filter.mp hp).1
          obtain ⟨hpmax, hpp⟩ := mem_filter.mp hpS
          exact mem_Icc.mpr ⟨hpp.one_le, by simpa only [mem_range, Nat.lt_succ_iff] using hpmax⟩
        · intro p _ _
          exact div_nonneg (idealVonMangoldt_nonneg K p) (Nat.cast_nonneg _)
  have H := sum_filter_add_sum_filter_not S (fun p => p ≤ N) f
  change (∑ p ∈ S, f p) ≤ _
  linarith

theorem exists_primeRootLogSum_idealMangoldt_bound {Q : ℤ[X]} (N : ℕ)
    (hmatch : ∀ p : ℕ, p.Prime → N < p → rootCount Q p = idealNormCount K p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      primeRootLogSum Q x ≤ idealMangoldtReciprocalSum K x + C := by
  refine ⟨primeRootLogSum Q N, ?_, primeRootLogSum_le_idealMangoldt_add K N hmatch⟩
  apply sum_nonneg
  intro p hp
  have hpp := (mem_filter.mp hp).2
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Real.log_nonneg (by exact_mod_cast hpp.one_le))

end NairTenenbaum
