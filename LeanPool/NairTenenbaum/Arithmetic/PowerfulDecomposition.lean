/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeSplitting

/-! # Separating squarefree and repeated prime factors

A powerful integer has no prime occurring to exponent one. Every positive
integer splits into coprime squarefree and powerful factors. Every powerful
integer has a canonical representation `a²b³`, useful for summability.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- An integer is powerful when every prime divisor occurs with exponent at least two. -/
def Powerful (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p : ℕ, n.factorization p ≠ 1

/-- The part formed by primes occurring to the first power. -/
noncomputable def singlePrimePart (n : ℕ+) : ℕ+ :=
  primeSelect (fun _ : Fin 1 => n) ((n : ℕ).primeFactors.filter (fun p => (n : ℕ).factorization p
      = 1)) 0

/-- The part formed by primes occurring with multiplicity at least two. -/
noncomputable def repeatedPrimePart (n : ℕ+) : ℕ+ :=
  primeReject (fun _ : Fin 1 => n) ((n : ℕ).primeFactors.filter (fun p => (n : ℕ).factorization p
      = 1)) 0

theorem singlePrimePart_mul_repeatedPrimePart (n : ℕ+) :
    singlePrimePart n * repeatedPrimePart n = n :=
  congrFun (primeSelect_mul_primeReject (fun _ : Fin 1 => n) _) 0

theorem singlePrimePart_coprime_repeatedPrimePart (n : ℕ+) :
    Nat.Coprime (singlePrimePart n) (repeatedPrimePart n) :=
  primeSelect_primeReject_coprime (fun _ : Fin 1 => n) _ 0 0

theorem squarefree_singlePrimePart (n : ℕ+) : Squarefree (singlePrimePart n : ℕ) := by
  rw [Nat.squarefree_iff_factorization_le_one (singlePrimePart n).ne_zero]
  intro p
  rw [singlePrimePart, factorization_primeSelect]
  split_ifs with h
  · exact le_of_eq (mem_filter.mp h).2
  · exact Nat.zero_le _

theorem powerful_repeatedPrimePart (n : ℕ+) : Powerful (repeatedPrimePart n : ℕ) := by
  refine ⟨(repeatedPrimePart n).ne_zero, fun p => ?_⟩
  rw [repeatedPrimePart, factorization_primeReject]
  split_ifs with h
  · decide
  · intro hp
    apply h
    exact mem_filter.mpr ⟨by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff, hp]
      decide, hp⟩

/-- The square base in the square-times-cube decomposition of a powerful integer. -/
noncomputable def powerfulSquareBase (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2 - n.factorization p % 2)

/-- The cube base in the square-times-cube decomposition of a powerful integer. -/
noncomputable def powerfulCubeBase (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)

theorem powerful_eq_square_mul_cube {n : ℕ} (hn : Powerful n) :
    powerfulSquareBase n ^ 2 * powerfulCubeBase n ^ 3 = n := by
  unfold powerfulSquareBase powerfulCubeBase
  rw [← prod_pow, ← prod_pow, ← prod_mul_distrib]
  calc
    _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      apply prod_congr rfl
      intro p _
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      have H := hn.2 p
      omega
    _ = n := (Nat.prod_primeFactors_pow_factorization hn.1).symm

theorem powerful_bases_injective : Function.Injective
    (fun n : {n : ℕ // Powerful n} => (powerfulSquareBase n.1, powerfulCubeBase n.1)) := by
  intro n m h
  apply Subtype.ext
  have h₁ : powerfulSquareBase n.1 = powerfulSquareBase m.1 := congrArg Prod.fst h
  have h₂ : powerfulCubeBase n.1 = powerfulCubeBase m.1 := congrArg Prod.snd h
  rw [← powerful_eq_square_mul_cube n.2, ← powerful_eq_square_mul_cube m.2, h₁, h₂]

end NairTenenbaum
