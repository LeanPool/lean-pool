/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Data.Nat.Squarefree

/-! # An exponential Euler bound for squarefree prime products

The finite bound uses the injection from squarefree integers to their prime
factor sets. Passing to all integers proves convergence as well as the bound.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem prime_finset_sum_le_tsum (a : ℕ → ℝ) (ha : ∀ p, p.Prime → 0 ≤ a p)
    (hs : Summable (fun p : Nat.Primes => a p.1)) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) : (∑ p ∈ S, a p) ≤ ∑' p : Nat.Primes, a p.1 := by
  classical
  let e : S → Nat.Primes := fun p => ⟨p.1, hS p.1 p.2⟩
  let P : Finset Nat.Primes := S.attach.image e
  have H := hs.sum_le_tsum P (fun p _ => ha p.1 p.2)
  have hsum : (∑ p ∈ P, a p.1) = ∑ p ∈ S, a p := by
    change (∑ p ∈ S.attach.image e, a p.1) = _
    rw [sum_image]
    · exact S.sum_attach a
    · intro p _ r _ h
      exact Subtype.ext (show (p : ℕ) = (r : ℕ) from congrArg (fun x : Nat.Primes => x.1) h)
  rwa [hsum] at H

/-- The product of the primes in a finite support. -/
noncomputable def squarefreePrimeProduct (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0

theorem squarefreePrimeProduct_nonneg {a : ℕ → ℝ} (ha : ∀ p, p.Prime → 0 ≤ a p) (n : ℕ) :
    0 ≤ squarefreePrimeProduct a n := by
  unfold squarefreePrimeProduct
  split_ifs
  · exact prod_nonneg fun p hp => ha p (Nat.prime_of_mem_primeFactors hp)
  · rfl

theorem squarefreePrimeProduct_sum_le_prod {a : ℕ → ℝ} (ha : ∀ p, p.Prime → 0 ≤ a p)
    (T S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hTS : ∀ n ∈ T, Squarefree n → n.primeFactors ⊆ S) :
    (∑ n ∈ T, squarefreePrimeProduct a n) ≤ ∏ p ∈ S, (1 + a p) := by
  classical
  rw [prod_one_add]
  simp only [squarefreePrimeProduct, ← sum_filter]
  apply sum_le_sum_of_injOn (fun n : ℕ => n.primeFactors)
  · intro n hn m hm heq
    change n.primeFactors = m.primeFactors at heq
    rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hn).2,
      ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hm).2, heq]
  · intro U hU
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hU
    exact mem_powerset.mpr (hTS n (mem_filter.mp hn).1 (mem_filter.mp hn).2)
  · intro n hn
    rfl
  · intro U hU _
    exact prod_nonneg fun p hp => ha p (hS p (mem_powerset.mp hU hp))

theorem summable_and_tsum_squarefreePrimeProduct_le_exp {a : ℕ → ℝ}
    (ha : ∀ p, p.Prime → 0 ≤ a p) (hs : Summable (fun p : Nat.Primes => a p.1)) :
    Summable (squarefreePrimeProduct a) ∧
      (∑' n, squarefreePrimeProduct a n) ≤ Real.exp (∑' p : Nat.Primes, a p.1) := by
  classical
  have hbound (T : Finset ℕ) :
      (∑ n ∈ T, squarefreePrimeProduct a n) ≤ Real.exp (∑' p : Nat.Primes, a p.1) := by
    let S := T.biUnion Nat.primeFactors
    have hS : ∀ p ∈ S, p.Prime := by
      intro p hp
      obtain ⟨n, _, hn⟩ := mem_biUnion.mp hp
      exact Nat.prime_of_mem_primeFactors hn
    calc
      _ ≤ ∏ p ∈ S, (1 + a p) := squarefreePrimeProduct_sum_le_prod ha T S hS
        (fun n hn _ p hp => mem_biUnion.mpr ⟨n, hn, hp⟩)
      _ ≤ ∏ p ∈ S, Real.exp (a p) := prod_le_prod₀
        (fun p hp => by linarith [ha p (hS p hp)])
        (fun p _ => by simpa only [add_comm] using Real.add_one_le_exp (a p))
      _ = Real.exp (∑ p ∈ S, a p) := (Real.exp_sum S a).symm
      _ ≤ _ := Real.exp_le_exp.mpr (prime_finset_sum_le_tsum a ha hs S hS)
  exact ⟨summable_of_sum_le (squarefreePrimeProduct_nonneg ha) hbound,
    Real.tsum_le_of_sum_le (squarefreePrimeProduct_nonneg ha) hbound⟩

end NairTenenbaum
