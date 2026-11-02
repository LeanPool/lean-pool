/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular

/-! # Reindexing logarithmic sums on squarefree integers

An integer with a selected prime divisor is equivalently a prime and a
positive cofactor. Nonnegativity and squarefree support justify the infinite
reindexing from a convergent logarithmically weighted series.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real

/-- The equivalence splitting an integer into its selected prime factor and cofactor. -/
def primeFactorCofactorEquiv :
    (Σ n : ℕ, {p : ℕ // p ∈ n.primeFactors}) ≃ Nat.Primes × ℕ+ where
  toFun x :=
    (⟨x.2.1, Nat.prime_of_mem_primeFactors x.2.2⟩,
      ⟨x.1 / x.2.1, Nat.div_pos (Nat.le_of_mem_primeFactors x.2.2)
        (Nat.pos_of_mem_primeFactors x.2.2)⟩)
  invFun x := ⟨x.1.1 * x.2.1, x.1.1, x.1.2.mem_primeFactors (dvd_mul_right _ _)
    (mul_ne_zero x.1.2.ne_zero x.2.ne_zero)⟩
  left_inv x := by
    have H := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors x.2.2)
    dsimp
    apply Sigma.ext H
    exact (Subtype.heq_iff_coe_eq (fun k => by
      change k ∈ (x.2.1 * (x.1 / x.2.1)).primeFactors ↔ k ∈ x.1.primeFactors
      rw [H])).mpr rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp
      exact Nat.mul_div_right _ x.1.2.pos

theorem log_eq_sum_primeFactors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log p := by
  calc
    _ = Real.log (∏ p ∈ n.primeFactors, (p : ℝ)) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
    _ = _ := Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)

theorem squarefree_log_sum_eq_primeFactors (f : ℕ → ℝ)
    (hf : ∀ n, ¬Squarefree n → f n = 0) (n : ℕ) :
    (∑ p ∈ n.primeFactors, f n * Real.log p) = f n * Real.log n := by
  by_cases hn : Squarefree n
  · rw [← mul_sum, ← log_eq_sum_primeFactors_of_squarefree hn]
  · simp [hf n hn]

theorem summable_squarefree_primeFactors (f : ℕ → ℝ)
    (hf₀ : ∀ n, 0 ≤ f n) (hf : ∀ n, ¬Squarefree n → f n = 0)
    (hs : Summable (fun n => f n * Real.log n)) :
    Summable (fun x : Σ n : ℕ, {p : ℕ // p ∈ n.primeFactors} => f x.1 * Real.log x.2.1) := by
  apply (summable_sigma_of_nonneg (fun x => mul_nonneg (hf₀ _) (Real.log_natCast_nonneg _))).mpr
  refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  convert hs using 1
  ext n
  simp only [tsum_fintype, Finset.univ_eq_attach]
  rw [n.primeFactors.sum_attach (fun p => f n * Real.log p)]
  exact squarefree_log_sum_eq_primeFactors f hf n

theorem summable_squarefree_prime_cofactors (f : ℕ → ℝ)
    (hf₀ : ∀ n, 0 ≤ f n) (hf : ∀ n, ¬Squarefree n → f n = 0)
    (hs : Summable (fun n => f n * Real.log n)) :
    Summable (fun x : Nat.Primes × ℕ+ => f (x.1.1 * x.2.1) * Real.log x.1.1) := by
  exact (primeFactorCofactorEquiv.symm.summable_iff
    (f := fun x : Σ n : ℕ, {p : ℕ // p ∈ n.primeFactors} =>
      f x.1 * Real.log x.2.1)).mpr (summable_squarefree_primeFactors f hf₀ hf hs)

theorem tsum_squarefree_log_eq_prime_cofactors (f : ℕ → ℝ)
    (hf₀ : ∀ n, 0 ≤ f n) (hf : ∀ n, ¬Squarefree n → f n = 0)
    (hs : Summable (fun n => f n * Real.log n)) :
    (∑' n : ℕ, f n * Real.log n) =
      ∑' p : Nat.Primes, ∑' m : ℕ+, f (p.1 * m.1) * Real.log p.1 := by
  have hsig := summable_squarefree_primeFactors f hf₀ hf hs
  have hprod := summable_squarefree_prime_cofactors f hf₀ hf hs
  calc
    _ = ∑' x : Σ n : ℕ, {p : ℕ // p ∈ n.primeFactors}, f x.1 * Real.log x.2.1 := by
      rw [hsig.tsum_sigma]
      apply tsum_congr
      intro n
      simp only [tsum_fintype, Finset.univ_eq_attach]
      rw [n.primeFactors.sum_attach (fun p => f n * Real.log p)]
      exact (squarefree_log_sum_eq_primeFactors f hf n).symm
    _ = ∑' x : Nat.Primes × ℕ+, f (x.1.1 * x.2.1) * Real.log x.1.1 :=
      (primeFactorCofactorEquiv.symm.tsum_eq _).symm
    _ = _ := hprod.tsum_prod

end NairTenenbaum
