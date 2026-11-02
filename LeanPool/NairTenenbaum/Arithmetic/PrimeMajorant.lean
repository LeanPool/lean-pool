/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.MinimalMajorant
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity

/-! # The prime-by-prime bound, equation (14) -/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The tuple of `p`-parts of the coordinates; nonprimes give the unit tuple. -/
def primePart {k : ℕ} (n : Tuple k) (p : ℕ) : Tuple k :=
  fun j => if hp : p.Prime then (⟨p, hp.pos⟩ : ℕ+) ^ (n j : ℕ).factorization p else 1

theorem primePart_coe {k : ℕ} (n : Tuple k) {p : ℕ} (hp : p.Prime) (j : Fin k) :
    (primePart n p j : ℕ) = p ^ (n j : ℕ).factorization p := by
  have hh : primePart n p j = (⟨p, hp.pos⟩ : ℕ+) ^ (n j : ℕ).factorization p := by
    simp [primePart, hp]
    rfl
  rw [hh]
  exact PNat.pow_coe _ _

theorem coordinate_dvd_mass {k : ℕ} (n : Tuple k) (j : Fin k) : (n j : ℕ) ∣ mass n :=
  Finset.dvd_prod_of_mem _ (mem_univ j)

theorem prod_primePart {k : ℕ} (n : Tuple k) :
    ∏ p ∈ (mass n).primeFactors, primePart n p = n := by
  funext j
  apply PNat.coe_injective
  simp only [Finset.prod_apply, PNat.coe_prod]
  calc
    ∏ p ∈ (mass n).primeFactors, (primePart n p j : ℕ) =
        ∏ p ∈ (mass n).primeFactors, p ^ (n j : ℕ).factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact primePart_coe n (Nat.prime_of_mem_primeFactors hp) j
    _ = ∏ p ∈ (n j : ℕ).primeFactors, p ^ (n j : ℕ).factorization p := by
      symm
      apply Finset.prod_subset
      · intro p hp
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans (coordinate_dvd_mass n j), (mass_pos n).ne'⟩
      · intro p _ hp
        have hz : (n j : ℕ).factorization p = 0 := by
          apply Finsupp.notMem_support_iff.mp
          simpa only [Nat.support_factorization] using hp
        simp [hz]
    _ = (n j : ℕ) := (Nat.prod_primeFactors_pow_factorization (n j).ne_zero).symm

theorem primePart_coprime {k : ℕ} (n : Tuple k) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : Coprime (primePart n p) (primePart n q) := by
  intro j
  rw [primePart_coe n hp j, primePart_coe n hq j]
  exact Nat.coprime_pow_primes _ _ hp hq hpq

theorem mass_primePart {k : ℕ} (n : Tuple k) {p : ℕ} (hp : p.Prime) :
    mass (primePart n p) = p ^ (mass n).factorization p := by
  simp only [mass, primePart_coe n hp]
  rw [Finset.prod_pow_eq_pow_sum, Nat.factorization_prod (fun j _ => (n j).ne_zero)]
  simp

theorem Admissible.minimalMajorant_prod_le {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {ι : Type*} (s : Finset ι) (a : ι → Tuple k)
    (ha : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Coprime (a i) (a j)) :
    minimalMajorant F (∏ i ∈ s, a i) ≤ ∏ i ∈ s, minimalMajorant F (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact minimalMajorant_le_of_bound hF.nonneg 1 zero_le_one (by intros; simp)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hc : Coprime (a i) (∏ j ∈ s, a j) := by
      intro l
      simp only [Finset.prod_apply, PNat.coe_prod, Nat.coprime_prod_right_iff]
      intro j hj
      exact ha i (mem_insert_self _ _) j (mem_insert_of_mem hj) (by aesop) l
    exact (hF.minimalMajorant_submultiplicative hA hB _ _ hc).trans
      (mul_le_mul_of_nonneg_left
        (ih (fun i hi j hj hij => ha i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij))
        (hF.minimalMajorant_nonneg hA hB _))

/-- The right hand side of equation (14). -/
noncomputable def primeMajorant (A B ε : ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors, min (A ^ N.factorization p) (B * (p : ℝ) ^ ((N.factorization p : ℝ) * ε))

/-- Equation (14), with the full multivariable majorant. -/
theorem Admissible.minimalMajorant_le_primeMajorant {k : ℕ} {A B ε : ℝ}
    {F : ArithmeticMap k} (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (n : Tuple k) : minimalMajorant F n ≤ primeMajorant A B ε (mass n) := by
  calc
    minimalMajorant F n = minimalMajorant F (∏ p ∈ (mass n).primeFactors, primePart n p) :=
      congrArg _ (prod_primePart n).symm
    _ ≤ ∏ p ∈ (mass n).primeFactors, minimalMajorant F (primePart n p) :=
      hF.minimalMajorant_prod_le hA hB _ _ (fun p hp q hq hpq =>
        primePart_coprime n (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)
            hpq)
    _ ≤ primeMajorant A B ε (mass n) := by
      apply Finset.prod_le_prod₀ (fun p _ => hF.minimalMajorant_nonneg hA hB _)
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have heq : growthBound A B ε (primePart n p) =
          min (A ^ (mass n).factorization p)
            (B * (p : ℝ) ^ (((mass n).factorization p : ℝ) * ε)) := by
        rw [growthBound, mass_primePart n hp']
        have hΩ : bigOmega (p ^ (mass n).factorization p) = (mass n).factorization p :=
          ArithmeticFunction.cardFactors_apply_prime_pow hp'
        rw [hΩ, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
      exact heq ▸ hF.minimalMajorant_le hA hB _

end NairTenenbaum
