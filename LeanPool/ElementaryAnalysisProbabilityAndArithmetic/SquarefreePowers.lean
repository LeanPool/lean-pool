/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.NumberTheory.CarmichaelNumber

/-!
# Powers modulo a squarefree number

Writing `λ` for the Carmichael function, a positive integer `n` is squarefree if and only if
`a ^ (λ n + 1) = a` for every `a : ZMod n`. For squarefree `n` this holds for all residues, not
only units, and with any multiple `k * λ n` in place of `λ n`: it is the identity behind the
correctness of RSA. As a consequence, a Carmichael number `n` satisfies `a ^ n = a` for every
`a : ZMod n`.

## Main statements

* `Squarefree.zmod_pow_mul_carmichael_add_one`: if `n` is squarefree, then
  `a ^ (k * λ n + 1) = a` for every `a : ZMod n`.
* `Nat.squarefree_iff_forall_zmod_pow_carmichael_add_one`: the converse, as an equivalence.
* `Nat.IsCarmichael.zmod_pow_eq_self`: a Carmichael number `n` satisfies `a ^ n = a` for every
  `a : ZMod n`.
-/

public section

namespace Nat

open ArithmeticFunction

variable {n : ℕ}

/-- If `n` is squarefree, then `a ^ (k * λ n + 1) = a` for every `a : ZMod n`, where `λ` is the
Carmichael function. This holds for all residues, not only units: it is the identity behind the
correctness of RSA. -/
theorem _root_.Squarefree.zmod_pow_mul_carmichael_add_one (hn : Squarefree n) (k : ℕ)
    (a : ZMod n) : a ^ (k * carmichael n + 1) = a := by
  have : NeZero n := ⟨hn.ne_zero⟩
  have hle (b : ℕ) : b ≤ b ^ (k * carmichael n + 1) := Nat.le_self_pow (by lia) b
  rw [← ZMod.natCast_zmod_val a, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
  refine ((Nat.modEq_iff_dvd' (hle _)).2 ?_).symm
  have key : ∏ p ∈ n.primeFactors, p ∣ a.val ^ (k * carmichael n + 1) - a.val := by
    refine Finset.prod_primes_dvd _ (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).prime)
      fun p hp ↦ ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hp'⟩
    rw [← Nat.modEq_iff_dvd' (hle _), ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow]
    obtain ⟨j, hj⟩ : p - 1 ∣ carmichael n :=
      carmichael_of_prime hp' ▸ carmichael_dvd (Nat.dvd_of_mem_primeFactors hp)
    by_cases hb : (a.val : ZMod p) = 0
    · simp [hb]
    · rw [pow_succ, hj, mul_comm k, mul_assoc, pow_mul, ZMod.pow_card_sub_one_eq_one hb, one_pow,
        one_mul]
  rwa [Nat.prod_primeFactors_of_squarefree hn] at key

/-- If `a ^ (m + 1) = a` for every `a : ZMod n`, with `m ≠ 0`, then `n` is squarefree. -/
theorem squarefree_of_forall_zmod_pow_add_one_eq {m : ℕ} (hm : m ≠ 0)
    (h : ∀ a : ZMod n, a ^ (m + 1) = a) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have h1 : p ^ (m + 1) ≡ p [MOD p * p] :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).1 (by exact_mod_cast h p)).of_dvd hpp
  have h2 : p ^ (m + 1) ≡ 0 [MOD p * p] :=
    Nat.modEq_zero_iff_dvd.2 (by rw [← sq]; exact pow_dvd_pow p (by lia))
  have h3 : p * p ≤ p := Nat.le_of_dvd hp.pos (Nat.modEq_zero_iff_dvd.1 (h1.symm.trans h2))
  nlinarith [hp.two_le]

/-- A positive integer `n` is squarefree if and only if `a ^ (λ n + 1) = a` for every
`a : ZMod n`, where `λ` is the Carmichael function. -/
theorem squarefree_iff_forall_zmod_pow_carmichael_add_one (hn : n ≠ 0) :
    Squarefree n ↔ ∀ a : ZMod n, a ^ (carmichael n + 1) = a := by
  have : NeZero n := ⟨hn⟩
  refine ⟨fun h a ↦ by simpa using h.zmod_pow_mul_carmichael_add_one 1 a,
    squarefree_of_forall_zmod_pow_add_one_eq
      (carmichael_eq_exponent hn ▸ Monoid.exponent_ne_zero_of_finite)⟩

/-- A Carmichael number `n` satisfies `a ^ n = a` for every `a : ZMod n`, including the residues
that are not coprime to `n`. -/
theorem IsCarmichael.zmod_pow_eq_self (h : n.IsCarmichael) (a : ZMod n) : a ^ n = a := by
  obtain ⟨d, hd⟩ := h.carmichael_dvd_sub_one
  have hn : n = d * carmichael n + 1 := by
    have := h.two_lt
    lia
  have e := h.squarefree.zmod_pow_mul_carmichael_add_one d a
  rwa [← hn] at e

end Nat
