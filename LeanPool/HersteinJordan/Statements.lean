/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module

/-
Adapted from https://github.com/stalex444/herstein-jordan-homomorphisms at
34dffa8aace3a1b565b11cbb561db3a58fa203da. The original MIT notice follows.

MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
public import LeanPool.HersteinJordan.Basic
public import LeanPool.HersteinJordan.Examples

/-!
# Herstein's theorem: proofs of the compared statements

Each of the six statements of the upstream `Challenge.lean` is proved here, with the identical
statement, by transfer from `LeanPool/HersteinJordan/Basic.lean` and
`LeanPool/HersteinJordan/Examples.lean`, in namespace `HersteinJordan`. No definition is added.

* Statement 1: `HersteinJordan.mul_or_antimul_of_prime`. A Jordan homomorphism into a ring
  without 2-torsion preserves squares and `a * b * a` (`map_sq_of_jordan`,
  `map_triple_of_jordan`). With `τ = φ (a * b) - φ a * φ b` and `ω = φ (a * b) - φ b * φ a`,
  evaluating `φ (a b r b a + b a r a b)` in two ways gives `τ * φ r * ω + ω * φ r * τ = 0`
  (`defect_sandwich`); surjectivity turns `φ r` into an arbitrary element, three uses of that
  relation give `τ x ω y τ + τ x ω y τ = 0`, the hypothesis on 2 and primeness (twice) give
  `τ = 0` or `ω = 0` for each pair, and the covering argument (`biadditive_cover`) makes the
  alternative uniform.
* Statement 2: `HersteinJordan.mul_or_antimul_of_noZeroDivisors`, from `τ * ω = 0`
  (`defect_mul_defect`), the absence of zero divisors, and the covering argument.
* Statement 3: witness `HersteinJordan.blockTranspose`; the target is prime by
  `HersteinJordan.matrix_prime` over the integers; the map is not onto by statement 1.
* Statement 4: witness `HersteinJordan.sndTranspose`; the target is not prime by statement 1.
* Statement 5: witness `HersteinJordan.sumMod2`; every clause is decided by `decide` on the
  finite rings `𝔽₂ × 𝔽₂` and `𝔽₂`.
* Statement 6: `HersteinJordan.mul_or_antimul_of_prime_of_twoIdentity_anyChar` (Smiley's
  argument). For every pair, `τ * ω = 0`, `ω * τ = 0` and `τ * x * ω + ω * x * τ = 0` for every
  `x` in the target (`defect_mul_defect`, `defect_mul_defect_mirror`, `defect_sandwich` and
  surjectivity); none of these uses a hypothesis on 2. If some `τ` has a nonzero square, these
  identities at sums of pairs and primeness make every `ω` vanish
  (`defect_eq_zero_of_sq_ne_zero`), so `φ` is anti-multiplicative; with the roles exchanged, `φ`
  is multiplicative. Otherwise every commutator of the target squares to zero, the target is
  commutative (`commutative_of_commutator_sq_zero`), hence has no zero divisors, and
  `mul_or_antimul_of_noZeroDivisors` (the theorem behind statement 2) finishes.
-/

@[expose] public section

namespace JordanPrime

open Matrix

/-- **1. Herstein's theorem, characteristic different from 2 (Smiley's form).** A Jordan
homomorphism onto a prime ring without 2-torsion is a homomorphism or an anti-homomorphism. -/
theorem jordan_onto_prime {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)
    (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hprime : ∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) :=
  HersteinJordan.mul_or_antimul_of_prime φ hJ hsurj hprime h2

/-- **2. The domain form (Jacobson–Rickart, Theorem 2), in every characteristic.** An additive
map preserving squares and `a * b * a`, into a ring without zero divisors, is multiplicative or
anti-multiplicative. -/
theorem twoIdentity_into_domain {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)
    (hsq : ∀ a, φ (a * a) = φ a * φ a) (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a)
    (hS : ∀ x y : S, x * y = 0 → x = 0 ∨ y = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) :=
  HersteinJordan.mul_or_antimul_of_noZeroDivisors φ hsq htri hS

/-- **3. Surjectivity is needed.** A Jordan homomorphism that is not onto, into a prime ring
without 2-torsion, and is neither multiplicative nor anti-multiplicative. -/
theorem onto_needed :
    ∃ φ : Matrix (Fin 2) (Fin 2) ℤ →+ Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ,
      (∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a) ∧
      ¬ Function.Surjective φ ∧
      (∀ x y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ,
        (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) ∧
      (∀ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ, x + x = 0 → x = 0) ∧
      (¬ ∀ a b, φ (a * b) = φ a * φ b) ∧ (¬ ∀ a b, φ (a * b) = φ b * φ a) :=
  ⟨HersteinJordan.blockTranspose, HersteinJordan.blockTranspose_jordan,
    fun hs => (HersteinJordan.mul_or_antimul_of_prime _ HersteinJordan.blockTranspose_jordan hs
      (HersteinJordan.matrix_prime HersteinJordan.int_prime)
      HersteinJordan.int_matrix_no_two_torsion).elim
      HersteinJordan.blockTranspose_not_mul HersteinJordan.blockTranspose_not_antimul,
    HersteinJordan.matrix_prime HersteinJordan.int_prime,
    HersteinJordan.int_matrix_no_two_torsion,
    HersteinJordan.blockTranspose_not_mul, HersteinJordan.blockTranspose_not_antimul⟩

/-- **4. Primeness is needed.** A Jordan homomorphism onto a ring that is not prime and has no
2-torsion; the map is neither multiplicative nor anti-multiplicative. -/
theorem prime_needed :
    ∃ φ : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ →+
        Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ,
      (∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a) ∧
      Function.Surjective φ ∧
      (¬ ∀ x y : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ,
        (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) ∧
      (∀ x : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ, x + x = 0 → x = 0) ∧
      (¬ ∀ a b, φ (a * b) = φ a * φ b) ∧ (¬ ∀ a b, φ (a * b) = φ b * φ a) := by
  have h2 : ∀ x : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ, x + x = 0 → x = 0 :=
    fun x hx => Prod.ext
      (HersteinJordan.int_matrix_no_two_torsion x.1 (congrArg Prod.fst hx))
      (HersteinJordan.int_matrix_no_two_torsion x.2 (congrArg Prod.snd hx))
  exact ⟨HersteinJordan.sndTranspose, HersteinJordan.sndTranspose_jordan,
    HersteinJordan.sndTranspose_surjective,
    fun hp => (HersteinJordan.mul_or_antimul_of_prime _ HersteinJordan.sndTranspose_jordan
      HersteinJordan.sndTranspose_surjective hp h2).elim
      HersteinJordan.sndTranspose_not_mul HersteinJordan.sndTranspose_not_antimul,
    h2, HersteinJordan.sndTranspose_not_mul, HersteinJordan.sndTranspose_not_antimul⟩

/-- **5. The hypothesis on 2 is needed.** A Jordan homomorphism onto a prime ring with
2-torsion that is neither multiplicative nor anti-multiplicative. -/
theorem two_needed :
    ∃ φ : ZMod 2 × ZMod 2 →+ ZMod 2,
      (∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a) ∧
      Function.Surjective φ ∧
      (∀ x y : ZMod 2, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) ∧
      (¬ ∀ x : ZMod 2, x + x = 0 → x = 0) ∧
      (¬ ∀ a b, φ (a * b) = φ a * φ b) ∧ (¬ ∀ a b, φ (a * b) = φ b * φ a) :=
  ⟨HersteinJordan.sumMod2, HersteinJordan.sumMod2_jordan, HersteinJordan.sumMod2_surjective,
    HersteinJordan.zmod2_prime, by decide, HersteinJordan.sumMod2_not_mul,
    HersteinJordan.sumMod2_not_antimul⟩

/-- **6. The theorem in every characteristic (Smiley, Added in proof).** An additive map
preserving squares and `a * b * a`, onto a prime ring, is a homomorphism or an
anti-homomorphism. No hypothesis on 2. -/
theorem twoIdentity_onto_prime {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)
    (hsq : ∀ a, φ (a * a) = φ a * φ a) (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hprime : ∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) :=
  HersteinJordan.mul_or_antimul_of_prime_of_twoIdentity_anyChar φ hsq htri hsurj hprime

end JordanPrime
