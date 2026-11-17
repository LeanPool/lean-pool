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
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Push

/-!
# Herstein's theorem: the proof library

An additive map `φ : R → S` between associative rings is a *Jordan homomorphism* when
`φ (a * b + b * a) = φ a * φ b + φ b * φ a`. This file proves Herstein's theorem in its
characteristic-not-two form: a Jordan homomorphism onto a prime ring without 2-torsion is
multiplicative or anti-multiplicative. It also proves the form in every characteristic: an
additive map that preserves squares and `a * b * a`, onto a prime ring, is multiplicative or
anti-multiplicative. Rings are not assumed to have an identity
(`NonUnitalRing`), and every hypothesis on the target is a plain `∀`-statement, so no new
typeclass is introduced.

The characteristic-not-two form is Smiley's theorem (Trans. Amer. Math. Soc. 84 (1957), p. 428).
Its proof follows the argument given in full by Beidar, Brešar and Chebotar (*Jordan
superhomomorphisms*, Comm. Algebra 31 (2003), Proposition 3.1, after Brešar 1989), there for
algebras over a ring containing `1/2`, with the remark that it also works in rings of
characteristic not 2; that ring-level argument is written out here. The domain form is Theorem 2
of Jacobson and Rickart (Trans. Amer. Math. Soc. 69 (1950), p. 482), proved as they prove it,
from their identity (7) and their Lemma 1; that lemma is proved here by the covering argument
(`biadditive_cover`).

The form in every characteristic is Smiley's remark (Added in proof, p. 429) that the two
identities may replace the hypothesis on 2 in his theorem. Its proof here is Smiley's argument:
his identity (7), his three alternatives, and the lemma of his section 3. Where he linearizes
(7) and `τ * ω = 0`, the identities are applied here to sums of pairs and subtracted.

The upstream formalization records consultation of the complex-linear, unital-algebra
case in `openai/math`, `lean/OAI/Analysis/KadisonKastler/Jordan.lean`, theorem
`OAI.KadisonKastler.PreservesJordan.multiplicative_or_antimultiplicative`.
It reports no copied code; see the source repository's README for the exact contact history.
The present statements allow additive maps on nonunital rings, and the two-identity
version allows every characteristic.

Layout.

* The two-identity form of the definition, `φ (a * a) = φ a * φ a` and
  `φ (a * b * a) = φ a * φ b * φ a` (no hypothesis on 2). From it: the Jordan identity
  (`map_jordan_of_sq`), the linearized triple identity (`map_triple_lin`), `τ * ω = 0`
  (`defect_mul_defect`; Jacobson and Rickart's identity (7)), and
  `τ * φ r * ω + ω * φ r * τ = 0` (`defect_sandwich`; Smiley's identity (7)), where
  `τ = φ (a * b) - φ a * φ b` and `ω = φ (a * b) - φ b * φ a`.
* `map_sq_of_jordan`, `map_triple_of_jordan`: a Jordan homomorphism into a ring without
  2-torsion satisfies the two identities.
* `biadditive_cover`: two biadditive maps whose zero sets cover every pair; one of them vanishes.
  `mul_or_antimul_of_pairwise` applies it to the two defects.
* `mul_or_antimul_of_noZeroDivisors`: the two-identity form into a ring without zero divisors,
  in every characteristic and with no surjectivity.
* `mul_or_antimul_of_prime_of_twoIdentity`, `mul_or_antimul_of_prime`: the theorem, in the
  two-identity form (still assuming no 2-torsion) and for Jordan homomorphisms.
* Every characteristic. `commutative_of_commutator_sq_zero`: a prime ring in which every
  commutator squares to zero is commutative (Smiley's lemma; `ringComm` is the commutator).
  `eq_zero_of_sq_ne_zero_of_sandwich`, `defect_row_eq_zero`, `defect_eq_zero_of_sq_ne_zero`: if
  some `τ` has a nonzero square, every `ω` vanishes. `defect_mul_defect_mirror` (`ω * τ = 0`),
  `defect_swap`, `antidefect_swap`. `mul_or_antimul_of_prime_of_twoIdentity_anyChar`: the
  two-identity form onto a prime ring, with no hypothesis on 2.

Primeness of matrix rings (`matrix_prime`) and the three examples are in
`LeanPool/HersteinJordan/Examples.lean`.
-/

@[expose] public section

namespace HersteinJordan


section Core

variable {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)

/-- The multiplicative defect is additive in the first argument. -/
theorem defect_add_left (a a' b : R) :
    φ ((a + a') * b) - φ (a + a') * φ b =
      φ (a * b) - φ a * φ b + (φ (a' * b) - φ a' * φ b) := by
  simp only [add_mul, map_add]
  abel

/-- The multiplicative defect is additive in the second argument. -/
theorem defect_add_right (a b b' : R) :
    φ (a * (b + b')) - φ a * φ (b + b') =
      φ (a * b) - φ a * φ b + (φ (a * b') - φ a * φ b') := by
  simp only [mul_add, map_add]
  abel

/-- The anti-multiplicative defect is additive in the first argument. -/
theorem antidefect_add_left (a a' b : R) :
    φ ((a + a') * b) - φ b * φ (a + a') =
      φ (a * b) - φ b * φ a + (φ (a' * b) - φ b * φ a') := by
  simp only [add_mul, mul_add, map_add]
  abel

/-- The anti-multiplicative defect is additive in the second argument. -/
theorem antidefect_add_right (a b b' : R) :
    φ (a * (b + b')) - φ (b + b') * φ a =
      φ (a * b) - φ b * φ a + (φ (a * b') - φ b' * φ a) := by
  simp only [add_mul, mul_add, map_add]
  abel

/-! ### The two-identity form -/

/-- The Jordan identity from the square identity (linearization; no division). -/
theorem map_jordan_of_sq (hsq : ∀ a, φ (a * a) = φ a * φ a) (a b : R) :
    φ (a * b + b * a) = φ a * φ b + φ b * φ a := by
  have h := hsq (a + b)
  have e : (a + b) * (a + b) = a * a + (a * b + b * a) + b * b := by
    simp only [mul_add, add_mul]; abel
  have e' : (φ a + φ b) * (φ a + φ b) = φ a * φ a + (φ a * φ b + φ b * φ a) + φ b * φ b := by
    simp only [mul_add, add_mul]; abel
  rw [e] at h
  simp only [map_add] at h
  rw [hsq a, hsq b, e'] at h
  rw [map_add]
  exact add_left_cancel (add_right_cancel h)

/-- The linearized triple identity. -/
theorem map_triple_lin (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a) (a b c : R) :
    φ (a * b * c + c * b * a) = φ a * φ b * φ c + φ c * φ b * φ a := by
  have h := htri (a + c) b
  have e : (a + c) * b * (a + c) = a * b * a + (a * b * c + c * b * a) + c * b * c := by
    simp only [mul_add, add_mul]; abel
  have e' : (φ a + φ c) * φ b * (φ a + φ c) =
      φ a * φ b * φ a + (φ a * φ b * φ c + φ c * φ b * φ a) + φ c * φ b * φ c := by
    simp only [mul_add, add_mul]; abel
  rw [e] at h
  simp only [map_add] at h
  rw [htri a b, htri c b, e'] at h
  rw [map_add]
  exact add_left_cancel (add_right_cancel h)

/-- `τ * ω = 0`: the two defects of multiplicativity annihilate each other. -/
theorem defect_mul_defect (hsq : ∀ a, φ (a * a) = φ a * φ a)
    (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a) (a b : R) :
    (φ (a * b) - φ a * φ b) * (φ (a * b) - φ b * φ a) = 0 := by
  have h1 := hsq (a * b)
  have h2 := htri a (b * b)
  have h3 := hsq b
  have h4 := map_triple_lin φ htri (a * b) b a
  have e : a * b * b * a + a * b * (a * b) = a * b * (a * b) + a * (b * b) * a := by
    simp only [mul_assoc]; abel
  rw [e, map_add, h1, h2, h3] at h4
  have e' : (φ (a * b) - φ a * φ b) * (φ (a * b) - φ b * φ a) =
      (φ (a * b) * φ (a * b) + φ a * (φ b * φ b) * φ a) -
        (φ (a * b) * φ b * φ a + φ a * φ b * φ (a * b)) := by
    simp only [mul_sub, sub_mul, mul_assoc]; abel
  rw [e', h4, sub_self]

/-- The key identity (Smiley 1957, identity (7), p. 427):
`τ * φ r * ω + ω * φ r * τ = 0`. -/
theorem defect_sandwich (hsq : ∀ a, φ (a * a) = φ a * φ a)
    (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a) (a b r : R) :
    (φ (a * b) - φ a * φ b) * φ r * (φ (a * b) - φ b * φ a) +
      (φ (a * b) - φ b * φ a) * φ r * (φ (a * b) - φ a * φ b) = 0 := by
  have hJ := map_jordan_of_sq φ hsq a b
  rw [map_add] at hJ
  have hba : φ (b * a) = φ a * φ b + φ b * φ a - φ (a * b) := eq_sub_of_add_eq' hJ
  have hW1 : φ (a * (b * r * b) * a) = φ a * (φ b * φ r * φ b) * φ a := by rw [htri, htri]
  have hW2 : φ (b * (a * r * a) * b) = φ b * (φ a * φ r * φ a) * φ b := by rw [htri, htri]
  have hL := map_triple_lin φ htri (a * b) r (b * a)
  have e : a * b * r * (b * a) + b * a * r * (a * b) =
      a * (b * r * b) * a + b * (a * r * a) * b := by
    simp only [mul_assoc]
  rw [e, map_add, hW1, hW2, hba] at hL
  have e' : (φ (a * b) - φ a * φ b) * φ r * (φ (a * b) - φ b * φ a) +
      (φ (a * b) - φ b * φ a) * φ r * (φ (a * b) - φ a * φ b) =
      (φ a * (φ b * φ r * φ b) * φ a + φ b * (φ a * φ r * φ a) * φ b) -
        (φ (a * b) * φ r * (φ a * φ b + φ b * φ a - φ (a * b)) +
          (φ a * φ b + φ b * φ a - φ (a * b)) * φ r * φ (a * b)) := by
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc]; abel
  rw [e', hL, sub_self]

/-! ### From the Jordan identity to the two identities -/

/-- A Jordan homomorphism into a ring without 2-torsion preserves squares. -/
theorem map_sq_of_jordan (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (h2 : ∀ x : S, x + x = 0 → x = 0) (a : R) : φ (a * a) = φ a * φ a := by
  have h := hJ a a
  rw [map_add] at h
  refine sub_eq_zero.mp (h2 _ ?_)
  have : φ (a * a) - φ a * φ a + (φ (a * a) - φ a * φ a) =
      (φ (a * a) + φ (a * a)) - (φ a * φ a + φ a * φ a) := by abel
  rw [this, h, sub_self]

/-- A Jordan homomorphism into a ring without 2-torsion preserves `a * b * a`. -/
theorem map_triple_of_jordan (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (h2 : ∀ x : S, x + x = 0 → x = 0) (a b : R) : φ (a * b * a) = φ a * φ b * φ a := by
  have hsq := map_sq_of_jordan φ hJ h2
  have h := hJ a (a * b + b * a)
  have h' := hJ (a * a) b
  have e : a * (a * b + b * a) + (a * b + b * a) * a =
      (a * a * b + b * (a * a)) + (a * b * a + a * b * a) := by
    simp only [mul_add, add_mul, mul_assoc]; abel
  rw [e, map_add, h', hsq, hJ, map_add] at h
  refine sub_eq_zero.mp (h2 _ ?_)
  have : φ (a * b * a) - φ a * φ b * φ a + (φ (a * b * a) - φ a * φ b * φ a) =
      (φ a * φ a * φ b + φ b * (φ a * φ a) + (φ (a * b * a) + φ (a * b * a))) -
        (φ a * (φ a * φ b + φ b * φ a) + (φ a * φ b + φ b * φ a) * φ a) := by
    simp only [mul_add, add_mul, mul_assoc]; abel
  rw [this, h, sub_self]

end Core

/-! ### The covering argument -/

/-- Two biadditive maps whose zero sets cover every pair: one of them vanishes identically.
(An additive group is not the union of two proper subgroups, applied twice.) -/
theorem biadditive_cover {G H K : Type*} [AddGroup G] [AddGroup H] [AddGroup K]
    (f g : G → H → K)
    (fl : ∀ a a' b, f (a + a') b = f a b + f a' b) (fr : ∀ a b b', f a (b + b') = f a b + f a b')
    (gl : ∀ a a' b, g (a + a') b = g a b + g a' b) (gr : ∀ a b b', g a (b + b') = g a b + g a b')
    (h : ∀ a b, f a b = 0 ∨ g a b = 0) :
    (∀ a b, f a b = 0) ∨ (∀ a b, g a b = 0) := by
  -- first in the second variable, for a fixed `a`
  have row : ∀ a, (∀ b, f a b = 0) ∨ (∀ b, g a b = 0) := by
    intro a
    by_contra hc
    push Not at hc
    obtain ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩ := hc
    have hgb : g a b = 0 := (h a b).resolve_left hb
    have hfb' : f a b' = 0 := (h a b').resolve_right hb'
    rcases h a (b + b') with h0 | h0
    · rw [fr, hfb', add_zero] at h0; exact hb h0
    · rw [gr, hgb, zero_add] at h0; exact hb' h0
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, b, hab⟩, ⟨a', b', hab'⟩⟩ := hc
  have hga : ∀ b, g a b = 0 := (row a).resolve_left (fun hf => hab (hf b))
  have hfa' : ∀ b, f a' b = 0 := (row a').resolve_right (fun hg => hab' (hg b'))
  rcases row (a + a') with h0 | h0
  · have := h0 b; rw [fl, hfa' b, add_zero] at this; exact hab this
  · have := h0 b'; rw [gl, hga b', zero_add] at this; exact hab' this

section Theorems

variable {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)

/-- From "for each pair, one defect vanishes" to "one defect vanishes identically". -/
theorem mul_or_antimul_of_pairwise
    (h : ∀ a b, φ (a * b) - φ a * φ b = 0 ∨ φ (a * b) - φ b * φ a = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) := by
  rcases biadditive_cover (fun a b => φ (a * b) - φ a * φ b) (fun a b => φ (a * b) - φ b * φ a)
      (defect_add_left φ) (defect_add_right φ)
      (antidefect_add_left φ) (antidefect_add_right φ) h with h | h
  · exact Or.inl fun a b => sub_eq_zero.mp (h a b)
  · exact Or.inr fun a b => sub_eq_zero.mp (h a b)

/-- **The domain form, in every characteristic** (two-identity definition; no surjectivity).
An additive map that preserves squares and `a * b * a`, into a ring without zero divisors, is
multiplicative or anti-multiplicative. -/
theorem mul_or_antimul_of_noZeroDivisors
    (hsq : ∀ a, φ (a * a) = φ a * φ a) (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a)
    (hS : ∀ x y : S, x * y = 0 → x = 0 ∨ y = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) :=
  mul_or_antimul_of_pairwise φ fun a b => hS _ _ (defect_mul_defect φ hsq htri a b)

/-- The two-identity form of the theorem: onto a prime ring without 2-torsion. -/
theorem mul_or_antimul_of_prime_of_twoIdentity
    (hsq : ∀ a, φ (a * a) = φ a * φ a) (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hprime : ∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) := by
  refine mul_or_antimul_of_pairwise φ fun a b => ?_
  set τ := φ (a * b) - φ a * φ b with hτ
  set ω := φ (a * b) - φ b * φ a with hω
  have key : ∀ x : S, τ * x * ω + ω * x * τ = 0 := by
    intro x
    obtain ⟨r, rfl⟩ := hsurj x
    exact defect_sandwich φ hsq htri a b r
  have quad : ∀ x y : S, τ * x * (ω * y * τ) = 0 := by
    intro x y
    refine h2 _ ?_
    have kx := key x
    have ky := key y
    have kc := key (x * τ * y)
    -- τ x (ω y τ) = -τ x (τ y ω) = ω (x τ y) τ = -(τ x ω) y τ
    have e : τ * x * (ω * y * τ) + τ * x * (ω * y * τ) =
        τ * x * (τ * y * ω + ω * y * τ) - (τ * (x * τ * y) * ω + ω * (x * τ * y) * τ) +
          (τ * x * ω + ω * x * τ) * y * τ := by
      simp only [mul_add, add_mul, mul_assoc]; abel
    rw [e, ky, kc, kx]
    simp
  by_cases hτ0 : τ = 0
  · exact Or.inl hτ0
  · right
    have h1 : ∀ y : S, ω * y * τ = 0 := fun y =>
      (hprime τ (ω * y * τ) fun x => quad x y).resolve_left hτ0
    exact (hprime ω τ h1).resolve_right hτ0

/-- **Herstein's theorem, characteristic-not-two form.** A Jordan homomorphism onto a prime ring
without 2-torsion is multiplicative or anti-multiplicative. -/
theorem mul_or_antimul_of_prime
    (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hprime : ∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) :=
  mul_or_antimul_of_prime_of_twoIdentity φ (map_sq_of_jordan φ hJ h2)
    (map_triple_of_jordan φ hJ h2) hsurj hprime h2

end Theorems

/-! ### Every characteristic: Smiley's argument -/

section PrimeRing

variable {P : Type*} [NonUnitalRing P]

/-- The ring commutator `a * b - b * a`. -/
def ringComm (a b : P) : P := a * b - b * a

/-- The commutator is additive in its second argument. -/
theorem ringComm_add (x y z : P) : ringComm x (y + z) = ringComm x y + ringComm x z := by
  simp only [ringComm, mul_add, add_mul]; abel

/-- Swapping the arguments of the commutator changes its sign. -/
theorem ringComm_swap (x y : P) : ringComm y x = -ringComm x y := by
  simp only [ringComm]; abel

/-- The commutator with a negative: `[x, -y] = -[x, y]`. -/
theorem ringComm_neg (x y : P) : ringComm x (-y) = -ringComm x y := by
  simp only [ringComm, mul_neg, neg_mul]; abel

/-- The commutator is a derivation in its second argument:
`[x, t * w] = t * [x, w] + [x, t] * w`. -/
theorem ringComm_mul (x t w : P) :
    ringComm x (t * w) = t * ringComm x w + ringComm x t * w := by
  simp only [ringComm, mul_sub, sub_mul, mul_assoc]; abel

/-- The Jacobi identity for the ring commutator. -/
theorem ringComm_jacobi (x y z : P) :
    ringComm x (ringComm z y) + ringComm z (ringComm y x) + ringComm y (ringComm x z) = 0 := by
  simp only [ringComm, mul_sub, sub_mul, mul_assoc]; abel

/-- A prime ring in which every commutator squares to zero is commutative (Smiley 1957,
section 3, Lemma). No hypothesis on 2 and no identity element. -/
theorem commutative_of_commutator_sq_zero
    (hprime : ∀ x y : P, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (hsq : ∀ x y : P, (x * y - y * x) * (x * y - y * x) = 0) : ∀ x y : P, x * y = y * x := by
  have hsq' : ∀ x y : P, ringComm x y * ringComm x y = 0 := hsq
  have h16 : ∀ x y z : P, ringComm x y * ringComm x z = -(ringComm x z * ringComm x y) := by
    intro x y z
    have h := hsq' x (y + z)
    rw [ringComm_add, mul_add, add_mul, add_mul, hsq' x y, hsq' x z, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have hW : ∀ x y w : P, ringComm x y * ringComm x w * ringComm x y = 0 := by
    intro x y w
    rw [h16 x y w, neg_mul, mul_assoc, hsq', mul_zero, neg_zero]
  have h16' : ∀ x y z : P, ringComm z y * ringComm x y = -(ringComm x y * ringComm z y) := by
    intro x y z
    have h := h16 y z x
    rw [ringComm_swap z y, ringComm_swap x y] at h
    simpa only [neg_mul, mul_neg, neg_neg] using h
  have hB : ∀ x y z t : P,
      ringComm x y * t * (ringComm x (ringComm z y) * ringComm x y) = 0 := by
    intro x y z t
    have h1 := hW x y (t * ringComm z y)
    rw [ringComm_mul, mul_add, add_mul] at h1
    have h2 : ringComm x y * (ringComm x t * ringComm z y) * ringComm x y = 0 := by
      calc ringComm x y * (ringComm x t * ringComm z y) * ringComm x y
          = ringComm x y * ringComm x t * (ringComm z y * ringComm x y) := by
            simp only [mul_assoc]
        _ = -(ringComm x y * ringComm x t * ringComm x y * ringComm z y) := by
            rw [h16' x y z]; simp only [mul_neg, mul_assoc]
        _ = 0 := by rw [hW x y t, zero_mul, neg_zero]
    rw [h2, add_zero] at h1
    simpa only [mul_assoc] using h1
  have hC : ∀ x y z : P, ringComm x (ringComm z y) * ringComm x y = 0 := by
    intro x y z
    rcases hprime (ringComm x y) (ringComm x (ringComm z y) * ringComm x y)
      (fun t => hB x y z t) with h | h
    · rw [h, mul_zero]
    · exact h
  have hD : ∀ x y z : P, ringComm x y * z * ringComm x y = 0 := by
    intro x y z
    have e1 := hC x y z
    have e2 := hC y x z
    rw [ringComm_swap x y, ringComm_swap x z, ringComm_neg] at e2
    simp only [neg_mul, mul_neg, neg_neg] at e2
    have e3 : ringComm z (ringComm y x) * ringComm x y = 0 := by
      have j := congrArg (· * ringComm x y) (ringComm_jacobi x y z)
      simp only [add_mul, zero_mul, e1, e2, zero_add, add_zero] at j
      exact j
    rw [ringComm_swap x y, ringComm_neg, neg_mul, neg_eq_zero] at e3
    have e4 : (z * ringComm x y - ringComm x y * z) * ringComm x y = 0 := e3
    rw [sub_mul, mul_assoc, hsq', mul_zero, zero_sub, neg_eq_zero] at e4
    exact e4
  intro x y
  rcases hprime (ringComm x y) (ringComm x y) (hD x y) with h | h <;> exact sub_eq_zero.mp h

/-- In a prime ring, if `T * T ≠ 0`, `T * w = 0` and `T * x * w + w * x * T = 0` for every `x`,
then `w = 0`. -/
theorem eq_zero_of_sq_ne_zero_of_sandwich
    (hprime : ∀ x y : P, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) {T w : P}
    (hT : T * T ≠ 0) (hTw : T * w = 0) (hsw : ∀ x, T * x * w + w * x * T = 0) : w = 0 := by
  refine (hprime (T * T) w fun x => ?_).resolve_left hT
  have e : T * T * x * w = T * (T * x * w + w * x * T) - T * w * x * T := by
    simp only [mul_add, mul_assoc]; abel
  rw [e, hsw, hTw, mul_zero, zero_mul, zero_mul, sub_zero]

/-- Let `τ ω : G → G → P` be additive in the second argument, into a prime ring, with
`τ a b * ω a b = 0` and `τ a b * x * ω a b + ω a b * x * τ a b = 0` for all `a b x`. If
`τ c d * τ c d ≠ 0`, then `ω c x = 0` for every `x`. -/
theorem defect_row_eq_zero {G : Type*} [Add G] (τ ω : G → G → P)
    (hprime : ∀ x y : P, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (τr : ∀ a b b', τ a (b + b') = τ a b + τ a b')
    (ωr : ∀ a b b', ω a (b + b') = ω a b + ω a b')
    (hτω : ∀ a b, τ a b * ω a b = 0)
    (hsw : ∀ a b x, τ a b * x * ω a b + ω a b * x * τ a b = 0)
    {c d : G} (hT : τ c d * τ c d ≠ 0) (x : G) : ω c x = 0 := by
  have hA : ω c d = 0 := eq_zero_of_sq_ne_zero_of_sandwich hprime hT (hτω c d) (hsw c d)
  have hω : ω c (d + x) = ω c x := by rw [ωr, hA, zero_add]
  refine eq_zero_of_sq_ne_zero_of_sandwich hprime hT ?_ fun r => ?_
  · have h1 := hτω c (d + x)
    rw [hω, τr, add_mul, hτω c x, add_zero] at h1
    exact h1
  · have h1 := hsw c (d + x) r
    rw [hω, τr] at h1
    have e : τ c d * r * ω c x + ω c x * r * τ c d =
        ((τ c d + τ c x) * r * ω c x + ω c x * r * (τ c d + τ c x)) -
          (τ c x * r * ω c x + ω c x * r * τ c x) := by
      simp only [mul_add, add_mul]; abel
    rw [e, h1, hsw c x r, sub_zero]

/-- Let `τ ω : G → G → P` be additive in each argument and antisymmetric, into a prime ring, with
`τ a b * ω a b = 0` and `τ a b * x * ω a b + ω a b * x * τ a b = 0` for all `a b x`. If
`τ c d * τ c d ≠ 0` for some `c d`, then `ω` vanishes identically. -/
theorem defect_eq_zero_of_sq_ne_zero {G : Type*} [Add G] (τ ω : G → G → P)
    (hprime : ∀ x y : P, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (τl : ∀ a a' b, τ (a + a') b = τ a b + τ a' b)
    (τr : ∀ a b b', τ a (b + b') = τ a b + τ a b')
    (ωl : ∀ a a' b, ω (a + a') b = ω a b + ω a' b)
    (ωr : ∀ a b b', ω a (b + b') = ω a b + ω a b')
    (τs : ∀ a b, τ b a = -τ a b) (ωs : ∀ a b, ω b a = -ω a b)
    (hτω : ∀ a b, τ a b * ω a b = 0)
    (hsw : ∀ a b x, τ a b * x * ω a b + ω a b * x * τ a b = 0)
    {c d : G} (hT : τ c d * τ c d ≠ 0) (y x : G) : ω y x = 0 := by
  have hc : ∀ x, ω c x = 0 := defect_row_eq_zero τ ω hprime τr ωr hτω hsw hT
  have hT' : τ d c * τ d c ≠ 0 := by rw [τs c d, neg_mul_neg]; exact hT
  have hd : ∀ x, ω d x = 0 := defect_row_eq_zero τ ω hprime τr ωr hτω hsw hT'
  have hyd : ω y d = 0 := by rw [ωs d y, hd, neg_zero]
  have w1 : ω (c + y) (d + x) = ω y x := by
    rw [ωl, ωr, ωr, hc, hc, hyd, zero_add, zero_add, zero_add]
  have w2 : ω (c + y) x = ω y x := by rw [ωl, hc, zero_add]
  have w3 : ω y (d + x) = ω y x := by rw [ωr, hyd, zero_add]
  have t1 : τ (c + y) (d + x) = τ c d + τ c x + (τ y d + τ y x) := by rw [τl, τr, τr]
  have t2 : τ (c + y) x = τ c x + τ y x := τl c y x
  have t3 : τ y (d + x) = τ y d + τ y x := τr y d x
  refine eq_zero_of_sq_ne_zero_of_sandwich hprime hT ?_ fun r => ?_
  · have h1 := hτω (c + y) (d + x)
    have h2 := hτω (c + y) x
    have h3 := hτω y (d + x)
    rw [w1, t1] at h1
    rw [w2, t2] at h2
    rw [w3, t3] at h3
    have e : τ c d * ω y x =
        (τ c d + τ c x + (τ y d + τ y x)) * ω y x - (τ c x + τ y x) * ω y x -
          (τ y d + τ y x) * ω y x + τ y x * ω y x := by
      simp only [add_mul]; abel
    rw [e, h1, h2, h3, hτω y x, sub_zero, sub_zero, add_zero]
  · have h1 := hsw (c + y) (d + x) r
    have h2 := hsw (c + y) x r
    have h3 := hsw y (d + x) r
    rw [w1, t1] at h1
    rw [w2, t2] at h2
    rw [w3, t3] at h3
    have e : τ c d * r * ω y x + ω y x * r * τ c d =
        ((τ c d + τ c x + (τ y d + τ y x)) * r * ω y x +
            ω y x * r * (τ c d + τ c x + (τ y d + τ y x))) -
          ((τ c x + τ y x) * r * ω y x + ω y x * r * (τ c x + τ y x)) -
          ((τ y d + τ y x) * r * ω y x + ω y x * r * (τ y d + τ y x)) +
          (τ y x * r * ω y x + ω y x * r * τ y x) := by
      simp only [mul_add, add_mul]; abel
    rw [e, h1, h2, h3, hsw y x r, sub_zero, sub_zero, add_zero]

end PrimeRing

section AnyChar

variable {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)

/-- `ω * τ = 0`: the mirror image of `defect_mul_defect`. -/
theorem defect_mul_defect_mirror (hsq : ∀ a, φ (a * a) = φ a * φ a)
    (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a) (a b : R) :
    (φ (a * b) - φ b * φ a) * (φ (a * b) - φ a * φ b) = 0 := by
  have h1 := hsq (a * b)
  have h2 := htri b (a * a)
  have h3 := hsq a
  have h4 := map_triple_lin φ htri (a * b) a b
  have e : a * b * a * b + b * a * (a * b) = a * b * (a * b) + b * (a * a) * b := by
    simp only [mul_assoc]
  rw [e, map_add, h1, h2, h3] at h4
  have e' : (φ (a * b) - φ b * φ a) * (φ (a * b) - φ a * φ b) =
      (φ (a * b) * φ (a * b) + φ b * (φ a * φ a) * φ b) -
        (φ (a * b) * φ a * φ b + φ b * φ a * φ (a * b)) := by
    simp only [mul_sub, sub_mul, mul_assoc]; abel
  rw [e', h4, sub_self]

/-- Antisymmetry of the defect `τ`: `φ (b * a) - φ b * φ a = -(φ (a * b) - φ a * φ b)`. -/
theorem defect_swap (hsq : ∀ a, φ (a * a) = φ a * φ a) (a b : R) :
    φ (b * a) - φ b * φ a = -(φ (a * b) - φ a * φ b) := by
  have hJ := map_jordan_of_sq φ hsq a b
  rw [map_add] at hJ
  rw [eq_sub_of_add_eq' hJ]; abel

/-- Antisymmetry of the defect `ω`: `φ (b * a) - φ a * φ b = -(φ (a * b) - φ b * φ a)`. -/
theorem antidefect_swap (hsq : ∀ a, φ (a * a) = φ a * φ a) (a b : R) :
    φ (b * a) - φ a * φ b = -(φ (a * b) - φ b * φ a) := by
  have hJ := map_jordan_of_sq φ hsq a b
  rw [map_add] at hJ
  rw [eq_sub_of_add_eq' hJ]; abel

/-- Smiley's theorem in every characteristic (Smiley 1957, Added in proof, p. 429): an additive
map that preserves squares and `a * b * a`, onto a prime ring, is multiplicative or
anti-multiplicative. No hypothesis on 2. -/
theorem mul_or_antimul_of_prime_of_twoIdentity_anyChar
    (hsq : ∀ a, φ (a * a) = φ a * φ a) (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hprime : ∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) := by
  have τl : ∀ a a' b : R, φ ((a + a') * b) - φ (a + a') * φ b =
      φ (a * b) - φ a * φ b + (φ (a' * b) - φ a' * φ b) := defect_add_left φ
  have τr : ∀ a b b' : R, φ (a * (b + b')) - φ a * φ (b + b') =
      φ (a * b) - φ a * φ b + (φ (a * b') - φ a * φ b') := defect_add_right φ
  have ωl : ∀ a a' b : R, φ ((a + a') * b) - φ b * φ (a + a') =
      φ (a * b) - φ b * φ a + (φ (a' * b) - φ b * φ a') := antidefect_add_left φ
  have ωr : ∀ a b b' : R, φ (a * (b + b')) - φ (b + b') * φ a =
      φ (a * b) - φ b * φ a + (φ (a * b') - φ b' * φ a) := antidefect_add_right φ
  have hsw : ∀ (a b : R) (x : S), (φ (a * b) - φ a * φ b) * x * (φ (a * b) - φ b * φ a) +
      (φ (a * b) - φ b * φ a) * x * (φ (a * b) - φ a * φ b) = 0 := fun a b x => by
    obtain ⟨r, rfl⟩ := hsurj x
    exact defect_sandwich φ hsq htri a b r
  have hsw' : ∀ (a b : R) (x : S), (φ (a * b) - φ b * φ a) * x * (φ (a * b) - φ a * φ b) +
      (φ (a * b) - φ a * φ b) * x * (φ (a * b) - φ b * φ a) = 0 := fun a b x => by
    rw [add_comm]; exact hsw a b x
  by_cases hτ : ∃ c d, (φ (c * d) - φ c * φ d) * (φ (c * d) - φ c * φ d) ≠ 0
  · obtain ⟨c, d, hT⟩ := hτ
    exact Or.inr fun a b => sub_eq_zero.mp <|
      defect_eq_zero_of_sq_ne_zero (fun a b => φ (a * b) - φ a * φ b)
        (fun a b => φ (a * b) - φ b * φ a) hprime τl τr ωl ωr (defect_swap φ hsq)
        (antidefect_swap φ hsq) (defect_mul_defect φ hsq htri) hsw hT a b
  by_cases hω : ∃ c d, (φ (c * d) - φ d * φ c) * (φ (c * d) - φ d * φ c) ≠ 0
  · obtain ⟨c, d, hT⟩ := hω
    exact Or.inl fun a b => sub_eq_zero.mp <|
      defect_eq_zero_of_sq_ne_zero (fun a b => φ (a * b) - φ b * φ a)
        (fun a b => φ (a * b) - φ a * φ b) hprime ωl ωr τl τr (antidefect_swap φ hsq)
        (defect_swap φ hsq) (defect_mul_defect_mirror φ hsq htri) hsw' hT a b
  push Not at hτ hω
  have hcomm : ∀ x y : S, x * y = y * x := by
    refine commutative_of_commutator_sq_zero hprime fun x y => ?_
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    have e : (φ a * φ b - φ b * φ a) * (φ a * φ b - φ b * φ a) =
        (φ (a * b) - φ b * φ a) * (φ (a * b) - φ b * φ a) -
          (φ (a * b) - φ b * φ a) * (φ (a * b) - φ a * φ b) -
          (φ (a * b) - φ a * φ b) * (φ (a * b) - φ b * φ a) +
          (φ (a * b) - φ a * φ b) * (φ (a * b) - φ a * φ b) := by
      simp only [mul_sub, sub_mul, mul_assoc]; abel
    rw [e, hω a b, defect_mul_defect_mirror φ hsq htri a b, defect_mul_defect φ hsq htri a b,
      hτ a b, sub_zero, sub_zero, add_zero]
  refine mul_or_antimul_of_noZeroDivisors φ hsq htri fun x y hxy => hprime x y fun z => ?_
  rw [mul_assoc, hcomm z y, ← mul_assoc, hxy, zero_mul]

end AnyChar

end HersteinJordan
