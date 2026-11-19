/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Spec.Basic
public import Mathlib.Algebra.Field.ZMod

import LeanPool.Ratpoints.Mathlib.Algebra.Group.Even
import LeanPool.Ratpoints.Proof.Containers

/-!
# Square residues of binary forms
-/

@[expose] public section

namespace Ratpoints

/-- The binary form `∑ fᵢ aⁱ b^(D - i)` of degree `D ≥ d` at `a = k b` is `f(k) b ^ D`, in any
commutative semiring; over a field, `k = a / b` for `b ≠ 0`, as `Polynomial.eval_homogenize` says
for polynomials. -/
theorem sum_mul_pow_mul_pow_sub_of_eq_mul {R : Type*} [CommSemiring R] {d D : ℕ} (hd : d ≤ D)
    (f : ℕ → R) {a b k : R} (h : a = k * b) :
    ∑ i ∈ Finset.range (d + 1), f i * a ^ i * b ^ (D - i) =
      (∑ i ∈ Finset.range (d + 1), f i * k ^ i) * b ^ D := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [h, mul_pow, ← pow_mul_pow_sub b ((Finset.mem_range_succ_iff.mp hi).trans hd)]
  ring

/-- The binary form `∑ fᵢ aⁱ b^(D - i)` of degree `D ≥ d` at `b = t a` is the value
`∑ fᵢ t^(D - i)` of the reversed polynomial times `a ^ D`, in any commutative semiring. -/
theorem sum_mul_pow_mul_pow_sub_of_eq_mul_right {R : Type*} [CommSemiring R] {d D : ℕ}
    (hd : d ≤ D) (f : ℕ → R) {a b t : R} (h : b = t * a) :
    ∑ i ∈ Finset.range (d + 1), f i * a ^ i * b ^ (D - i) =
      (∑ i ∈ Finset.range (d + 1), f i * t ^ (D - i)) * a ^ D := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [h, mul_pow, ← pow_mul_pow_sub a ((Finset.mem_range_succ_iff.mp hi).trans hd)]
  ring

/-- A point `(a, y, b)` whose denominator `b` is a unit of the commutative ring `R` makes `f` take a
square value at the `k` with `a = k b` in `R`: `F(a, b) = f(k) b ^ D` with `D` even. -/
theorem isSquare_sum_mul_pow_of_sq_eq_binaryForm {R : Type*} [CommRing R] {c : List ℤ}
    {a y : ℤ} {b : ℕ} {k : R} (hb : IsUnit (b : R)) (hk : (a : R) = k * b)
    (hy : y ^ 2 = binaryForm c a b) :
    IsSquare (∑ i ∈ Finset.range (degree c + 1), (c.getD i 0 : R) * k ^ i) := by
  have h2 := congr(($hy : R))
  push_cast [binaryForm] at h2
  rw [sum_mul_pow_mul_pow_sub_of_eq_mul (by lia) _ hk] at h2
  exact hb.isSquare_of_sq_eq_mul_pow (Nat.even_iff.mpr (by lia)) h2

/-- A point `(a, y, b)` whose numerator `a` is a unit of the commutative ring `R` makes the reversed
polynomial take a square value `∑ cᵢ t^(D - i)` at the `t` with `b = t a` in `R`:
`F(a, b) = a ^ D ∑ cᵢ t^(D - i)` with `D` even. -/
theorem isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm {R : Type*} [CommRing R] {c : List ℤ}
    {a y : ℤ} {b : ℕ} {t : R} (ha : IsUnit (a : R)) (ht : (b : R) = t * a)
    (hy : y ^ 2 = binaryForm c a b) :
    IsSquare (∑ i ∈ Finset.range (degree c + 1),
      (c.getD i 0 : R) * t ^ (degree c + degree c % 2 - i)) := by
  have h2 := congr(($hy : R))
  push_cast [binaryForm] at h2
  rw [sum_mul_pow_mul_pow_sub_of_eq_mul_right (by lia) _ ht] at h2
  exact ha.isSquare_of_sq_eq_mul_pow (Nat.even_iff.mpr (by lia)) h2

namespace Sieve

/-- A point `(a, y, b)` with `p ∣ b`, among them the points at infinity, makes the leading
coefficient `c_d` a square modulo `p` for even `d`: since `gcd(a, b) = 1`, `p ∤ a`, and
`y ^ 2 ≡ c_d a ^ d (mod p)`. -/
theorem isSquare_getD_degree_of_sq_eq_binaryForm {c : List ℤ} {p : ℕ} [Fact p.Prime]
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hb : b % p = 0) (hd : degree c % 2 = 0)
    (hy : y ^ 2 = binaryForm c a b) : IsSquare (c.getD (degree c) 0 : ZMod p) := by
  have hb' : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hb)
  have ha : (a : ZMod p) ≠ 0 := fun h ↦
    Int.toNat_emod_ne_zero_of_gcd_eq_one (Fact.out : p.Prime).one_lt hab hb
      (by simp [Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)])
  have h2 := congr(($hy : ZMod p))
  push_cast [binaryForm, hb', hd, Nat.add_zero] at h2
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi ↦ by
    rw [zero_pow (by lia [Finset.mem_range.mp hi]), mul_zero], zero_add, Nat.sub_self,
    pow_zero, mul_one] at h2
  rw [eq_div_of_mul_eq (pow_ne_zero _ ha) h2.symm]
  exact (IsSquare.sq (y : ZMod p)).div ((Nat.even_iff.mpr hd).isSquare_pow _)

end Sieve

end Ratpoints

end
