/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineDescription
public import Mathlib.Data.Nat.Size
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Length of fixed-program descriptions with numerical input

The concrete compiler packages a fixed partial-recursive program and its
numerical input using `Nat.pair`, then writes that number in binary.  Pairing
costs at most twice the larger binary size.  Consequently polynomially bounded
input and advice fit the affine-description test's rank budget for every
sufficiently large rank.

This is an encoding theorem.  A stage-specific reconstruction algorithm and
the correctness of its output remain separate obligations.
-/

@[expose] public section

namespace Klr.AffineProgramLength

open Filter AffineDescription

/-- The natural-number pairing function uses at most twice the larger binary size. -/
theorem size_pair_le (a b : ℕ) :
    Nat.size (Nat.pair a b) ≤ 2 * max (Nat.size a) (Nat.size b) := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ max (Nat.size a) (Nat.size b) :=
    (Nat.lt_size_self a).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hb : b < 2 ^ max (Nat.size a) (Nat.size b) :=
    (Nat.lt_size_self b).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have hab : max a b + 1 ≤ 2 ^ max (Nat.size a) (Nat.size b) := by omega
  calc
    Nat.pair a b < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
    _ ≤ (2 ^ max (Nat.size a) (Nat.size b)) ^ 2 := by gcongr
    _ = 2 ^ (2 * max (Nat.size a) (Nat.size b)) := by
      rw [← pow_mul, Nat.mul_comm]

/-- The compiler's exact bit length. -/
theorem programFor_length (e : Nat.Partrec.Code) (n : ℕ) :
    (programFor e n).length = Nat.size (Nat.pair (Encodable.encode e) n) :=
  Nat.size_eq_bits_len _

/-- A direct binary-length bound for a fixed algorithm and arbitrary numerical input. -/
theorem programFor_length_le_max (e : Nat.Partrec.Code) (n : ℕ) :
    (programFor e n).length ≤
      2 * max (Nat.size (Encodable.encode e)) (Nat.size n) := by
  rw [programFor_length]
  exact size_pair_le _ _

/-- An additive version separates the fixed program header from the input size. -/
theorem programFor_length_le (e : Nat.Partrec.Code) (n : ℕ) :
    (programFor e n).length ≤
      2 * (Nat.size (Encodable.encode e) + Nat.size n) := by
  apply (programFor_length_le_max e n).trans
  omega

/-- A polynomial input has logarithmic binary size, including the constant polynomial. -/
theorem size_pow_le (r k : ℕ) : Nat.size (r ^ k) ≤ k * Nat.size r + 1 := by
  calc
    Nat.size (r ^ k) ≤ Nat.size ((2 ^ Nat.size r) ^ k) := by
      apply Nat.size_le_size
      gcongr
      exact (Nat.lt_size_self r).le
    _ = k * Nat.size r + 1 := by
      rw [← pow_mul, Nat.size_pow, Nat.mul_comm]

/-- An elementary exponential comparison used to avoid analytic logarithm estimates. -/
theorem sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- An explicit threshold beyond which every fixed affine function of binary size
is bounded by the number itself. -/
theorem linear_size_le_of_ge (A B : ℕ) {r : ℕ}
    (hr : 2 ^ (A + B + 4) ≤ r) : A * Nat.size r + B ≤ r := by
  have hs : A + B + 4 < Nat.size r := Nat.lt_size.mpr hr
  let t := Nat.size r - 1
  have ht : t + 1 = Nat.size r := by dsimp [t]; omega
  have ht4 : 4 ≤ t := by dsimp [t]; omega
  have hAB : A + B ≤ t := by omega
  have hA : A + 1 ≤ t := by omega
  have hpow : 2 ^ t ≤ r := Nat.lt_size.mp (by omega : t < Nat.size r)
  calc
    A * Nat.size r + B = A * (t + 1) + B := by rw [ht]
    _ ≤ t ^ 2 := by nlinarith [Nat.mul_le_mul_right t hA]
    _ ≤ 2 ^ t := sq_le_two_pow ht4
    _ ≤ r := hpow

/-- Binary description length is eventually negligible compared with any rank budget. -/
theorem eventually_linear_size_le (A B : ℕ) :
    ∀ᶠ r : ℕ in atTop, A * Nat.size r + B ≤ r :=
  (eventually_ge_atTop (2 ^ (A + B + 4))).mono fun _ hr => linear_size_le_of_ge A B hr

/-- Uniformly over all inputs of an affine binary-size bound, the concrete compiler
eventually meets the affine-description test's rank requirement. -/
theorem eventually_programFor_length_budget (e : Nat.Partrec.Code) (k b level : ℕ) :
    ∀ᶠ r : ℕ in atTop, ∀ n : ℕ, Nat.size n ≤ k * Nat.size r + b →
      2 * (programFor e n).length + level + 1 ≤ r := by
  filter_upwards [eventually_linear_size_le (4 * k)
    (4 * Nat.size (Encodable.encode e) + 4 * b + level + 1)] with r hr
  intro n hn
  have hlen := programFor_length_le e n
  nlinarith

/-- Polynomially bounded numerical advice fits the rank budget, uniformly in the advice. -/
theorem eventually_programFor_bounded_pow_length_budget
    (e : Nat.Partrec.Code) (k level : ℕ) :
    ∀ᶠ r : ℕ in atTop, ∀ n : ℕ, n ≤ r ^ k →
      2 * (programFor e n).length + level + 1 ≤ r := by
  filter_upwards [eventually_programFor_length_budget e k 1 level] with r hr
  intro n hn
  exact hr n ((Nat.size_le_size hn).trans (size_pow_le r k))

/-- In particular, a polynomial input to a fixed algorithm has a sufficiently
short program for every fixed test level once the rank is large enough. -/
theorem eventually_programFor_pow_length_budget (e : Nat.Partrec.Code) (k level : ℕ) :
    ∀ᶠ r : ℕ in atTop, 2 * (programFor e (r ^ k)).length + level + 1 ≤ r :=
  (eventually_programFor_bounded_pow_length_budget e k level).mono fun r hr =>
    hr (r ^ k) le_rfl

/-- A stage parameter can be accompanied by any polynomially bounded advice
index.  Encoding the parameter/advice pair still meets the same eventual budget. -/
theorem eventually_programFor_pair_advice_length_budget
    (e : Nat.Partrec.Code) (k level : ℕ) :
    ∀ᶠ r : ℕ in atTop, ∀ q : ℕ, q ≤ r ^ k →
      2 * (programFor e (Nat.pair r q)).length + level + 1 ≤ r := by
  filter_upwards [eventually_programFor_length_budget e (2 * (k + 1)) 2 level]
    with r hr
  intro q hq
  apply hr
  have hs := size_pair_le r q
  have hqsize := (Nat.size_le_size hq).trans (size_pow_le r k)
  have hmax : max (Nat.size r) (Nat.size q) ≤ Nat.size r + Nat.size q := by omega
  nlinarith

end Klr.AffineProgramLength
