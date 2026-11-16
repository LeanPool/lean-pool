/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Data.Nat.Choose.Dvd

/-!
# Powers of a product in nilpotency class two

Let `u`, `v` be elements of a group whose commutator `d` (`v * u = d * u * v`) commutes with both.
Then `(u * v) ^ n = u ^ n * v ^ n * d ^ (n choose 2)`; for `p` an odd prime with `d ^ p = 1`,
`(u * v) ^ p = u ^ p * v ^ p`.

## Main statements

* `pow_mul_eq_of_commute_commutator`: `v ^ n * u = d ^ n * u * v ^ n`.
* `mul_pow_eq_of_commute_commutator`: `(u * v) ^ n = u ^ n * v ^ n * d ^ n.choose 2`.
* `mul_pow_eq_mul_pow_of_commute_commutator`: for `p` an odd prime and `d ^ p = 1`,
  `(u * v) ^ p = u ^ p * v ^ p`.
-/

public section

variable {G : Type*} [Group G]

/-- If `v * u = d * u * v` and `d` commutes with `v`, then `v ^ n * u = d ^ n * u * v ^ n`. -/
theorem pow_mul_eq_of_commute_commutator {u v d : G} (hd : v * u = d * u * v)
    (hdv : Commute d v) (n : ℕ) : v ^ n * u = d ^ n * u * v ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc v ^ (n + 1) * u = v ^ n * (v * u) := by rw [pow_succ, mul_assoc]
      _ = v ^ n * d * u * v := by rw [hd]; simp only [mul_assoc]
      _ = d * (v ^ n * u) * v := by rw [← (hdv.pow_right n).eq]; simp only [mul_assoc]
      _ = d ^ (n + 1) * u * v ^ (n + 1) := by
        rw [ih, pow_succ' d n, pow_succ v n]; simp only [mul_assoc]

/-- The power formula in class 2: if `v * u = d * u * v` and `d` commutes with `u` and `v`, then
`(u * v) ^ n = u ^ n * v ^ n * d ^ n.choose 2`. -/
theorem mul_pow_eq_of_commute_commutator {u v d : G} (hd : v * u = d * u * v)
    (hdu : Commute d u) (hdv : Commute d v) (n : ℕ) :
    (u * v) ^ n = u ^ n * v ^ n * d ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    set c := n.choose 2
    calc (u * v) ^ (n + 1) = u ^ n * v ^ n * (d ^ c * u) * v := by
          rw [pow_succ, ih]; simp only [mul_assoc]
      _ = u ^ n * (v ^ n * u) * d ^ c * v := by
          rw [(hdu.pow_left c).eq]; simp only [mul_assoc]
      _ = u ^ n * (d ^ n * u) * v ^ n * d ^ c * v := by
          rw [pow_mul_eq_of_commute_commutator hd hdv n]; simp only [mul_assoc]
      _ = u ^ n * u * (d ^ n * v ^ n) * d ^ c * v := by
          rw [(hdu.pow_left n).eq]; simp only [mul_assoc]
      _ = u ^ n * u * (v ^ n * ((d ^ n * d ^ c) * v)) := by
          rw [((hdv.pow_left n).pow_right n).eq]; simp only [mul_assoc]
      _ = u ^ n * u * (v ^ n * (v * (d ^ n * d ^ c))) := by
          rw [((hdv.pow_left n).mul_left (hdv.pow_left c)).eq]
      _ = u ^ (n + 1) * v ^ (n + 1) * d ^ (n + 1).choose 2 := by
          rw [pow_succ u n, pow_succ v n, hc, pow_add]; simp only [mul_assoc]

/-- For `p` an odd prime, if the commutator `d` of `u` and `v` commutes with both and satisfies
`d ^ p = 1`, then `(u * v) ^ p = u ^ p * v ^ p`. -/
theorem mul_pow_eq_mul_pow_of_commute_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u v d : G} (hd : v * u = d * u * v) (hdu : Commute d u) (hdv : Commute d v)
    (hdp : d ^ p = 1) : (u * v) ^ p = u ^ p * v ^ p := by
  obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero (hp.two_le.lt_of_ne' hp2)
  rw [mul_pow_eq_of_commute_commutator hd hdu hdv, hk, pow_mul, hdp, one_pow, mul_one]
