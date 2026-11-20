/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Spec.Basic
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

import LeanPool.Ratpoints.Mathlib.Data.Int.GCD
import LeanPool.Ratpoints.Mathlib.NumberTheory.Padics.PadicVal.Basic
import LeanPool.Ratpoints.Proof.Setup
import Mathlib.Data.Nat.Squarefree

/-!
# Valuation constraints on denominators of points on odd-degree curves
-/

@[expose] public section

namespace Ratpoints

/-! ### The denominators of the points -/

/-- For odd degree, a point `(a, y, b)` whose term `c_d a ^ d b` of `F(a, b)` is `p ^ V u` with
`p ∤ u`, while `p ^ (V + 1)` divides every other term, has an even `V`
(`Int.even_and_exists_isSquare_add_of_sq_eq_sum`). -/
theorem even_of_sq_eq_binaryForm_of_odd_of_dvd {c : List ℤ} {a y : ℤ} {b : ℕ} {p V : ℕ}
    [Fact p.Prime] (hd : degree c % 2 = 1) (hy : y ^ 2 = binaryForm c a b) {u : ℤ}
    (hu : c.getD (degree c) 0 * a ^ degree c * b = (p : ℤ) ^ V * u) (hpu : ¬(p : ℤ) ∣ u)
    (h : ∀ i < degree c, (p : ℤ) ^ (V + 1) ∣ c.getD i 0 * a ^ i * (b : ℤ) ^ (degree c + 1 - i)) :
    Even V := by
  rw [binaryForm, hd] at hy
  exact (Int.even_and_exists_isSquare_add_of_sq_eq_sum hy (Finset.self_mem_range_succ _)
    (by rw [Nat.add_sub_cancel_left, pow_one, hu]) hpu
    fun i hi hne ↦ h i (by lia [Finset.mem_range.mp hi])).1

-- The terms of `F(a, b)` other than `c_d a ^ d b`, for `b = p ^ m b'` and `k < d`, when
-- `(d - k) m ≥ 1 + val - v_p(c_k)` for `c_k ≠ 0`, are divisible by `p ^ (val + m + 1)`.
private theorem pow_dvd_of_add_one_le {c : List ℤ} {a b' : ℤ} {p m val k : ℕ} (hk : k < degree c)
    (hmin : c.getD k 0 ≠ 0 → val + 1 ≤ padicValNat p (c.getD k 0).natAbs + (degree c - k) * m) :
    (p : ℤ) ^ (val + m + 1) ∣ c.getD k 0 * a ^ k * ((p : ℤ) ^ m * b') ^ (degree c + 1 - k) := by
  rcases eq_or_ne (c.getD k 0) 0 with h0 | h0
  · rw [h0, zero_mul, zero_mul]
    exact dvd_zero _
  have hc : (p : ℤ) ^ padicValNat p (c.getD k 0).natAbs ∣ c.getD k 0 := by
    rw [Nat.padicValNat_def, ← Nat.cast_pow]
    exact Int.natCast_dvd.mpr (pow_multiplicity_dvd ..)
  have hle : val + m + 1 ≤ padicValNat p (c.getD k 0).natAbs + m * (degree c + 1 - k) := by
    rw [Nat.sub_add_comm hk.le]
    lia [hmin h0]
  refine (pow_dvd_pow _ hle).trans ?_
  rw [pow_add, mul_pow, ← pow_mul]
  exact mul_dvd_mul (hc.mul_right _) (dvd_mul_right _ _)

/-- **The valuation test of the slopes** (odd degree): for a prime `p` with `v_p(c_d) = val` and a
denominator `b` of a point with `m = v_p(b) ≥ 1` and `(d - k) m ≥ 1 + val - v_p(c_k)` for every
`k < d` with `c_k ≠ 0`, the term `c_d a ^ d b` of `F(a, b)` alone has the least valuation
`val + m`, which is then even. -/
theorem even_add_of_sq_eq_binaryForm_of_odd {c : List ℤ} {a y : ℤ} {b p val : ℕ}
    [hp : Fact p.Prime] (hd : degree c % 2 = 1)
    (hval : padicValNat p (c.getD (degree c) 0).natAbs = val)
    (hmin : ∀ k < degree c, c.getD k 0 ≠ 0 →
      val + 1 ≤ padicValNat p (c.getD k 0).natAbs + (degree c - k) * padicValNat p b)
    (hab : Int.gcd a b = 1) (hm : padicValNat p b ≠ 0) (hy : y ^ 2 = binaryForm c a b) :
    Even (val + padicValNat p b) := by
  simp only [Nat.padicValNat_def] at hval hmin hm ⊢
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpa := Int.not_natCast_dvd_of_gcd_eq_one hp.out.ne_one hab
    (dvd_of_one_le_multiplicity (Nat.one_le_iff_ne_zero.mpr hm))
  obtain ⟨b', hb', hpb'⟩ := Int.exists_eq_pow_padicValInt_mul hp.out.ne_one (n := b)
    fun h ↦ by simp_all
  rw [padicValInt.of_nat] at hb'
  obtain ⟨r, hr, hpr⟩ := Int.exists_eq_pow_padicValInt_mul hp.out.ne_one
    (getD_degree_ne_zero_of_pos (c := c) (by lia))
  rw [padicValInt, hval] at hr
  refine even_of_sq_eq_binaryForm_of_odd_of_dvd hd hy (u := r * a ^ degree c * b')
    (by rw [hr, hb', pow_add]; ring)
    (hpp.not_dvd_mul (hpp.not_dvd_mul hpr (mt hpp.dvd_of_dvd_pow hpa)) hpb') fun i hi ↦ ?_
  rw [hb']
  exact pow_dvd_of_add_one_le hi (by simpa only [Nat.padicValNat_def] using hmin i hi)

/-- For odd degree, a prime `p ∤ c_d` divides the denominator `b` of every point an even number of
times: for `v_p(b) ≥ 1` the term `c_d a ^ d b` of `F(a, b)` alone has the least valuation `v_p(b)`
(`Ratpoints.even_add_of_sq_eq_binaryForm_of_odd` with `v_p(c_d) = 0`). -/
theorem even_of_sq_eq_binaryForm_of_odd {c : List ℤ} {a y : ℤ} {b p : ℕ} [Fact p.Prime]
    (hd : degree c % 2 = 1) (hc : ¬(p : ℤ) ∣ c.getD (degree c) 0) (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) : Even (padicValNat p b) := by
  rcases eq_or_ne (padicValNat p b) 0 with h0 | hm
  · simp [h0]
  simpa using even_add_of_sq_eq_binaryForm_of_odd hd
    (Nat.padicValNat_def.trans (multiplicity_eq_zero_of_not_dvd (mt Int.natCast_dvd.mpr hc)))
    (fun k hk _ ↦ le_add_left (Nat.mul_pos (Nat.sub_pos_of_lt hk) (Nat.pos_of_ne_zero hm)))
    hab hm hy

/-- For odd degree and a leading coefficient `±1`, the denominator `b` of every point is a square:
its valuation `v_p(b)` at every prime `p` is even (`Ratpoints.even_of_sq_eq_binaryForm_of_odd`),
since for `v_p(b) ≥ 1` the term `c_d a ^ d b` of `F(a, b)` alone has the least valuation. -/
theorem isSquare_of_sq_eq_binaryForm_of_odd {c : List ℤ} (hd : degree c % 2 = 1)
    (hc : IsUnit (c.getD (degree c) 0)) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) : IsSquare b := by
  refine Nat.isSquare_iff_even_factorization.mpr fun p hp ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, ← Nat.padicValNat_def]
  exact even_of_sq_eq_binaryForm_of_odd hd
    (fun h ↦ (Nat.prime_iff_prime_int.mp hp).not_isUnit (isUnit_of_dvd_unit h hc)) hab hy

/-- For odd degree, the denominator of every point is `s k ^ 2` with `s` squarefree and dividing the
leading coefficient: a prime that divides `b` an odd number of times divides `c_d`
(`Ratpoints.even_of_sq_eq_binaryForm_of_odd`). -/
theorem exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd {c : List ℤ} (hd : degree c % 2 = 1)
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    ∃ s k : ℕ, Squarefree s ∧ s ∣ (c.getD (degree c) 0).natAbs ∧ b = s * k * k := by
  rcases eq_or_ne b 0 with rfl | hb
  · exact ⟨1, 0, squarefree_one, one_dvd _, by simp⟩
  obtain ⟨k, s, hks, hs⟩ := exists_sq_mul_squarefree b
  refine ⟨s, k, hs, ?_, by rw [← hks]; ring⟩
  rcases eq_or_ne (c.getD (degree c) 0) 0 with h0 | h0
  · rw [h0, Int.natAbs_zero]
    exact dvd_zero s
  rw [← Nat.prod_primeFactors_of_squarefree hs, Nat.prod_primeFactors_dvd_iff (by simpa using h0)]
  intro p hp
  obtain ⟨hpp, hps, -⟩ := Nat.mem_primeFactors.mp hp
  refine Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp (by_contra fun hc ↦ ?_),
    by simpa using h0⟩
  have : Fact p.Prime := ⟨hpp⟩
  have hev := even_of_sq_eq_binaryForm_of_odd hd hc hab hy
  rw [Nat.padicValNat_def, ← Nat.factorization_def _ hpp, ← hks,
    Nat.factorization_mul (left_ne_zero_of_mul (hks ▸ hb)) hs.ne_zero, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_eq_one_of_squarefree hs hpp hps] at hev
  exact Nat.not_even_iff_odd.mpr ⟨_, rfl⟩ hev

end Ratpoints

end
