/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.FLT.Four
public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.NumberTheory.Fermat
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set

/-!
# Français 9115, views 704–730: Manuscript C and the notes on quadratic residues

Adapted from `lean/Germain/Fr9115Arithmetic.lean` of
https://github.com/Commutator-IO/germain-project
at commit `167c171` (CC0, same author).

The modernised reading `transcripts/fr-9115/fr-9115.modern.tex`, sections « Le manuscrit C
(ff. 348r--349r, vues 708 à 710) » and « Résidus quadratiques : notes de travail » (views 704–730,
batches 36 and 37). Findings `fr-9115-manuscript-c-case-one` and `fr-9115-fermat-primes-residues`
of `src/content/findings.ts`.

Manuscript C (views 708–710).
* `manuscriptC_not_as_written`, `manuscriptC_n_one`: the theorem on `2z^{2n} = x^{2n} + y^{2n}` as
  written fails at `x = y = z = 1`; for `n = 1` there are other solutions.
* `manuscriptC_odd`: coprime solutions have `x`, `y`, `z` odd (unstated on the page).
* `param_identity`, `system_one`, `system_two`, `UV_identity`: the parametrisations and the
  systems (1) and (2) of the page, as identities.
* `factor_Phi`, `Phi_modEq`, `dvd_n_of_dvd_both`: `x^{2n} + y^{2n} = (x^2+y^2) Φ`,
  `Φ ≡ n y^{2n-2}`, so a common divisor of `x^2 + y^2` and `Φ` divides `n`; `Phi_counterexample`:
  `n = 5`, `x = 1`, `y = 3`, where `5` divides both.
* `N_dvd_UV`: `p q (p^2 - q^2) ∣ U V` from system (2).
* `two_signs`: the page's step from « l'un et l'autre signes », *under that hypothesis*.
* `inequality_identity`, `inequality_counterexamples`: `2(y^2-x^2) - (x+y)^2 = (x+y)(y-3x)`, and
  the cases `x = ∓7`, `y = 17` where the chain of inequalities of view 709 breaks.
* `trivial_case`: `x^n = x` for `x = ±1`, `n` odd.
* `fermat_not_both_odd`, `fermat_two_n_of_even`, `fermat_two_n_of_three_dvd`, `even_n_no_factor`:
  for `Z^{2n} = X^{2n} + Y^{2n}`, one of `X`, `Y` is even; no solution for `n` even (Fermat's
  exponent 4, mathlib) or `3 ∣ n` (exponent 3, mathlib); for even `n` the reduction's
  divisibility fails.

Quadratic residues (views 704–730).
* `residue_of_dvd_pred_one`, `neg_residue_of_dvd_pred_three`, `two_nonresidue_of_three_mod_eight`,
  `two_residue_of_seven_mod_eight`, `two_residue_of_odd_two_power`: the method of view 704,
  through the divisors of `(p-1)/2`; the second supplement is Mathlib's
  `ZMod.exists_sq_eq_two_iff`.
* `neg_residue_of_one_mod_four`, `four_square_expansion`: view 706, whose reciprocity for primes
  `P ≡ p ≡ 1 (mod 4)` is Mathlib's `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`.
* `exists_prime_nonresidue`: every integer that is not a square is a non-residue of some prime
  not dividing it (view 722), via `exists_jacobiSym_eq_neg_one`.
* `four_n_two_nonresidue`, `neg_nonresidue_smaller`, `pos_nonresidue_smaller`, `three_exception`:
  the arguments of views 720–723, with the bound « moindre »; `false_extension`: `-5`, `-17`, `-21`
  refute the extension of view 720; `nineteen_exception`, `three_eleven`: views 718 and 726.
* `neg_residue_of_nonresidue`, `twelve_n_eleven`, `neg_three_of_dvd`, `cube_identity`: view 728.
* `three_primitive_root`: `3` is a primitive root of every prime `12n + 5` with `3n + 1` prime
  (view 729).
* `fermatNumber_mod`, `fermat_residue_iff`, `three_nonresidue_fermat`, `five_nonresidue_fermat`,
  `fermat_residue_of_two_le`, `seventeen_residue`, `fermat_primitive_root`,
  `seven_nonresidue_fermat` and the `*_primitive_root_fermat`: view 730.

Not formalised: the theorem of Manuscript C itself (Darmon–Merel) and Fermat's equation for odd
`n` with no factor `3` (Wiles); Gauss's art. 125 statement for primes `4n + 1`; the induction of
view 726 beyond its counterexample.
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Fr9115Arithmetic

open Finset

/-! ## Manuscript C -/

/-- The statement of view 708 as written fails: `x = y = z = 1`. -/
theorem manuscriptC_not_as_written (n : ℕ) :
    ¬ ∀ x y z : ℤ, IsCoprime x y → 2 * z ^ (2 * n) ≠ x ^ (2 * n) + y ^ (2 * n) := by
  intro h
  exact h 1 1 1 isCoprime_one_left (by ring)

/-- For `n = 1` there are solutions besides the trivial one. -/
theorem manuscriptC_n_one :
    (1 : ℤ) ^ 2 + 7 ^ 2 = 2 * 5 ^ 2 ∧ (7 : ℤ) ^ 2 + 17 ^ 2 = 2 * 13 ^ 2 := by
  norm_num

/-- The first parametrisation of the page. -/
theorem param_identity (P Q : ℤ) :
    (P ^ 2 - Q ^ 2 - 2 * P * Q) ^ 2 + (P ^ 2 - Q ^ 2 + 2 * P * Q) ^ 2 =
      2 * (P ^ 2 + Q ^ 2) ^ 2 := by
  ring

lemma sq_mod_four_of_odd {x : ℤ} (hx : Odd x) : ((x : ZMod 4)) ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := hx
  push_cast
  generalize (a : ZMod 4) = b
  revert b; decide

lemma sq_mod_four_of_even {x : ℤ} (hx : Even x) : ((x : ZMod 4)) ^ 2 = 0 := by
  obtain ⟨a, rfl⟩ := hx
  push_cast
  generalize (a : ZMod 4) = b
  revert b; decide

/-- Coprime solutions of `x^{2n} + y^{2n} = 2 z^{2n}` (`n ≥ 1`) have `x`, `y`, `z` odd. -/
theorem manuscriptC_odd {n : ℕ} (hn : 1 ≤ n) {x y z : ℤ} (hxy : IsCoprime x y)
    (h : x ^ (2 * n) + y ^ (2 * n) = 2 * z ^ (2 * n)) : Odd x ∧ Odd y ∧ Odd z := by
  have h4 : ((x : ZMod 4) ^ 2) ^ n + ((y : ZMod 4) ^ 2) ^ n = 2 * ((z : ZMod 4) ^ 2) ^ n := by
    have := congrArg (fun t : ℤ => (t : ZMod 4)) h
    simpa [pow_mul] using this
  have hpos : n ≠ 0 := by omega
  have not_both_even : ¬ (Even x ∧ Even y) := by
    rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    have h2 : IsUnit (2 : ℤ) :=
      hxy.isUnit_of_dvd' (show (2 : ℤ) ∣ a + a from ⟨a, by ring⟩)
        (show (2 : ℤ) ∣ b + b from ⟨b, by ring⟩)
    rcases Int.isUnit_iff.mp h2 with h | h <;> omega
  have hx : Odd x := by
    by_contra hx
    rw [Int.not_odd_iff_even] at hx
    have hy : Odd y := by
      by_contra hy; rw [Int.not_odd_iff_even] at hy; exact not_both_even ⟨hx, hy⟩
    rw [sq_mod_four_of_even hx, sq_mod_four_of_odd hy, one_pow, zero_pow hpos] at h4
    rcases Int.even_or_odd z with hz | hz
    · rw [sq_mod_four_of_even hz, zero_pow hpos] at h4; revert h4; decide
    · rw [sq_mod_four_of_odd hz, one_pow] at h4; revert h4; decide
  have hy : Odd y := by
    by_contra hy
    rw [Int.not_odd_iff_even] at hy
    rw [sq_mod_four_of_even hy, sq_mod_four_of_odd hx, one_pow, zero_pow hpos] at h4
    rcases Int.even_or_odd z with hz | hz
    · rw [sq_mod_four_of_even hz, zero_pow hpos] at h4; revert h4; decide
    · rw [sq_mod_four_of_odd hz, one_pow] at h4; revert h4; decide
  refine ⟨hx, hy, ?_⟩
  by_contra hz
  rw [Int.not_odd_iff_even] at hz
  rw [sq_mod_four_of_odd hx, sq_mod_four_of_odd hy, sq_mod_four_of_even hz, one_pow,
    zero_pow hpos] at h4
  revert h4; decide

/-- The cofactor `Φ = x^{2n-2} - x^{2n-4} y^2 + ⋯ + y^{2n-2}`. -/
def Phi (n : ℕ) (x y : ℤ) : ℤ := ∑ i ∈ range n, (x ^ 2) ^ i * (-(y ^ 2)) ^ (n - 1 - i)

/-- For odd `n`, `x^{2n} + y^{2n} = (x^2 + y^2) Φ`. -/
theorem factor_Phi {n : ℕ} (hn : Odd n) (x y : ℤ) :
    x ^ (2 * n) + y ^ (2 * n) = (x ^ 2 + y ^ 2) * Phi n x y := by
  have := geom_sum₂_mul (x ^ 2) (-(y ^ 2)) n
  rw [hn.neg_pow, ← pow_mul, ← pow_mul] at this
  simp only [sub_neg_eq_add] at this
  rw [Phi, ← this]; ring

/-- `Φ ≡ n y^{2n-2} (mod x^2 + y^2)` for odd `n`. -/
theorem Phi_modEq {n : ℕ} (hn : Odd n) (x y : ℤ) :
    x ^ 2 + y ^ 2 ∣ Phi n x y - n * y ^ (2 * n - 2) := by
  have hev : Even (n - 1) := by obtain ⟨k, rfl⟩ := hn; exact ⟨k, by omega⟩
  have hy : y ^ (2 * n - 2) = (-(y ^ 2)) ^ (n - 1) := by
    rw [hev.neg_pow, ← pow_mul]; congr 1; omega
  set c : ℤ := -(y ^ 2) with hc
  have hsum : (n : ℤ) * c ^ (n - 1) = ∑ i ∈ range n, c ^ i * c ^ (n - 1 - i) := by
    rw [Finset.sum_congr rfl (g := fun _ => c ^ (n - 1)) (fun i hi => by
      rw [← pow_add]; congr 1; simp only [mem_range] at hi; omega)]
    simp
  have key : Phi n x y - n * y ^ (2 * n - 2) =
      ∑ i ∈ range n, ((x ^ 2) ^ i - c ^ i) * c ^ (n - 1 - i) := by
    rw [Phi, hy, hsum, ← sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  refine Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left ?_ _
  simpa [hc, sub_neg_eq_add] using sub_dvd_pow_sub_pow (x ^ 2) c i

lemma isCoprime_sq_add_sq_right {x y : ℤ} (h : IsCoprime x y) : IsCoprime (x ^ 2 + y ^ 2) y := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a ^ 2, -(a ^ 2 * y) + 2 * b - b ^ 2 * y, by linear_combination (a * x + 1 - b * y) * hab⟩

lemma isCoprime_sq_sub_sq {p q : ℤ} (h : IsCoprime p q) :
    IsCoprime (p ^ 2 - q ^ 2) p ∧ IsCoprime (p ^ 2 - q ^ 2) q := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨⟨-b ^ 2, b ^ 2 * p + 2 * a - a ^ 2 * p, by linear_combination (b * q + 1 - a * p) * hab⟩,
    ⟨a ^ 2, a ^ 2 * q + 2 * b - b ^ 2 * q, by linear_combination (a * p + 1 - b * q) * hab⟩⟩

/-- A common divisor of `x^2 + y^2` and `Φ` divides `n` (`x`, `y` coprime, `n` odd). -/
theorem dvd_n_of_dvd_both {n : ℕ} (hn : Odd n) {x y : ℤ} (hxy : IsCoprime x y) {d : ℤ}
    (h1 : d ∣ x ^ 2 + y ^ 2) (h2 : d ∣ Phi n x y) : d ∣ n := by
  have h3 : d ∣ n * y ^ (2 * n - 2) := by
    have h4 := dvd_sub h2 (h1.trans (Phi_modEq hn x y))
    simpa using h4
  have hc : IsCoprime d (y ^ (2 * n - 2)) :=
    ((isCoprime_sq_add_sq_right hxy).of_isCoprime_of_dvd_left h1).pow_right
  exact hc.dvd_of_dvd_mul_right h3

/-- The relative-primality flaw: `n = 5`, `x = 1`, `y = 3`, where `5` divides both
`x^2 + y^2 = 10` and `Φ = 5905`. -/
theorem Phi_counterexample : Phi 5 1 3 = 5905 ∧ (5 : ℤ) ∣ 1 ^ 2 + 3 ^ 2 ∧ (5 : ℤ) ∣ Phi 5 1 3 := by
  have h : Phi 5 1 3 = 5905 := by simp [Phi, Finset.sum_range_succ]
  exact ⟨h, ⟨2, by norm_num⟩, ⟨1181, by rw [h]; norm_num⟩⟩

/-- The second parametrisation and the quantities of system (1). -/
theorem system_one (p q : ℤ) :
    (p ^ 2 - q ^ 2 - 2 * p * q) + (p ^ 2 - q ^ 2 + 2 * p * q) = 2 * (p ^ 2 - q ^ 2) ∧
    (p ^ 2 - q ^ 2 + 2 * p * q) - (p ^ 2 - q ^ 2 - 2 * p * q) = 4 * (p * q) ∧
    (p ^ 2 - q ^ 2 + 2 * p * q) ^ 2 - (p ^ 2 - q ^ 2 - 2 * p * q) ^ 2 =
      8 * (p * q * (p ^ 2 - q ^ 2)) := by
  refine ⟨by ring, by ring, by ring⟩

/-- System (2): `P = U q + s V p`, `Q = U p - s V q`, `s = ±1`. -/
theorem system_two (U V p q s : ℤ) (hs : s ^ 2 = 1) :
    (U * q + s * V * p) ^ 2 + (U * p - s * V * q) ^ 2 = (U ^ 2 + V ^ 2) * (p ^ 2 + q ^ 2) ∧
    (U * q + s * V * p) ^ 2 - (U * p - s * V * q) ^ 2 =
      (U * (p + q) + s * V * (p - q)) * (U * (q - p) + s * V * (p + q)) ∧
    (U * q + s * V * p) ^ 2 - (U * p - s * V * q) ^ 2 =
      (p ^ 2 - q ^ 2) * (V ^ 2 - U ^ 2) + s * (4 * p * q * (U * V)) ∧
    (U * q + s * V * p) * (U * p - s * V * q) =
      (U ^ 2 - V ^ 2) * (p * q) + s * ((p ^ 2 - q ^ 2) * (U * V)) := by
  refine ⟨by linear_combination (V ^ 2 * (p ^ 2 + q ^ 2)) * hs, by ring,
    by linear_combination (V ^ 2 * (p ^ 2 - q ^ 2)) * hs,
    by linear_combination (-(V ^ 2 * p * q)) * hs⟩

/-- From system (2): `p q (p^2 - q^2)` divides `U V`, for `p`, `q` coprime of opposite parity. -/
theorem N_dvd_UV {p q U V H F s : ℤ} (hs : s ^ 2 = 1) (hpq : IsCoprime p q) (hpar : Odd (p + q))
    (h1 : (U * q + s * V * p) ^ 2 - (U * p - s * V * q) ^ 2 = H * (p ^ 2 - q ^ 2))
    (h2 : (U * q + s * V * p) * (U * p - s * V * q) = F * (p * q)) :
    p * q * (p ^ 2 - q ^ 2) ∣ U * V := by
  obtain ⟨hcp, hcq⟩ := isCoprime_sq_sub_sq hpq
  have hodd : Odd (p ^ 2 - q ^ 2) := by
    have e : p ^ 2 - q ^ 2 = (p + q) * (p + q - 2 * q) := by ring
    rw [e]
    obtain ⟨k, hk⟩ := id hpar
    exact hpar.mul ⟨k - q, by rw [hk]; ring⟩
  have hc2 : IsCoprime (p ^ 2 - q ^ 2) 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]; exact ⟨1, -k, by ring⟩
  have hc4 : IsCoprime (p ^ 2 - q ^ 2) 4 := by
    have := hc2.mul_right hc2; norm_num at this; exact this
  have hc4pq : IsCoprime (p ^ 2 - q ^ 2) (4 * p * q) := (hc4.mul_right hcp).mul_right hcq
  -- first equation
  have hX : s * (4 * p * q * (U * V)) = (p ^ 2 - q ^ 2) * (H - (V ^ 2 - U ^ 2)) := by
    linear_combination h1 - (V ^ 2 * (p ^ 2 - q ^ 2)) * hs
  have d1 : p ^ 2 - q ^ 2 ∣ 4 * p * q * (U * V) := by
    have h := dvd_mul_of_dvd_right (⟨_, hX⟩ : p ^ 2 - q ^ 2 ∣ s * (4 * p * q * (U * V))) s
    rwa [show s * (s * (4 * p * q * (U * V))) = 4 * p * q * (U * V) by
      linear_combination (4 * p * q * (U * V)) * hs] at h
  have e1 : p ^ 2 - q ^ 2 ∣ U * V := hc4pq.dvd_of_dvd_mul_left d1
  -- second equation
  have hY : s * ((p ^ 2 - q ^ 2) * (U * V)) = p * q * (F - (U ^ 2 - V ^ 2)) := by
    linear_combination h2 + (p * q * V ^ 2) * hs
  have d2 : p * q ∣ (p ^ 2 - q ^ 2) * (U * V) := by
    have h := dvd_mul_of_dvd_right (⟨_, hY⟩ : p * q ∣ s * ((p ^ 2 - q ^ 2) * (U * V))) s
    rwa [show s * (s * ((p ^ 2 - q ^ 2) * (U * V))) = (p ^ 2 - q ^ 2) * (U * V) by
      linear_combination ((p ^ 2 - q ^ 2) * (U * V)) * hs] at h
  have hpq' : IsCoprime (p * q) (p ^ 2 - q ^ 2) := (hcp.symm.mul_left hcq.symm)
  have e2 : p * q ∣ U * V := hpq'.dvd_of_dvd_mul_left d2
  exact hpq'.mul_dvd e2 e1

/-- The third decomposition: `U = U' u + s V' v`, `V = U' v - s V' u`. -/
theorem UV_identity (U' V' u v s : ℤ) (hs : s ^ 2 = 1) :
    (U' * u + s * V' * v) * (U' * v - s * V' * u) =
      (U' ^ 2 - V' ^ 2) * u * v + s * ((v ^ 2 - u ^ 2) * U' * V') := by
  linear_combination (-(V' ^ 2 * u * v)) * hs

/-- The page's conclusion from « l'un et l'autre signes »: *if* `N` divides both values of `UV`,
then `N ∣ 2 (v^2 - u^2) u v` (with `U'`, `V'` coprime). The hypothesis that both values are
divisible is the page's, and is not established. -/
theorem two_signs {N U' V' u v : ℤ} (hc : IsCoprime U' V')
    (hplus : N ∣ (U' ^ 2 - V' ^ 2) * u * v + (v ^ 2 - u ^ 2) * U' * V')
    (hminus : N ∣ (U' ^ 2 - V' ^ 2) * u * v - (v ^ 2 - u ^ 2) * U' * V') :
    N ∣ 2 * (v ^ 2 - u ^ 2) * u * v := by
  obtain ⟨c1, c2⟩ := isCoprime_sq_sub_sq hc
  obtain ⟨a, b, hab⟩ := c1.mul_right c2
  have hA : N ∣ 2 * ((U' ^ 2 - V' ^ 2) * u * v) := by
    have := dvd_add hplus hminus; convert this using 1; ring
  have hB : N ∣ 2 * ((v ^ 2 - u ^ 2) * U' * V') := by
    have := dvd_sub hplus hminus; convert this using 1; ring
  have e : 2 * (v ^ 2 - u ^ 2) * u * v =
      (a * (v ^ 2 - u ^ 2)) * (2 * ((U' ^ 2 - V' ^ 2) * u * v)) +
        (b * u * v) * (2 * ((v ^ 2 - u ^ 2) * U' * V')) := by
    linear_combination (-(2 * (v ^ 2 - u ^ 2) * u * v)) * hab
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hB _)

/-- The inequality `2(y^2 - x^2) > (x + y)^2` of view 709 holds only when `(x+y)(y-3x) > 0`. -/
theorem inequality_identity (x y : ℤ) :
    2 * (y ^ 2 - x ^ 2) - (x + y) ^ 2 = (x + y) * (y - 3 * x) := by
  ring

/-- The two cases of the reading: `p = 3`, `q = 2` gives `x = -7`, `y = 17`, where
`2(y^2-x^2) > (x+y)^2` but `(x+y)^2 < y^2`; with `x = 7`, `y = 17`, `2(y^2-x^2) < (x+y)^2`. -/
theorem inequality_counterexamples :
    ((3 : ℤ) ^ 2 - 2 ^ 2 - 2 * 3 * 2 = -7 ∧ (3 : ℤ) ^ 2 - 2 ^ 2 + 2 * 3 * 2 = 17) ∧
    ((-7 : ℤ) ^ 2 + 17 ^ 2 = 2 * 13 ^ 2 ∧ (-7 + 17 : ℤ) ^ 2 < 2 * (17 ^ 2 - (-7) ^ 2) ∧
      (-7 + 17 : ℤ) ^ 2 < 17 ^ 2) ∧
    ((7 : ℤ) ^ 2 + 17 ^ 2 = 2 * 13 ^ 2 ∧ 2 * ((17 : ℤ) ^ 2 - 7 ^ 2) < (7 + 17) ^ 2) := by
  norm_num

/-- The trivial case the conclusion « n = 1 » misses: `x^n = x` for `x = ±1` and `n` odd. -/
theorem trivial_case {n : ℕ} (hn : Odd n) {x : ℤ} (hx : x = 1 ∨ x = -1) : x ^ n = x := by
  rcases hx with rfl | rfl
  · simp
  · exact hn.neg_one_pow

/-- In `Z^{2n} = X^{2n} + Y^{2n}` (`n ≥ 1`), `X` and `Y` are not both odd. -/
theorem fermat_not_both_odd {n : ℕ} (hn : 1 ≤ n) {X Y Z : ℤ}
    (h : X ^ (2 * n) + Y ^ (2 * n) = Z ^ (2 * n)) : Even X ∨ Even Y := by
  by_contra hc
  push Not at hc
  have h4 : ((X : ZMod 4) ^ 2) ^ n + ((Y : ZMod 4) ^ 2) ^ n = ((Z : ZMod 4) ^ 2) ^ n := by
    have := congrArg (fun t : ℤ => (t : ZMod 4)) h
    simpa [pow_mul] using this
  have hpos : n ≠ 0 := by omega
  rw [sq_mod_four_of_odd hc.1, sq_mod_four_of_odd hc.2, one_pow] at h4
  rcases Int.even_or_odd Z with hz | hz
  · rw [sq_mod_four_of_even hz, zero_pow hpos] at h4; revert h4; decide
  · rw [sq_mod_four_of_odd hz, one_pow] at h4; revert h4; decide

/-- Fermat's equation with exponent `2n` has no solution in nonzero integers when `n` is even
(it contains `X^4 + Y^4 = W^4`). -/
theorem fermat_two_n_of_even {n : ℕ} (hn : Even n) : FermatLastTheoremWith ℤ (2 * n) := by
  obtain ⟨k, rfl⟩ := hn
  exact fermatLastTheoremFor_iff_int.mp (fermatLastTheoremFour.mono ⟨k, by ring⟩)

/-- The same when `3 ∣ n`. -/
theorem fermat_two_n_of_three_dvd {n : ℕ} (hn : 3 ∣ n) : FermatLastTheoremWith ℤ (2 * n) :=
  fermatLastTheoremFor_iff_int.mp (fermatLastTheoremThree.mono (dvd_mul_of_dvd_right hn 2))

/-- For even `n` the page's reduction fails: `Z + Y` need not divide `Z^n + Y^n` (`n = 2`). -/
theorem even_n_no_factor : ¬ ((3 : ℤ) + 1 ∣ 3 ^ 2 + 1 ^ 2) := by decide

/-! ## Quadratic residues -/

lemma not_sq_two_three : ¬ IsSquare ((2 : ℕ) : ZMod 3) := by unfold IsSquare; decide
lemma not_sq_two_five : ¬ IsSquare (2 : ZMod 5) := by unfold IsSquare; decide
lemma not_sq_three_seven : ¬ IsSquare ((3 : ℕ) : ZMod 7) := by unfold IsSquare; decide
lemma not_sq_five_seven : ¬ IsSquare ((5 : ℕ) : ZMod 7) := by unfold IsSquare; decide

lemma isSquare_of_mul_sq {F : Type*} [Field F] {a b c : F} (hb : b ≠ 0) (h : a * b ^ 2 = c ^ 2) :
    IsSquare a := by
  refine ⟨c / b, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb hb)]
  linear_combination h

lemma two_ne_zero_zmod {q : ℕ} (hq : 3 ≤ q) : (2 : ZMod q) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd two_pos this
  omega

/-- The fact the page uses without saying it: a divisor `m ≡ 1 (mod 4)` of `p - 1` is a residue
of `p`. -/
theorem residue_of_dvd_pred_one {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : m % 4 = 1)
    (hdvd : m ∣ p - 1) : IsSquare ((m : ℤ) : ZMod p) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hd : (m : ℤ) ∣ (p : ℤ) - 1 := by
    have := Int.natCast_dvd_natCast.mpr hdvd
    rwa [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at this
  apply ZMod.isSquare_of_jacobiSym_eq_one
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hm hpodd]
  have hmod : (p : ℤ) ≡ 1 [ZMOD m] := (Int.modEq_iff_dvd.mpr hd).symm
  rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]

/-- A divisor `m ≡ 3 (mod 4)` of `p - 1` is a residue of `p` when taken with the sign `-`. -/
theorem neg_residue_of_dvd_pred_three {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : m % 4 = 3)
    (hdvd : m ∣ p - 1) : IsSquare ((-(m : ℤ) : ℤ) : ZMod p) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  have hd : (m : ℤ) ∣ (p : ℤ) - 1 := by
    have := Int.natCast_dvd_natCast.mpr hdvd
    rwa [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at this
  apply ZMod.isSquare_of_jacobiSym_eq_one
  have hmod : (p : ℤ) ≡ 1 [ZMOD m] := (Int.modEq_iff_dvd.mpr hd).symm
  rw [jacobiSym.neg _ hpodd, jacobiSym.quadratic_reciprocity hmodd hpodd,
    jacobiSym.mod_left' hmod, jacobiSym.one_left, mul_one,
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hpodd), ← pow_add,
    show p / 2 + m / 2 * (p / 2) = 2 * ((m / 4 + 1) * (p / 2)) by
      rw [show m / 2 = 2 * (m / 4) + 1 by omega]; ring, pow_mul]
  simp

/-- View 704, case `p = 8K' + 3`: `2` is a non-residue, by `-1 ≡ 2 · (p-1)/2`. -/
theorem two_nonresidue_of_three_mod_eight {p : ℕ} [Fact p.Prime] (hp : p % 8 = 3) :
    ¬ IsSquare (2 : ZMod p) := by
  set m := (p - 1) / 2 with hmdef
  have hpm : p = 2 * m + 1 := by omega
  have hm := residue_of_dvd_pred_one (p := p) (m := m) (by omega) (by omega) ⟨2, by omega⟩
  have hneg1 : ¬ IsSquare (-1 : ZMod p) := by rw [ZMod.exists_sq_eq_neg_one_iff]; omega
  have hz : (2 * (m : ZMod p) + 1) = 0 := by
    have : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by rw [← hpm]; exact ZMod.natCast_self p
    exact_mod_cast this
  rintro ⟨r, hr⟩
  obtain ⟨s, hs⟩ := hm
  rw [Int.cast_natCast] at hs
  apply hneg1
  exact ⟨r * s, by linear_combination -hz + (m : ZMod p) * hr + r * r * hs⟩

/-- View 704, case `p = 8K' + 7`: `2` is a residue. -/
theorem two_residue_of_seven_mod_eight {p : ℕ} [Fact p.Prime] (hp : p % 8 = 7) :
    IsSquare (2 : ZMod p) := by
  set m := (p - 1) / 2 with hmdef
  have hpm : p = 2 * m + 1 := by omega
  have hm := neg_residue_of_dvd_pred_three (p := p) (m := m) (by omega) (by omega) ⟨2, by omega⟩
  have hz : (2 * (m : ZMod p) + 1) = 0 := by
    have : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by rw [← hpm]; exact ZMod.natCast_self p
    exact_mod_cast this
  obtain ⟨s, hs⟩ := hm
  push_cast at hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : (1 : ZMod p) = 0 := by linear_combination hz + 2 * hs
    exact one_ne_zero this
  exact isSquare_of_mul_sq (c := 1) hs0 (by linear_combination -2 * hs - hz)

/-- View 704, case `p = 4n + 1` with `n` divisible by an odd power of `2`, that is
`p = 2^{2k+3} w + 1`, `w` odd: `2` is a residue. -/
theorem two_residue_of_odd_two_power {p k w : ℕ} [Fact p.Prime] (hw : Odd w)
    (hp : p = 2 ^ (2 * k + 3) * w + 1) : IsSquare (2 : ZMod p) := by
  have h8 : 2 ^ (2 * k + 3) = 8 * 2 ^ (2 * k) := by ring
  have hw1 : 1 ≤ w := hw.pos
  have hpos : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
  obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ (2 * k) * w := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; positivity
  have hpX : p = 8 * X + 1 := by rw [hp, h8, hX, mul_assoc]
  have hp4 : p % 4 = 1 := by omega
  have hp9 : 9 ≤ p := by omega
  have hdvd : w ∣ p - 1 := ⟨2 ^ (2 * k + 3), by rw [hp]; simp [mul_comm]⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨t, ht⟩ : IsSquare (-1 : ZMod p) := by rw [ZMod.exists_sq_eq_neg_one_iff]; omega
  have hws : IsSquare (w : ZMod p) := by
    have hw2 := Nat.odd_iff.mp hw
    rcases (by omega : w % 4 = 1 ∨ w % 4 = 3) with h | h
    · have := residue_of_dvd_pred_one hp2 h hdvd
      rwa [Int.cast_natCast] at this
    · obtain ⟨u, hu⟩ := neg_residue_of_dvd_pred_three hp2 h hdvd
      push_cast at hu
      exact ⟨t * u, by linear_combination -hu + u * u * ht⟩
  obtain ⟨s, hs⟩ := hws
  have hz : (2 : ZMod p) ^ (2 * k + 3) * w + 1 = 0 := by
    have : ((2 ^ (2 * k + 3) * w + 1 : ℕ) : ZMod p) = 0 := by
      rw [← hp]; exact ZMod.natCast_self p
    exact_mod_cast this
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : (1 : ZMod p) = 0 := by linear_combination hz - (2 : ZMod p) ^ (2 * k + 3) * hs
    exact one_ne_zero this
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod (by omega)
  refine isSquare_of_mul_sq (b := 2 ^ (k + 1) * s) (c := t) (mul_ne_zero (pow_ne_zero _ h2) hs0) ?_
  linear_combination (-(2 : ZMod p) ^ (2 * k + 3)) * hs + hz + ht

/-- View 706: if `P` is a residue of a prime `p ≡ 1 (mod 4)`, so is `-P`. -/
theorem neg_residue_of_one_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) {P : ZMod p}
    (h : IsSquare P) : IsSquare (-P) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨t, ht⟩ : IsSquare (-1 : ZMod p) := by rw [ZMod.exists_sq_eq_neg_one_iff]; omega
  exact ⟨t * r, by linear_combination r * r * ht - hr⟩

/-- View 706: the page's expansion of `(a^2+b^2)(p₁^2+p₂^2+p₃^2+p₄^2)`, `s = ±1`. -/
theorem four_square_expansion (a b p₁ p₂ p₃ p₄ s : ℤ) (hs : s ^ 2 = 1) :
    (a ^ 2 + b ^ 2) * (p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2) =
      (a * p₁ + s * b * p₂) ^ 2 + (b * p₁ - s * a * p₂) ^ 2 + (a * p₃ + s * b * p₄) ^ 2 +
        (a * p₄ - s * b * p₃) ^ 2 := by
  linear_combination (-((a ^ 2 + b ^ 2) * p₂ ^ 2 + b ^ 2 * (p₃ ^ 2 + p₄ ^ 2))) * hs

/-- A squarefree number with no odd prime factor is `1` or `2`. -/
lemma squarefree_no_odd_prime {s : ℕ} (hs : Squarefree s)
    (h : ∀ q, q.Prime → q ∣ s → q = 2) : s = 1 ∨ s = 2 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hs.ne_zero
  have hm1 : m = 1 := by
    by_contra hm1
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd hm1
    have := h r hr (dvd_mul_of_dvd_right hrm _)
    subst this
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hrm)
  subst hm1
  have hk : k < 2 := by
    by_contra hk
    have h4 : (2 : ℕ) ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := hs 2 (by rw [mul_one]; simpa [sq] using h4)
    exact absurd (Nat.isUnit_iff.mp this) (by norm_num)
  interval_cases k <;> simp

/-- The key step: an integer that is not a square has Jacobi symbol `-1` at some odd `N`. -/
theorem exists_jacobiSym_eq_neg_one {a : ℤ} (ha : ¬ IsSquare a) : ∃ N : ℕ, jacobiSym a N = -1 := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  obtain ⟨s, b, hs0, hb0, hbs, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr ha0)
  have hA : (a.natAbs : ℤ) = (b : ℤ) ^ 2 * s := by rw [← hbs]; push_cast; ring
  have hsign : a = (b : ℤ) ^ 2 * s ∨ a = -((b : ℤ) ^ 2 * s) := by
    rcases Int.natAbs_eq a with h | h
    · exact Or.inl (h.trans hA)
    · exact Or.inr (h.trans (congrArg Neg.neg hA))
  by_cases hq : ∃ q, q.Prime ∧ q ≠ 2 ∧ q ∣ s
  · obtain ⟨q, hqp, hq2, s', hs'⟩ := hq
    have := Fact.mk hqp
    have hs'0 : 0 < s' := Nat.pos_of_ne_zero (by rintro rfl; simp at hs'; omega)
    have hqs' : ¬ q ∣ s' := by
      rintro ⟨t, rfl⟩
      have := hsf q ⟨t, by rw [hs']; ring⟩
      exact hqp.one_lt.ne' (Nat.isUnit_iff.mp this)
    obtain ⟨e, b', hqb', hb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb0.ne' q hqp.one_lt.ne'
    obtain ⟨c0, hc0⟩ := FiniteField.exists_nonsquare (F := ZMod q)
      (by rw [ZMod.ringChar_zmod_n]; exact hq2)
    set K := 4 * s' * b' with hK
    have hcop : Nat.Coprime q K := by
      have h2 : Nat.Coprime q 2 := (Nat.coprime_primes hqp Nat.prime_two).mpr hq2
      have h4 : Nat.Coprime q 4 := by simpa using h2.pow_right 2
      exact (h4.mul_right ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqs')).mul_right
        ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqb')
    obtain ⟨N, hNq, hNK⟩ := Nat.chineseRemainder hcop c0.val 1
    have hN4 : N % 4 = 1 := by
      have := Nat.ModEq.of_dvd (show 4 ∣ K from ⟨s' * b', by rw [hK]; ring⟩) hNK
      unfold Nat.ModEq at this; omega
    have hNodd : Odd N := Nat.odd_iff.mpr (by omega)
    have hcN : (N : ZMod q) = c0 := by
      have hNq' : N % q = c0.val % q := hNq
      rw [← ZMod.natCast_mod N q, hNq', ZMod.natCast_mod, ZMod.natCast_zmod_val]
    have hqN : ¬ q ∣ N := by
      intro h
      rw [← ZMod.natCast_eq_zero_iff, hcN] at h
      exact hc0 ⟨0, by rw [h]; simp⟩
    have hb'N : Nat.Coprime b' N := by
      have := Nat.ModEq.of_dvd (show b' ∣ K from ⟨4 * s', by rw [hK]; ring⟩) hNK
      exact (show Nat.Coprime N b' from (Nat.ModEq.gcd_eq this).trans (Nat.gcd_one_left b')).symm
    have hbN : Nat.Coprime b N := by
      rw [hb]
      exact Nat.coprime_mul_iff_left.mpr
        ⟨Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqN), hb'N⟩
    have hgcd : Int.gcd (b : ℤ) (N : ℤ) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp (Nat.isCoprime_iff_coprime.mpr hbN)
    have hJq : jacobiSym (q : ℤ) N = -1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' (hqp.odd_of_ne_two hq2) hN4,
        ZMod.nonsquare_iff_jacobiSym_eq_neg_one, Int.cast_natCast, hcN]
      exact hc0
    have hJs : jacobiSym (s' : ℤ) N = 1 := by
      rw [jacobiSym.mod_right' s' hNodd]
      have : N % (4 * s') = 1 := by
        have := Nat.ModEq.of_dvd (show 4 * s' ∣ K from ⟨b', by rw [hK]⟩) hNK
        unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_of_lt (by omega)
      rw [this, jacobiSym.one_right]
    refine ⟨N, ?_⟩
    have hsq : (s : ℤ) = (q : ℤ) * s' := by rw [hs']; push_cast; ring
    rcases hsign with h | h
    · rw [h, hsq, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.sq_one' hgcd, hJq, hJs]
      norm_num
    · rw [h, hsq, jacobiSym.neg _ hNodd, ZMod.χ₄_nat_one_mod_four hN4, jacobiSym.mul_left,
        jacobiSym.mul_left, jacobiSym.sq_one' hgcd, hJq, hJs]
      norm_num
  · push Not at hq
    have h' : ∀ q, q.Prime → q ∣ s → q = 2 := fun q hqp hd => by
      by_contra h; exact hq q hqp h hd
    obtain ⟨j, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd hb0.ne'
    obtain ⟨t, rfl⟩ := hm
    obtain ⟨X, hX⟩ : ∃ X : ℕ, X = 2 * t ^ 2 + 2 * t := ⟨_, rfl⟩
    have hbZ : (b : ℤ) = 2 ^ j * (2 * t + 1) := by rw [hbm]; push_cast; ring
    have hXZ : (X : ℤ) = 2 * t ^ 2 + 2 * t := by rw [hX]; push_cast; ring
    have cop3 : IsCoprime (b : ℤ) ((8 * X + 3 : ℕ) : ℤ) := by
      rw [hbZ]; push_cast
      refine IsCoprime.mul_left (IsCoprime.pow_left ⟨-(4 * X + 1), 1, by ring⟩)
        ⟨8 * t + 4, -1, by linear_combination (-8) * hXZ⟩
    have cop5 : IsCoprime (b : ℤ) ((8 * X + 5 : ℕ) : ℤ) := by
      rw [hbZ]; push_cast
      refine IsCoprime.mul_left (IsCoprime.pow_left ⟨-(4 * X + 2), 1, by ring⟩)
        ⟨-(8 * t + 4), 1, by linear_combination 8 * hXZ⟩
    have g3 := Int.isCoprime_iff_gcd_eq_one.mp cop3
    have g5 := Int.isCoprime_iff_gcd_eq_one.mp cop5
    have o3 : Odd (8 * X + 3) := Nat.odd_iff.mpr (by omega)
    have o5 : Odd (8 * X + 5) := Nat.odd_iff.mpr (by omega)
    rcases squarefree_no_odd_prime hsf h' with rfl | rfl
    · rcases hsign with h | h
      · exact absurd ⟨(b : ℤ), by rw [h]; push_cast; ring⟩ ha
      · refine ⟨8 * X + 3, ?_⟩
        rw [h]; push_cast; rw [mul_one, jacobiSym.neg _ o3, jacobiSym.sq_one' g3,
          ZMod.χ₄_nat_three_mod_four (by omega)]
        norm_num
    · rcases hsign with h | h
      · refine ⟨8 * X + 3, ?_⟩
        rw [h]; push_cast
        rw [jacobiSym.mul_left, jacobiSym.sq_one' g3, jacobiSym.at_two o3,
          ZMod.χ₈_nat_eq_if_mod_eight]
        simp [show (8 * X + 3) % 2 = 1 by omega, show (8 * X + 3) % 8 = 3 by omega]
      · refine ⟨8 * X + 5, ?_⟩
        rw [h]; push_cast
        rw [show -((b : ℤ) ^ 2 * 2) = (b : ℤ) ^ 2 * (-2) by ring, jacobiSym.mul_left,
          jacobiSym.sq_one' g5, jacobiSym.at_neg_two o5, ZMod.χ₈'_nat_eq_if_mod_eight]
        simp [show (8 * X + 5) % 2 = 1 by omega, show (8 * X + 5) % 8 = 5 by omega]

/-- View 722: « Tout nombre, excepté les quarrés positivement pris, est non résidu de quelque
nombre premier »: an integer that is not a square is a non-residue of some prime not dividing it. -/
theorem exists_prime_nonresidue {a : ℤ} (ha : ¬ IsSquare a) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ ¬ IsSquare (a : ZMod p) := by
  obtain ⟨N, hN⟩ := exists_jacobiSym_eq_neg_one ha
  obtain ⟨p, hp, -, hJ⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hN
  have := Fact.mk hp
  have hns := ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hJ
  refine ⟨p, hp, fun hd => hns ⟨0, ?_⟩, hns⟩
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hd, mul_zero]

/-- The converse: a square is a residue of every prime. -/
theorem isSquare_zmod_of_isSquare {a : ℤ} (ha : IsSquare a) (p : ℕ) : IsSquare (a : ZMod p) := by
  obtain ⟨r, rfl⟩ := ha
  exact ⟨r, by push_cast; ring⟩

lemma prime_divisor_nonresidue {a : ℤ} {M : ℕ} (h : jacobiSym a M = -1) :
    ∃ q, q.Prime ∧ q ∣ M ∧ ¬ IsSquare ((a : ℤ) : ZMod q) := by
  obtain ⟨q, hq, hd, hJ⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one h
  have := Fact.mk hq
  exact ⟨q, hq, hd, ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hJ⟩

/-- View 722: a number `m ≡ 2 (mod 4)` is a non-residue of a prime `q ≡ 3 (mod 4)` (via `m + 1`). -/
theorem four_n_two_nonresidue {m : ℕ} (hm : m % 4 = 2) :
    ∃ q, q.Prime ∧ q % 4 = 3 ∧ ¬ IsSquare (m : ZMod q) := by
  have hodd : Odd (m + 1) := Nat.odd_iff.mpr (by omega)
  have hJ : jacobiSym (-1) (m + 1) = -1 := by
    rw [jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four (by omega)]
  obtain ⟨q, hq, hqM, hns⟩ := prime_divisor_nonresidue hJ
  have := Fact.mk hq
  have hns' : ¬ IsSquare (-1 : ZMod q) := by simpa using hns
  have hq4 : q % 4 = 3 := by
    by_contra h; exact hns' (ZMod.exists_sq_eq_neg_one_iff.mpr h)
  have hmq : (m : ZMod q) = -1 := by
    have := (ZMod.natCast_eq_zero_iff (m + 1) q).mpr hqM
    push_cast at this; linear_combination this
  exact ⟨q, hq, hq4, by rw [hmq]; exact hns'⟩

/-- View 720: a number `N ≡ 3 (mod 4)`, `N ≥ 7`, prime or not, taken negatively, is a non-residue
of a prime `q ≡ 3 (mod 4)` smaller than `N` (via `N - 4`). -/
theorem neg_nonresidue_smaller {N : ℕ} (hN : N % 4 = 3) (h7 : 7 ≤ N) :
    ∃ q, q.Prime ∧ q < N ∧ q % 4 = 3 ∧ ¬ IsSquare (-(N : ZMod q)) := by
  have hodd : Odd (N - 4) := Nat.odd_iff.mpr (by omega)
  have hJ : jacobiSym (-1) (N - 4) = -1 := by
    rw [jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four (by omega)]
  obtain ⟨q, hq, hqM, hns⟩ := prime_divisor_nonresidue hJ
  have := Fact.mk hq
  have hns' : ¬ IsSquare (-1 : ZMod q) := by simpa using hns
  have hq4 : q % 4 = 3 := by
    by_contra h; exact hns' (ZMod.exists_sq_eq_neg_one_iff.mpr h)
  have hlt : q < N := by have := Nat.le_of_dvd (by omega) hqM; omega
  have hNq : (N : ZMod q) = 4 := by
    have := (ZMod.natCast_eq_zero_iff (N - 4) q).mpr hqM
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; linear_combination this
  refine ⟨q, hq, hlt, hq4, ?_⟩
  rw [hNq]
  rintro ⟨r, hr⟩
  exact hns' (isSquare_of_mul_sq (b := 2) (c := r) (two_ne_zero_zmod (by omega))
    (by linear_combination hr))

/-- View 720: a number `N ≡ 3 (mod 4)`, `N ≥ 7`, taken positively, is a non-residue of a prime
smaller than `N` (via `N - 8` if `N ≡ 3`, `N - 2` if `N ≡ 7 (mod 8)`). -/
theorem pos_nonresidue_smaller {N : ℕ} (hN : N % 4 = 3) (h7 : 7 ≤ N) :
    ∃ q, q.Prime ∧ q < N ∧ ¬ IsSquare (N : ZMod q) := by
  rcases (by omega : N % 8 = 3 ∨ N % 8 = 7) with h8 | h8
  · have hodd : Odd (N - 8) := Nat.odd_iff.mpr (by omega)
    have hJ : jacobiSym 2 (N - 8) = -1 := by
      rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [show (N - 8) % 2 = 1 by omega, show (N - 8) % 8 = 3 by omega]
    obtain ⟨q, hq, hqM, hns⟩ := prime_divisor_nonresidue hJ
    have := Fact.mk hq
    have hq2 : q ≠ 2 := by rintro rfl; omega
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have hlt : q < N := by have := Nat.le_of_dvd (by omega) hqM; omega
    have hNq : (N : ZMod q) = 8 := by
      have := (ZMod.natCast_eq_zero_iff (N - 8) q).mpr hqM
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this; linear_combination this
    refine ⟨q, hq, hlt, ?_⟩
    rw [hNq]
    rintro ⟨r, hr⟩
    exact hns (isSquare_of_mul_sq (b := 2) (c := r) (two_ne_zero_zmod hq3)
      (by push_cast; linear_combination hr))
  · have hodd : Odd (N - 2) := Nat.odd_iff.mpr (by omega)
    have hJ : jacobiSym 2 (N - 2) = -1 := by
      rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [show (N - 2) % 2 = 1 by omega, show (N - 2) % 8 = 5 by omega]
    obtain ⟨q, hq, hqM, hns⟩ := prime_divisor_nonresidue hJ
    have hlt : q < N := by have := Nat.le_of_dvd (by omega) hqM; omega
    have hNq : (N : ZMod q) = 2 := by
      have := (ZMod.natCast_eq_zero_iff (N - 2) q).mpr hqM
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this; linear_combination this
    refine ⟨q, hq, hlt, ?_⟩
    rw [hNq]
    simpa using hns

/-- The exception `p = 3`: `±3` is a residue of the only smaller prime. -/
theorem three_exception : ∀ q, q.Prime → q < 3 →
    IsSquare ((3 : ℕ) : ZMod q) ∧ IsSquare (-((3 : ℕ) : ZMod q)) := by
  intro q hq hlt
  interval_cases q
  · norm_num at hq
  · norm_num at hq
  · exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

/-- View 720, the false extension: `-5`, `-17`, `-21` are residues of every prime `q ≡ 3 (mod 4)`
smaller than them (those dividing them included, `0` being a square). -/
theorem false_extension :
    (∀ q, q.Prime → q % 4 = 3 → q < 5 → IsSquare (-(5 : ZMod q))) ∧
    (∀ q, q.Prime → q % 4 = 3 → q < 17 → IsSquare (-(17 : ZMod q))) ∧
    (∀ q, q.Prime → q % 4 = 3 → q < 21 → IsSquare (-(21 : ZMod q))) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq h4 hlt <;> interval_cases q <;>
    first | omega | (unfold IsSquare; decide) | (norm_num at hq)

/-- Views 718–719: for `p = 19`, the even `a` just above `√(19/3)` is `4`, and
`3a^2 - p = 29 > p`. -/
theorem nineteen_exception :
    3 * 2 ^ 2 < 19 ∧ 19 < 3 * 4 ^ 2 ∧ 19 < 3 * 4 ^ 2 - 19 ∧ ¬ IsSquare (19 : ZMod 7) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by unfold IsSquare; decide⟩

/-- View 726: `3` is a residue of `11` though `11` is not of the form `3m + b^2`. -/
theorem three_eleven : IsSquare (3 : ZMod 11) ∧ ¬ ∃ m b : ℤ, (11 : ℤ) = 3 * m + b ^ 2 := by
  refine ⟨⟨5, by decide⟩, ?_⟩
  rintro ⟨m, b, h⟩
  have := congrArg (fun t : ℤ => (t : ZMod 3)) h
  push_cast at this
  revert this
  generalize (m : ZMod 3) = c
  generalize (b : ZMod 3) = d
  revert c d
  decide

/-- View 728: for a prime `p ≡ 3 (mod 4)`, if `n` is a non-residue, `-n` is a residue. -/
theorem neg_residue_of_nonresidue {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {n : ZMod p}
    (h : ¬ IsSquare n) : IsSquare (-n) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact h ⟨0, by simp⟩
  have hn : n ^ (p / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one p hn0).resolve_left
      (fun h1 => h ((ZMod.euler_criterion p hn0).mpr h1))
  have hodd : Odd (p / 2) := Nat.odd_iff.mpr (by omega)
  rw [ZMod.euler_criterion p (neg_ne_zero.mpr hn0), neg_pow, hn, hodd.neg_one_pow]
  norm_num

/-- View 728: for primes `p ≡ 11 (mod 12)`, `3` is a residue and `-3` a non-residue. -/
theorem twelve_n_eleven {p : ℕ} [Fact p.Prime] (hp : p % 12 = 11) :
    IsSquare (3 : ZMod p) ∧ ¬ IsSquare (-3 : ZMod p) := by
  have h3 : IsSquare (3 : ZMod p) := by
    have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 3) (by omega)
      (by norm_num) (by omega)
    rw [Nat.cast_ofNat] at this
    rw [this, ← ZMod.natCast_mod, show p % 3 = 2 by omega]
    exact not_sq_two_three
  refine ⟨h3, ?_⟩
  obtain ⟨r, hr⟩ := h3
  have hneg1 : ¬ IsSquare (-1 : ZMod p) := by rw [ZMod.exists_sq_eq_neg_one_iff]; omega
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : ((3 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat, hr]; ring
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rintro ⟨s, hs⟩
  exact hneg1 (isSquare_of_mul_sq (b := r) (c := s) hr0
    (by linear_combination hs - (-1 : ZMod p) * hr))

/-- View 728: a prime dividing `a^2 + a + 1` has `-3` as a residue, by
`4(a^2+a+1) = (2a+1)^2 + 3`; hence no prime `12n + 11` divides `a^2 + a + 1`. -/
theorem neg_three_of_dvd {p : ℕ} {a : ZMod p} (h : a ^ 2 + a + 1 = 0) : IsSquare (-3 : ZMod p) :=
  ⟨2 * a + 1, by linear_combination (-4) * h⟩

theorem cube_identity (a : ℤ) : 4 * (a ^ 3 - 1) = (a - 1) * ((2 * a + 1) ^ 2 + 3) := by ring

theorem twelve_n_eleven_not_dvd {p : ℕ} [Fact p.Prime] (hp : p % 12 = 11) (a : ZMod p) :
    a ^ 2 + a + 1 ≠ 0 :=
  fun h => (twelve_n_eleven hp).2 (neg_three_of_dvd h)

/-! ## Primitive roots and Fermat primes -/

/-- View 729: `3` is a primitive root of every prime `12n + 5` for which `3n + 1` is prime. -/
theorem three_primitive_root {n : ℕ} (hq : (3 * n + 1).Prime) (hp : (12 * n + 5).Prime) :
    IsPrimitiveRoot (3 : ZMod (12 * n + 5)) (12 * n + 4) := by
  have := Fact.mk hp
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · norm_num at hq
    · exact h
  have hp2 : Fact (2 < 12 * n + 5) := ⟨by omega⟩
  have h3 : ¬ IsSquare (3 : ZMod (12 * n + 5)) := by
    have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 12 * n + 5) (q := 3) (by omega)
      (by norm_num)
    rw [Nat.cast_ofNat] at this
    rw [this, ← ZMod.natCast_mod, show (12 * n + 5) % 3 = 2 by omega]
    exact not_sq_two_three
  have h30 : (3 : ZMod (12 * n + 5)) ≠ 0 := by rintro h; exact h3 ⟨0, by rw [h]; simp⟩
  have hhalf : (3 : ZMod (12 * n + 5)) ^ ((12 * n + 5) / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one _ h30).resolve_left
      (fun h1 => h3 ((ZMod.euler_criterion _ h30).mpr h1))
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime
  · have := ZMod.pow_card_sub_one_eq_one h30
    simpa using this
  · intro r hr hrd
    have hrd' : r ∣ 4 * (3 * n + 1) := by rw [show 4 * (3 * n + 1) = 12 * n + 4 by ring]; exact hrd
    rcases (Nat.Prime.dvd_mul hr).mp hrd' with h | h
    · have hr2 : r = 2 := by
        have : r ∣ 2 ^ 2 := by simpa using h
        exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow this)
      subst hr2
      rw [show (12 * n + 4) / 2 = (12 * n + 5) / 2 by omega, hhalf]
      exact ZMod.neg_one_ne_one
    · have hrq : r = 3 * n + 1 := (Nat.prime_dvd_prime_iff_eq hr hq).mp h
      subst hrq
      rw [show (12 * n + 4) / (3 * n + 1) = 4 by
        rw [show 12 * n + 4 = 4 * (3 * n + 1) by ring]; exact Nat.mul_div_cancel _ (by omega)]
      intro h81
      have : ((80 : ℕ) : ZMod (12 * n + 5)) = 0 := by
        push_cast; linear_combination h81
      rw [ZMod.natCast_eq_zero_iff] at this
      have hle := Nat.le_of_dvd (by norm_num) this
      have : n ≤ 6 := by omega
      interval_cases n <;> omega

/-- `F_k ≡ 2 (mod F_j)` for `j < k`. -/
theorem fermatNumber_mod {j k : ℕ} (hjk : j < k) : Nat.fermatNumber k % Nat.fermatNumber j = 2 := by
  have hd : Nat.fermatNumber j ∣ Nat.fermatNumber k - 2 := by
    rw [← Nat.prod_fermatNumber]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hjk)
  obtain ⟨c, hc⟩ := hd
  have h2 := Nat.two_lt_fermatNumber k
  have h3 := Nat.two_lt_fermatNumber j
  rw [show Nat.fermatNumber k = 2 + Nat.fermatNumber j * c by omega, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h3

theorem fermatNumber_mod_four {k : ℕ} (hk : 1 ≤ k) : Nat.fermatNumber k % 4 = 1 := by
  have : 4 ∣ 2 ^ 2 ^ k := by
    have h : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    obtain ⟨c, hc⟩ := pow_dvd_pow 2 h
    exact ⟨c, by rw [hc]; norm_num⟩
  unfold Nat.fermatNumber; omega

/-- View 730: for Fermat primes `F_j < F_k`, `F_j` is a residue of `F_k` iff `2` is a residue
of `F_j`. -/
theorem fermat_residue_iff {j k : ℕ} (hjk : j < k) (hj : (Nat.fermatNumber j).Prime)
    (hk : (Nat.fermatNumber k).Prime) :
    IsSquare ((Nat.fermatNumber j : ℕ) : ZMod (Nat.fermatNumber k)) ↔
      IsSquare (2 : ZMod (Nat.fermatNumber j)) := by
  have := Fact.mk hj
  have := Fact.mk hk
  rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (fermatNumber_mod_four (by omega))
    (by have := Nat.two_lt_fermatNumber j; omega), ← ZMod.natCast_mod, fermatNumber_mod hjk,
    Nat.cast_ofNat]

/-- `3` and `5` are non-residues of every larger Fermat prime. -/
theorem three_nonresidue_fermat {k : ℕ} (hk1 : 1 ≤ k) (hk : (Nat.fermatNumber k).Prime) :
    ¬ IsSquare (3 : ZMod (Nat.fermatNumber k)) := by
  have := fermat_residue_iff (j := 0) (by omega) (by norm_num) hk
  rw [show ((Nat.fermatNumber 0 : ℕ) : ZMod (Nat.fermatNumber k)) = 3 by simp] at this
  rw [this]; exact not_sq_two_three

theorem five_nonresidue_fermat {k : ℕ} (hk2 : 2 ≤ k) (hk : (Nat.fermatNumber k).Prime) :
    ¬ IsSquare (5 : ZMod (Nat.fermatNumber k)) := by
  have := fermat_residue_iff (j := 1) (by omega) (by norm_num) hk
  rw [show ((Nat.fermatNumber 1 : ℕ) : ZMod (Nat.fermatNumber k)) = 5 by simp] at this
  rw [this]; exact not_sq_two_five

/-- From `17` on, a smaller Fermat prime is a residue of a larger one: the page's « cela est
faux » is right. -/
theorem fermat_residue_of_two_le {j k : ℕ} (hj2 : 2 ≤ j) (hjk : j < k)
    (hj : (Nat.fermatNumber j).Prime) (hk : (Nat.fermatNumber k).Prime) :
    IsSquare ((Nat.fermatNumber j : ℕ) : ZMod (Nat.fermatNumber k)) := by
  rw [fermat_residue_iff hjk hj hk]
  have := Fact.mk hj
  rw [ZMod.exists_sq_eq_two_iff (by have := Nat.two_lt_fermatNumber j; omega)]
  left
  have : 8 ∣ 2 ^ 2 ^ j := by
    have h : 3 ≤ 2 ^ j := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    obtain ⟨c, hc⟩ := pow_dvd_pow 2 h
    exact ⟨c, by rw [hc]; norm_num⟩
  unfold Nat.fermatNumber; omega

theorem seventeen_residue :
    IsSquare ((17 : ℕ) : ZMod 257) ∧ IsSquare ((17 : ℕ) : ZMod 65537) ∧
      IsSquare ((257 : ℕ) : ZMod 65537) := by
  have p17 : (Nat.fermatNumber 2).Prime := by norm_num
  have p257 : (Nat.fermatNumber 3).Prime := by norm_num [Nat.fermatNumber]
  have p65537 : (Nat.fermatNumber 4).Prime := by norm_num [Nat.fermatNumber]
  have a := fermat_residue_of_two_le (le_refl 2) (by norm_num : 2 < 3) p17 p257
  have b := fermat_residue_of_two_le (le_refl 2) (by norm_num : 2 < 4) p17 p65537
  have c := fermat_residue_of_two_le (by norm_num : 2 ≤ 3) (by norm_num : 3 < 4) p257 p65537
  simp only [Nat.fermatNumber, Nat.reducePow, Nat.reduceAdd] at a b c
  exact ⟨a, b, c⟩

/-- Every non-residue of a Fermat prime is a primitive root. -/
theorem fermat_primitive_root {k : ℕ} (hk : (Nat.fermatNumber k).Prime)
    {a : ZMod (Nat.fermatNumber k)} (ha : ¬ IsSquare a) :
    IsPrimitiveRoot a (Nat.fermatNumber k - 1) := by
  have := Fact.mk hk
  have : Fact (2 < Nat.fermatNumber k) := ⟨Nat.two_lt_fermatNumber k⟩
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have hhalf : a ^ (Nat.fermatNumber k / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one _ ha0).resolve_left
      (fun h1 => ha ((ZMod.euler_criterion _ ha0).mpr h1))
  set m := 2 ^ k - 1 with hm
  have hk2 : 2 ^ k = m + 1 := by have := Nat.one_le_two_pow (n := k); omega
  have hF : Nat.fermatNumber k = 2 * 2 ^ m + 1 := by
    rw [Nat.fermatNumber, hk2, pow_succ]; ring
  have hF1 : Nat.fermatNumber k - 1 = 2 ^ (m + 1) := by rw [hF, pow_succ]; omega
  have hF2 : Nat.fermatNumber k / 2 = 2 ^ m := by rw [hF]; omega
  rw [IsPrimitiveRoot.iff_orderOf, hF1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow
  · rw [← hF2, hhalf]; exact ZMod.neg_one_ne_one
  · rw [← hF1]; exact ZMod.pow_card_sub_one_eq_one ha0

theorem three_primitive_root_fermat {k : ℕ} (hk1 : 1 ≤ k) (hk : (Nat.fermatNumber k).Prime) :
    IsPrimitiveRoot (3 : ZMod (Nat.fermatNumber k)) (Nat.fermatNumber k - 1) :=
  fermat_primitive_root hk (three_nonresidue_fermat hk1 hk)

theorem five_primitive_root_fermat {k : ℕ} (hk2 : 2 ≤ k) (hk : (Nat.fermatNumber k).Prime) :
    IsPrimitiveRoot (5 : ZMod (Nat.fermatNumber k)) (Nat.fermatNumber k - 1) :=
  fermat_primitive_root hk (five_nonresidue_fermat hk2 hk)

lemma two_pow_two_pow_mod_seven (k : ℕ) : 2 ^ 2 ^ k % 7 = 2 ∨ 2 ^ 2 ^ k % 7 = 4 := by
  induction k with
  | zero => left; norm_num
  | succ k ih =>
    rw [pow_succ, pow_mul, Nat.pow_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

/-- View 730: `7` is a non-residue, hence a primitive root, of every Fermat prime `F_k`, `k ≥ 1`. -/
theorem seven_nonresidue_fermat {k : ℕ} (hk1 : 1 ≤ k) (hk : (Nat.fermatNumber k).Prime) :
    ¬ IsSquare (7 : ZMod (Nat.fermatNumber k)) := by
  have := Fact.mk hk
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := Nat.fermatNumber k) (q := 7)
    (fermatNumber_mod_four hk1) (by norm_num)
  rw [Nat.cast_ofNat] at this
  rw [this, ← ZMod.natCast_mod]
  have h7 : Nat.fermatNumber k % 7 = 3 ∨ Nat.fermatNumber k % 7 = 5 := by
    unfold Nat.fermatNumber; rcases two_pow_two_pow_mod_seven k with h | h <;> omega
  rcases h7 with h | h <;> rw [h]
  · exact not_sq_three_seven
  · exact not_sq_five_seven

theorem seven_primitive_root_fermat {k : ℕ} (hk1 : 1 ≤ k) (hk : (Nat.fermatNumber k).Prime) :
    IsPrimitiveRoot (7 : ZMod (Nat.fermatNumber k)) (Nat.fermatNumber k - 1) :=
  fermat_primitive_root hk (seven_nonresidue_fermat hk1 hk)

end LeanPool.SophieGermainArchives.Fr9115Arithmetic
