/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Table.Common
public import LeanPool.Zeta5Irrational.Certificates
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Reusable upper certificates for arcsine potentials

The rational versions read endpoints from the existing table and transfer their closed
arithmetic certificates to the real analytic lemmas once.
-/

@[expose] public section

namespace Zeta5Irrational

/-- An upper certificate for an arcsine potential to the left of its support. -/
lemma Uω_le_left_certificate {a b t s q U : ℝ} (hab : a < b) (ht : t ≤ a) (hs : 0 ≤ s)
    (hsq : (t - a) * (t - b) ≤ s ^ 2) (hq : ((a + b) / 2 - t + s) / 2 ≤ q)
    (hlog : Real.log q ≤ U) : Uω a b t ≤ U := by
  rw [Uω_of_le hab ht]
  have hroot := sqrt_le_of_sq_le hs hsq
  have hroot0 := Real.sqrt_nonneg ((t - a) * (t - b))
  apply (Real.log_le_log (by linarith) ?_).trans hlog
  linarith

/-- An upper certificate for an arcsine potential to the right of its support. -/
lemma Uω_le_right_certificate {a b t s q U : ℝ} (hab : a < b) (ht : b ≤ t) (hs : 0 ≤ s)
    (hsq : (t - a) * (t - b) ≤ s ^ 2) (hq : (t - (a + b) / 2 + s) / 2 ≤ q)
    (hlog : Real.log q ≤ U) : Uω a b t ≤ U := by
  rw [Uω_of_ge hab ht]
  have hroot := sqrt_le_of_sq_le hs hsq
  have hroot0 := Real.sqrt_nonneg ((t - a) * (t - b))
  apply (Real.log_le_log (by linarith) ?_).trans hlog
  linarith

/-- The left endpoint of an arcsine interval, evaluated in the rationals. -/
def rationalLeftEndpoint (j : ℕ) : ℚ :=
  ((table1.getD (j - 1) (0, 0, 0)).1 : ℚ) / 10 ^ 12

/-- The right endpoint of an arcsine interval, evaluated in the rationals. -/
def rationalRightEndpoint (j : ℕ) : ℚ :=
  ((table1.getD (j - 1) (0, 0, 0)).2.1 : ℚ) / 10 ^ 12

lemma aρ_eq_rationalLeftEndpoint (j : ℕ) : aρ j = (rationalLeftEndpoint j : ℝ) := by
  simp only [aρ, rationalLeftEndpoint, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat]

lemma bρ_eq_rationalRightEndpoint (j : ℕ) : bρ j = (rationalRightEndpoint j : ℝ) := by
  simp only [bρ, rationalRightEndpoint, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat]

/-- A rational certificate to the left of a tabulated arcsine interval. -/
lemma Uω_le_left_certificate_rational {j : ℕ} {t s q U : ℚ}
    (certificate : rationalLeftEndpoint j < rationalRightEndpoint j ∧
      t ≤ rationalLeftEndpoint j ∧ 0 ≤ s ∧
      (t - rationalLeftEndpoint j) * (t - rationalRightEndpoint j) ≤ s ^ 2 ∧
      ((rationalLeftEndpoint j + rationalRightEndpoint j) / 2 - t + s) / 2 ≤ q)
    (hlog : Real.log (q : ℝ) ≤ (U : ℝ)) :
    Uω (aρ j) (bρ j) (t : ℝ) ≤ (U : ℝ) := by
  rw [aρ_eq_rationalLeftEndpoint, bρ_eq_rationalRightEndpoint]
  apply Uω_le_left_certificate (s := (s : ℝ)) (q := (q : ℝ))
  · exact_mod_cast certificate.1
  · exact_mod_cast certificate.2.1
  · exact_mod_cast certificate.2.2.1
  · exact_mod_cast certificate.2.2.2.1
  · exact_mod_cast certificate.2.2.2.2
  · exact hlog

/-- A rational certificate to the right of a tabulated arcsine interval. -/
lemma Uω_le_right_certificate_rational {j : ℕ} {t s q U : ℚ}
    (certificate : rationalLeftEndpoint j < rationalRightEndpoint j ∧
      rationalRightEndpoint j ≤ t ∧ 0 ≤ s ∧
      (t - rationalLeftEndpoint j) * (t - rationalRightEndpoint j) ≤ s ^ 2 ∧
      (t - (rationalLeftEndpoint j + rationalRightEndpoint j) / 2 + s) / 2 ≤ q)
    (hlog : Real.log (q : ℝ) ≤ (U : ℝ)) :
    Uω (aρ j) (bρ j) (t : ℝ) ≤ (U : ℝ) := by
  rw [aρ_eq_rationalLeftEndpoint, bρ_eq_rationalRightEndpoint]
  apply Uω_le_right_certificate (s := (s : ℝ)) (q := (q : ℝ))
  · exact_mod_cast certificate.1
  · exact_mod_cast certificate.2.1
  · exact_mod_cast certificate.2.2.1
  · exact_mod_cast certificate.2.2.2.1
  · exact_mod_cast certificate.2.2.2.2
  · exact hlog

/-- Combine componentwise bounds for the sixteen weighted arcsine potentials. -/
lemma Uρ_le_weighted_bounds {t : ℝ} {u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 : ℝ}
    (h1 : Uω (aρ 1) (bρ 1) t ≤ u1)
    (h2 : Uω (aρ 2) (bρ 2) t ≤ u2)
    (h3 : Uω (aρ 3) (bρ 3) t ≤ u3)
    (h4 : Uω (aρ 4) (bρ 4) t ≤ u4)
    (h5 : Uω (aρ 5) (bρ 5) t ≤ u5)
    (h6 : Uω (aρ 6) (bρ 6) t ≤ u6)
    (h7 : Uω (aρ 7) (bρ 7) t ≤ u7)
    (h8 : Uω (aρ 8) (bρ 8) t ≤ u8)
    (h9 : Uω (aρ 9) (bρ 9) t ≤ u9)
    (h10 : Uω (aρ 10) (bρ 10) t ≤ u10)
    (h11 : Uω (aρ 11) (bρ 11) t ≤ u11)
    (h12 : Uω (aρ 12) (bρ 12) t ≤ u12)
    (h13 : Uω (aρ 13) (bρ 13) t ≤ u13)
    (h14 : Uω (aρ 14) (bρ 14) t ≤ u14)
    (h15 : Uω (aρ 15) (bρ 15) t ≤ u15)
    (h16 : Uω (aρ 16) (bρ 16) t ≤ u16) :
    Uρ t ≤ cρ 1 * u1 + cρ 2 * u2 + cρ 3 * u3 + cρ 4 * u4 +
      cρ 5 * u5 + cρ 6 * u6 + cρ 7 * u7 + cρ 8 * u8 +
      cρ 9 * u9 + cρ 10 * u10 + cρ 11 * u11 + cρ 12 * u12 +
      cρ 13 * u13 + cρ 14 * u14 + cρ 15 * u15 + cρ 16 * u16 := by
  rw [Uρ_expand]
  have bound1 := mul_le_mul_of_nonneg_left h1 (cρ_pos 1 (by decide)).le
  have bound2 := mul_le_mul_of_nonneg_left h2 (cρ_pos 2 (by decide)).le
  have bound3 := mul_le_mul_of_nonneg_left h3 (cρ_pos 3 (by decide)).le
  have bound4 := mul_le_mul_of_nonneg_left h4 (cρ_pos 4 (by decide)).le
  have bound5 := mul_le_mul_of_nonneg_left h5 (cρ_pos 5 (by decide)).le
  have bound6 := mul_le_mul_of_nonneg_left h6 (cρ_pos 6 (by decide)).le
  have bound7 := mul_le_mul_of_nonneg_left h7 (cρ_pos 7 (by decide)).le
  have bound8 := mul_le_mul_of_nonneg_left h8 (cρ_pos 8 (by decide)).le
  have bound9 := mul_le_mul_of_nonneg_left h9 (cρ_pos 9 (by decide)).le
  have bound10 := mul_le_mul_of_nonneg_left h10 (cρ_pos 10 (by decide)).le
  have bound11 := mul_le_mul_of_nonneg_left h11 (cρ_pos 11 (by decide)).le
  have bound12 := mul_le_mul_of_nonneg_left h12 (cρ_pos 12 (by decide)).le
  have bound13 := mul_le_mul_of_nonneg_left h13 (cρ_pos 13 (by decide)).le
  have bound14 := mul_le_mul_of_nonneg_left h14 (cρ_pos 14 (by decide)).le
  have bound15 := mul_le_mul_of_nonneg_left h15 (cρ_pos 15 (by decide)).le
  have bound16 := mul_le_mul_of_nonneg_left h16 (cρ_pos 16 (by decide)).le
  have firstFour := add_le_add (add_le_add (add_le_add bound1 bound2) bound3) bound4
  have firstEight :=
    add_le_add (add_le_add (add_le_add (add_le_add firstFour bound5) bound6) bound7) bound8
  have firstTwelve :=
    add_le_add (add_le_add (add_le_add (add_le_add firstEight bound9) bound10) bound11) bound12
  exact
    add_le_add (add_le_add (add_le_add (add_le_add firstTwelve bound13) bound14) bound15) bound16

end Zeta5Irrational
