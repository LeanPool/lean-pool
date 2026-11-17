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

end Zeta5Irrational
