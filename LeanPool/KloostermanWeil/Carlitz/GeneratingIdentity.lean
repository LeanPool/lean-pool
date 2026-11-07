/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.NewtonSum
public import LeanPool.KloostermanWeil.Carlitz.FormalAlgebra


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Extension-field generating identity

Derives the generating-series identity from the formal algebra and Newton sums,
following Carlitz (1969). The exact sign and trace normalization has not yet been
compared equation by equation with the original article.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open PowerSeries
open KloostermanWeil.Dickson

/-- Total sequence wrapper: Carlitz sums live only in positive extension degree. -/
noncomputable def Kseq
    (p : ℕ) [Fact p.Prime] (t : Fp p) : ℕ → ℂ
  | 0 => 0
  | n + 1 =>
      letI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      Kext p (n + 1) t

@[simp] theorem Kseq_zero
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    Kseq p t 0 = 0 := rfl

@[simp] theorem Kseq_succ
    (p : ℕ) [Fact p.Prime] (t : Fp p) (n : ℕ) :
    Kseq p t (n + 1) = Kext p (n + 1) t := by
  rfl

noncomputable def LSeriesA
    (p : ℕ) [Fact p.Prime] (t : Fp p) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => A p t n

@[simp] theorem coeff_LSeriesA
    (p : ℕ) [Fact p.Prime] (t : Fp p) (n : ℕ) :
    coeff n (LSeriesA p t) = A p t n := by
  simp [LSeriesA]

@[simp] theorem constantCoeff_LSeriesA
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    constantCoeff (LSeriesA p t) = 1 := by
  change A p t 0 = 1
  exact A_zero_eq_one p t

theorem Kseq_one_eq_baseKloosterman
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    Kseq p t 1 = baseKloosterman p t := by
  rw [Kseq_succ]
  rw [Kext_one_eq_kloostermanSumPrime]
  simp [baseKloosterman, KloostermanWeil.kloostermanSumPrime]

theorem LSeriesA_eq_quadratic
    (p : ℕ) [Fact p.Prime] {t : Fp p} (ht : t ≠ 0) :
    LSeriesA p t =
      quadraticL (Kseq p t 1) (p : ℂ) := by
  ext n
  rcases n with _ | _ | n
  · simp [LSeriesA, quadraticL, A_zero_eq_one]
  · rw [coeff_LSeriesA, A_one_eq_K]
    simp only [quadraticL, map_add, coeff_one, coeff_C_mul,
      coeff_X, coeff_X_pow]
    simpa using (Kseq_one_eq_baseKloosterman p t).symm
  · rcases n with _ | n
    · simp [LSeriesA, quadraticL, A_two_eq_card p ht]
    · have hn3 : 3 ≤ n + 3 := by omega
      rw [show n + 1 + 1 + 1 = n + 3 by omega]
      rw [coeff_LSeriesA, A_eq_zero_of_three_le p (n + 3) hn3 t]
      simp [quadraticL, coeff_X_pow]

theorem derivative_KSeries_mul_LSeriesA
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    d⁄dX (KSeries (Kseq p t)) * LSeriesA p t =
      d⁄dX (LSeriesA p t) := by
  ext n
  rw [coeff_mul]
  calc
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      coeff ij.1 (d⁄dX (KSeries (Kseq p t))) *
        coeff ij.2 (LSeriesA p t)) =
      ∑ k ∈ Finset.range n.succ,
        coeff k (d⁄dX (KSeries (Kseq p t))) *
          coeff (n - k) (LSeriesA p t) := by
            exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j =>
                coeff i (d⁄dX (KSeries (Kseq p t))) *
                  coeff j (LSeriesA p t)) n
    _ = coeff n (d⁄dX (LSeriesA p t)) := by
      simp only [coeff_derivative_KSeries, coeff_LSeriesA]
      rw [coeff_derivative, coeff_LSeriesA]
      have hnewton := newton_Kext p (n + 1) t
      rw [← Fin.sum_univ_eq_sum_range]
      simpa [Kseq_succ, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, mul_comm] using hnewton.symm

theorem generating_identity_with_LSeriesA
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    KSeries (Kseq p t) = logOf (LSeriesA p t) := by
  have hK :=
    derivative_KSeries_mul_LSeriesA p t
  have hlog :
      d⁄dX (logOf (LSeriesA p t)) * LSeriesA p t =
        d⁄dX (LSeriesA p t) :=
    derivative_logOf_mul_self (constantCoeff_LSeriesA p t)
  have hunit : IsUnit (LSeriesA p t) :=
    isUnit_iff_constantCoeff.mpr (by simp)
  have hder :
      d⁄dX (KSeries (Kseq p t)) =
        d⁄dX (logOf (LSeriesA p t)) :=
    hunit.mul_right_cancel (hK.trans hlog.symm)
  ext n
  rcases n with _ | n
  · simp [KSeries, constantCoeff_logOf (constantCoeff_LSeriesA p t)]
  · have hc := congrArg (coeff n) hder
    rw [coeff_derivative, coeff_derivative] at hc
    have hn0 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hn : (n : ℂ) + 1 ≠ 0 := by
      simpa using hn0
    exact mul_right_cancel₀ hn hc

/-- Carlitz generating-series identity in the exact prime-modulus Kloosterman
normalization. -/
theorem carlitz_generating_identity
    (p : ℕ) [Fact p.Prime] {t : Fp p} (ht : t ≠ 0) :
    KSeries (Kseq p t) =
      logOf (quadraticL (Kseq p t 1) (p : ℂ)) := by
  rw [generating_identity_with_LSeriesA p t,
    LSeriesA_eq_quadratic p ht]


end KloostermanWeil.Carlitz
