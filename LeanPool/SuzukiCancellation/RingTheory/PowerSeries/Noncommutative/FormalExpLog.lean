/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ScalarComposition
public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Formal exponential and logarithm over noncommutative rational algebras

The exponential of a series with constant coefficient zero and the logarithm of
a series with constant coefficient one are mutually inverse. The proof uses
scalar composition at one positive element and does not expand words.

## Main results

* `formalExp_formalLog`, `formalLog_formalExp`: the formal inverse identities.
* `coeff_formalExp_congr`, `coeff_formalLog_congr`: preservation of finite prefixes.
* `expListTerm_eq_sum_log_powers`: recovery of product coefficients from the logarithm.
-/

@[expose] public noncomputable section

namespace FQFP

open PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The formal exponential of the positive part of a series. -/
def formalExp (p : PowerSeries A) : PowerSeries A :=
  scalarSeriesApply (exp ℚ) (fun n ↦ coeff n p)

/-- The formal logarithm, evaluated on the positive part of `p - 1`. -/
def formalLog (p : PowerSeries A) : PowerSeries A :=
  scalarSeriesApply (log ℚ) (fun n ↦ coeff n (p - 1))

@[simp]
theorem constantCoeff_formalLog (p : PowerSeries A) : constantCoeff (formalLog p) = 0 := by
  rw [formalLog, constantCoeff_scalarSeriesApply, constantCoeff_log, map_zero]

@[simp]
theorem constantCoeff_formalExp (p : PowerSeries A) : constantCoeff (formalExp p) = 1 := by
  rw [formalExp, constantCoeff_scalarSeriesApply, constantCoeff_exp, map_one]

/-- Formal exponential inverts formal logarithm at every homogeneous degree. -/
theorem formalExp_formalLog (p : PowerSeries A) (hp : constantCoeff p = 1) :
    formalExp (formalLog p) = p := by
  let u := fun n ↦ coeff n (p - 1)
  have h := scalarSeriesApply_subst (exp ℚ) (log ℚ) (by simp) u
  rw [subst_exp_log] at h
  change scalarSeriesApply (exp ℚ) (fun n ↦ coeff n (scalarSeriesApply (log ℚ) u)) = p
  rw [← h]
  change scalarSeriesApplyHom u (1 + X) = p
  rw [map_add, map_one, scalarSeriesApplyHom_apply, scalarSeriesApply_X,
    positiveSeries_coeff _ (by simp [hp])]
  simp

/-- Formal logarithm inverts formal exponential at every homogeneous degree. -/
theorem formalLog_formalExp (p : PowerSeries A) (hp : constantCoeff p = 0) :
    formalLog (formalExp p) = p := by
  let u := fun n ↦ coeff n p
  have h := scalarSeriesApply_subst (log ℚ) (exp ℚ - 1) (by simp [constantCoeff_exp]) u
  rw [subst_log_exp_sub_one, scalarSeriesApply_X, positiveSeries_coeff p hp] at h
  have hs : scalarSeriesApply (exp ℚ - 1) u = formalExp p - 1 := by
    change scalarSeriesApplyHom u (exp ℚ - 1) = formalExp p - 1
    rw [map_sub, map_one, scalarSeriesApplyHom_apply]
    rfl
  rw [hs] at h
  exact h.symm

/-- The scalar logarithm coefficients are the existing finite logarithm coefficients. -/
theorem coeff_log_eq_logCoeff (n : ℕ) : coeff n (log ℚ) = logCoeff n := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp [coeff_log, logCoeff, hn]

/-- The logarithm of an exponential list has exactly the existing homogeneous coefficients. -/
theorem coeff_formalLog_expListSeries (l : List A) (n : ℕ) :
    coeff n (formalLog (expListSeries l)) = expListLogCoeff l n := by
  have hp : positiveSeries (fun k ↦ coeff k (expListSeries l - 1)) =
      positiveSeries (expListTerm l) := by
    rw [positiveSeries_coeff _ (by simp [expListSeries]),
      ← positiveSeries_expListTerm l]
    simp
  rw [formalLog, scalarSeriesApply_congr _ _ _ hp]
  simp only [scalarSeriesApply, coeff_mk, coeff_log_eq_logCoeff, expListLogCoeff]

/-- Exponentiating the logarithm recovers each ordered product coefficient. -/
theorem expListTerm_eq_sum_log_powers (l : List A) (n : ℕ) :
    expListTerm l n = ∑ k ∈ Finset.range (n + 1),
      (Nat.factorial k : ℚ)⁻¹ • positivePowerCoeff (expListLogCoeff l) k n := by
  have h := congrArg (coeff n)
    (formalExp_formalLog (expListSeries l) (by simp [expListSeries]))
  simpa only [formalExp, scalarSeriesApply, coeff_mk, coeff_exp,
    Algebra.algebraMap_self_apply, one_div, coeff_formalLog_expListSeries,
    coeff_expListSeries] using h.symm

/-- The formal logarithm of one is zero. -/
@[simp]
theorem formalLog_one : formalLog (1 : PowerSeries A) = 0 := by
  ext n
  rw [← expListSeries_nil, coeff_formalLog_expListSeries]
  simp

/-- Formal exponential coefficients are finite factorial-weighted power coefficients. -/
theorem coeff_formalExp (p : PowerSeries A) (n : ℕ) :
    coeff n (formalExp p) = ∑ k ∈ Finset.range (n + 1),
      (Nat.factorial k : ℚ)⁻¹ • positivePowerCoeff (fun i ↦ coeff i p) k n := by
  simp only [formalExp, scalarSeriesApply, coeff_mk, coeff_exp,
    Algebra.algebraMap_self_apply, one_div]

/-- Formal logarithms depend only on the positive coefficients of the input. -/
theorem coeff_formalLog (p : PowerSeries A) (n : ℕ) :
    coeff n (formalLog p) = ∑ k ∈ Finset.range (n + 1),
      logCoeff k • positivePowerCoeff (fun i ↦ coeff i p) k n := by
  simp only [formalLog, scalarSeriesApply, coeff_mk, coeff_log_eq_logCoeff]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply positivePowerCoeff_congr
  intro i hi _
  simp [coeff_one, hi.ne']

/-- Equality of positive prefixes is preserved by formal logarithms. -/
theorem coeff_formalLog_congr (p q : PowerSeries A) (n : ℕ)
    (h : ∀ i, 0 < i → i ≤ n → coeff i p = coeff i q) :
    coeff n (formalLog p) = coeff n (formalLog q) := by
  simp only [coeff_formalLog]
  exact Finset.sum_congr rfl fun k _ ↦ congrArg (logCoeff k • ·)
    (positivePowerCoeff_congr _ _ n h k)

/-- Equality of positive prefixes is preserved by formal exponentials. -/
theorem coeff_formalExp_congr (p q : PowerSeries A) (n : ℕ)
    (h : ∀ i, 0 < i → i ≤ n → coeff i p = coeff i q) :
    coeff n (formalExp p) = coeff n (formalExp q) := by
  simp only [coeff_formalExp]
  exact Finset.sum_congr rfl fun k _ ↦ congrArg ((Nat.factorial k : ℚ)⁻¹ • ·)
    (positivePowerCoeff_congr _ _ n h k)

end FQFP
