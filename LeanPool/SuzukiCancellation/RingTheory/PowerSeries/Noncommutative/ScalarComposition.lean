/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ScalarSubstitution
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Composition in scalar functional calculus

Scalar formal composition identities can be interpreted at a single positive
series in a noncommutative algebra. This requires no commutativity among the
coefficients of the target series.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

/-- In a scalar algebra, positive substitution agrees with Mathlib's formal substitution. -/
theorem scalarSeriesApply_eq_subst (f c : PowerSeries ℚ) (hc : constantCoeff c = 0) :
    scalarSeriesApply f (fun n ↦ coeff n c) = f.subst c := by
  ext n
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hc)]
  rw [finsum_eq_sum_of_support_subset _ (s := range (n + 1))]
  · simp only [scalarSeriesApply, coeff_mk, ← coeff_positiveSeries_pow,
      positiveSeries_coeff c hc]
  · intro k hk
    by_contra hn
    have hkn : n < k := by have := mem_range.not.mp hn; lia
    have hz : coeff n (c ^ k) = 0 := by
      rw [← positiveSeries_coeff c hc]
      exact coeff_positiveSeries_pow_eq_zero_of_lt _ _ _ hkn
    exact hk (by simp [hz])

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The constant coefficient of scalar functional calculus. -/
theorem constantCoeff_scalarSeriesApply (f : PowerSeries ℚ) (u : ℕ → A) :
    constantCoeff (scalarSeriesApply f u) = algebraMap ℚ A (constantCoeff f) := by
  simp only [← coeff_zero_eq_constantCoeff_apply]
  simp [scalarSeriesApply, positivePowerCoeff, Algebra.smul_def]

/-- Scalar substitution is local in its scalar argument, uniformly through a finite prefix. -/
theorem scalarSeriesApply_trunc_subst_prefix (f c : PowerSeries ℚ)
    (hc : constantCoeff c = 0) (n k : ℕ) (hk : k ≤ n) :
    coeff k (f.subst c) = coeff k ((trunc (n + 1) f : PowerSeries ℚ).subst c) := by
  rw [← scalarSeriesApply_eq_subst f c hc,
    ← scalarSeriesApply_eq_subst (trunc (n + 1) f) c hc]
  apply coeff_scalarSeriesApply_congr
  intro j hj
  simp only [Polynomial.coeff_coe, coeff_trunc, ite_eq_left (by lia : j < n + 1)]

/-- Scalar functional calculus transports formal composition into a noncommutative target. -/
theorem scalarSeriesApply_subst (f c : PowerSeries ℚ) (hc : constantCoeff c = 0)
    (u : ℕ → A) :
    scalarSeriesApply (f.subst c) u =
      scalarSeriesApply f (fun n ↦ coeff n (scalarSeriesApply c u)) := by
  ext n
  have hc' : constantCoeff (scalarSeriesApply c u) = 0 := by
    rw [constantCoeff_scalarSeriesApply, hc, map_zero]
  calc
    coeff n (scalarSeriesApply (f.subst c) u) =
        coeff n (scalarSeriesApply ((trunc (n + 1) f : PowerSeries ℚ).subst c) u) :=
      coeff_scalarSeriesApply_congr _ _ _ _ (fun k hk ↦
        scalarSeriesApply_trunc_subst_prefix f c hc n k hk)
    _ = coeff n (scalarSeriesApply (Polynomial.aeval c (trunc (n + 1) f)) u) := by
      rw [subst_coe (HasSubst.of_constantCoeff_zero' hc)]
    _ = coeff n (Polynomial.aeval (scalarSeriesApply c u) (trunc (n + 1) f)) := by
      rw [← scalarSeriesApplyHom_apply, ← Polynomial.aeval_algHom_apply,
        scalarSeriesApplyHom_apply]
    _ = coeff n (scalarSeriesApply f (fun k ↦ coeff k (scalarSeriesApply c u))) := by
      rw [coeff_scalarSeriesApply_eq_aeval_trunc f _ n (n + 1) (by lia),
        positiveSeries_coeff _ hc']

end FQFP
