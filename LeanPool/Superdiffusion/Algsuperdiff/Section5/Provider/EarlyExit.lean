/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OneStepLaplace
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.AuxiliaryScale

/-!
# EarlyExit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The canonical chain length and the Chernoff budget

The hit--exit bridge asks for a chain length below the usable trace count of a
good cube.  This file fixes the canonical choice — the usable count, after one
reserved site, divided by the overlap multiplicity — and verifies its counting
condition.  It also carries the deterministic Chernoff calculation that turns a
contraction bounded by `exp (-kappa)` together with a budget
`lam * t + b ≤ kappa * N` into the decay `exp (-b)`.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support Algsuperdiff.Section5.Trace
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- The number of trace sites left after the two endpoint losses. -/
def earlyExitTraceCount (d k : ℕ) : ℕ := 3 * 3 ^ k / 4 - 2 * d

/-- The largest chain length obtained by dividing the usable trace count,
after reserving one site, by the overlap multiplicity `3^d`. -/
def earlyExitChainLength (d k : ℕ) : ℕ :=
  (earlyExitTraceCount d k - 1) / 3 ^ d

/-- The canonical chain length satisfies the strict counting condition of the
hit--exit bridge whenever at least one trace site remains. -/
theorem earlyExitChainLength_mul_lt (d k : ℕ) (hcount : 0 < earlyExitTraceCount d k) :
    earlyExitChainLength d k * 3 ^ d < earlyExitTraceCount d k := by
  have hle : earlyExitChainLength d k * 3 ^ d ≤ earlyExitTraceCount d k - 1 := by
    unfold earlyExitChainLength
    exact Nat.div_mul_le_self _ _
  exact hle.trans_lt (Nat.sub_lt hcount zero_lt_one)

/-- The deterministic Chernoff calculation after chaining.  A contraction
bounded by `exp (-kappa)` and a budget `lam * t + b ≤ kappa * N` leave the
decay `exp (-b)`. -/
theorem ofReal_exp_mul_pow_le_of_budget {lam t kappa b : ℝ} {rho : ℝ≥0∞} {N : ℕ}
    (hrho : rho ≤ ENNReal.ofReal (Real.exp (-kappa)))
    (hbudget : lam * t + b ≤ kappa * (N : ℝ)) :
    ENNReal.ofReal (Real.exp (lam * t)) * rho ^ N ≤
      ENNReal.ofReal (Real.exp (-b)) := by
  calc
    ENNReal.ofReal (Real.exp (lam * t)) * rho ^ N ≤
        ENNReal.ofReal (Real.exp (lam * t)) *
          (ENNReal.ofReal (Real.exp (-kappa))) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left' hrho N)
        (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (lam * t)))
    _ = ENNReal.ofReal (Real.exp (lam * t - kappa * (N : ℝ))) := by
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _) N, ← Real.exp_nat_mul,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-b)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith only [hbudget]

end

end Algsuperdiff.Section5.Provider
