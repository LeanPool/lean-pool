/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepTwoEnergy

/-!
# HomStepThreeCoarse

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3b: the arithmetic of the gap absorption

## The two targets

Step 3 (the coarse graining application): substitute the mesoscale energy bound
(the Step 2b) into the general coarse-graining estimate and obtain the gradient
homogenization bound.

Step 3 (the gap absorption): the mesoscale gap `s^{-9/2} 3^{(n-m)/2} ≤ C γ^5`,
substituted back, compared with the definition of `EthmB(m)`, yielding the weak
gradient bound.

## THE SECOND CONDITIONAL EDGE — disclosed

The general coarse-graining proposition is a declared dependency AND a declared
source hypothesis of the Step-3a node ("the general coarse-graining proposition
applied with `p → ∞` … substituted into the general coarse-graining estimate"),
so its conclusion enters here as a NAMED TRANSCRIBED HYPOTHESIS `hCG`, exactly
as Theorem C's display enters as `hC`.  It is **not** available as a theorem:

* the graph marks the node a BOUNDARY LEAF (Section 2, out of this lane) with
  `LEAN_STATUS: NOT_STARTED`;
* `CoarseGraining`'s relative, `Ch03.generalCoarseGrainingL2TwoExponentTheory`, is the
  **`p = 2` / negative-Besov-`L²`** package
  (`homogenizationComparisonNegativeBesovLHS`), not the `W^{-s,∞}` object this
  step needs;
* it is recorded that the literal endpoint `p = ∞` is UNAVAILABLE from the
  source (the dual exponent `p' = 1` breaks the flat-cube CZ estimate behind
  the Calderón--Zygmund flux comparison lemma), and neither a `p`-uniformity remark on `C(p,d)` nor an
  explicit large-`q` conclusion is given.

The chain that consumes that Proposition reads the `p → ∞` reading of its
display through a transcribed `hCG` binder.  The `W^{-s,∞}` left-hand side is
carried as an abstract nonnegative real, so nothing about the negative-norm
carrier is assumed either.

## What is proved

The elementary arithmetic behind the gap absorption: `1 < log 3`
(`one_lt_log_three`) and the lever `t^5 ≤ 3125 e^t` (`pow_five_le_exp`).
Together they give the "`gapAbsorb` computation"
`s^{-9/2}3^{(n-m)/2} ≤ C_gap0(d-free) γ^5` at the EXPLICIT constant
`C_gap0 = (log 3 - 1)^{-5}`.  `5 log 3 = 5.49… > 5` is genuine and is exactly the
slack the proof spends; the lever is `t ≤ exp t` applied at
`t = (log 3 - 1)|log γ|`, with no series and no factorials.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 4. Step 3b: the gap absorption -/

theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have he : Real.exp 1 < 3 := by
    have h := Real.exp_one_lt_d9
    linarith only [h]
  have h := Real.log_lt_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at h

/-- The elementary lever: `t ≤ exp t` at `t/5`, raised to the fifth power.  No
series, no factorials. -/
theorem pow_five_le_exp {t : ℝ} (ht : 0 ≤ t) : t ^ (5 : ℕ) ≤ 3125 * Real.exp t := by
  have hbase : t / 5 ≤ Real.exp (t / 5) := by
    have h := Real.add_one_le_exp (t / 5)
    linarith only [h]
  have hpow : (t / 5) ^ (5 : ℕ) ≤ (Real.exp (t / 5)) ^ (5 : ℕ) :=
    pow_le_pow_left₀ (by linarith only [ht]) hbase 5
  have hexp : (Real.exp (t / 5)) ^ (5 : ℕ) = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hpow
  have hdiv : (t / 5) ^ (5 : ℕ) = t ^ (5 : ℕ) / 3125 := by
    rw [div_pow]
    norm_num
  rw [hdiv] at hpow
  linarith only [hpow]

end

end Algsuperdiff.Section4.Provider.Homogenization
