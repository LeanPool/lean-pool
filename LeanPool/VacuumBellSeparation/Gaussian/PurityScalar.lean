/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The scalar factor in Gaussian Rényi purity

For the manuscript's covariance normalization (pure symplectic eigenvalue `1/2`),
the scalar factor is `fᵣ(x) = (x + 1/2)^r - (x - 1/2)^r`.
This file proves its logarithmic derivative bound, including the pure boundary.
It does not assume differentiability of ordered symplectic eigenvalue branches,
or identify an operator trace with a product of these scalar factors.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- The one-mode denominator of the Rényi purity, in the source normalization. -/
noncomputable def purityFactor (r v : ℝ) : ℝ :=
  (v + 1 / 2) ^ r - (v - 1 / 2) ^ r

/-- The factor is positive on the physical scalar domain. -/
theorem purityFactor_pos {r v : ℝ} (hr : 0 < r) (hv : 1 / 2 ≤ v) :
    0 < purityFactor r v := by
  exact sub_pos.mpr (Real.rpow_lt_rpow (by linarith) (by linarith) hr)

/-- The derivative exists even at `v = 1/2` when `r > 1`. -/
theorem hasDerivAt_purityFactor {r v : ℝ} (hr : 1 < r) :
    HasDerivAt (purityFactor r)
      (r * ((v + 1 / 2) ^ (r - 1) - (v - 1 / 2) ^ (r - 1))) v := by
  have hp := ((hasDerivAt_id' (x := v)).add_const (1 / 2 : ℝ)).rpow_const
    (p := r) (Or.inr hr.le)
  have hm := ((hasDerivAt_id' (x := v)).sub_const (1 / 2 : ℝ)).rpow_const
    (p := r) (Or.inr hr.le)
  unfold purityFactor
  convert hp.sub hm using 1; ring

/-- An exact decomposition which proves the logarithmic derivative upper bound
without introducing a quotient coordinate at the pure boundary. -/
theorem purityFactor_decomposition {r v : ℝ} (hr : 1 < r) (hv : 1 / 2 ≤ v) :
    purityFactor r v =
      v * ((v + 1 / 2) ^ (r - 1) - (v - 1 / 2) ^ (r - 1)) +
      (1 / 2) * ((v + 1 / 2) ^ (r - 1) + (v - 1 / 2) ^ (r - 1)) := by
  have hp := Real.rpow_add_one' (x := v + 1 / 2) (y := r - 1)
    (by linarith) (by linarith)
  have hm := Real.rpow_add_one' (x := v - 1 / 2) (y := r - 1)
    (by linarith) (by linarith)
  rw [sub_add_cancel] at hp hm
  rw [purityFactor, hp, hm]
  ring

/-- Section 4.1 of the manuscript: `0 ≤ x fᵣ'(x) / fᵣ(x) ≤ r` for `r > 1` and `x ≥ 1/2`, here at
`x = v`. -/
theorem purityFactor_logarithmic_derivative_bound {r v : ℝ}
    (hr : 1 < r) (hv : 1 / 2 ≤ v) :
    0 ≤ v * deriv (purityFactor r) v / purityFactor r v ∧
      v * deriv (purityFactor r) v / purityFactor r v ≤ r := by
  have hr0 : 0 < r := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hpos := purityFactor_pos hr0 hv
  have hp : 0 ≤ (v + 1 / 2) ^ (r - 1) := Real.rpow_nonneg (by linarith) _
  have hm : 0 ≤ (v - 1 / 2) ^ (r - 1) := Real.rpow_nonneg (by linarith) _
  have hdiff : 0 ≤ (v + 1 / 2) ^ (r - 1) - (v - 1 / 2) ^ (r - 1) :=
    sub_nonneg.mpr (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
  have hupper : v * ((v + 1 / 2) ^ (r - 1) - (v - 1 / 2) ^ (r - 1)) ≤
      purityFactor r v := by
    rw [purityFactor_decomposition hr hv]
    linarith
  rw [(hasDerivAt_purityFactor hr).deriv]
  constructor
  · exact div_nonneg (mul_nonneg hv0 (mul_nonneg hr0.le hdiff)) hpos.le
  · apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hupper hr0.le]

/-- The logarithm of the scalar factor; its negative is the one-mode log purity
once the separate Gaussian spectral formula has been established. -/
noncomputable def logPurityFactor (r v : ℝ) : ℝ := Real.log (purityFactor r v)

theorem hasDerivAt_logPurityFactor {r v : ℝ} (hr : 1 < r) (hv : 1 / 2 ≤ v) :
    HasDerivAt (logPurityFactor r)
      (deriv (purityFactor r) v / purityFactor r v) v := by
  change HasDerivAt (fun x => Real.log (purityFactor r x)) _ v
  rw [(hasDerivAt_purityFactor hr).deriv]
  exact (hasDerivAt_purityFactor (v := v) hr).log (purityFactor_pos (by linarith) hv).ne'

/-- The logarithmic slope bound with an actual derivative of the log factor. -/
theorem logPurityFactor_derivative_bound {r v : ℝ} (hr : 1 < r) (hv : 1 / 2 ≤ v) :
    0 ≤ v * deriv (logPurityFactor r) v ∧
      v * deriv (logPurityFactor r) v ≤ r := by
  rw [(hasDerivAt_logPurityFactor hr hv).deriv, ← mul_div_assoc]
  exact purityFactor_logarithmic_derivative_bound hr hv

end VacuumBellSeparation.Gaussian
