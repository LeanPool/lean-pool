/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.LogTrig

/-!
# A006: `∫₀^{π/4} log cos x dx` and `∫₀^{π/4} log sin x dx`

* `LeanPolyLog.Proofs.A006_cos`: `∫₀^{π/4} log cos x dx = G/2 - (π/4) log 2`.
* `LeanPolyLog.Proofs.A006_sin`: `∫₀^{π/4} log sin x dx = -G/2 - (π/4) log 2`.

Both follow from the sum and the difference of the two integrals, which are computed in
`LeanPolyLog.Lemmas.LogTrig`:
* `∫₀^{π/4} log sin + ∫₀^{π/4} log cos = -(π/2) log 2`;
* `∫₀^{π/4} log cos - ∫₀^{π/4} log sin = G`.
-/

open Real

namespace LeanPolyLog.Proofs

/-- A006 (first half): `∫₀^{π/4} log cos x dx = G/2 - (π/4) log 2`. -/
public theorem A006_cos :
    ∫ x in (0 : ℝ)..(π / 4), Real.log (Real.cos x) = G / 2 - π / 4 * Real.log 2 := by
  have h₁ := LogTrig.integral_log_sin_add_integral_log_cos
  have h₂ := LogTrig.integral_log_cos_sub_integral_log_sin
  linarith

/-- A006 (second half): `∫₀^{π/4} log sin x dx = -G/2 - (π/4) log 2`. -/
public theorem A006_sin :
    ∫ x in (0 : ℝ)..(π / 4), Real.log (Real.sin x) = -G / 2 - π / 4 * Real.log 2 := by
  have h₁ := LogTrig.integral_log_sin_add_integral_log_cos
  have h₂ := LogTrig.integral_log_cos_sub_integral_log_sin
  linarith

end LeanPolyLog.Proofs
