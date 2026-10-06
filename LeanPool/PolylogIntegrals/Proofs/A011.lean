/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Arcsin
public import LeanPool.PolylogIntegrals.Proofs.A009

/-!
# A011: `∫₀¹ Li₂(x) / (x √(1-x²)) dx = (3/8) π² log 2 - (7/16) ζ(3)`

The weight `w(y) = -log y` has the moments `∫₀¹ yⁿ (-log y) dy = 1/(n+1)²`, so
`LeanPolyLog.Arcsin.integral_Lir_div_mul_sqrt` (Fubini, then `y = sin φ`) gives
`∫₀¹ Li₂(x) / (x √(1-x²)) dx = ∫₀^{π/2} (-log sin φ) (π/2 + φ) dφ = (π/2)·(π/2) log 2 - J`,
where `J = ∫₀^{π/2} φ log sin φ dφ = -(π²/8) log 2 + (7/16) ζ(3)` is
`LeanPolyLog.Proofs.integral_mul_log_sin`, proved on the way to A009.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.Proofs

/-- A011: `∫₀¹ Li₂(x) / (x √(1-x²)) dx = (3/8) π² log 2 - (7/16) ζ(3)`. -/
public theorem A011 : ∫ x in (0 : ℝ)..1, Lir 2 x / (x * Real.sqrt (1 - x ^ 2)) =
    3 / 8 * π ^ 2 * Real.log 2 - 7 / 16 * zeta3 := by
  rw [Arcsin.integral_Lir_div_mul_sqrt le_rfl (w := fun y ↦ -log y) measurable_log.neg
    (fun y hy ↦ neg_nonneg.2 (log_nonpos hy.1.le hy.2)) LogTrig.integrableOn_pow_mul_neg_log
    LogTrig.integral_pow_mul_neg_log]
  have hint : IntervalIntegrable (fun φ ↦ log (sin φ)) volume 0 (π / 2) :=
    intervalIntegrable_log_sin
  have hint' : IntervalIntegrable (fun φ ↦ φ * log (sin φ)) volume 0 (π / 2) :=
    intervalIntegrable_log_sin.continuousOn_mul continuousOn_id
  have h : (fun φ ↦ -log (sin φ) * (π / 2 + φ)) =
      fun φ ↦ -(π / 2) * log (sin φ) - φ * log (sin φ) := by
    ext φ
    ring
  rw [h, intervalIntegral.integral_sub (hint.const_mul _) hint',
    intervalIntegral.integral_const_mul, integral_log_sin_zero_pi_div_two, integral_mul_log_sin]
  ring

end LeanPolyLog.Proofs
