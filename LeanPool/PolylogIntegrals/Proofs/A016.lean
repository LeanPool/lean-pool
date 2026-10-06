/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Arcsin
public import LeanPool.PolylogIntegrals.Proofs.A015

/-!
# A016: `∫₀¹ Li₃(x) / (x √(1-x²)) dx = Li₄(1/2)/2 + 41π⁴/5760 + log⁴2/48 + π² log²2/6`

The weight `w(y) = log² y / 2` has the moments `∫₀¹ yⁿ log² y / 2 dy = 1/(n+1)³`, so
`LeanPolyLog.Arcsin.integral_Lir_div_mul_sqrt` (Fubini, then `y = sin φ`) gives
`∫₀¹ Li₃(x) / (x √(1-x²)) dx = ∫₀^{π/2} (log² sin φ / 2) (π/2 + φ) dφ = (π/4) L + A015/2`,
where `L = ∫₀^{π/2} log² sin φ dφ = π³/24 + (π/2) log² 2` is
`LeanPolyLog.LogSinSq.integral_log_sin_sq` and A015 is `∫₀^{π/2} φ log² sin φ dφ`.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.Proofs

/-- A016: `∫₀¹ Li₃(x) / (x √(1-x²)) dx = Li₄(1/2)/2 + 41π⁴/5760 + log⁴2/48 + π² log²2/6`. -/
public theorem A016 : ∫ x in (0 : ℝ)..1, Lir 3 x / (x * Real.sqrt (1 - x ^ 2)) =
    Lir 4 (1 / 2) / 2 + 41 * π ^ 4 / 5760 + Real.log 2 ^ 4 / 48 + π ^ 2 * Real.log 2 ^ 2 / 6 := by
  have hfun : ∀ n : ℕ, (fun y : ℝ ↦ y ^ n * (log y ^ 2 / 2)) =
      fun y ↦ 1 / 2 * (y ^ n * log y ^ 2) := fun n ↦ by
    ext y
    ring
  rw [Arcsin.integral_Lir_div_mul_sqrt (by norm_num) (w := fun y ↦ log y ^ 2 / 2)
    ((measurable_log.pow_const 2).div_const 2) (fun y _ ↦ by positivity)
    (fun n ↦ by
      rw [hfun n]
      exact (Arctan.intervalIntegrable_pow_mul_log_sq n).1.const_mul _)
    (fun n ↦ by
      rw [hfun n, intervalIntegral.integral_const_mul, Arctan.integral_pow_mul_log_sq]
      ring)]
  have hS : IntervalIntegrable (fun φ ↦ log (sin φ) ^ 2) volume 0 (π / 2) :=
    LogSinSq.intervalIntegrable_log_sin_sq
  have hS' : IntervalIntegrable (fun φ ↦ φ * log (sin φ) ^ 2) volume 0 (π / 2) :=
    hS.continuousOn_mul continuousOn_id
  have h : (fun φ ↦ log (sin φ) ^ 2 / 2 * (π / 2 + φ)) =
      fun φ ↦ π / 4 * log (sin φ) ^ 2 + 1 / 2 * (φ * log (sin φ) ^ 2) := by
    ext φ
    ring
  rw [h, intervalIntegral.integral_add (hS.const_mul _) (hS'.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    LogSinSq.integral_log_sin_sq, A015]
  ring

end LeanPolyLog.Proofs
