/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.PowerSeriesEulerDerivative
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # Formal logarithmic derivatives of the factors `1/(1-X^f)` -/

@[expose] public section

namespace NairTenenbaum

/-- A geometric series with coefficients weighted by their index. -/
noncomputable def weightedGeometricSeries (f : ℕ) (hf : f ≠ 0) : PowerSeries ℝ :=
  PowerSeries.expand f hf (PowerSeries.mk (1 : ℕ → ℝ))

theorem weightedGeometricSeries_coeff (f : ℕ) (hf : f ≠ 0) (k : ℕ) :
    PowerSeries.coeff k (weightedGeometricSeries f hf) = if f ∣ k then 1 else 0 := by
  simp only [weightedGeometricSeries, PowerSeries.coeff_expand, PowerSeries.coeff_mk, Pi.one_apply]

theorem weightedGeometricSeries_mul_one_sub (f : ℕ) (hf : f ≠ 0) :
    weightedGeometricSeries f hf * (1 - PowerSeries.X ^ f) = 1 := by
  have H := congrArg (PowerSeries.expand (R := ℝ) f hf) (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
  simpa only [map_mul, map_sub, map_one, PowerSeries.expand_X, weightedGeometricSeries] using H

theorem weightedGeometricSeries_eulerDerivative (f : ℕ) (hf : f ≠ 0) :
    powerSeriesEulerDerivative (weightedGeometricSeries f hf) * (1 - PowerSeries.X ^ f) =
      (f : PowerSeries ℝ) * (weightedGeometricSeries f hf - 1) := by
  let G := weightedGeometricSeries f hf
  have HG : G * (1 - PowerSeries.X ^ f) = 1 := weightedGeometricSeries_mul_one_sub f hf
  have HD := congrArg (fun F : PowerSeries ℝ => PowerSeries.derivative F) HG
  simp only [Derivation.leibniz, smul_eq_mul, map_sub, PowerSeries.derivative_one,
    PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one, zero_sub] at HD
  have HX : PowerSeries.X * (PowerSeries.X : PowerSeries ℝ) ^ (f - 1) = PowerSeries.X ^ f := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hf)]
  have Hprod : G * PowerSeries.X ^ f = G - 1 := by linear_combination -HG
  change (PowerSeries.X * PowerSeries.derivative G) * (1 - PowerSeries.X ^ f) = (f : PowerSeries
      ℝ) * (G - 1)
  calc
    _ = (f : PowerSeries ℝ) * G * (PowerSeries.X * PowerSeries.X ^ (f - 1)) := by
      linear_combination PowerSeries.X * HD
    _ = _ := by rw [HX]; linear_combination (f : PowerSeries ℝ) * Hprod

end NairTenenbaum
