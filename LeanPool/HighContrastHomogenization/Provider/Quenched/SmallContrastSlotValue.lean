/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSmallnessPack

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSlotValue

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The variance slot in recursion shape

The last purely algebraic step of the slot instantiation: the value that
`entry_lagged_variance_supply_of_block_split` delivers is put into the shape
`vsrcSeq + cV·F(j_b)` that `weakValueSharpMajorant_le_three_group_summed_at_level`
consumes, and its source part is put into the shallow-leg shape
`c₁·3^{-e(J-j)} + c₂·3^{-(J-j)}` that `slot_source_sum_split_sharp` consumes, with
`e = d/2 ≥ 1`.

The three named constants:

* `supplyMsc` — the supply's law constant (the only place a source moment
  survives), `Msc = (2d)^{1/2}·κ₂·2(𝔪₁(K)·bC·3^{g(G+1)})·√(𝔪₂(K))`;
* `slotSourceValue d Csub Msc m = √(2d)·(18·Csub·3^{-dm/2}·Msc + 288·3^{-m})`
  — the per-leg source, carrying all the decay in the lag `m = p - j_b`;
* `slotBaseCoefficient d = 580·√(2d)` — the coefficient of the base-scale
  excess `F(j_b)`, dimension-only.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The supply's law constant: the only surviving source moment. -/
@[expose]
def supplyMsc (Cd g : ℝ) (mAl : Mat d) (Gacc : ℕ) (E : BlockMat d) (K : ℝ) : ℝ :=
  (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * kap2Value Cd g mAl (Gacc + 1) E *
    (2 * (sourceMomentOne K * boundaryConst Cd g mAl *
      (3 : ℝ) ^ (g * ((Gacc + 1 : ℕ) : ℝ)))) * Real.sqrt (sourceMomentTwo K)

/-- The per-leg source value of the variance slot, at lag `m = p - j_b`. -/
@[expose]
def slotSourceValue (d : ℕ) (Csub Msc : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (2 * d) *
    (18 * (Csub * ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc) +
      576 * ((1 / 2 : ℝ) * (3 : ℝ) ^ (-(m : ℝ))))

/-- The base-scale coefficient of the variance slot. -/
@[expose]
def slotBaseCoefficient (d : ℕ) : ℝ := Real.sqrt (2 * d) * 580

theorem slotBaseCoefficient_nonneg (d : ℕ) : 0 ≤ slotBaseCoefficient d :=
  mul_nonneg (Real.sqrt_nonneg _) (by norm_num)

/-- **The supply value in slot shape.**  This is `supply_value_bound`
instantiated at the supply's own pieces. -/
theorem supply_value_slot_bound (d : ℕ) {Csub Msc Y c : ℝ} {m : ℕ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcY : c ≤ 4 * Y)
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hY0 : 0 ≤ Y) :
    Real.sqrt (2 * d) * 1 *
        ((2 + 4 * (1 + c) ^ 2) *
            (Csub * ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc) +
          4 * (1 + c) ^ 2 *
            (36 * (Y + (1 / 2 : ℝ) * (3 : ℝ) ^ (-(m : ℝ)))) + c) ≤
      slotSourceValue d Csub Msc m + slotBaseCoefficient d * Y := by
  have hX0 : 0 ≤ Csub * ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc := by
    have hpow : (0 : ℝ) ≤ ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_nonneg (mul_nonneg hCsub hpow) hMsc
  have hZ0 : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (-(m : ℝ)) := by
    have : (0 : ℝ) ≤ (3 : ℝ) ^ (-(m : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    linarith only [this]
  have hbase := supply_value_bound (X := Csub * ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc)
    (Y := Y) (Z := (1 / 2 : ℝ) * (3 : ℝ) ^ (-(m : ℝ))) (c := c) (cN := 1)
    (dd := Real.sqrt (2 * d)) hc0 hc1 hcY hX0 hY0 hZ0 (by norm_num)
    (Real.sqrt_nonneg _)
  rw [slotSourceValue, slotBaseCoefficient]
  calc Real.sqrt (2 * d) * 1 *
        ((2 + 4 * (1 + c) ^ 2) *
            (Csub * ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc) +
          4 * (1 + c) ^ 2 *
            (36 * (Y + (1 / 2 : ℝ) * (3 : ℝ) ^ (-(m : ℝ)))) + c)
      ≤ Real.sqrt (2 * d) * 1 *
          (18 * (Csub * ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc) +
            576 * ((1 / 2 : ℝ) * (3 : ℝ) ^ (-(m : ℝ)))) +
          Real.sqrt (2 * d) * 1 * 580 * Y := hbase
    _ = Real.sqrt (2 * d) *
          (18 * (Csub * ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc) +
            576 * ((1 / 2 : ℝ) * (3 : ℝ) ^ (-(m : ℝ)))) +
          Real.sqrt (2 * d) * 580 * Y := by ring

/-- The subdivision power in real-exponent form. -/
theorem cast_three_pow_rpow (d m : ℕ) :
    ((3 ^ (d * m) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) =
      (3 : ℝ) ^ (-((d : ℝ) / 2) * (m : ℝ)) := by
  have hcast : ((3 ^ (d * m) : ℕ) : ℝ) = (3 : ℝ) ^ ((d * m : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  rw [hcast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-- **The per-leg source in shallow-leg shape.**  This is the form
`slot_source_sum_split_sharp` consumes, at `e = d/2`. -/
theorem slotSourceValue_eq (d : ℕ) (Csub Msc : ℝ) (m : ℕ) :
    slotSourceValue d Csub Msc m =
      (Real.sqrt (2 * d) * 18 * Csub * Msc) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * (m : ℝ)) +
        (Real.sqrt (2 * d) * 288) * (3 : ℝ) ^ (-(1 : ℝ) * (m : ℝ)) := by
  rw [slotSourceValue, cast_three_pow_rpow]
  have hone : (3 : ℝ) ^ (-(m : ℝ)) = (3 : ℝ) ^ (-(1 : ℝ) * (m : ℝ)) := by
    congr 1
    ring
  rw [hone]
  ring

theorem slotSourceValue_nonneg (d : ℕ) {Csub Msc : ℝ} (hCsub : 0 ≤ Csub)
    (hMsc : 0 ≤ Msc) (m : ℕ) : 0 ≤ slotSourceValue d Csub Msc m := by
  rw [slotSourceValue_eq]
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / 2) * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 : ℝ) * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have h3 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 18 * Csub * Msc := by
    have := Real.sqrt_nonneg (2 * (d : ℝ))
    positivity
  have h4 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 288 := by
    have := Real.sqrt_nonneg (2 * (d : ℝ))
    positivity
  exact add_nonneg (mul_nonneg h3 h1) (mul_nonneg h4 h2)

end

end HCPolySupport.HighContrast.Quenched
