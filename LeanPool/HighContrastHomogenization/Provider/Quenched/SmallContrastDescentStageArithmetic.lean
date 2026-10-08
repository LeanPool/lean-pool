/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEchoWitness

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastDescentStageArithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The round arithmetic of the adaptive-depth descent

The descent at level-adapted lag proceeds in stages; this module collects the
four arithmetic facts those stages live on.

* `geometric_le_of_logb` — the generic threshold: a geometric term
  `C·3^{−rate·L}` sits below a positive target once `L` exceeds the
  explicit logarithm.  Instantiated twice downstream: the second error
  term `S_Π·3^{−2(ν−γ)·L}` at the level-adapted lag, and the drop-channel
  memory `A·δ₀·ra^T` at the stage length.
* the lag telescoping: when each stage at least
  doubles the level's logarithm, the SUM of the round lags is at most
  twice the final one.  The total threshold is therefore linear in
  `log₃ Π + log(1/λ_final)`, with no `loglog` accumulation: the round
  count enters only through the per-round constant factor.
* the first error term's absolute part:
  `S·3^{2(γ·L − k)} ≤ S·3^{−2(1−γ)k}` for any lag `L ≤ k`, hence below
  target for `k` past the explicit burn-in.
* the prefactor identity — the compounded per-stage constant `C^J`
  rewritten as `3^{J·log₃C}`, the form `hpref` absorbs (the stage count
  `J` is logarithmic in the total scale, so this is the polylog factor).
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- A geometric term sits below a positive target past the explicit
logarithmic threshold. -/
theorem geometric_le_of_logb {C target rate : ℝ} (hC : 0 < C)
    (htarget : 0 < target) (hrate : 0 < rate) {L : ℝ}
    (hL : Real.logb 3 (C / target) / rate ≤ L) :
    C * (3 : ℝ) ^ (-(rate * L)) ≤ target := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  have hCt : 0 < C / target := div_pos hC htarget
  have hlog : Real.logb 3 (C / target) ≤ rate * L := by
    have := mul_le_mul_of_nonneg_left hL hrate.le
    calc Real.logb 3 (C / target) =
        rate * (Real.logb 3 (C / target) / rate) := by
          field_simp
      _ ≤ rate * L := this
  have hle : C / target ≤ (3 : ℝ) ^ (rate * L) := by
    calc C / target = (3 : ℝ) ^ Real.logb 3 (C / target) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hCt).symm
      _ ≤ (3 : ℝ) ^ (rate * L) :=
          Real.rpow_le_rpow_of_exponent_le h3.le hlog
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (rate * L) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hCle : C ≤ (3 : ℝ) ^ (rate * L) * target := by
    have := mul_le_mul_of_nonneg_right hle htarget.le
    calc C = C / target * target := by field_simp
      _ ≤ (3 : ℝ) ^ (rate * L) * target := this
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  calc C * ((3 : ℝ) ^ (rate * L))⁻¹ ≤
      (3 : ℝ) ^ (rate * L) * target * ((3 : ℝ) ^ (rate * L))⁻¹ :=
        mul_le_mul_of_nonneg_right hCle (inv_pos.mpr hpow).le
    _ = target := by field_simp

end

end HCPolySupport.HighContrast.Quenched
