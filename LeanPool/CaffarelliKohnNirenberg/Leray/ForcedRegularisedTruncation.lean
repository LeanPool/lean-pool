/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLipschitz

/-!
# Radial truncation of the regularized tensor

To solve `eq:reg-mild-forced` on a whole interval at once, the velocity in
the regularized tensor is first retracted onto a ball of radius `R`. The
retraction is a scalar multiple of the velocity with factor in `[0, 1]`, it is
`2`-Lipschitz, and it is the identity inside the ball; the truncated tensor is
therefore globally Lipschitz. The energy bound of `lem:regularised-forced`
later shows that the truncation is inactive.
-/

public section

open MeasureTheory

noncomputable section

namespace CKN.Leray

/-- The radial truncation factor `min(1, R/‖v‖)`. -/
@[expose]
def forcedTruncFactor (R : ℝ) (v : RealVectorL2) : ℝ :=
  if ‖v‖ ≤ R then 1 else R / ‖v‖

/-- The radial retraction onto the ball of radius `R`. -/
@[expose]
def forcedTrunc (R : ℝ) (v : RealVectorL2) : RealVectorL2 :=
  forcedTruncFactor R v • v

theorem forcedTruncFactor_nonneg {R : ℝ} (hR : 0 ≤ R) (v : RealVectorL2) :
    0 ≤ forcedTruncFactor R v := by
  unfold forcedTruncFactor
  split_ifs
  · exact zero_le_one
  · positivity

theorem forcedTruncFactor_le_one (R : ℝ) (v : RealVectorL2) : forcedTruncFactor R v ≤ 1 := by
  unfold forcedTruncFactor
  split_ifs with h
  · exact le_rfl
  · exact div_le_one_of_le₀ (not_le.1 h).le (norm_nonneg v)

theorem forcedTrunc_of_norm_le {R : ℝ} {v : RealVectorL2} (hv : ‖v‖ ≤ R) :
    forcedTrunc R v = v := by
  simp [forcedTrunc, forcedTruncFactor, hv]

theorem norm_forcedTrunc_le {R : ℝ} (hR : 0 ≤ R) (v : RealVectorL2) :
    ‖forcedTrunc R v‖ ≤ R := by
  unfold forcedTrunc forcedTruncFactor
  split_ifs with h
  · simpa using h
  · have hv : 0 < ‖v‖ := hR.trans_lt (not_le.1 h)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_cancel₀ _ hv.ne']

/-- The truncation factors of two vectors differ, after multiplication by the
second norm, by at most the difference of the norms. -/
theorem abs_forcedTruncFactor_sub_mul_le {R : ℝ} (hR : 0 ≤ R) (v w : RealVectorL2) :
    |forcedTruncFactor R v - forcedTruncFactor R w| * ‖w‖ ≤ |‖v‖ - ‖w‖| := by
  set a := ‖v‖ with ha
  set b := ‖w‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg v
  have hb0 : 0 ≤ b := norm_nonneg w
  unfold forcedTruncFactor
  rw [← ha, ← hb]
  by_cases hva : a ≤ R <;> by_cases hwb : b ≤ R
  · simp [hva, hwb]
  · simp only [hva, hwb, ↓reduceIte]
    have hbR : R < b := not_le.1 hwb
    have hb' : 0 < b := hR.trans_lt hbR
    have hle : R / b ≤ 1 := (div_le_one hb').2 hbR.le
    rw [abs_of_nonneg (by linarith only [hle]), sub_mul, one_mul, div_mul_cancel₀ _ hb'.ne',
      abs_of_nonpos (by linarith only [hva, hbR])]
    linarith only [hva]
  · simp only [hva, hwb, ↓reduceIte]
    have haR : R < a := not_le.1 hva
    have ha' : 0 < a := hR.trans_lt haR
    have hle : R / a ≤ 1 := (div_le_one ha').2 haR.le
    rw [abs_of_nonpos (by linarith only [hle]), abs_of_nonneg (by linarith only [haR, hwb])]
    have h1 : -(R / a - 1) * b ≤ -(R / a - 1) * R :=
      mul_le_mul_of_nonneg_left hwb (by linarith only [hle])
    have h2 : -(R / a - 1) * R ≤ a - R := by
      have : -(R / a - 1) * R = R - R * R / a := by field_simp; ring
      rw [this]
      have h3 : R * R / a ≥ 2 * R - a := by
        rw [ge_iff_le, le_div_iff₀ ha']
        nlinarith only [sq_nonneg (a - R)]
      linarith only [h3]
    linarith only [h1, h2, hwb]
  · simp only [hva, hwb, ↓reduceIte]
    have haR : R < a := not_le.1 hva
    have hbR : R < b := not_le.1 hwb
    have ha' : 0 < a := hR.trans_lt haR
    have hb' : 0 < b := hR.trans_lt hbR
    have heq : (R / a - R / b) * b = R * (b - a) / a := by field_simp
    have key : |R / a - R / b| * b = R * |a - b| / a := by
      calc |R / a - R / b| * b = |(R / a - R / b) * b| := by rw [abs_mul, abs_of_nonneg hb0]
        _ = |R * (b - a) / a| := by rw [heq]
        _ = R * |a - b| / a := by
          rw [abs_div, abs_mul, abs_of_nonneg hR, abs_of_pos ha', abs_sub_comm]
    rw [key, div_le_iff₀ ha']
    exact mul_le_mul_of_nonneg_right haR.le (abs_nonneg _) |>.trans_eq (mul_comm _ _)

/-- The radial retraction is `2`-Lipschitz. -/
theorem norm_forcedTrunc_sub_le {R : ℝ} (hR : 0 ≤ R) (v w : RealVectorL2) :
    ‖forcedTrunc R v - forcedTrunc R w‖ ≤ 2 * ‖v - w‖ := by
  unfold forcedTrunc
  have hdecomp : forcedTruncFactor R v • v - forcedTruncFactor R w • w =
      forcedTruncFactor R v • (v - w) + (forcedTruncFactor R v - forcedTruncFactor R w) • w := by
    rw [smul_sub, sub_smul]
    abel
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (forcedTruncFactor_nonneg hR v)]
  have h1 : forcedTruncFactor R v * ‖v - w‖ ≤ ‖v - w‖ :=
    mul_le_of_le_one_left (norm_nonneg _) (forcedTruncFactor_le_one R v)
  have h2 := abs_forcedTruncFactor_sub_mul_le hR v w
  have h3 : |‖v‖ - ‖w‖| ≤ ‖v - w‖ := abs_norm_sub_norm_le v w
  linarith only [h1, h2, h3]

/-- The regularized tensor of the truncated velocity. -/
@[expose]
def forcedTruncTensor (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (R : ℝ)
    (v : RealVectorL2) : RealTensorL2 :=
  regularizedMildTensor ρ ε hε (forcedTrunc R v)

theorem norm_forcedTruncTensor_le (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {R : ℝ}
    (hR : 0 ≤ R) (v : RealVectorL2) :
    ‖forcedTruncTensor ρ ε hε R v‖ ≤ regularizedMildMollifierConstant ρ ε * R ^ 2 := by
  refine (regularizedMildTensor_norm_le ρ ε hε _).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_forcedTrunc_le hR v) 2)
    ((ENNReal.toReal_nonneg : 0 ≤ regularizedMildMollifierConstant ρ ε))

theorem norm_forcedTruncTensor_sub_le (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {R : ℝ}
    (hR : 0 ≤ R) (v w : RealVectorL2) :
    ‖forcedTruncTensor ρ ε hε R v - forcedTruncTensor ρ ε hε R w‖ ≤
      4 * regularizedMildMollifierConstant ρ ε * R * ‖v - w‖ := by
  refine (regularizedMildTensor_sub_norm_le ρ ε hε _ _).trans ?_
  have hK := (ENNReal.toReal_nonneg : 0 ≤ regularizedMildMollifierConstant ρ ε)
  have h1 := norm_forcedTrunc_le hR v
  have h2 := norm_forcedTrunc_le hR w
  have h3 := norm_forcedTrunc_sub_le hR v w
  calc regularizedMildMollifierConstant ρ ε * (‖forcedTrunc R v‖ + ‖forcedTrunc R w‖) *
        ‖forcedTrunc R v - forcedTrunc R w‖
      ≤ regularizedMildMollifierConstant ρ ε * (R + R) * (2 * ‖v - w‖) := by
        gcongr
    _ = 4 * regularizedMildMollifierConstant ρ ε * R * ‖v - w‖ := by ring

end CKN.Leray

end
