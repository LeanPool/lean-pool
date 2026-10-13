/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.UniformExhaustionProfile

/-!
# UniformExhaustionBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Uniform exhaustion budgets

The shift-uniform profile has a finite cubic layer-cake budget.  Its cubic-log
cutoff also has an explicit subpolynomial growth bound for exponents strictly
between one and two.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open HCPolySupport
open HCPolySupport.Book.Ch02
open MeasureTheory Set

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The uniform cubic layer-cake budget. -/
def streamUniformExhaustionBudget (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ  :=
  (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal
    (streamUniformExhaustionEnvelope M omega s * s ^ 3)).toReal

/-- The explicit constant in the subpolynomial cutoff-growth estimate. -/
def streamUniformExhaustionGrowth (M : ABKModel d)
    (omega : FullSample d M.gamma) (q : ℝ) : ℝ :=
  if 1 < q ∧ q < 2 then
    streamUniformExhaustionScale M omega ^ 12 *
      (1 + 12 / (2 - q)) ^ 12
  else 0

omit [NeZero d] in
private theorem streamUniformExhaustionRate_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    0 < streamUniformExhaustionRate M omega := by
  unfold streamUniformExhaustionRate
  exact div_pos (streamTailDecayConst_pos M omega) (by norm_num)

omit [NeZero d] in
private theorem streamUniformExhaustionScale_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    0 < streamUniformExhaustionScale M omega := by
  unfold streamUniformExhaustionScale
  have hp : 0 < streamTailAmplitudeExponent M := by
    unfold streamTailAmplitudeExponent
    have he := streamFreezingExponent_pos M
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hprod := mul_nonneg hd he.le
    linarith only [hprod]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc := streamTailDecayConst_pos M omega
  have hnum : 0 < 1 + streamTailAmplitudeExponent M + (d : ℝ) + 1 := by
    linarith only [hp, hd]
  have hterm : 0 < 100000 *
      (1 + streamTailAmplitudeExponent M + (d : ℝ) + 1) /
        streamTailDecayConst M omega := by positivity
  linarith only [hterm]

omit [NeZero d] in
private theorem one_le_streamUniformExhaustionScale (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    1 ≤ streamUniformExhaustionScale M omega := by
  unfold streamUniformExhaustionScale
  have hp : 0 < streamTailAmplitudeExponent M := by
    unfold streamTailAmplitudeExponent
    have he := streamFreezingExponent_pos M
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hprod := mul_nonneg hd he.le
    linarith only [hprod]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc := streamTailDecayConst_pos M omega
  have hterm : 0 ≤ 100000 *
      (1 + streamTailAmplitudeExponent M + (d : ℝ) + 1) /
        streamTailDecayConst M omega := by positivity
  linarith only [hterm]

private theorem one_le_streamUniformShiftWeight (lam : ℝ) :
    1 ≤ streamUniformShiftWeight lam := by
  unfold streamUniformShiftWeight
  have hmax : (1 : ℝ) ≤ max lam 1 := le_max_right _ _
  exact le_add_of_nonneg_right (Real.log_nonneg hmax)

omit [NeZero d] in
private theorem continuous_streamUniformExhaustionEnvelope
    (M : ABKModel d) (omega : FullSample d M.gamma) :
    Continuous (streamUniformExhaustionEnvelope M omega)  := by
  unfold streamUniformExhaustionEnvelope
  have hmax : Continuous (fun s : ℝ ↦ max s 0) :=
    continuous_id.max continuous_const
  have hroot : Continuous (fun s : ℝ ↦ (max s 0) ^ (1 / 3 : ℝ)) :=
    hmax.rpow_const (fun _ ↦ Or.inr (show (0 : ℝ) ≤ 1 / 3 by norm_num))
  have harg : Continuous (fun s : ℝ ↦
      -(streamUniformExhaustionRate M omega * (max s 0) ^ (1 / 3 : ℝ))) :=
    (continuous_const.mul hroot).neg
  exact continuous_const.mul harg.rexp

omit [NeZero d] in
private theorem integrableOn_streamUniformExhaustionEnvelope_mul_cube
    (M : ABKModel d) (omega : FullSample d M.gamma) :
    IntegrableOn
      (fun s : ℝ ↦ streamUniformExhaustionEnvelope M omega s * s ^ 3)
      (Ioi 1)  := by
  let A := streamTailAmplitudeConst M omega
  let b := streamUniformExhaustionRate M omega
  have hb : 0 < b := streamUniformExhaustionRate_pos M omega
  have hbase : IntegrableOn
      (fun s : ℝ ↦ s ^ (3 : ℝ) * Real.exp (-b * s ^ (1 / 3 : ℝ)))
      (Ioi 0) := by
    rw [← integrableOn_Ioi_comp_rpow_iff'
      (fun s : ℝ ↦ s ^ (3 : ℝ) * Real.exp (-b * s ^ (1 / 3 : ℝ)))
      (show (3 : ℝ) ≠ 0 by norm_num)]
    have hmajor : IntegrableOn
        (fun x : ℝ ↦ x ^ (11 : ℝ) * Real.exp (-b * x ^ (1 : ℝ)))
        (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := (11 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num) hb
    refine hmajor.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := hx.le
    have hroot : (x ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = x := by
      rw [← Real.rpow_mul hx0, show (3 : ℝ) * (1 / 3 : ℝ) = 1 by norm_num,
        Real.rpow_one]
    change x ^ (11 : ℝ) * Real.exp (-b * x ^ (1 : ℝ)) =
      x ^ ((3 : ℝ) - 1) *
        ((x ^ (3 : ℝ)) ^ (3 : ℝ) *
          Real.exp (-b * (x ^ (3 : ℝ)) ^ (1 / 3 : ℝ)))
    rw [hroot, show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_one]
    rw [← Real.rpow_mul hx0]
    rw [show x ^ (2 : ℝ) * (x ^ ((3 : ℝ) * 3) * Real.exp (-b * x)) =
      (x ^ (2 : ℝ) * x ^ ((3 : ℝ) * 3)) * Real.exp (-b * x) by ring]
    rw [← Real.rpow_add hx, show (2 : ℝ) + 3 * 3 = 11 by norm_num]
  have hrestricted : IntegrableOn
      (fun s : ℝ ↦ A * (s ^ (3 : ℝ) * Real.exp (-b * s ^ (1 / 3 : ℝ))))
      (Ioi 1) := IntegrableOn.mono_set (hbase.const_mul A)
    (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro s hs
      exact zero_lt_one.trans (show 1 < s from hs))
  refine hrestricted.congr_fun ?_ measurableSet_Ioi
  intro s hs
  have hs0 : 0 ≤ s := (zero_lt_one.trans (show 1 < s from hs)).le
  dsimp only [A, b]
  unfold streamUniformExhaustionEnvelope
  rw [max_eq_left hs0]
  change streamTailAmplitudeConst M omega *
      (Real.rpow s ((3 : ℕ) : ℝ) * Real.exp
        (-streamUniformExhaustionRate M omega * s ^ (1 / 3 : ℝ))) =
    streamTailAmplitudeConst M omega *
      Real.exp (-(streamUniformExhaustionRate M omega * s ^ (1 / 3 : ℝ))) * s ^ 3
  have hpoweq : Real.rpow s ((3 : ℕ) : ℝ) = s ^ (3 : ℕ) :=
    Real.rpow_natCast s 3
  rw [hpoweq]
  ring_nf

omit [NeZero d] in
/-- The displayed uniform budget is nonnegative. -/
theorem streamUniformExhaustionBudget_nonneg (M : ABKModel d) (omega : FullSample d M.gamma) :
    0 ≤ streamUniformExhaustionBudget M omega  :=
  ENNReal.toReal_nonneg

omit [NeZero d] in
/-- Above the cutting radius, the cubic layer-cake integral is bounded by the
shift-independent displayed budget. -/
theorem lintegral_streamUniformExhaustionProfile_mul_cube_le
    (M : ABKModel d) (omega : FullSample d M.gamma)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    ∫⁻ s in Ioi (streamUniformExhaustionCutoff M omega lam),
        ENNReal.ofReal (streamUniformExhaustionProfile M omega lam s * s ^ 3) ≤
      ENNReal.ofReal (streamUniformExhaustionBudget M omega)  := by
  have hweight : 1 ≤ streamUniformShiftWeight lam := by
    unfold streamUniformShiftWeight
    rw [max_eq_left hlam]
    exact le_add_of_nonneg_right (Real.log_nonneg hlam)
  have hcut : 1 ≤ streamUniformExhaustionCutoff M omega lam := by
    unfold streamUniformExhaustionCutoff
    apply one_le_pow₀
    nlinarith only [one_le_streamUniformExhaustionScale M omega, hweight]
  have hmono : Ioi (streamUniformExhaustionCutoff M omega lam) ⊆ Ioi (1 : ℝ) := by
    intro s hs
    exact lt_of_le_of_lt hcut hs
  have hcont := (continuous_streamUniformExhaustionEnvelope M omega).mul
    (continuous_id.pow 3)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))]
      fun s : ℝ ↦ streamUniformExhaustionEnvelope M omega s * s ^ 3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg
      (mul_nonneg (streamTailAmplitudeConst_nonneg M omega) (Real.exp_pos _).le)
      (pow_nonneg (le_of_lt (zero_lt_one.trans hs)) 3)
  have hne : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal
      (streamUniformExhaustionEnvelope M omega s * s ^ 3)) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hcont.aestronglyMeasurable hnonneg).2
      (integrableOn_streamUniformExhaustionEnvelope_mul_cube M omega)
  calc
    ∫⁻ s in Ioi (streamUniformExhaustionCutoff M omega lam),
        ENNReal.ofReal (streamUniformExhaustionProfile M omega lam s * s ^ 3) =
        ∫⁻ s in Ioi (streamUniformExhaustionCutoff M omega lam),
          ENNReal.ofReal (streamUniformExhaustionEnvelope M omega s * s ^ 3) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      unfold streamUniformExhaustionProfile
      change ENNReal.ofReal
        ((if streamUniformExhaustionCutoff M omega lam < s then
          streamUniformExhaustionEnvelope M omega s else 1) * s ^ 3) = _
      rw [ite_eq_left (show streamUniformExhaustionCutoff M omega lam < s from hs)]
    _ ≤ ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal
          (streamUniformExhaustionEnvelope M omega s * s ^ 3) :=
      lintegral_mono_set hmono
    _ = ENNReal.ofReal (streamUniformExhaustionBudget M omega) := by
      unfold streamUniformExhaustionBudget
      rw [ENNReal.ofReal_toReal hne]

omit [NeZero d] in
/-- The cutoff-growth coefficient is nonnegative in the admissible exponent
range. -/
theorem streamUniformExhaustionGrowth_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    0 ≤ streamUniformExhaustionGrowth M omega q := by
  unfold streamUniformExhaustionGrowth
  rw [ite_eq_left ⟨hq1, hq2⟩]
  exact mul_nonneg (pow_nonneg (streamUniformExhaustionScale_pos M omega).le _)
    (pow_nonneg (by have : 0 < 2 - q := sub_pos.mpr hq2; positivity) _)

omit [NeZero d] in
/-- The fourth power of the cubic-log cutoff is subpolynomial in the shift,
with an explicit coefficient for every fixed exponent `q ∈ (1,2)`. -/
theorem streamUniformExhaustionCutoff_pow_le
    (M : ABKModel d) (omega : FullSample d M.gamma)
    {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    streamUniformExhaustionCutoff M omega lam ^ 4 ≤
      streamUniformExhaustionGrowth M omega q * lam ^ (2 - q) := by
  let eps : ℝ := (2 - q) / 12
  let C : ℝ := 1 + 12 / (2 - q)
  have heps : 0 < eps := by
    unfold eps
    exact div_pos (sub_pos.mpr hq2) (by norm_num)
  have hlam0 : 0 ≤ lam := zero_le_one.trans hlam
  have hlamPos : 0 < lam := zero_lt_one.trans_le hlam
  have hpowOne : 1 ≤ lam ^ eps := Real.one_le_rpow hlam heps.le
  have hlog := Real.log_le_rpow_div hlam0 heps
  have hweight : streamUniformShiftWeight lam ≤ C * lam ^ eps := by
    unfold streamUniformShiftWeight C eps
    rw [max_eq_left hlam]
    have hfactor : lam ^ ((2 - q) / 12) / ((2 - q) / 12) =
        lam ^ ((2 - q) / 12) * (12 / (2 - q)) := by
      field_simp [ne_of_gt (sub_pos.mpr hq2)]
    change Real.log lam ≤ lam ^ ((2 - q) / 12) / ((2 - q) / 12) at hlog
    rw [hfactor] at hlog
    calc
      1 + Real.log lam ≤ 1 + (lam ^ ((2 - q) / 12)) *
          (12 / (2 - q)) := by linarith only [hlog]
      _ ≤ lam ^ ((2 - q) / 12) +
          (lam ^ ((2 - q) / 12)) * (12 / (2 - q)) := by
        linarith only [hpowOne]
      _ = (1 + 12 / (2 - q)) * lam ^ ((2 - q) / 12) := by ring
  have hweightPow := pow_le_pow_left₀
    (by exact zero_le_one.trans (one_le_streamUniformShiftWeight lam)) hweight 12
  have hpowIdentity : (lam ^ eps) ^ 12 = lam ^ (2 - q) := by
    rw [← Real.rpow_mul_natCast hlam0]
    congr 1
    unfold eps
    ring
  unfold streamUniformExhaustionCutoff streamUniformExhaustionGrowth
  rw [ite_eq_left ⟨hq1, hq2⟩]
  rw [← pow_mul, show 3 * 4 = 12 by norm_num, mul_pow]
  calc
    streamUniformExhaustionScale M omega ^ 12 *
        streamUniformShiftWeight lam ^ 12 ≤
      streamUniformExhaustionScale M omega ^ 12 * (C * lam ^ eps) ^ 12 :=
        mul_le_mul_of_nonneg_left hweightPow
          (pow_nonneg (streamUniformExhaustionScale_pos M omega).le _)
    _ = streamUniformExhaustionScale M omega ^ 12 * C ^ 12 * lam ^ (2 - q) := by
      rw [mul_pow, hpowIdentity]
      ring
    _ = streamUniformExhaustionScale M omega ^ 12 *
        (1 + 12 / (2 - q)) ^ 12 * lam ^ (2 - q) := by rfl

end

end Algsuperdiff.Section5.Field
