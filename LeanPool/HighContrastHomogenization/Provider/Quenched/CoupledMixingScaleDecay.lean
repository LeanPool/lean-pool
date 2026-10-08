/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScale

/-!
# High-contrast homogenization: Provider.Quenched.CoupledMixingScaleDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Decay from a coupled mixing-scale certificate

The least triadic generation above a positive scale loses at most one factor
of three.  Combining that rounding with one nonnegative summand of the bad-row
series turns the coupled certificate into all-later decay.
-/

namespace HCPolySupport.HighContrast.Quenched

open Filter MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first natural triadic generation whose scale is at least `x`. -/
@[expose]
def triadicCeilingIndex (x : ℝ) : ℕ :=
  Nat.ceil (Real.log x / Real.log 3)

/-- A positive scale at least one is below its triadic ceiling. -/
theorem le_pow_triadicCeilingIndex {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (3 : ℝ) ^ triadicCeilingIndex x := by
  rw [← Real.rpow_natCast]
  simpa only [triadicCeilingIndex] using!
    Book.Ch05.Section57.le_rpow_three_natCeil_log_div_log hx

/-- The triadic ceiling is less than three times the original scale. -/
theorem pow_triadicCeilingIndex_le_three_mul {x : ℝ} (hx : 1 ≤ x) :
    (3 : ℝ) ^ triadicCeilingIndex x ≤ 3 * x := by
  rw [← Real.rpow_natCast]
  simpa only [triadicCeilingIndex] using!
    Book.Ch05.Section57.rpow_three_natCeil_log_div_log_le_three_mul hx

/-- Any natural generation whose triadic scale dominates `x` lies above the
triadic ceiling of `x`. -/
theorem triadicCeilingIndex_le_of_le_pow {x : ℝ} {m : ℕ}
    (hx : 1 ≤ x) (hxm : x ≤ (3 : ℝ) ^ m) :
    triadicCeilingIndex x ≤ m := by
  rw [triadicCeilingIndex, Nat.ceil_le]
  change Real.logb 3 x ≤ (m : ℝ)
  rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 3)
    (lt_of_lt_of_le zero_lt_one hx)]
  simpa only [Real.rpow_natCast] using hxm

private theorem triadic_gap_rpow_eq
    {n m : ℕ} (hnm : n ≤ m) (kappa : ℝ) :
    (((3 : ℝ) ^ m) / ((3 : ℝ) ^ n)) ^ (-kappa) =
      (3 : ℝ) ^ (-kappa * ((m - n : ℕ) : ℝ)) := by
  have hmn : m = n + (m - n) := (Nat.add_sub_of_le hnm).symm
  have hratio :
      ((3 : ℝ) ^ m) / ((3 : ℝ) ^ n) = (3 : ℝ) ^ (m - n) := by
    rw [hmn, pow_add]
    field_simp
    simp
  rw [hratio, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

private theorem triadic_weight_inv_eq_gap_rpow
    {n m : ℕ} (hnm : n ≤ m) (kappa : ℝ) :
    ((3 : ℝ) ^ (kappa * ((m - n : ℕ) : ℝ)))⁻¹ =
      (((3 : ℝ) ^ m) / ((3 : ℝ) ^ n)) ^ (-kappa) := by
  rw [triadic_gap_rpow_eq hnm]
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

private theorem rpow_neg_div_mono_of_le
    {A X Y kappa : ℝ} (hA : 0 < A) (hX : 0 < X) (hY : 0 < Y)
    (hXY : X ≤ Y) (hkappa : 0 < kappa) :
    (A / X) ^ (-kappa) ≤ (A / Y) ^ (-kappa) := by
  have hbaseX : 0 < A / X := div_pos hA hX
  have hbaseY : 0 < A / Y := div_pos hA hY
  have hbaseYX : A / Y ≤ A / X :=
    div_le_div_of_nonneg_left hA.le hX hXY
  exact
    (Real.rpow_le_rpow_iff_of_neg hbaseX hbaseY
      (neg_neg_of_pos hkappa)).2 hbaseYX

/-- The same selected certificate controls every later row relative to any
common scale that dominates its mixing scale.  The final normalizer pays for
the one-generation rounding of the stopping normalizer. -/
theorem CoupledMixingScaleWitness.eventually_row_le_scaled_rpow
    {P : Measure Ω} {selectedRow : ℕ → Ω → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta)
    {commonScale : Ω → ℝ}
    (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (hone : ∀ ω, 1 ≤ commonScale ω)
    (hscale : ∀ ω, W.scale ω ≤ commonScale ω) :
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      W.normalization * commonScale ω ≤ (3 : ℝ) ^ m →
        W.row m ω ≤
          delta *
            (((3 : ℝ) ^ m) /
              (W.normalization * commonScale ω)) ^ (-kappa) := by
  filter_upwards [W.eventually_weighted_row_lt]
    with ω hweighted
  intro m hm
  let x : ℝ := W.stoppingNormalization * commonScale ω
  let n : ℕ := triadicCeilingIndex x
  let j : ℕ := m - n
  have hx_one : 1 ≤ x := by
    exact one_le_mul_of_one_le_of_one_le
      W.one_le_stoppingNormalization (hone ω)
  have hx_pow : x ≤ (3 : ℝ) ^ n := by
    simpa only [n] using le_pow_triadicCeilingIndex hx_one
  have hpow_final :
      (3 : ℝ) ^ n ≤ W.normalization * commonScale ω := by
    have hround : (3 : ℝ) ^ n ≤ 3 * x := by
      simpa only [n] using pow_triadicCeilingIndex_le_three_mul hx_one
    have hbuffer := mul_le_mul_of_nonneg_right
      W.three_mul_stoppingNormalization_le
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (hone ω))
    calc
      (3 : ℝ) ^ n ≤ 3 * x := hround
      _ = (3 * W.stoppingNormalization) * commonScale ω := by
        simp only [x]
        ring
      _ ≤ W.normalization * commonScale ω := hbuffer
  have hn_m : n ≤ m := by
    exact triadicCeilingIndex_le_of_le_pow hx_one
      (hx_pow.trans (hpow_final.trans hm))
  have hn_add_j : n + j = m := by
    simpa only [j] using Nat.add_sub_of_le hn_m
  have hstop_scale :
      W.stoppingNormalization * W.scale ω ≤ (3 : ℝ) ^ n := by
    have hleft := mul_le_mul_of_nonneg_left (hscale ω)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1)
        W.one_le_stoppingNormalization)
    exact hleft.trans hx_pow
  have hrow_weighted :
      (3 : ℝ) ^ (kappa * (j : ℝ)) * W.row m ω < delta := by
    simpa only [hn_add_j] using hweighted n j hstop_scale
  have hweight_pos : 0 < (3 : ℝ) ^ (kappa * (j : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrow_div :
      W.row m ω < delta / (3 : ℝ) ^ (kappa * (j : ℝ)) := by
    apply (lt_div_iff₀ hweight_pos).2
    simpa only [mul_comm] using hrow_weighted
  have hdiv_gap :
      delta / (3 : ℝ) ^ (kappa * (j : ℝ)) =
        delta * ((((3 : ℝ) ^ m) / ((3 : ℝ) ^ n)) ^ (-kappa)) := by
    rw [div_eq_mul_inv]
    congr 1
    simpa only [j] using triadic_weight_inv_eq_gap_rpow hn_m kappa
  have hpow_m_pos : 0 < (3 : ℝ) ^ m := by positivity
  have hpow_n_pos : 0 < (3 : ℝ) ^ n := by positivity
  have hfinal_pos : 0 < W.normalization * commonScale ω :=
    mul_pos (lt_of_lt_of_le zero_lt_one W.one_le_normalization)
      (lt_of_lt_of_le zero_lt_one (hone ω))
  have hratio := rpow_neg_div_mono_of_le
    hpow_m_pos hpow_n_pos hfinal_pos hpow_final hkappa
  have hdelta_ratio := mul_le_mul_of_nonneg_left hratio hdelta.le
  exact le_of_lt (hrow_div.trans_le (hdiv_gap ▸ hdelta_ratio))

end


end HCPolySupport.HighContrast.Quenched
