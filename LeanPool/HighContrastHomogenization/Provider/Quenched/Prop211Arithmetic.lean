/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.RenormalizationParameterArithmetic
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedContrastAntitone

/-!
# High-contrast homogenization: Provider.Quenched.Prop211Arithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Arithmetic for the one-time rebase

The constants in this file are selected before the coefficient law.  The
triadic bracket is selected afterwards from the law's polynomial base.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- A positive enlargement below one that preserves a prescribed strict
small-contrast margin. -/
theorem exists_rebase_enlargement {cSc cStar : ℝ}
    (hc : cStar ∈ Set.Ioo (0 : ℝ) cSc) :
    ∃ delta : ℝ, delta ∈ Set.Ioo (0 : ℝ) 1 ∧
      (1 + delta) ^ 2 * (1 + cStar) ≤ 1 + cSc := by
  let e : ℝ := min (1 / 2) ((cSc - cStar) / (8 * (1 + cStar)))
  have hstar1 : 0 < 1 + cStar := by linarith only [hc.1]
  have hgap : 0 < cSc - cStar := sub_pos.mpr hc.2
  have he0 : 0 < e := by
    dsimp only [e]
    exact lt_min (by norm_num) (div_pos hgap (by positivity))
  have he2 : e ≤ 1 / 2 := min_le_left _ _
  have hegap : e ≤ (cSc - cStar) / (8 * (1 + cStar)) := min_le_right _ _
  have he1 : e ≤ 1 := by linarith only [he2]
  have heSq : e ^ 2 ≤ e := by nlinarith only [he0, he1]
  have hmul : 8 * e * (1 + cStar) ≤ cSc - cStar := by
    have hden : 0 < 8 * (1 + cStar) := by positivity
    have := (le_div_iff₀ hden).mp hegap
    nlinarith only [this]
  refine ⟨e, ⟨he0, by linarith only [he2]⟩, ?_⟩
  calc
    (1 + e) ^ 2 * (1 + cStar)
        = 1 + cStar + (2 * e + e ^ 2) * (1 + cStar) := by ring
    _ ≤ 1 + cStar + 3 * e * (1 + cStar) := by
      have hcoef : 2 * e + e ^ 2 ≤ 3 * e := by
        linarith only [heSq]
      have hterm := mul_le_mul_of_nonneg_right hcoef hstar1.le
      exact add_le_add_right hterm (1 + cStar)
    _ ≤ 1 + cSc := by
      have hsmall : 3 * e * (1 + cStar) ≤ 8 * e * (1 + cStar) := by
        have heStar : 0 ≤ e * (1 + cStar) := mul_nonneg he0.le hstar1.le
        nlinarith only [heStar]
      linarith only [hmul, hsmall]

variable {d : ℕ}

/-- The polynomial base of the rebase is uniformly at least three. -/
theorem three_le_rebaseBase [NeZero d] {P : MeasureTheory.Measure (CoeffSpace d)}
    [MeasureTheory.IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S) :
    3 ≤ 2 + aspectRatio E * K := by
  have hA : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hK : 1 < K := hdag.one_lt_growthWitness
  have hprod : 1 ≤ aspectRatio E * K := by
    nlinarith only [hA, hK]
  linarith only [hprod]

/-- A bracket for the square of a base at least three costs at most four
powers of that base. -/
theorem pow_three_bracket_sq_le_four {base : ℝ} {q : ℕ}
    (hbase : 3 ≤ base) (hlow : base ^ 2 ≤ (3 : ℝ) ^ (q : ℤ))
    (hupp : (3 : ℝ) ^ (q : ℤ) ≤ 1 + 3 * base ^ 2) :
    1 ≤ q ∧ (3 : ℝ) ^ (q : ℤ) ≤ base ^ (4 : ℕ) := by
  have hbase0 : 0 < base := lt_of_lt_of_le (by norm_num) hbase
  have hq : 1 ≤ q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    have hsq : base ^ 2 ≤ 1 := by simpa [hq0] using hlow
    nlinarith only [hbase, hsq]
  have hone : 1 ≤ base ^ 2 := by nlinarith only [sq_nonneg base, hbase]
  have hnine : 9 ≤ base ^ 2 := by nlinarith only [hbase]
  have hlarge : 1 + 3 * base ^ 2 ≤ base ^ 2 * base ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hnine (sq_nonneg base)
    nlinarith only [hmul, hone]
  refine ⟨hq, ?_⟩
  calc
    (3 : ℝ) ^ (q : ℤ) ≤ 1 + 3 * base ^ 2 := hupp
    _ ≤ base ^ 2 * base ^ 2 := hlarge
    _ = base ^ (4 : ℕ) := by ring

/-- The lower-floor parameter follows from the selected gain multiplier. -/
theorem T_le_renormBase_of_gain_bound
    {gamma nu mu delta Gain G0 T base : ℝ} {l0 h D q : ℕ}
    (hT : 1 ≤ T) (hdelta : 0 < delta) (hGain : 0 < Gain)
    (hGainBound : Gain ≤ G0 * base)
    (hpow : G0 * T / delta * base ≤
      (3 : ℝ) ^ (mu * ((D * q : ℕ) : ℝ) - mu))
    (hexp : gamma - nu + mu * ((l0 : ℝ) - (h : ℝ)) =
      mu * ((D * q : ℕ) : ℝ) - mu) :
    T ≤ renormBase gamma nu mu delta Gain l0 h := by
  let R : ℝ := (3 : ℝ) ^ (mu * ((D * q : ℕ) : ℝ) - mu)
  have hR : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hgainT : Gain * T ≤ G0 * base * T :=
    mul_le_mul_of_nonneg_right hGainBound hT0
  have hscaled := mul_le_mul_of_nonneg_left hpow hdelta.le
  have hscaleEq : delta * (G0 * T / delta * base) = G0 * base * T := by
    field_simp
  rw [hscaleEq] at hscaled
  have hmain : Gain * T ≤ delta * R := hgainT.trans (by simpa only [R] using hscaled)
  have hTR : T ≤ Gain⁻¹ * delta * R := by
    rw [show Gain⁻¹ * delta * R = delta * R / Gain by field_simp]
    exact (le_div_iff₀ hGain).2 (by simpa only [mul_comm] using hmain)
  rw [renormBase, hexp]
  exact hTR

/-- The old-reference comparison is absorbed by the exponent gap across the
selected recent window. -/
theorem kappa_burn_of_multiplier {kappa delta diff base : ℝ} {A q : ℕ}
    (hdelta : 0 < delta) (hq : 1 ≤ q)
    (hcoef : 0 ≤ diff * (A : ℝ) - 1)
    (hfixed : 12 / (1 + delta) ≤
      (3 : ℝ) ^ (diff * (A : ℝ) - 1))
    (hbase0 : 0 ≤ base) (hbaseq : base ≤ (3 : ℝ) ^ q)
    (hkappa : kappa ≤ 6 * base) :
    2 * kappa ≤ (1 + delta) * (3 : ℝ) ^ (diff * ((A * q : ℕ) : ℝ)) := by
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbaseq' : base ≤ (3 : ℝ) ^ (q : ℝ) := by
    rwa [Real.rpow_natCast]
  have hmul : 12 / (1 + delta) * base ≤
      (3 : ℝ) ^ (diff * (A : ℝ) - 1 + (q : ℝ)) := by
    calc
      12 / (1 + delta) * base ≤
          (3 : ℝ) ^ (diff * (A : ℝ) - 1) * (3 : ℝ) ^ (q : ℝ) :=
        (mul_le_mul_of_nonneg_right hfixed hbase0).trans
          (mul_le_mul_of_nonneg_left hbaseq'
            (Real.rpow_nonneg (by norm_num) _))
      _ = (3 : ℝ) ^ (diff * (A : ℝ) - 1 + (q : ℝ)) := by
        rw [Real.rpow_add (by norm_num)]
  have hexp : diff * (A : ℝ) - 1 + (q : ℝ) ≤
      diff * ((A * q : ℕ) : ℝ) := by
    push_cast
    have hnonneg := mul_nonneg hcoef (sub_nonneg.mpr hqreal)
    nlinarith only [hnonneg]
  have hmul' : 12 / (1 + delta) * base ≤
      (3 : ℝ) ^ (diff * ((A * q : ℕ) : ℝ)) :=
    hmul.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  have hleft : 2 * kappa ≤ 12 * base := by linarith only [hkappa]
  have hdelta1 : 0 < 1 + delta := by linarith only [hdelta]
  have hscaled := mul_le_mul_of_nonneg_left hmul' hdelta1.le
  have hscaled' : 12 * base ≤ (1 + delta) *
      (3 : ℝ) ^ (diff * ((A * q : ℕ) : ℝ)) := by
    have heq : (1 + delta) * (12 / (1 + delta) * base) = 12 * base := by
      field_simp
    rwa [heq] at hscaled
  exact hleft.trans hscaled'

end

end HCPolySupport.HighContrast.Quenched
