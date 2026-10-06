/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeSubgaussianSums
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeGaussianGauge

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeConcentration

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Concentration for sums from unit range of dependence

The concentration-for-sums condition, with the parameters supplied by unit range
of dependence, asks that the normalized average of a family of centred
observables bounded by one, each carried by its own standard aligned cube of a
common scale, obey a weak-Orlicz tail at the exponent `ν = d/2` with a gauge
that depends on the dimension alone.

This file derives that condition from unit range of dependence.  The sub-Gaussian
moment bound of the colouring argument gives, through the Chernoff inequality
applied to the sum and to its negative, a two-sided Gaussian tail with a
dimensional prefactor two; the prefactor is absorbed into the dimensional
threshold constant `C_fr(d)`, leaving exactly the Gaussian concentration gauge
`Ψ_fr(t) = exp(c_fr(d) t²)`.  The averaged form is the printed display: the
average of `N` such observables is
`O_{Ψ_fr}(C_fr(d) N^{-1/2})`, and `N^{-1/2} = 3^{-ν(m-n)}` for the family of
scale-`n` cubes centred in `□_m`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory ProbabilityTheory

open scoped NNReal

noncomputable section

variable {d : ℕ}

/-! ## The two-sided Chernoff bound -/

/-- **The two-sided Gaussian tail of a sum of bounded centred local
observables.**  Both constants depend on the dimension alone. -/
theorem measureReal_abs_sum_standardCell_ge_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {k : ℤ} (hk : 0 ≤ k)
    {X : (Fin d → ℤ) → CoeffSpace d → ℝ}
    (hXloc : ∀ w, @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d k w)) _ (X w))
    (hXbd : ∀ w, ∀ᵐ a ∂P, |X w a| ≤ 1)
    (hXmean : ∀ w, ∫ a, X w a ∂P = 0) (Z : Finset (Fin d → ℤ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {a | ε ≤ |∑ w ∈ Z, X w a|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * ((3 ^ d * Z.card : ℕ) : ℝ))) := by
  have hSG := hasSubgaussianMGF_sum_standardCell hP hk hXloc hXbd hXmean Z
  have hSGneg := hSG.neg
  have h1 := hSG.measure_ge_le hε
  have h2 := hSGneg.measure_ge_le hε
  have h2' : P.real {a : CoeffSpace d | ε ≤ -∑ w ∈ Z, X w a} ≤
      Real.exp (-ε ^ 2 / (2 * ((3 ^ d * Z.card : ℕ) : ℝ))) := by
    simpa using h2
  have h1' : P.real {a : CoeffSpace d | ε ≤ ∑ w ∈ Z, X w a} ≤
      Real.exp (-ε ^ 2 / (2 * ((3 ^ d * Z.card : ℕ) : ℝ))) := by
    simpa using h1
  have hsub : {a : CoeffSpace d | ε ≤ |∑ w ∈ Z, X w a|} ⊆
      {a : CoeffSpace d | ε ≤ ∑ w ∈ Z, X w a} ∪
        {a : CoeffSpace d | ε ≤ -∑ w ∈ Z, X w a} := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha
    rcases abs_cases (∑ w ∈ Z, X w a) with ⟨heq, -⟩ | ⟨heq, -⟩
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq, heq] using ha)
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq, heq] using ha)
  calc P.real {a : CoeffSpace d | ε ≤ |∑ w ∈ Z, X w a|}
      ≤ P.real ({a : CoeffSpace d | ε ≤ ∑ w ∈ Z, X w a} ∪
          {a : CoeffSpace d | ε ≤ -∑ w ∈ Z, X w a}) := measureReal_mono hsub
    _ ≤ P.real {a : CoeffSpace d | ε ≤ ∑ w ∈ Z, X w a} +
          P.real {a : CoeffSpace d | ε ≤ -∑ w ∈ Z, X w a} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * ((3 ^ d * Z.card : ℕ) : ℝ))) := by
        linarith only [h1', h2']

/-! ## The prefactor is absorbed by the threshold constant -/

/-- The dimensional threshold constant absorbs the two-sided union bound: at the
enlarged threshold the doubled Gaussian tail is again a Gaussian tail at the
dimensional constant `c_fr(d)`. -/
theorem two_mul_exp_le_inv_frGauge (d : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    2 * Real.exp (-(frThreshold d ^ 2 * t ^ 2 * frGaugeConst d)) ≤ (frGauge d t)⁻¹ := by
  have hlog : Real.log 2 ≤ frGaugeConst d * (frThreshold d ^ 2 - 1) :=
    log_two_le_frGaugeConst_mul_threshold d
  have hcpos : 0 < frGaugeConst d := frGaugeConst_pos d
  have hthree : (3 : ℝ) ≤ frThreshold d := three_le_frThreshold d
  have ht2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith only [ht]
  set L : ℝ := Real.log 2 with hLdef
  clear_value L
  have hgap : (0 : ℝ) ≤ frGaugeConst d * (frThreshold d ^ 2 - 1) :=
    mul_nonneg hcpos.le (by nlinarith only [hthree])
  have harg : L + -(frThreshold d ^ 2 * t ^ 2 * frGaugeConst d)
      ≤ -(frGaugeConst d * t ^ 2) := by
    have hscale : frGaugeConst d * (frThreshold d ^ 2 - 1)
        ≤ frGaugeConst d * (frThreshold d ^ 2 - 1) * t ^ 2 := by
      nlinarith only [hgap, ht2]
    nlinarith only [hlog, hscale]
  have hrw : 2 * Real.exp (-(frThreshold d ^ 2 * t ^ 2 * frGaugeConst d))
      = Real.exp (L + -(frThreshold d ^ 2 * t ^ 2 * frGaugeConst d)) := by
    rw [Real.exp_add, hLdef, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hrw, inv_frGauge]
  exact Real.exp_le_exp.2 harg

/-! ## The concentration-for-sums estimate -/

/-- **Concentration for sums from unit range of dependence, on the sum.**  For a
family of centred observables bounded by one, each measurable for the local
sigma-field of its own standard aligned cube of a common nonnegative scale, the
sum exceeds `C_fr(d) t √N` with probability at most `Ψ_fr(t)⁻¹`, for every
`t ≥ 1`.  Both dimensional numbers are fixed before any law datum. -/
theorem measureReal_abs_sum_standardCell_ge_le_frGauge
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {k : ℤ} (hk : 0 ≤ k)
    {X : (Fin d → ℤ) → CoeffSpace d → ℝ}
    (hXloc : ∀ w, @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d k w)) _ (X w))
    (hXbd : ∀ w, ∀ᵐ a ∂P, |X w a| ≤ 1)
    (hXmean : ∀ w, ∫ a, X w a ∂P = 0) {Z : Finset (Fin d → ℤ)} (hZ : Z.Nonempty)
    {t : ℝ} (ht : 1 ≤ t) :
    P.real {a | frThreshold d * t * Real.sqrt (Z.card : ℝ) ≤ |∑ w ∈ Z, X w a|} ≤
      (frGauge d t)⁻¹ := by
  have hNpos : (0 : ℝ) < (Z.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hZ
  have hthree : (0 : ℝ) < (3 : ℝ) ^ d := three_pow_pos d
  have hCpos : 0 < frThreshold d := frThreshold_pos d
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hεnonneg : (0 : ℝ) ≤ frThreshold d * t * Real.sqrt (Z.card : ℝ) := by
    have := Real.sqrt_nonneg ((Z.card : ℝ))
    positivity
  have hchernoff := measureReal_abs_sum_standardCell_ge_le hP hk hXloc hXbd hXmean Z
    (ε := frThreshold d * t * Real.sqrt (Z.card : ℝ)) hεnonneg
  have hsq : Real.sqrt (Z.card : ℝ) ^ 2 = (Z.card : ℝ) := Real.sq_sqrt hNpos.le
  have hNne : (Z.card : ℝ) ≠ 0 := ne_of_gt hNpos
  have h3ne : (3 : ℝ) ^ d ≠ 0 := ne_of_gt hthree
  have hcast : ((3 ^ d * Z.card : ℕ) : ℝ) = (3 : ℝ) ^ d * (Z.card : ℝ) := by push_cast; ring
  have hexp : -(frThreshold d * t * Real.sqrt (Z.card : ℝ)) ^ 2 /
      (2 * ((3 ^ d * Z.card : ℕ) : ℝ))
      = -(frThreshold d ^ 2 * t ^ 2 * frGaugeConst d) := by
    rw [hcast, frGaugeConst]
    have hexpand : (frThreshold d * t * Real.sqrt (Z.card : ℝ)) ^ 2
        = frThreshold d ^ 2 * t ^ 2 * (Z.card : ℝ) := by
      rw [mul_pow, mul_pow, hsq]
    rw [hexpand]
    field_simp
  rw [hexp] at hchernoff
  exact hchernoff.trans (two_mul_exp_le_inv_frGauge d ht)

/-- **Concentration for sums from unit range of dependence, printed form.**  The
average of `N` centred observables bounded by one and local to their own
standard aligned cubes exceeds `C_fr(d) t N^{-1/2}` with probability at most
`Ψ_fr(t)⁻¹`.  For the family of scale-`n` cubes centred in `□_m` the factor
`N^{-1/2}` is `3^{-ν(m-n)}` with `ν = d/2`. -/
theorem measureReal_abs_average_standardCell_ge_le_frGauge
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {k : ℤ} (hk : 0 ≤ k)
    {X : (Fin d → ℤ) → CoeffSpace d → ℝ}
    (hXloc : ∀ w, @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d k w)) _ (X w))
    (hXbd : ∀ w, ∀ᵐ a ∂P, |X w a| ≤ 1)
    (hXmean : ∀ w, ∫ a, X w a ∂P = 0) {Z : Finset (Fin d → ℤ)} (hZ : Z.Nonempty)
    {t : ℝ} (ht : 1 ≤ t) :
    P.real {a | frThreshold d * t * (Real.sqrt (Z.card : ℝ))⁻¹ ≤
        |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, X w a|} ≤ (frGauge d t)⁻¹ := by
  have hNpos : (0 : ℝ) < (Z.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hZ
  have hspos : (0 : ℝ) < Real.sqrt (Z.card : ℝ) := Real.sqrt_pos.2 hNpos
  have hkey : (Z.card : ℝ) * (Real.sqrt (Z.card : ℝ))⁻¹ = Real.sqrt (Z.card : ℝ) := by
    rw [← div_eq_mul_inv]
    exact Real.div_sqrt
  have hid : (Z.card : ℝ) * (frThreshold d * t * (Real.sqrt (Z.card : ℝ))⁻¹)
      = frThreshold d * t * Real.sqrt (Z.card : ℝ) := by
    calc (Z.card : ℝ) * (frThreshold d * t * (Real.sqrt (Z.card : ℝ))⁻¹)
        = frThreshold d * t * ((Z.card : ℝ) * (Real.sqrt (Z.card : ℝ))⁻¹) := by ring
      _ = frThreshold d * t * Real.sqrt (Z.card : ℝ) := by rw [hkey]
  have hsub : {a : CoeffSpace d | frThreshold d * t * (Real.sqrt (Z.card : ℝ))⁻¹ ≤
        |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, X w a|} ⊆
      {a : CoeffSpace d | frThreshold d * t * Real.sqrt (Z.card : ℝ) ≤
        |∑ w ∈ Z, X w a|} := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hmul := mul_le_mul_of_nonneg_left ha hNpos.le
    have habs : (Z.card : ℝ) * |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, X w a| = |∑ w ∈ Z, X w a| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hNpos.le), ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hNpos), one_mul]
    rw [habs, hid] at hmul
    exact hmul
  exact (measureReal_mono hsub).trans
    (measureReal_abs_sum_standardCell_ge_le_frGauge hP hk hXloc hXbd hXmean hZ ht)

end

end Quenched
end HighContrast
end HCPolySupport
