/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Moments
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.RowSumFinite

/-!
# G2RowConversion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `𝒢₂` row: from the manuscript's one-sided `ℝ≥0∞` sum to Appendix D's
# two-sided real sum

ABK26, §4.1, `l.ratio.of.good.scales.for.mathcal.E` Step 4 reconciled with
Appendix D's row (`e.Yk.def.twosided`).

This module supplies the conversion, exactly as `RowSumFinite` does for the
`𝒢₀` lane and by the same device:

1. `lintegral_XcalE_le` — Tonelli over the inner series defining `X_j`, with the
   per-annulus two-term displays of `G2AtomTail.isTwoTermBigOWith_errorAnnMax`
   at `p = 1`.  The bound `xcalMoment` is **uniform in `j`**: the Step-1
   amplitudes depend on `j − n`, not on `j`.
2. `lintegral_XrowTwoE_le` — Tonelli again over the `ℤ`-row, with the geometric
   weight sum `Σ_{j ∈ ℤ} 3^{−¼s|m−j|} ≤ 12/s`.
3. `measure_compl_goodRowSetG2` — the two finite expectations make the countable
   families `{X_j = ∞}` and `{row_m = ∞}` null.
4. `XrowE_le_XrowTwoE` — on the good set the one-sided row sits below the
   two-sided one (the inequality is in the manuscript's favour: the `j > m` rows
   are nonnegative).
5. `lt_Yk_of_notMem_eventG2` — the deterministic half of the `hreduce` slot of
   the Appendix-D concentration interface, entered through `G2Score`'s exact
   event characterization.

Everything is a first-moment computation; **no** Borel--Cantelli is used, and the
null set is paid for by `RowSumFinite.measure_scaleProp_le_of_null_enlargement`.

## Scope

Provider material: proved local helpers.  `hcube` is a conditional A
obligation, discharged at the caller by `G2CubeBound`.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Two small `ℝ≥0∞` devices -/

private theorem ofReal_toReal_le (a : ℝ≥0∞) : ENNReal.ofReal a.toReal ≤ a := by
  rcases eq_or_ne a (⊤ : ℝ≥0∞) with h | h
  · rw [h]
    exact le_top
  · rw [ENNReal.ofReal_toReal h]

private theorem measure_eq_top_eq_zero_g2 {f : Cutoff.CutoffSample d → ℝ≥0∞}
    (M : ABKModel d) (hf : Measurable f)
    (hfin : ∫⁻ omega, f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure ≠ ⊤) :
    (Cutoff.cutoffSampleLaw M).toMeasure {omega | f omega = ⊤} = 0 := by
  have h := ae_lt_top (μ := (Cutoff.cutoffSampleLaw M).toMeasure) hf hfin
  rw [MeasureTheory.ae_iff] at h
  refine measure_mono_null (fun omega homega => ?_) h
  rw [Set.mem_ofPred_eq] at homega ⊢
  rw [homega]
  exact lt_irrefl _

/-- `3^{−s'(m−n)} = 3^{−s'|m−n|}` for `n ≤ m`: the `𝒢₂` lane's bridge between the
`ℕ`-indexed weight of `SeriesTail` and Appendix D's `ℤ`-indexed row weight. -/
private theorem weightThird_toNat_eq_wt {sprime : ℝ} {m n : ℤ} (hn : n ≤ m) :
    weightThird sprime (m - n).toNat = wt sprime m n := by
  exact _root_.Algsuperdiff.Section4.Provider.Proportion.weightThird_eq_wt hn

/-! ## 2. Measurability of the `𝒢₂` atom in both readings -/

theorem measurable_XcalE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ) :
    Measurable (XcalE M s j) := by
  have hrw : XcalE M s j = fun omega : Cutoff.CutoffSample d =>
      ∑' i : ℕ, ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1) *
        errorAnnMax M s j (j - 1 - (i : ℤ)) omega) := by
    funext omega
    rw [XcalE_eq_wsumE M s j omega]
    rfl
  rw [hrw]
  exact Measurable.tsum (L := SummationFilter.unconditional ℕ) fun i =>
    (((measurable_errorAnnMax M s j (j - 1 - (i : ℤ))).const_mul _).ennreal_ofReal)

theorem measurable_XcalE_toReal (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d => (XcalE M s j omega).toReal := by
  have heq : (fun omega : Cutoff.CutoffSample d => (XcalE M s j omega).toReal)
      = wsum (fun i => errorAnnMax M s j (j - 1 - (i : ℤ)))
        (fun i => weightThird ((s : ℝ) / 4) (i + 1)) := by
    funext omega
    rw [XcalE_eq_wsumE M s j omega]
    rfl
  rw [heq]
  exact measurable_wsum fun i => measurable_errorAnnMax M s j (j - 1 - (i : ℤ))

/-! ## 3. The first moment of the `𝒢₂` atom -/

/-- **The uniform first-moment majorant of the `𝒢₂` atom `X_j`.**  The two Step-2
weighted penalty series, weighted by the moment constants of the two Orlicz
lanes.  It does not depend on `j`. -/
def xcalMoment (d : ℕ) (s A1 A2 : ℝ) : ℝ :=
  gammaMomentConst 1 *
      ∑' i : ℕ, weightThird (s / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) +
    gammaMomentConst (1 / 4) *
      ∑' i : ℕ,
        weightThird (s / 4) (i + 1) * (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2))

private theorem summable_pen_one (d : ℕ) {s A1 : ℝ} (hs : 0 < s) :
    Summable fun i : ℕ =>
      weightThird (s / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) := by
  have h := summable_weightThird_mul_annulusPenalty d (sprime := s / 4) (A := 2 * A1 ^ 2)
    (N := 1) (by linarith only [hs]) (by norm_num) (by positivity)
  simpa only [Nat.cast_one, inv_one] using h

private theorem summable_pen_quarter (d : ℕ) {s A2 : ℝ} (hs : 0 < s) :
    Summable fun i : ℕ =>
      weightThird (s / 4) (i + 1) * (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2)) := by
  have h := summable_weightThird_mul_annulusPenalty d (sprime := s / 4) (A := 2 * A2 ^ 2)
    (N := 4) (by linarith only [hs]) (by norm_num) (by positivity)
  have hcast : (((4 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 4 := by norm_num
  rwa [hcast] at h

theorem xcalMoment_nonneg (d : ℕ) (s A1 A2 : ℝ) : 0 ≤ xcalMoment d s A1 A2 := by
  have hpen1 : ∀ i : ℕ, (0 : ℝ) ≤ annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2) := by
    intro i
    have h1 := one_le_annulusPenalty d (by norm_num : (0 : ℝ) < 1) (i + 1)
    exact mul_nonneg (by linarith only [h1]) (by positivity)
  have hpen2 : ∀ i : ℕ, (0 : ℝ) ≤ annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2) := by
    intro i
    have h1 := one_le_annulusPenalty d (by norm_num : (0 : ℝ) < 1 / 4) (i + 1)
    exact mul_nonneg (by linarith only [h1]) (by positivity)
  refine add_nonneg (mul_nonneg (gammaMomentConst_pos (by norm_num)).le ?_)
    (mul_nonneg (gammaMomentConst_pos (by norm_num)).le ?_)
  · exact tsum_nonneg fun i => mul_nonneg (weightThird_pos _).le (hpen1 i)
  · exact tsum_nonneg fun i => mul_nonneg (weightThird_pos _).le (hpen2 i)

/-- **The `p = 1` case of the two-term moment engine.**  A nonnegative random
variable with a two-term weak-Orlicz display has first moment at most the sum of
the two lanes' one-term moments. -/
theorem lintegral_ofReal_le_of_twoTerm {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {X : Omega → ℝ}
    {sigma1 sigma2 A1 A2 : ℝ} (hs1 : 0 < sigma1) (hs2 : 0 < sigma2)
    (hX0 : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (gammaSigma sigma1) (gammaSigma sigma2)
      X A1 A2) :
    ∫⁻ omega, ENNReal.ofReal (X omega) ∂mu
      ≤ ENNReal.ofReal (gammaMomentConst sigma1 * A1 + gammaMomentConst sigma2 * A2) := by
  have hbase := lintegral_rpow_le_of_twoTerm (p := (1 : ℝ)) hs1 hs2 le_rfl hX0 h
  simpa only [Real.rpow_one, Real.one_rpow, mul_one] using hbase

/-- **`E[X_j] ≤ xcalMoment`, by Tonelli over the inner series.**  Uniform in `j`. -/
theorem lintegral_XcalE_le (M : ABKModel d) (s : {s : ℝ // 0 < s}) {A1 A2 : ℝ}
    (hcube : ∀ n : ℤ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        A1 A2) (j : ℤ) :
    ∫⁻ omega, XcalE M s j omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (xcalMoment d (s : ℝ) A1 A2) := by
  classical
  have hs : (0 : ℝ) < (s : ℝ) := s.2
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  have hpen1 : ∀ i : ℕ, (0 : ℝ) ≤ annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2) := by
    intro i
    have h1 := one_le_annulusPenalty d (by norm_num : (0 : ℝ) < 1) (i + 1)
    exact mul_nonneg (by linarith only [h1]) (by positivity)
  have hpen2 : ∀ i : ℕ, (0 : ℝ) ≤ annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2) := by
    intro i
    have h1 := one_le_annulusPenalty d (by norm_num : (0 : ℝ) < 1 / 4) (i + 1)
    exact mul_nonneg (by linarith only [h1]) (by positivity)
  have hstep : ∫⁻ omega, XcalE M s j omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      = ∑' i : ℕ, ∫⁻ omega, ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1) *
          errorAnnMax M s j (j - 1 - (i : ℤ)) omega)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    have hrw : XcalE M s j = fun omega : Cutoff.CutoffSample d =>
        ∑' i : ℕ, ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1) *
          errorAnnMax M s j (j - 1 - (i : ℤ)) omega) := by
      funext omega
      rw [XcalE_eq_wsumE M s j omega]
      rfl
    rw [hrw]
    exact lintegral_tsum fun i =>
      ((((measurable_errorAnnMax M s j (j - 1 - (i : ℤ))).const_mul _).ennreal_ofReal)).aemeasurable
  have hterm : ∀ i : ℕ,
      ∫⁻ omega, ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1) *
          errorAnnMax M s j (j - 1 - (i : ℤ)) omega) ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1) *
            (gammaMomentConst 1 * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) +
              gammaMomentConst (1 / 4) *
                (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2)))) := by
    intro i
    have hw : (0 : ℝ) ≤ weightThird ((s : ℝ) / 4) (i + 1) := (weightThird_pos _).le
    have hidx : (j - (j - 1 - (i : ℤ))).toNat = i + 1 := by omega
    have hdisp := isTwoTermBigOWith_errorAnnMax M s j (j - 1 - (i : ℤ))
      (hcube (j - 1 - (i : ℤ)))
    rw [hidx] at hdisp
    have hmom := lintegral_ofReal_le_of_twoTerm (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1 / 4)
      (fun omega => errorAnnMax_nonneg M s j (j - 1 - (i : ℤ)) omega) hdisp
    have hsplit : (fun omega : Cutoff.CutoffSample d =>
        ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1) *
          errorAnnMax M s j (j - 1 - (i : ℤ)) omega))
        = fun omega => ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1)) *
            ENNReal.ofReal (errorAnnMax M s j (j - 1 - (i : ℤ)) omega) :=
      funext fun omega => ENNReal.ofReal_mul hw
    rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1)) *
            ∫⁻ omega, ENNReal.ofReal (errorAnnMax M s j (j - 1 - (i : ℤ)) omega)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1)) *
            ENNReal.ofReal (gammaMomentConst 1 * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) +
              gammaMomentConst (1 / 4) *
                (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2))) := mul_le_mul_right hmom _
      _ = _ := (ENNReal.ofReal_mul hw).symm
  have hsum1 := summable_pen_one (d := d) (A1 := A1) hs
  have hsum2 := summable_pen_quarter (d := d) (A2 := A2) hs
  have hsumtot : Summable fun i : ℕ => weightThird ((s : ℝ) / 4) (i + 1) *
      (gammaMomentConst 1 * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) +
        gammaMomentConst (1 / 4) * (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2))) := by
    refine ((hsum1.mul_left (gammaMomentConst 1)).add
      (hsum2.mul_left (gammaMomentConst (1 / 4)))).congr fun i => ?_
    ring
  have hval : ∑' i : ℕ, weightThird ((s : ℝ) / 4) (i + 1) *
      (gammaMomentConst 1 * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) +
        gammaMomentConst (1 / 4) * (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2)))
      = xcalMoment d (s : ℝ) A1 A2 := by
    rw [xcalMoment, ← tsum_mul_left, ← tsum_mul_left,
      ← (hsum1.mul_left (gammaMomentConst 1)).tsum_add (hsum2.mul_left (gammaMomentConst (1 / 4)))]
    exact tsum_congr fun i => by ring
  rw [hstep]
  calc ∑' i : ℕ, ∫⁻ omega, ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1) *
          errorAnnMax M s j (j - 1 - (i : ℤ)) omega) ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ∑' i : ℕ, ENNReal.ofReal (weightThird ((s : ℝ) / 4) (i + 1) *
          (gammaMomentConst 1 * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) +
            gammaMomentConst (1 / 4) *
              (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2)))) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' i : ℕ, weightThird ((s : ℝ) / 4) (i + 1) *
          (gammaMomentConst 1 * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) +
            gammaMomentConst (1 / 4) *
              (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2)))) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun i => mul_nonneg (weightThird_pos _).le
            (add_nonneg (mul_nonneg hgmc1.le (hpen1 i)) (mul_nonneg hgmc4.le (hpen2 i))))
          hsumtot).symm
    _ = ENNReal.ofReal (xcalMoment d (s : ℝ) A1 A2) := by rw [hval]

/-! ## 4. The two-sided Appendix-D row, formed in `ℝ≥0∞` -/

/-- **The Appendix-D row of the `𝒢₂` atoms, formed in `ℝ≥0∞`.**  Two-sided,
matching `ScalesConcentration.Yk` at the `𝒢₂` lane rate `s' = ¼s`, and total.
The manuscript's one-sided row `XrowE`  sits below it. -/
def XrowTwoE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal (wt ((s : ℝ) / 4) m j * (XcalE M s j omega).toReal)

theorem measurable_XrowTwoE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (m : ℤ) :
    Measurable (XrowTwoE M s m) := by
  have hrw : XrowTwoE M s m = fun omega : Cutoff.CutoffSample d =>
      ∑' j : ℤ, ENNReal.ofReal (wt ((s : ℝ) / 4) m j * (XcalE M s j omega).toReal) := rfl
  rw [hrw]
  exact Measurable.tsum (L := SummationFilter.unconditional ℤ) fun j =>
    (((measurable_XcalE_toReal M s j).const_mul _).ennreal_ofReal)

private theorem summable_wt_quarter {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (m : ℤ) :
    Summable fun j : ℤ => wt (s / 4) m j := by
  have h := summable_wt_half (s := s / 2) (by linarith only [hs0]) (by linarith only [hs1]) m
  simpa only [show (s / 2 / 2 : ℝ) = s / 4 from by ring] using h

private theorem tsum_wt_quarter_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (m : ℤ) :
    ∑' j : ℤ, wt (s / 4) m j ≤ 12 / s := by
  have h := sum_wt_half_le (s := s / 2) (by linarith only [hs0]) (by linarith only [hs1]) m
  simp only [show (s / 2 / 2 : ℝ) = s / 4 from by ring] at h
  refine h.trans (le_of_eq ?_)
  field_simp
  norm_num

/-- **`E[Y_m] < ∞`, by Tonelli over the `ℤ`-row.** -/
theorem lintegral_XrowTwoE_le (M : ABKModel d) (s : {s : ℝ // 0 < s}) {A1 A2 : ℝ}
    (hs1 : (s : ℝ) ≤ 1)
    (hcube : ∀ n : ℤ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        A1 A2) (m : ℤ) :
    ∫⁻ omega, XrowTwoE M s m omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (12 / (s : ℝ) * xcalMoment d (s : ℝ) A1 A2) := by
  classical
  have hs : (0 : ℝ) < (s : ℝ) := s.2
  have hmom0 : (0 : ℝ) ≤ xcalMoment d (s : ℝ) A1 A2 := xcalMoment_nonneg d (s : ℝ) A1 A2
  have hstep : ∫⁻ omega, XrowTwoE M s m omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      = ∑' j : ℤ, ∫⁻ omega, ENNReal.ofReal (wt ((s : ℝ) / 4) m j *
          (XcalE M s j omega).toReal) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    have hrw : XrowTwoE M s m = fun omega : Cutoff.CutoffSample d =>
        ∑' j : ℤ, ENNReal.ofReal (wt ((s : ℝ) / 4) m j * (XcalE M s j omega).toReal) := rfl
    rw [hrw]
    exact lintegral_tsum fun j =>
      ((((measurable_XcalE_toReal M s j).const_mul _).ennreal_ofReal)).aemeasurable
  have hterm : ∀ j : ℤ,
      ∫⁻ omega, ENNReal.ofReal (wt ((s : ℝ) / 4) m j * (XcalE M s j omega).toReal)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (wt ((s : ℝ) / 4) m j * xcalMoment d (s : ℝ) A1 A2) := by
    intro j
    have hw : (0 : ℝ) ≤ wt ((s : ℝ) / 4) m j := wt_nonneg _ m j
    have hsplit : (fun omega : Cutoff.CutoffSample d =>
        ENNReal.ofReal (wt ((s : ℝ) / 4) m j * (XcalE M s j omega).toReal))
        = fun omega => ENNReal.ofReal (wt ((s : ℝ) / 4) m j) *
            ENNReal.ofReal ((XcalE M s j omega).toReal) :=
      funext fun omega => ENNReal.ofReal_mul hw
    have hbase : ∫⁻ omega, ENNReal.ofReal ((XcalE M s j omega).toReal)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (xcalMoment d (s : ℝ) A1 A2) :=
      le_trans (lintegral_mono fun omega => ofReal_toReal_le _)
        (lintegral_XcalE_le M s hcube j)
    rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (wt ((s : ℝ) / 4) m j) *
            ∫⁻ omega, ENNReal.ofReal ((XcalE M s j omega).toReal)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (wt ((s : ℝ) / 4) m j) *
            ENNReal.ofReal (xcalMoment d (s : ℝ) A1 A2) := mul_le_mul_right hbase _
      _ = _ := (ENNReal.ofReal_mul hw).symm
  have hsumw := summable_wt_quarter hs hs1 m
  have hsum' : Summable fun j : ℤ => wt ((s : ℝ) / 4) m j * xcalMoment d (s : ℝ) A1 A2 :=
    hsumw.mul_right _
  rw [hstep]
  calc ∑' j : ℤ, ∫⁻ omega, ENNReal.ofReal (wt ((s : ℝ) / 4) m j *
          (XcalE M s j omega).toReal) ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ∑' j : ℤ, ENNReal.ofReal (wt ((s : ℝ) / 4) m j * xcalMoment d (s : ℝ) A1 A2) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℤ, wt ((s : ℝ) / 4) m j * xcalMoment d (s : ℝ) A1 A2) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (wt_nonneg _ m j) hmom0) hsum').symm
    _ ≤ ENNReal.ofReal (12 / (s : ℝ) * xcalMoment d (s : ℝ) A1 A2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_right]
        exact mul_le_mul_of_nonneg_right (tsum_wt_quarter_le hs hs1 m) hmom0

/-! ## 5. The null set of the enlargement -/

/-- **The full-measure set on which the `𝒢₂` Appendix-D row is the honest
series.**  Both the inner series defining each `X_j` and the `ℤ`-row of the `X_j`
are finite there; off it the real `tsum` carries no information. -/
def goodRowSetG2 (M : ABKModel d) (s : {s : ℝ // 0 < s}) : Set (Cutoff.CutoffSample d) :=
  {omega | (∀ j : ℤ, XcalE M s j omega ≠ ⊤) ∧ (∀ m : ℤ, XrowTwoE M s m omega ≠ ⊤)}

/-- **The enlargement's null set is null.** -/
theorem measure_compl_goodRowSetG2 (M : ABKModel d) (s : {s : ℝ // 0 < s}) {A1 A2 : ℝ}
    (hs1 : (s : ℝ) ≤ 1)
    (hcube : ∀ n : ℤ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        A1 A2) :
    (Cutoff.cutoffSampleLaw M).toMeasure (goodRowSetG2 M s)ᶜ = 0 := by
  classical
  have hAtomNull : ∀ j : ℤ, (Cutoff.cutoffSampleLaw M).toMeasure
      {omega | XcalE M s j omega = ⊤} = 0 := by
    intro j
    refine measure_eq_top_eq_zero_g2 M (measurable_XcalE M s j) ?_
    exact ne_of_lt (lt_of_le_of_lt (lintegral_XcalE_le M s hcube j) ENNReal.ofReal_lt_top)
  have hRowNull : ∀ m : ℤ, (Cutoff.cutoffSampleLaw M).toMeasure
      {omega | XrowTwoE M s m omega = ⊤} = 0 := by
    intro m
    refine measure_eq_top_eq_zero_g2 M (measurable_XrowTwoE M s m) ?_
    exact ne_of_lt (lt_of_le_of_lt (lintegral_XrowTwoE_le M s hs1 hcube m) ENNReal.ofReal_lt_top)
  have hsub : (goodRowSetG2 M s)ᶜ
      ⊆ (⋃ j : ℤ, {omega | XcalE M s j omega = ⊤})
        ∪ (⋃ m : ℤ, {omega | XrowTwoE M s m omega = ⊤}) := by
    intro omega homega
    by_cases h1 : ∀ j : ℤ, XcalE M s j omega ≠ ⊤
    · refine Or.inr ?_
      have h2 : ¬ ∀ m : ℤ, XrowTwoE M s m omega ≠ ⊤ := fun h2 => homega ⟨h1, h2⟩
      push Not at h2
      obtain ⟨m, hm⟩ := h2
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    · refine Or.inl ?_
      push Not at h1
      obtain ⟨j, hj⟩ := h1
      exact Set.mem_iUnion.2 ⟨j, hj⟩
  exact measure_mono_null hsub
    (measure_union_null (measure_iUnion_null hAtomNull) (measure_iUnion_null hRowNull))

/-! ## 6. The row conversion and the Appendix-D reduction -/

/-- **The `ℝ≥0∞` one-sided row is below the real two-sided row**, on the set where
the atoms are finite.  This is the reconciliation of the manuscript's `Σ_{j ≤
m}` with Appendix D's `Σ_{j ∈ ℤ}`, the inequality being in the manuscript's
favour: the `j > m` rows are nonnegative. -/
theorem XrowE_le_XrowTwoE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (m : ℤ)
    {omega : Cutoff.CutoffSample d} (hfin : ∀ j : ℤ, XcalE M s j omega ≠ ⊤) :
    XrowE M s m omega ≤ XrowTwoE M s m omega := by
  have hcongr : XrowE M s m omega
      = ∑' j : {j : ℤ // j ≤ m},
          ENNReal.ofReal (wt ((s : ℝ) / 4) m j.1 * (XcalE M s j.1 omega).toReal) := by
    rw [XrowE]
    refine tsum_congr fun j => ?_
    have hle : (0 : ℤ) ≤ m - j.1 := by have := j.2; omega
    have hX : XcalE M s j.1 omega = ENNReal.ofReal ((XcalE M s j.1 omega).toReal) :=
      (ENNReal.ofReal_toReal (hfin j.1)).symm
    calc annularWeight (s : ℝ) (m - j.1) * XcalE M s j.1 omega
        = ENNReal.ofReal (weightThird ((s : ℝ) / 4) (m - j.1).toNat) *
            XcalE M s j.1 omega := by rw [annularWeight_eq_weightThird hle]
      _ = ENNReal.ofReal (wt ((s : ℝ) / 4) m j.1) *
            ENNReal.ofReal ((XcalE M s j.1 omega).toReal) := by
          rw [weightThird_toNat_eq_wt j.2, ← hX]
      _ = ENNReal.ofReal (wt ((s : ℝ) / 4) m j.1 * (XcalE M s j.1 omega).toReal) :=
          (ENNReal.ofReal_mul (wt_nonneg _ m j.1)).symm
  rw [hcongr]
  exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun j : {j : ℤ // j ≤ m} => j.1)
    Subtype.val_injective
    (fun j : ℤ => ENNReal.ofReal (wt ((s : ℝ) / 4) m j * (XcalE M s j omega).toReal))

/-- **The Appendix-D reduction of `𝒢₂`, off the null set.**  Off `𝒢₂(m;s,ε)` — and
off the null set of `goodRowSetG2` — the Appendix-D row sum of the normalized
atoms exceeds `D^{-1}ε²s^{-1}`.  The entry point is
`G2Score.notMem_eventG2_iff`, which is an exact characterization, so nothing is
lost here beyond the `j > m` rows. -/
theorem lt_Yk_of_notMem_eventG2 (M : ABKModel d) (s : {s : ℝ // 0 < s}) {ep D : ℝ}
    (hD : 0 < D) (m : ℤ) {omega : Cutoff.CutoffSample d}
    (hgood : omega ∈ goodRowSetG2 M s)
    (hnot : omega ∉ Support.eventG2 M m s ep) :
    D⁻¹ * (ep ^ 2 / (s : ℝ)) < Yk (xcalArray M s D) ((s : ℝ) / 4) m omega := by
  have hs : (0 : ℝ) < (s : ℝ) := s.2
  have hfin : XrowTwoE M s m omega ≠ ⊤ := hgood.2 m
  have hbase : ENNReal.ofReal (ep ^ 2)
      < ENNReal.ofReal (s : ℝ) * XrowE M s m omega :=
    (notMem_eventG2_iff M m s ep omega).1 hnot
  have hlt : ENNReal.ofReal (ep ^ 2)
      < ENNReal.ofReal (s : ℝ) * XrowTwoE M s m omega :=
    lt_of_lt_of_le hbase (mul_le_mul' le_rfl (XrowE_le_XrowTwoE M s m hgood.1))
  have hprodfin : ENNReal.ofReal (s : ℝ) * XrowTwoE M s m omega ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hreal : ep ^ 2 < (s : ℝ) * (XrowTwoE M s m omega).toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hprodfin).2 hlt
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le,
      ENNReal.toReal_ofReal (sq_nonneg ep)] at h
  have htoReal : (XrowTwoE M s m omega).toReal
      = ∑' j : ℤ, wt ((s : ℝ) / 4) m j * (XcalE M s j omega).toReal := by
    rw [XrowTwoE, ENNReal.tsum_toReal_eq (fun _j => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun j => ENNReal.toReal_ofReal
      (mul_nonneg (wt_nonneg _ m j) ENNReal.toReal_nonneg)
  have hYk : Yk (xcalArray M s D) ((s : ℝ) / 4) m omega
      = D⁻¹ * ∑' j : ℤ, wt ((s : ℝ) / 4) m j * (XcalE M s j omega).toReal := by
    rw [show xcalArray M s D
        = colArray (fun j omega => D⁻¹ * (XcalE M s j omega).toReal) from rfl,
      Yk_colArray_const_mul, Yk_colArray]
  rw [hYk, ← htoReal]
  have hstep : ep ^ 2 / (s : ℝ) < (XrowTwoE M s m omega).toReal := by
    rw [div_lt_iff₀ hs]
    calc ep ^ 2 < (s : ℝ) * (XrowTwoE M s m omega).toReal := hreal
      _ = (XrowTwoE M s m omega).toReal * (s : ℝ) := by ring
  exact mul_lt_mul_of_pos_left hstep (inv_pos.2 hD)

end

end Algsuperdiff.Section4.Provider.Proportion
