/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ScoreDomination
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.Concentration

/-!
# RowSumFinite

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `a.s.` finiteness of the `𝒴` row sum, and the Appendix-D reduction of `𝒢₀`

ABK26, §4.1, `l.good.scales.ratio.lambda`, score domination, and the threshold
identification.

`ScoreDomination.one_lt_YcalRowE_of_notMem_eventG0` is the *deterministic* half of
the reduction `hreduce` the `𝒢₀` lane consumes: off `𝒢₀(m)`
the `ℝ≥0∞`-formed row sum `Σ_{n ≤ m} 3^{−s'(m−n)} 𝒴_n` exceeds `1`.  The
Appendix-D row sum `Y_m`, by contrast, is the **real**, **two-sided** series
`Σ_{j ∈ ℤ} 3^{−s'|m−j|} D^{-1}𝒴_j`, which is a `tsum` in `ℝ` and therefore only
carries information where the family is summable.  This module supplies the
missing half: the `a.s.` finiteness that converts the one into the other.

## Route

Everything is a first-moment computation; **no** Borel--Cantelli is used.

1. `lintegral_ofReal_le_of_isBigOWith` — the `p = 1` case of the ambient
   library's tail-to-moment engine: a `Γ_σ` upper tail at scale `K` gives
   `E[Y] ≤ gammaMomentConst σ · K`.
2. `lintegral_YcalE_le` — Tonelli (`lintegral_tsum`) over the `k`-series
   defining `𝒴_n`, with the per-annulus tails of `Ycal.isBigOWith_annMax`:
   `E[𝒴_n] ≤ gammaMomentConst σ · Σ_j 3^{−s'j} a_j < ∞`.
3. `lintegral_YcalRowTwoE_le` — Tonelli again over the `ℤ`-row, with the
   `𝒴`-tail of `Ycal.isBigOWith_Ycal` and the geometric weight sum
   `Σ_{j ∈ ℤ} 3^{−s'|m−j|} ≤ 3/s'`.
4. `measure_compl_goodRowSet` — the two finite expectations make the countable
   family `{𝒴_n = ∞}` and `{row_m = ∞}` null; their union `N` is the null set of
   the enlargement.
5. `lt_Yk_of_notMem_eventG0` — on `Nᶜ` the `ℝ≥0∞` row sum IS the real row sum,
   the one-sided row is below the two-sided one, and the deterministic half
   delivers `D^{-1} < Y_m`.

The final bookkeeping lemma `measure_scaleProp_le_of_null_enlargement` pays for
the enlargement `Ev m := 𝒢₀(m) ∪ N` with `+ ℙ[N] = 0`, so the tail proved for the
enlarged family is a tail for `𝒢₀` itself.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.good.scales.ratio.lambda`.
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

/-! ## 1. Two carrier-neutral devices -/

section Generic

variable {Omega : Type*} [MeasurableSpace Omega]

/-- **The first moment of a `Γ_σ` upper tail.**  The `p = 1` instance of the
ambient library's tail-to-moment engine, in its `∫⁻` reading: a nonnegative
random variable with a stretched-exponential upper tail at scale `K` has
`E[Y] ≤ gammaMomentConst σ · K`. -/
theorem lintegral_ofReal_le_of_isBigOWith {mu : Measure Omega} [IsProbabilityMeasure mu]
    {Y : Omega → ℝ} {sigma K : ℝ} (hsigma : 0 < sigma) (hK : 0 < K)
    (hYnn : ∀ omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hY : IsBigOWith mu (gammaSigma sigma) Y K) :
    ∫⁻ omega, ENNReal.ofReal (Y omega) ∂mu
      ≤ ENNReal.ofReal (gammaMomentConst sigma * K) := by
  have h := lintegral_rpow_le_of_isBigOWith_gammaSigma (μ := mu) (Y := Y) (K := K)
    (σ := sigma) (p := (1 : ℝ)) hsigma hK le_rfl hYnn hYm hY
  simpa only [Real.rpow_one, Real.one_rpow, mul_one] using h

/-- **Null-set enlargement of an event family.**  Enlarging every member of an
event family by one fixed null set `N` costs `+ ℙ[N] = 0` in the bad-density
tail: off `N` the two families have the same indicator sums, so the `θ`-excess
event of the original family is contained in that of the enlarged family
together with `N`. -/
theorem measure_scaleProp_le_of_null_enlargement (P : Measure Omega)
    (Ev : ℤ → Set Omega) (N : Set Omega) (hN : P N = 0) {theta : ℝ} (n : ℕ) :
    P {omega | theta < scaleProp (fun k => (Ev k)ᶜ) n omega}
      ≤ P {omega | theta < scaleProp (fun k => (Ev k ∪ N)ᶜ) n omega} := by
  classical
  have hsub : {omega | theta < scaleProp (fun k => (Ev k)ᶜ) n omega}
      ⊆ {omega | theta < scaleProp (fun k => (Ev k ∪ N)ᶜ) n omega} ∪ N := by
    intro omega homega
    by_cases hmem : omega ∈ N
    · exact Or.inr hmem
    · refine Or.inl ?_
      have heq : scaleProp (fun k => (Ev k)ᶜ) n omega
          = scaleProp (fun k => (Ev k ∪ N)ᶜ) n omega := by
        simp only [scaleProp]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        have hiff : omega ∈ (Ev k ∪ N)ᶜ ↔ omega ∈ (Ev k)ᶜ := by
          simp only [Set.mem_compl_iff, Set.mem_union, not_or]
          exact ⟨fun h => h.1, fun h => ⟨h, hmem⟩⟩
        by_cases h : omega ∈ (Ev k)ᶜ
        · rw [ite_eq_left h, ite_eq_left (hiff.2 h)]
        · rw [ite_eq_right h, ite_eq_right (fun hc => h (hiff.1 hc))]
      change theta < scaleProp (fun k => (Ev k ∪ N)ᶜ) n omega
      rw [← heq]
      exact homega
  calc P {omega | theta < scaleProp (fun k => (Ev k)ᶜ) n omega}
      ≤ P ({omega | theta < scaleProp (fun k => (Ev k ∪ N)ᶜ) n omega} ∪ N) :=
        measure_mono hsub
    _ ≤ P {omega | theta < scaleProp (fun k => (Ev k ∪ N)ᶜ) n omega} + P N :=
        measure_union_le _ _
    _ = P {omega | theta < scaleProp (fun k => (Ev k ∪ N)ᶜ) n omega} := by
        rw [hN, add_zero]

end Generic

variable {d : ℕ}

/-! ## 2. The `ℝ≥0∞` score field: measurability and first moment -/

theorem measurable_YcalE (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ) :
    Measurable (YcalE M Ccg sprime n) := by
  have hrw : YcalE M Ccg sprime n = fun omega =>
      ∑' j : ℕ, ENNReal.ofReal (weightThird sprime j *
        annMax M Ccg n (n - (j : ℤ)) omega) := rfl
  rw [hrw]
  exact Measurable.tsum fun j =>
    ((measurable_annMax M Ccg n (n - (j : ℤ))).const_mul _).ennreal_ofReal

/-- **`E[𝒴_n] < ∞`, by Tonelli over the `k`-series.**  The per-annulus maxima
have `Γ_σ` tails at the penalised atom scales (`isBigOWith_annMax`), so each has
a finite first moment; the weighted series of those moments is the convergent
`Σ_j 3^{−s'j} a_j` of the `𝒴`-tail hypothesis.  The bound is uniform in `n`. -/
theorem lintegral_YcalE_le (M : ABKModel d) (Ccg : ℝ) {sigma sprime A : ℝ} {a : ℕ → ℝ}
    (hsigma : 0 < sigma) (hA : 0 ≤ A)
    (hatom : ∀ (k : ℤ) (z : Vec d),
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
        (fun omega => Localize.cgExcess M Ccg (k - 2) z omega) A)
    (hapos : ∀ j : ℕ, 0 < a j)
    (hdom : ∀ j : ℕ, annulusPenalty d sigma (j + 2) * A ≤ a j)
    (hsum : Summable fun j : ℕ => weightThird sprime j * a j) (n : ℤ) :
    ∫⁻ omega, YcalE M Ccg sprime n omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (gammaMomentConst sigma * ∑' j : ℕ, weightThird sprime j * a j) := by
  classical
  have hatomTail : ∀ j : ℕ,
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
        (annMax M Ccg n (n - (j : ℤ))) (a j) := by
    intro j
    have hidx : (n - (n - (j : ℤ) - 2)).toNat = j + 2 := by omega
    have hbase := isBigOWith_annMax M Ccg hsigma hA hatom n (n - (j : ℤ))
    rw [hidx] at hbase
    exact hbase.mono_scale (hdom j)
  have hstep : ∫⁻ omega, YcalE M Ccg sprime n omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      = ∑' j : ℕ, ∫⁻ omega, ENNReal.ofReal (weightThird sprime j *
          annMax M Ccg n (n - (j : ℤ)) omega) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    have hrw : YcalE M Ccg sprime n = fun omega =>
        ∑' j : ℕ, ENNReal.ofReal (weightThird sprime j *
          annMax M Ccg n (n - (j : ℤ)) omega) := rfl
    rw [hrw]
    exact lintegral_tsum fun j =>
      (((measurable_annMax M Ccg n (n - (j : ℤ))).const_mul _).ennreal_ofReal).aemeasurable
  have hterm : ∀ j : ℕ,
      ∫⁻ omega, ENNReal.ofReal (weightThird sprime j *
          annMax M Ccg n (n - (j : ℤ)) omega) ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (weightThird sprime j * (gammaMomentConst sigma * a j)) := by
    intro j
    have hw : (0 : ℝ) ≤ weightThird sprime j := (weightThird_pos j).le
    have hsplit : (fun omega => ENNReal.ofReal (weightThird sprime j *
        annMax M Ccg n (n - (j : ℤ)) omega))
        = fun omega => ENNReal.ofReal (weightThird sprime j) *
            ENNReal.ofReal (annMax M Ccg n (n - (j : ℤ)) omega) :=
      funext fun omega => ENNReal.ofReal_mul hw
    rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hmom := lintegral_ofReal_le_of_isBigOWith hsigma (hapos j)
      (fun omega => annMax_nonneg M Ccg n (n - (j : ℤ)) omega)
      (measurable_annMax M Ccg n (n - (j : ℤ))).aemeasurable (hatomTail j)
    calc ENNReal.ofReal (weightThird sprime j) *
            ∫⁻ omega, ENNReal.ofReal (annMax M Ccg n (n - (j : ℤ)) omega)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (weightThird sprime j) *
            ENNReal.ofReal (gammaMomentConst sigma * a j) := mul_le_mul_right hmom _
      _ = ENNReal.ofReal (weightThird sprime j * (gammaMomentConst sigma * a j)) :=
          (ENNReal.ofReal_mul hw).symm
  have hsum' : Summable fun j : ℕ => weightThird sprime j * (gammaMomentConst sigma * a j) := by
    refine (hsum.mul_left (gammaMomentConst sigma)).congr fun j => ?_
    ring
  rw [hstep]
  calc ∑' j : ℕ, ∫⁻ omega, ENNReal.ofReal (weightThird sprime j *
          annMax M Ccg n (n - (j : ℤ)) omega) ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ∑' j : ℕ, ENNReal.ofReal (weightThird sprime j *
          (gammaMomentConst sigma * a j)) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, weightThird sprime j * (gammaMomentConst sigma * a j)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (weightThird_pos j).le
            (mul_nonneg (gammaMomentConst_pos hsigma).le (hapos j).le)) hsum').symm
    _ = ENNReal.ofReal (gammaMomentConst sigma * ∑' j : ℕ, weightThird sprime j * a j) := by
        congr 1
        rw [← tsum_mul_left]
        exact tsum_congr fun j => by ring

/-! ## 3. The two-sided Appendix-D row, formed in `ℝ≥0∞` -/

/-- **The Appendix-D row sum of the `𝒴`-atoms, formed in `ℝ≥0∞`.**  Two-sided,
matching `ScalesConcentration.Yk`, and total. -/
def YcalRowTwoE (M : ABKModel d) (Ccg sprime : ℝ) (m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal (wt sprime m j * Ycal M Ccg sprime j omega)

theorem measurable_YcalRowTwoE (M : ABKModel d) (Ccg sprime : ℝ) (m : ℤ) :
    Measurable (YcalRowTwoE M Ccg sprime m) := by
  have hrw : YcalRowTwoE M Ccg sprime m = fun omega =>
      ∑' j : ℤ, ENNReal.ofReal (wt sprime m j * Ycal M Ccg sprime j omega) := rfl
  rw [hrw]
  exact Measurable.tsum fun j =>
    ((measurable_Ycal M Ccg sprime j).const_mul _).ennreal_ofReal

private theorem summable_wt_row {sprime : ℝ} (hs0 : 0 < sprime) (hs2 : 2 * sprime ≤ 1)
    (m : ℤ) : Summable fun j : ℤ => wt sprime m j := by
  have h := summable_wt_half (s := 2 * sprime) (by linarith only [hs0]) hs2 m
  simpa only [show (2 * sprime / 2 : ℝ) = sprime from by ring] using h

private theorem tsum_wt_row_le {sprime : ℝ} (hs0 : 0 < sprime) (hs2 : 2 * sprime ≤ 1)
    (m : ℤ) : ∑' j : ℤ, wt sprime m j ≤ 3 / sprime := by
  have h := sum_wt_half_le (s := 2 * sprime) (by linarith only [hs0]) hs2 m
  simp only [show (2 * sprime / 2 : ℝ) = sprime from by ring] at h
  refine h.trans (le_of_eq ?_)
  field_simp
  norm_num

/-- **`E[Y_m] < ∞`, by Tonelli over the `ℤ`-row.**  The `𝒴`-tail gives each atom
a finite first moment, and the geometric weights are summable with
`Σ_{j ∈ ℤ} 3^{−s'|m−j|} ≤ 3/s'`. -/
theorem lintegral_YcalRowTwoE_le (M : ABKModel d) (Ccg : ℝ) {sigma sprime K : ℝ}
    (hsigma : 0 < sigma) (hK : 0 < K) (hs0 : 0 < sprime) (hs2 : 2 * sprime ≤ 1)
    (htail : ∀ n : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
      (Ycal M Ccg sprime n) K) (m : ℤ) :
    ∫⁻ omega, YcalRowTwoE M Ccg sprime m omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (3 / sprime * (gammaMomentConst sigma * K)) := by
  classical
  have hgmc : (0 : ℝ) ≤ gammaMomentConst sigma := (gammaMomentConst_pos hsigma).le
  have hcst : (0 : ℝ) ≤ gammaMomentConst sigma * K := mul_nonneg hgmc hK.le
  have hstep : ∫⁻ omega, YcalRowTwoE M Ccg sprime m omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      = ∑' j : ℤ, ∫⁻ omega, ENNReal.ofReal (wt sprime m j * Ycal M Ccg sprime j omega)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    have hrw : YcalRowTwoE M Ccg sprime m = fun omega =>
        ∑' j : ℤ, ENNReal.ofReal (wt sprime m j * Ycal M Ccg sprime j omega) := rfl
    rw [hrw]
    exact lintegral_tsum fun j =>
      (((measurable_Ycal M Ccg sprime j).const_mul _).ennreal_ofReal).aemeasurable
  have hterm : ∀ j : ℤ,
      ∫⁻ omega, ENNReal.ofReal (wt sprime m j * Ycal M Ccg sprime j omega)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (wt sprime m j * (gammaMomentConst sigma * K)) := by
    intro j
    have hw : (0 : ℝ) ≤ wt sprime m j := wt_nonneg sprime m j
    have hsplit : (fun omega => ENNReal.ofReal (wt sprime m j * Ycal M Ccg sprime j omega))
        = fun omega => ENNReal.ofReal (wt sprime m j) *
            ENNReal.ofReal (Ycal M Ccg sprime j omega) :=
      funext fun omega => ENNReal.ofReal_mul hw
    rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hmom := lintegral_ofReal_le_of_isBigOWith hsigma hK
      (fun omega => Ycal_nonneg M Ccg sprime j omega)
      (measurable_Ycal M Ccg sprime j).aemeasurable (htail j)
    calc ENNReal.ofReal (wt sprime m j) *
            ∫⁻ omega, ENNReal.ofReal (Ycal M Ccg sprime j omega)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (wt sprime m j) * ENNReal.ofReal (gammaMomentConst sigma * K) :=
          mul_le_mul_right hmom _
      _ = ENNReal.ofReal (wt sprime m j * (gammaMomentConst sigma * K)) :=
          (ENNReal.ofReal_mul hw).symm
  have hsumw := summable_wt_row hs0 hs2 m
  have hsum' : Summable fun j : ℤ => wt sprime m j * (gammaMomentConst sigma * K) :=
    hsumw.mul_right _
  rw [hstep]
  calc ∑' j : ℤ, ∫⁻ omega, ENNReal.ofReal (wt sprime m j * Ycal M Ccg sprime j omega)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ∑' j : ℤ, ENNReal.ofReal (wt sprime m j * (gammaMomentConst sigma * K)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℤ, wt sprime m j * (gammaMomentConst sigma * K)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (wt_nonneg sprime m j) hcst) hsum').symm
    _ ≤ ENNReal.ofReal (3 / sprime * (gammaMomentConst sigma * K)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_right]
        exact mul_le_mul_of_nonneg_right (tsum_wt_row_le hs0 hs2 m) hcst

/-! ## 4. The null set of the enlargement -/

/-- **The full-measure set on which the Appendix-D row sum is the honest series.**
Both the `k`-series defining each `𝒴_n` and the `ℤ`-row of the `𝒴_n` are finite
there; off it the real `tsum` defining `Y_m` carries no information. -/
def goodRowSet (M : ABKModel d) (Ccg sprime : ℝ) : Set (Cutoff.CutoffSample d) :=
  {omega | (∀ n : ℤ, YcalE M Ccg sprime n omega ≠ ⊤) ∧
      (∀ m : ℤ, YcalRowTwoE M Ccg sprime m omega ≠ ⊤)}

private theorem measure_eq_top_eq_zero {f : Cutoff.CutoffSample d → ℝ≥0∞}
    (M : ABKModel d) (hf : Measurable f)
    (hfin : ∫⁻ omega, f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure ≠ ⊤) :
    (Cutoff.cutoffSampleLaw M).toMeasure {omega | f omega = ⊤} = 0 := by
  have h := ae_lt_top (μ := (Cutoff.cutoffSampleLaw M).toMeasure) hf hfin
  rw [MeasureTheory.ae_iff] at h
  refine measure_mono_null (fun omega homega => ?_) h
  rw [Set.mem_ofPred_eq] at homega ⊢
  rw [homega]
  exact lt_irrefl _

/-- **The enlargement's null set is null.**  Both defining families are countable
and every member is null by the two first-moment bounds. -/
theorem measure_compl_goodRowSet (M : ABKModel d) (Ccg : ℝ) {sigma sprime A K : ℝ}
    {a : ℕ → ℝ} (hsigma : 0 < sigma) (hA : 0 ≤ A) (hK : 0 < K)
    (hs0 : 0 < sprime) (hs2 : 2 * sprime ≤ 1)
    (hatom : ∀ (k : ℤ) (z : Vec d),
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
        (fun omega => Localize.cgExcess M Ccg (k - 2) z omega) A)
    (hapos : ∀ j : ℕ, 0 < a j)
    (hdom : ∀ j : ℕ, annulusPenalty d sigma (j + 2) * A ≤ a j)
    (hsum : Summable fun j : ℕ => weightThird sprime j * a j)
    (htail : ∀ n : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
      (Ycal M Ccg sprime n) K) :
    (Cutoff.cutoffSampleLaw M).toMeasure (goodRowSet M Ccg sprime)ᶜ = 0 := by
  classical
  have hAtomNull : ∀ n : ℤ, (Cutoff.cutoffSampleLaw M).toMeasure
      {omega | YcalE M Ccg sprime n omega = ⊤} = 0 := by
    intro n
    refine measure_eq_top_eq_zero M (measurable_YcalE M Ccg sprime n) ?_
    exact ne_of_lt (lt_of_le_of_lt
      (lintegral_YcalE_le M Ccg hsigma hA hatom hapos hdom hsum n) ENNReal.ofReal_lt_top)
  have hRowNull : ∀ m : ℤ, (Cutoff.cutoffSampleLaw M).toMeasure
      {omega | YcalRowTwoE M Ccg sprime m omega = ⊤} = 0 := by
    intro m
    refine measure_eq_top_eq_zero M (measurable_YcalRowTwoE M Ccg sprime m) ?_
    exact ne_of_lt (lt_of_le_of_lt
      (lintegral_YcalRowTwoE_le M Ccg hsigma hK hs0 hs2 htail m) ENNReal.ofReal_lt_top)
  have hsub : (goodRowSet M Ccg sprime)ᶜ
      ⊆ (⋃ n : ℤ, {omega | YcalE M Ccg sprime n omega = ⊤})
        ∪ (⋃ m : ℤ, {omega | YcalRowTwoE M Ccg sprime m omega = ⊤}) := by
    intro omega homega
    by_cases h1 : ∀ n : ℤ, YcalE M Ccg sprime n omega ≠ ⊤
    · refine Or.inr ?_
      have h2 : ¬ ∀ m : ℤ, YcalRowTwoE M Ccg sprime m omega ≠ ⊤ := fun h2 => homega ⟨h1, h2⟩
      push Not at h2
      obtain ⟨m, hm⟩ := h2
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    · refine Or.inl ?_
      push Not at h1
      obtain ⟨n, hn⟩ := h1
      exact Set.mem_iUnion.2 ⟨n, hn⟩
  refine measure_mono_null hsub ?_
  refine measure_union_null (measure_iUnion_null hAtomNull) (measure_iUnion_null hRowNull)

/-! ## 5. The reduction -/

private theorem weightThird_eq_wt {sprime : ℝ} {m n : ℤ} (hn : n ≤ m) :
    weightThird sprime (m - n).toNat = wt sprime m n := by
  have h1 : (((m - n).toNat : ℕ) : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  have h2 : (((m - n).toNat : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by exact_mod_cast h1
  have h3 : idist m n = (((m - n).toNat : ℕ) : ℝ) := by
    rw [idist, h2, ← Int.cast_sub]
    exact abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ m - n))
  rw [weightThird_eq, wt, h3]

/-- **The `ℝ≥0∞` one-sided row is below the real two-sided row**, on the
full-measure set where the score fields are finite. -/
theorem YcalRowE_le_YcalRowTwoE (M : ABKModel d) (Ccg sprime : ℝ) (m : ℤ)
    {omega : Cutoff.CutoffSample d} (hfin : ∀ n : ℤ, YcalE M Ccg sprime n omega ≠ ⊤) :
    YcalRowE M Ccg sprime m omega ≤ YcalRowTwoE M Ccg sprime m omega := by
  refine ENNReal.tsum_le_tsum fun n => ?_
  by_cases hn : n ≤ m
  · rw [ite_eq_left hn, weightThird_eq_wt hn,
      show YcalE M Ccg sprime n omega = ENNReal.ofReal (Ycal M Ccg sprime n omega) from
        (ENNReal.ofReal_toReal (hfin n)).symm,
      ← ENNReal.ofReal_mul (wt_nonneg sprime m n)]
  · rw [ite_eq_right hn]
    exact zero_le

/-- **The Appendix-D reduction of `𝒢₀`, off the null set.**

Off `𝒢₀(m)` — and off the null set of `goodRowSet` — the Appendix-D row sum of
the normalized atoms `D^{-1}𝒴` exceeds `D^{-1}`.  Chaining the deterministic
`one_lt_YcalRowE_of_notMem_eventG0` with the `ℝ≥0∞ → ℝ` conversion this module
supplies, this is the missing half of `hreduce`. -/
theorem lt_Yk_of_notMem_eventG0 (M : ABKModel d) (Ccg : ℝ) {D : ℝ} (hD : 0 < D) (m : ℤ)
    {omega : Cutoff.CutoffSample d} (hgood : omega ∈ goodRowSet M Ccg (M.gamma / 4))
    (hnot : omega ∉ Support.eventG0 M Ccg m) :
    D⁻¹ < Yk (ycalArray M Ccg (M.gamma / 4) D) (M.gamma / 4) m omega := by
  have hfin : YcalRowTwoE M Ccg (M.gamma / 4) m omega ≠ ⊤ := hgood.2 m
  have hlt1 : 1 < YcalRowTwoE M Ccg (M.gamma / 4) m omega :=
    lt_of_lt_of_le (one_lt_YcalRowE_of_notMem_eventG0 M Ccg m hnot)
      (YcalRowE_le_YcalRowTwoE M Ccg (M.gamma / 4) m hgood.1)
  have htoReal : (YcalRowTwoE M Ccg (M.gamma / 4) m omega).toReal
      = ∑' j : ℤ, wt (M.gamma / 4) m j * Ycal M Ccg (M.gamma / 4) j omega := by
    rw [YcalRowTwoE, ENNReal.tsum_toReal_eq (fun _j => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun j => ENNReal.toReal_ofReal
      (mul_nonneg (wt_nonneg _ m j) (Ycal_nonneg M Ccg (M.gamma / 4) j omega))
  have h1lt : (1 : ℝ) < (YcalRowTwoE M Ccg (M.gamma / 4) m omega).toReal := by
    have h := (ENNReal.toReal_lt_toReal (by simp) hfin).2 hlt1
    simpa only [ENNReal.toReal_one] using h
  have hYk : Yk (ycalArray M Ccg (M.gamma / 4) D) (M.gamma / 4) m omega
      = D⁻¹ * ∑' j : ℤ, wt (M.gamma / 4) m j * Ycal M Ccg (M.gamma / 4) j omega := by
    rw [show ycalArray M Ccg (M.gamma / 4) D
        = colArray (fun n omega => D⁻¹ * Ycal M Ccg (M.gamma / 4) n omega) from rfl,
      Yk_colArray_const_mul, Yk_colArray]
  rw [hYk, ← htoReal]
  calc D⁻¹ = D⁻¹ * 1 := (mul_one _).symm
    _ < D⁻¹ * (YcalRowTwoE M Ccg (M.gamma / 4) m omega).toReal :=
        mul_lt_mul_of_pos_left h1lt (inv_pos.2 hD)

end

end Algsuperdiff.Section4.Provider.Proportion
