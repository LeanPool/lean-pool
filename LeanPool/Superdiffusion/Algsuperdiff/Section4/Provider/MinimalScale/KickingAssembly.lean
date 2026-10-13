/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.KickingLemma

/-!
# KickingAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.good.scale.kicking`: the assembly

ABK26, §4.2.  `KickingLemma.lean` supplies the bridges, the finiteness and the
`ℝ≥0∞ → ℝ` conversion; this module performs the three-term addition of
`l.minimal.scale.sep` and states the lemma.

* `exists_cesaro_dTwo_bound` — `e.D2k.kicked` read at the `D`-decomposition's own
  `D₂` and at the lemma's envelopes (`s^{−7/2}` deterministic, `s^{−9/2}`
  fluctuation).
* `exists_cesaro_dThree_bound` — the same for `D₃`, with `stepThree_det_closed` /
  `stepThree_fluc_closed` supplying the two closed `s`-powers.
* `exists_goodScaleKicking` — **the kicking lemma**.

The three `Γ₂` fluctuations are added by `isBigO_gammaSigma_add3`
(`l.Gamma.sigma.triangle`, three-term form) at the constant
`(1 + log 3)^{1/2} ≤ 2` (`triangleConstThree_le`), which is the manuscript's
"adding the previous three displays".

## The single output constant

`C = C_dec + C_end + C_dec·(C_end + 2·stepTwoDetConst + 2·stepThreeDetConst d + 1)
      + C_dec·2·(C_end + 2·stepTwoConst + 2·stepThreeFlucConst d)`,

a function of `d` alone: `C_dec` is the `D`-decomposition's constant, `C_end`
the `D₁` endpoint's, and the four Step-2/Step-3 constants are the proved
absolute / dimensional ones.  It dominates `C_dec` and `C_end` so that the
lemma's own regime clause passes down to both inputs, and the factors `2` are
the two prefactor conversions (`c⋆^{−1/2} ≤ 2c⋆^{−1}` and the triangle
constant).

## References

* ABK26, `l.minimal.scale.sep`; `l.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion
open Algsuperdiff.Probability
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `D₂` Cesàro bound at the lemma's envelopes -/

/-- **`e.D2k.kicked` at the `D`-decomposition's own `D₂`.**  The Cesàro average of
`D₂` over the window splits into a deterministic level below
`2·stepTwoDetConst·c⋆^{−1}s^{−7/2}√γ` and a `Γ₂` fluctuation of scale
`2·stepTwoConst·c⋆^{−1}s^{−9/2}√γ(m−n)^{−1/2}`.  Both readings pay the single
absolute factor `2` of `sqrt_cstar_inv_le`. -/
theorem exists_cesaro_dTwo_bound (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (hs1 : (s : ℝ) ≤ 1) {n m : ℤ} (hnm : n < m) :
    ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
      (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          cesaroAvg (fun k => (dTwo M s k omega).toReal) n m ≤ Xdet omega + Xfluc omega) ∧
        (∀ omega, Xdet omega ≤
          2 * stepTwoDetConst *
            ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma)) ∧
        IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
          (2 * stepTwoConst *
              ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
            ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
  have hmn0 : (0 : ℝ) < ((m - n : ℤ) : ℝ) := by
    have h : (0 : ℤ) < m - n := by omega
    exact_mod_cast h
  have hNm0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hmn0.le _
  obtain ⟨Xdet, Xfluc, hdom, hdet, hfluc⟩ :=
    exists_D2k_kicked M hnm
      (pref := (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma)
      (jPref_nonneg M s)
  refine ⟨Xdet, Xfluc, ?_, ?_, ?_⟩
  · filter_upwards [hdom] with omega homega
    have hfun : (fun k => (dTwo M s k omega).toReal)
        = fun k => (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma *
            gradInner M k omega := funext fun k => dTwo_toReal_eq M s k omega
    rw [hfun]
    exact homega
  · intro omega
    refine (hdet omega).trans ?_
    have h := mul_le_mul_of_nonneg_left (pref_le_two_mul_envSeven M s hs1)
      stepTwoDetConst_nonneg
    linarith only [h]
  · refine hfluc.mono_scale ?_
    have hp : (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma ≤
        2 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) := by
      have h7 := pref_le_two_mul_envSeven M s hs1
      have h79 := envSeven_le_envNine M s hs1
      linarith only [h7, h79]
    have hb : stepTwoConst * ((Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ *
          Real.sqrt M.gamma) ≤
        2 * stepTwoConst *
          ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) := by
      have h := mul_le_mul_of_nonneg_left hp stepTwoConst_pos.le
      linarith only [h]
    exact mul_le_mul_of_nonneg_right hb hNm0

/-! ## 2. The `D₃` Cesàro bound at the lemma's envelopes -/

/-- The almost-sure convergence of that channel is proved, not assumed. -/
theorem exists_cesaro_dThree_bound (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (hs2 : (s : ℝ) ≤ 1 / 2) {n m : ℤ} (hnm : n < m) :
    ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
      (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          cesaroAvg (fun k => (dThree M s k omega).toReal) n m ≤ Xdet omega + Xfluc omega) ∧
        (∀ omega, Xdet omega ≤
          2 * stepThreeDetConst d *
            ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma)) ∧
        IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
          (2 * stepThreeFlucConst d *
              ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
            ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs1 : (s : ℝ) ≤ 1 := by linarith only [hs2]
  have halpha : (0 : ℝ) < (s : ℝ) / 4 := by linarith only [hs0]
  have hmn0 : (0 : ℝ) < ((m - n : ℤ) : ℝ) := by
    have h : (0 : ℤ) < m - n := by omega
    exact_mod_cast h
  have hNm0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hmn0.le _
  obtain ⟨Xdet, Xfluc, hdom, hdet, hfluc⟩ :=
    exists_D3k_kicked M halpha hnm
      (pref := (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma)
      (jPref_nonneg M s)
  refine ⟨Xdet, Xfluc, ?_, ?_, ?_⟩
  · filter_upwards [hdom, ae_hessHeadSeries_finite M halpha hnm.le] with omega homega hfin
    exact le_trans (cesaroAvg_mono hnm.le fun k hk => dThree_toReal_le M s hfin hk) homega
  · intro omega
    refine (hdet omega).trans ?_
    refine le_trans (mul_le_mul_of_nonneg_left (stepThree_det_closed d hs0 hs2)
      (jPref_nonneg M s)) ?_
    have h := mul_le_mul_of_nonneg_left (pref_mul_inv_five_le M s hs1)
      (stepThreeDetConst_pos d).le
    linarith only [h]
  · refine hfluc.mono_scale ?_
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (stepThree_fluc_closed d hs0 hs2) (jPref_nonneg M s)) hNm0) ?_
    have hb : (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma *
          (stepThreeFlucConst d * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹) ≤
        2 * stepThreeFlucConst d *
          ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) := by
      have h := mul_le_mul_of_nonneg_left (pref_mul_inv_seven_le M s hs1)
        (stepThreeFlucConst_pos d).le
      linarith only [h]
    exact mul_le_mul_of_nonneg_right hb hNm0

/-! ## 3. The kicking lemma -/

/-- **`l.minimal.scale.sep` / `e.good.scale.kicking`.**

There is a dimensional constant `C` such that, in the printed regime
`γ ≤ C^{−10}c⋆^{10}` and on the window `s ∈ [8γ, 1/4]`, for every window
`[n, m]` with `n < m`,

```
avsum_{k=n}^m sup_{L ≥ k} 𝓔_{s,∞,2}(□_k; a_L − (k_L − k_k)_{□_k}, σ_k) 1_{𝒢(k;s,1)}
  ≤ C c⋆^{−1}s^{−7/2}√γ + 𝒪_{Γ₂}( C c⋆^{−1}s^{−9/2}√γ (m−n)^{−1/2} ) ,
```

the left side being the frozen statement's own `ℝ≥0∞` window average at the
origin centre and the additive `𝒪_{Γ₂}` being unfolded into the explicit `∃
Xdet Xfluc` split (the reading the proved apparatus consumes).

`s^{−7/2} = ((√s)⁷)⁻¹` and `s^{−9/2} = ((√s)⁹)⁻¹`, so no `rpow` appears in
either envelope. -/
theorem exists_goodScaleKicking (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ ^ 10 * Disorder.cstar M ^ 10 →
        ∀ s : {s : ℝ // 0 < s}, 8 * M.gamma ≤ (s : ℝ) → (s : ℝ) ≤ 1 / 4 →
          ∀ n m : ℤ, n < m →
            ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
              (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
                      ∑ k ∈ Finset.Icc n m,
                        Set.indicator (goodEventBase M (cgEllipLowerConstant d) k s 1)
                          (fun omega' => fluxCorrectedErrorObservableSup M k s omega')
                          omega ≤
                    ENNReal.ofReal (Xdet omega + Xfluc omega)) ∧
              (∀ omega, Xdet omega ≤
                C * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
                  Real.sqrt M.gamma)) ∧
              IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
                (C * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ *
                    Real.sqrt M.gamma) *
                  ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨CD, hCD, hdec⟩ := exists_dDecomposition_absorbed d
  obtain ⟨C1, hC1, hd1⟩ := exists_stepOne_d1_bound d
  have hs2d : (0 : ℝ) ≤ stepTwoDetConst := stepTwoDetConst_nonneg
  have hs2c : (0 : ℝ) < stepTwoConst := stepTwoConst_pos
  have hs3d : (0 : ℝ) < stepThreeDetConst d := stepThreeDetConst_pos d
  have hs3f : (0 : ℝ) < stepThreeFlucConst d := stepThreeFlucConst_pos d
  refine ⟨CD + C1 + CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) +
      CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) := by
      have hb : (0 : ℝ) < C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1 := by
        linarith only [hC1, hs2d, hs3d]
      exact mul_pos hCD hb
    have h2 : (0 : ℝ) < CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d)) := by
      have hb : (0 : ℝ) < 2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d) := by
        linarith only [hC1, hs2c, hs3f]
      exact mul_pos hCD hb
    linarith only [hCD, hC1, h1, h2]
  intro M hreg s hs8 hs4 n m hnm
  have hnm' : n ≤ m := hnm.le
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs1 : (s : ℝ) ≤ 1 := by linarith only [hs4]
  have hs12 : (s : ℝ) ≤ 1 / 2 := by linarith only [hs4]
  have halpha : (0 : ℝ) < (s : ℝ) / 4 := by linarith only [hs0]
  have hmn0 : (0 : ℝ) < ((m - n : ℤ) : ℝ) := by
    have h : (0 : ℤ) < m - n := by omega
    exact_mod_cast h
  have hNm0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hmn0.le _
  have hE7 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
      Real.sqrt M.gamma := envSeven_nonneg M s
  have hE9 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ *
      Real.sqrt M.gamma := envNine_nonneg M s
  -- the two constant floors of the output constant
  have hCDle : CD ≤ CD + C1 + CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) +
      CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d)) := by
    have h1 : (0 : ℝ) ≤ CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) := by
      have hb : (0 : ℝ) ≤ C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1 := by
        linarith only [hC1, hs2d, hs3d]
      exact mul_nonneg hCD.le hb
    have h2 : (0 : ℝ) ≤ CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d)) := by
      have hb : (0 : ℝ) ≤ 2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d) := by
        linarith only [hC1, hs2c, hs3f]
      exact mul_nonneg hCD.le hb
    linarith only [hC1, h1, h2]
  have hC1le : C1 ≤ CD + C1 + CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) +
      CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d)) := by
    have h1 : (0 : ℝ) ≤ CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) := by
      have hb : (0 : ℝ) ≤ C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1 := by
        linarith only [hC1, hs2d, hs3d]
      exact mul_nonneg hCD.le hb
    have h2 : (0 : ℝ) ≤ CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d)) := by
      have hb : (0 : ℝ) ≤ 2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d) := by
        linarith only [hC1, hs2c, hs3f]
      exact mul_nonneg hCD.le hb
    linarith only [hCD, h1, h2]
  have hregD : M.gamma ≤ CD⁻¹ ^ 10 * Disorder.cstar M ^ 10 := by
    refine hreg.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hcs0.le 10))
    exact pow_le_pow_left₀ (inv_nonneg.2 (lt_of_lt_of_le hCD hCDle).le)
      (inv_anti₀ hCD hCDle) 10
  have hreg1 : M.gamma ≤ C1⁻¹ ^ 10 * Disorder.cstar M ^ 10 := by
    refine hreg.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hcs0.le 10))
    exact pow_le_pow_left₀ (inv_nonneg.2 (lt_of_lt_of_le hC1 hC1le).le)
      (inv_anti₀ hC1 hC1le) 10
  -- the three endpoints
  obtain ⟨X1det, X1fluc, hdom1, hdet1, hfluc1⟩ :=
    hd1 M hreg1 s hs8 hs4 (cgEllipLowerConstant d) n m hnm'
  obtain ⟨X2det, X2fluc, hdom2, hdet2, hfluc2⟩ := exists_cesaro_dTwo_bound M s hs1 hnm
  obtain ⟨X3det, X3fluc, hdom3, hdet3, hfluc3⟩ := exists_cesaro_dThree_bound M s hs12 hnm
  refine ⟨fun omega => CD * (X1det omega + X2det omega + X3det omega +
      (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma),
    fun omega => CD * (X1fluc omega + X2fluc omega + X3fluc omega), ?_, ?_, ?_⟩
  · -- the almost-sure `ℝ≥0∞` display
    have hdecall : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ k : ℤ,
        Set.indicator (goodEventBase M (cgEllipLowerConstant d) k s 1)
            (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega ≤
          ENNReal.ofReal CD *
            (dOne M (cgEllipLowerConstant d) s k omega + dTwo M s k omega +
              dThree M s k omega +
              ENNReal.ofReal ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
                Real.sqrt M.gamma)) :=
      MeasureTheory.ae_all_iff.2 fun k => hdec M hregD s hs8 hs4 k
    filter_upwards [hdecall, ae_gradSeries_finite M,
      ae_hessHeadSeries_finite M halpha hnm', hdom2, hdom3] with omega hdω hg2 hg3 hd2 hd3
    have h1 : ∀ k ∈ Finset.Icc n m, dOne M (cgEllipLowerConstant d) s k omega ≠ (⊤ : ℝ≥0∞) :=
      fun k _ => dOne_ne_top M s (cgEllipLowerConstant d) hs1 omega
    have h2 : ∀ k ∈ Finset.Icc n m, dTwo M s k omega ≠ (⊤ : ℝ≥0∞) :=
      fun k _ => dTwo_ne_top M s k (hg2 k)
    have h3 : ∀ k ∈ Finset.Icc n m, dThree M s k omega ≠ (⊤ : ℝ≥0∞) :=
      fun k hk => dThree_ne_top M s hg3 hk
    refine (window_avg_le_ofReal_cesaro M (cgEllipLowerConstant d) s hnm' hCD.le hE7
      (fun k _ => hdω k) h1 h2 h3).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc1 := hdom1 omega
    have hsum : cesaroAvg (fun k => (dOne M (cgEllipLowerConstant d) s k omega).toReal) n m +
        cesaroAvg (fun k => (dTwo M s k omega).toReal) n m +
        cesaroAvg (fun k => (dThree M s k omega).toReal) n m +
        (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma ≤
      (X1det omega + X2det omega + X3det omega +
          (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma) +
        (X1fluc omega + X2fluc omega + X3fluc omega) := by
      linarith only [hc1, hd2, hd3]
    have hmul := mul_le_mul_of_nonneg_left hsum hCD.le
    linarith only [hmul]
  · -- the deterministic level
    intro omega
    have hb1 := hdet1 omega
    have hb2 := hdet2 omega
    have hb3 := hdet3 omega
    have hstep : X1det omega + X2det omega + X3det omega +
        (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma ≤
      (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma) := by
      linarith only [hb1, hb2, hb3]
    have hmul := mul_le_mul_of_nonneg_left hstep hCD.le
    have hrest : (0 : ℝ) ≤ (CD + C1 +
        CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d))) *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma) := by
      refine mul_nonneg ?_ hE7
      have hb : (0 : ℝ) ≤ 2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d) := by
        linarith only [hC1, hs2c, hs3f]
      have h2 : (0 : ℝ) ≤ CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d)) :=
        mul_nonneg hCD.le hb
      linarith only [hCD, hC1, h2]
    linarith only [hmul, hrest]
  · -- the `Γ₂` fluctuation
    have ha1 : (0 : ℝ) ≤ C1 *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
        ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg hC1.le hE9) hNm0
    have ha2 : (0 : ℝ) ≤ 2 * stepTwoConst *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
        ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) := by
      refine mul_nonneg (mul_nonneg ?_ hE9) hNm0
      linarith only [hs2c]
    have ha3 : (0 : ℝ) ≤ 2 * stepThreeFlucConst d *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
        ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) := by
      refine mul_nonneg (mul_nonneg ?_ hE9) hNm0
      linarith only [hs3f]
    have hrpow : ((m - n + 1 : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) := by
      refine rpow_neg_half_le_rpow_neg_half hmn0 ?_
      have h : (m - n : ℤ) ≤ m - n + 1 := by omega
      exact_mod_cast h
    have h1' : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) X1fluc
        (C1 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
          ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
      refine hfluc1.mono_scale ?_
      have hbase : C1 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
          Real.sqrt M.gamma) ≤
          C1 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ *
            Real.sqrt M.gamma) :=
        mul_le_mul_of_nonneg_left (envSeven_le_envNine M s hs1) hC1.le
      have hmn10 : (0 : ℝ) ≤ ((m - n + 1 : ℤ) : ℝ) := by
        have h : (0 : ℤ) ≤ m - n + 1 := by omega
        exact_mod_cast h
      refine mul_le_mul hbase hrpow (Real.rpow_nonneg hmn10 _) ?_
      exact mul_nonneg hC1.le hE9
    have hsum := isBigO_gammaSigma_add3 (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (by norm_num : (0 : ℝ) < 2) ha1 ha2 ha3 h1' hfluc2 hfluc3
    have hmul := IsBigO.const_mul (c := CD) hCD.le hsum
    refine hmul.mono_scale ?_
    -- the triangle constant and the coefficient bookkeeping
    set S : ℝ := C1 *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
        ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) +
      2 * stepTwoConst *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
        ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) +
      2 * stepThreeFlucConst d *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
        ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) with hSdef
    have hS0 : (0 : ℝ) ≤ S := by
      rw [hSdef]
      linarith only [ha1, ha2, ha3]
    have htri : (1 + Real.log 3) ^ ((2 : ℝ))⁻¹ * S ≤ 2 * S :=
      mul_le_mul_of_nonneg_right triangleConstThree_le hS0
    have hSeq : S = (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d) *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
        ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [hSdef]
      ring
    have hrest : (0 : ℝ) ≤ (CD + C1 +
        CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1)) *
        (((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
          ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
      refine mul_nonneg ?_ (mul_nonneg hE9 hNm0)
      have hb : (0 : ℝ) ≤ C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1 := by
        linarith only [hC1, hs2d, hs3d]
      have h1 : (0 : ℝ) ≤ CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) :=
        mul_nonneg hCD.le hb
      linarith only [hCD, hC1, h1]
    have hCDtri := mul_le_mul_of_nonneg_left htri hCD.le
    calc CD * ((1 + Real.log 3) ^ ((2 : ℝ))⁻¹ * S) ≤ CD * (2 * S) := hCDtri
      _ = 2 * CD * ((C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d) *
            ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
            ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2)) := by rw [hSeq]; ring
      _ ≤ (CD + C1 + CD * (C1 + 2 * stepTwoDetConst + 2 * stepThreeDetConst d + 1) +
            CD * (2 * (C1 + 2 * stepTwoConst + 2 * stepThreeFlucConst d))) *
            ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
            ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) := by linarith only [hrest]

end

end Algsuperdiff.Section4.Provider.MinimalScale
