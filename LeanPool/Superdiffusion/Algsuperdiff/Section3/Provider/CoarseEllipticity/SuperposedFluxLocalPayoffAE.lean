/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLocalPayoff
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.RandomHsepAllLWaveEnvelope
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# SuperposedFluxLocalPayoffAE

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Unconditional a.e. local lower payoff

The priced all-cutoff payoff has a target independent of its separation depth
`H` and wave amplitude `t`.  This file chooses the explicit sequence
`H_j = j + 1`, `t_j = sqrt (j + 1)` and proves that both terms of the price
vanish.  It then bounds the outer measure of the target's failure set by every
price in the sequence.  This does not require the target itself to be
measurable and never promotes an almost-everywhere assertion to a pointwise
one.

The resulting one-cube payoff is intersected over the finite descendant grid,
and the local random lane is replaced by its honest finite-grid maximum.  A
final producer pairs this a.e. payoff with the existing direct-gate Orlicz
certificate.  Its exponent upper gate remains explicit because the payoff
hypotheses do not imply it.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Filter MeasureTheory Topology
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

/-- Separation depth in the explicit zero-price limiting sequence. -/
def allLPriceLimitDepth (j : ℕ) : ℕ := j + 1

/-- Wave amplitude in the explicit zero-price limiting sequence. -/
def allLPriceLimitAmplitude (j : ℕ) : ℝ :=
  Real.sqrt ((j : ℝ) + 1)

/-- Along `H_j = j + 1` and `t_j = sqrt (j + 1)`, the all-cutoff price tends
to zero.  The wave term is polynomial times exponential decay, while the
separation term is double-exponential. -/
theorem tendsto_randomHsepAllLWavePrice_limitSequence
    {sigma b : ℝ} (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) :
    Tendsto
      (fun j : ℕ => randomHsepAllLWavePrice sigma b
        (allLPriceLimitDepth j) (allLPriceLimitAmplitude j))
      atTop (𝓝 0) := by
  have hx : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hxexp : Tendsto
      (fun j : ℕ => ((j : ℝ) + 1) * Real.exp (-((j : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [pow_one] using!
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
  have hexp : Tendsto (fun j : ℕ => Real.exp (-((j : ℝ) + 1)))
      atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
  have hwave : Tendsto
      (fun j : ℕ => (((j : ℝ) + 1) + 1) *
        (2 * Real.exp (-((j : ℝ) + 1)) *
          (1 - Real.exp (-1))⁻¹)) atTop (𝓝 0) := by
    have hsum := hxexp.add hexp
    have hmul := hsum.mul_const (2 * (1 - Real.exp (-1))⁻¹)
    have hmul' : Tendsto
        (fun j : ℕ => (((j : ℝ) + 1) * Real.exp (-((j : ℝ) + 1)) +
          Real.exp (-((j : ℝ) + 1))) *
            (2 * (1 - Real.exp (-1))⁻¹)) atTop (𝓝 0) := by
      simpa only [zero_add, zero_mul] using hmul
    convert hmul' using 1
    funext j
    ring
  have halpha : 0 < (1 - sigma) * b := by
    have : 0 < 1 - sigma := by linarith
    exact mul_pos this hb0
  have halphaTop : Tendsto
      (fun j : ℕ => (1 - sigma) * b * ((j : ℝ) + 1)) atTop atTop := by
    simpa only [mul_assoc] using hx.const_mul_atTop halpha
  have hthreeTop : Tendsto
      (fun j : ℕ => (3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + 1)))
      atTop atTop := by
    have hlogTop := halphaTop.const_mul_atTop
      (lt_trans zero_lt_one one_lt_log_three)
    have h := Real.tendsto_exp_atTop.comp hlogTop
    simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)] using! h
  have htail : Tendsto
      (fun j : ℕ => hsepTailConst sigma b *
        Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + 1)))))
      atTop (𝓝 0) := by
    have hzero := Real.tendsto_exp_neg_atTop_nhds_zero.comp hthreeTop
    simpa only [Function.comp_apply, mul_zero] using
      hzero.const_mul (hsepTailConst sigma b)
  have hsum := hwave.add htail
  have hsum' : Tendsto
      (fun j : ℕ => (((j : ℝ) + 1) + 1) *
          (2 * Real.exp (-((j : ℝ) + 1)) *
            (1 - Real.exp (-1))⁻¹) +
        hsepTailConst sigma b *
          Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + 1)))))
      atTop (𝓝 0) := by
    simpa only [zero_add] using hsum
  convert hsum' using 1
  funext j
  rw [randomHsepAllLWavePrice, allLPriceLimitDepth, allLPriceLimitAmplitude,
    allLWavePrice, gammaSigma]
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  rw [Real.rpow_two, Real.sq_sqrt hj0, ← Real.exp_neg]
  push_cast
  ring

/-- The finite pure-flux coordinate sum is strictly positive in positive dimension,
so the shifted local payoff constant meets the strict scale premise of the
`bfa` Orlicz A. -/
theorem superposedFluxLocalConst_pos
    {d : ℕ} (hd : 2 ≤ d) (M : ABKModel d) (n i : ℤ)
    (eps beta : ℝ) (k₀ kp : ℕ) :
    0 < superposedFluxLocalConst M n i eps beta k₀ kp := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  have hsimplex : 0 < simplexCrudeConst d (1 / 4) := by
    have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hpow := Real.rpow_lt_one_of_one_lt_of_neg
        (show (1 : ℝ) < 3 by norm_num) (show (-(1 / 2 : ℝ)) < 0 by norm_num)
      linarith
    rw [simplexCrudeConst]
    norm_num
    positivity
  have hktot : ∀ j : Fin d,
      0 < ktotConst M n i 3 0 (0 : Vec d) (basisVec j) := by
    intro j
    rw [ktotConst, vecNormSq_basisVec]
    simp only [vecNormSq, vecDot_zero_left, mul_zero, mul_one]
    positivity
  have hlayer : ∀ j : Fin d,
      0 < layerSumConst beta (2 * M.gamma + eps) kp
        (ktotConst M n i 3 0 (0 : Vec d) (basisVec j))
        (4 * (superposedDivConst d) ^ 2 *
          ktotConst M n i 3 0 (0 : Vec d) (basisVec j))
        (6 * (d : ℝ)) := by
    intro j
    have hI : 0 < (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
      apply inv_pos.mpr
      linarith [three_rpow_neg_quarter_lt_one]
    have hcol : 0 ≤ 4 * (superposedDivConst d) ^ 2 *
        ktotConst M n i 3 0 (0 : Vec d) (basisVec j) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hktot j).le
    have hmass : 0 < 6 * (d : ℝ) := mul_pos (by norm_num) hdR
    have hfirst : 0 <
        ktotConst M n i 3 0 (0 : Vec d) (basisVec j) * (6 * (d : ℝ)) *
          (3 : ℝ) ^ ((2 * M.gamma + eps) * ((kp : ℝ) + 1)) :=
      mul_pos (mul_pos (hktot j) hmass) (Real.rpow_pos_of_pos (by norm_num) _)
    have hsecond : 0 ≤
        2 * (4 * (superposedDivConst d) ^ 2 *
          ktotConst M n i 3 0 (0 : Vec d) (basisVec j) *
            Real.sqrt (6 * (d : ℝ))) * (3 : ℝ) ^ (2 * beta) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (mul_nonneg hcol (Real.sqrt_nonneg _)))
        (Real.rpow_nonneg (by norm_num) _)
    rw [layerSumConst]
    exact mul_pos hI (add_pos_of_pos_of_nonneg hfirst hsecond)
  let j0 : Fin d := ⟨0, by omega⟩
  have hcoordinate : 0 < superposedFluxCoordinateConst M n i eps beta kp := by
    unfold superposedFluxCoordinateConst
    exact (hlayer j0).trans_le
      (Finset.single_le_sum (fun j _ => (hlayer j).le) (Finset.mem_univ j0))
  unfold superposedFluxLocalConst
  exact mul_pos hcoordinate (Real.rpow_pos_of_pos (by norm_num) _)

/-- Stationarity transports the all-cutoff wave failure bound to an arbitrary
real translation.  Measurability is supplied by the literal wave event. -/
theorem measureReal_not_randomHsepAllLWaveEnvelope_translate_le
    {d : ℕ} (hd : 2 ≤ d) (M : ABKModel d) {n : ℤ} {E sigma b : ℝ}
    (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (n - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) (k₀ : ℕ)
    {L₀ : ℤ} (hnL₀ : n ≤ L₀) {H : ℕ} (hH : 1 ≤ H)
    {t : ℝ} (ht : 1 ≤ t) (z : Vec d) :
    (cutoffSampleLaw M).toMeasure.real
        {omega : CutoffSample d |
          ¬ randomHsepAllLWaveEnvelope M n E b k₀ L₀ t
            (translateCutoffSample z omega)} ≤
      randomHsepAllLWavePrice sigma b H t := by
  have hcenter := measureReal_not_randomHsepAllLWaveEnvelope_le
    hd M hE hS hsigma0 hsigma hb0 hb hEexp hE4 hunit hgamma20 hinvSq
      hEb hgamma k₀ hnL₀ hH ht
  have heq := measureReal_preimage_translateCutoffSample M z
    (measurableSet_randomHsepAllLWaveEnvelope M n E b k₀ L₀ t).compl
  calc
    (cutoffSampleLaw M).toMeasure.real
        {omega : CutoffSample d |
          ¬ randomHsepAllLWaveEnvelope M n E b k₀ L₀ t
            (translateCutoffSample z omega)} =
      (cutoffSampleLaw M).toMeasure.real
        (translateCutoffSample z ⁻¹'
          {omega : CutoffSample d |
            ¬ randomHsepAllLWaveEnvelope M n E b k₀ L₀ t omega}) := rfl
    _ = (cutoffSampleLaw M).toMeasure.real
        {omega : CutoffSample d |
          ¬ randomHsepAllLWaveEnvelope M n E b k₀ L₀ t omega} := heq
    _ ≤ randomHsepAllLWavePrice sigma b H t := hcenter


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
