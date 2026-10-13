/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.LayerBrackets
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.CesaroAlgebra
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.TruncatedScaleTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.WindowRearrange

/-!
# StepTwoDTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 2 of the kicking lemma: the `D₂` half of `e.kick.Dees.Dees`

ABK26, §4.2, `l.minimal.scale.sep`, Step 2.  The manuscript's `D₂` is

```
D₂(k) = c⋆^{−1/2} s^{−1} γ^{1/2} Σ_{l ≥ k} 3^{(2−γ)k} ‖∇j_l‖_{W^{1,∞}(□_k)}
```

and Step 2 proves the display `e.D2k.kicked`

```
avsum_{k=n}^m D₂(k) ≤ C c⋆^{−1/2}s^{−1}γ^{1/2}
                        + 𝒪_{Γ₂}( C c⋆^{−1/2}s^{−1}γ^{1/2}(m−n)^{−1/2} ) .
```

## The three ingredients

* the window rearrangement — `cesaro_gradInner_le`;
* the layer gradient tail — proved in `LayerBrackets`;
* the Step-2 conclusion — `exists_stepTwo_kicked` and its prefactor form
  `exists_D2k_kicked`.

## The rearrangement, and the two corrections it respects

The manuscript rearranges `Σ_{k=n}^m Σ_{l≥k}` into `Σ_{l≥n} Σ_{k=n}^{m∧l}` and
then majorizes the inner `k`-sum.  Two corrections are built into the route:

* the printed majorant `3^{(2−γ)(m∧l)}‖∇j_l‖_{W^{1,∞}(□_l)}` enlarges the
  cube, and the *volume-normalized* gauge is not monotone in the cube, so that
  step is false as printed for `l > m`.  Here the comparison is always `□_k`
  versus `□_l` at the same centre with both `3^{(2−γ)·}` weights attached
  (`LayerBrackets.gradCross_le`), which is the honest form; the printed
  majorant is never formed.
* the shell weight that survives the comparison is `1 − γ`, not `2 − γ`.  Since
  `γ ≤ 1/4` (frozen `ShellLawPrefix.gamma_le_quarter`), the rate is at
  least `3/4` and the geometric closure `geomTailConst` is bounded by an
  absolute numeral; no `γ`-dependence enters the output constant.

The window arithmetic itself is the carrier-free
`Algsuperdiff.Probability.window_geom_tail_rearrange_le`, applied at
`α = 1 − γ`.

## Why the endpoint is almost sure

The manuscript's inner sum is an infinite series over the field index `l`; the
anchor forms it in `ℝ≥0∞`.  The real reading `.toReal` is dominated by the
majorant series only where that series converges, and convergence holds almost
surely — proved, not assumed, from the per-layer first moments
(`LayerBrackets.ae_wsumE_ne_top`).  The anchor's clause (i) is itself an almost
sure statement, so nothing is lost.

## Independence

Step 2 applies `p.concentration` to the layer family `{3^{(2−γ)l}‖∇j_l‖}`,
which is genuinely independent: each layer is a functional of its own shell and
the single-shell sigma-fields are mutually independent
(`LayerBrackets.iIndepFun_gradLayer`).  The manuscript's own justification ("by
the independence of the sequence `{j_n}`") is exactly this.

## References

* ABK26, `l.minimal.scale.sep` Step 2.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Probability
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `(1−γ)` rate -/

theorem gradRate_pos (M : ABKModel d) : 0 < 1 - M.gamma := by
  have h := M.shellPrefix.gamma_le_quarter
  linarith only [h]

/-- On the frozen window `γ ≤ 1/4` the Step-2 rate is at least `3/4`. -/
theorem three_quarters_le_gradRate (M : ABKModel d) : (3 : ℝ) / 4 ≤ 1 - M.gamma := by
  have h := M.shellPrefix.gamma_le_quarter
  linarith only [h]

/-- The geometric closure constant is antitone in the rate. -/
theorem geomTailConst_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    geomTailConst b ≤ geomTailConst a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hmono : (3 : ℝ) ^ (-b) ≤ (3 : ℝ) ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hab])
  have hpa : 0 < 1 - (3 : ℝ) ^ (-a) := one_sub_three_rpow_neg_pos ha
  have hpb : 0 < 1 - (3 : ℝ) ^ (-b) := one_sub_three_rpow_neg_pos hb
  simp only [geomTailConst, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpa (by linarith only [hmono])

/-- The absolute bound on the Step-2 geometric closure: it is at most the
numeral `geomTailConst (3/4)`, with no `γ` left in it. -/
theorem geomTailConst_gradRate_le (M : ABKModel d) :
    geomTailConst (1 - M.gamma) ≤ geomTailConst (3 / 4) :=
  geomTailConst_anti (by norm_num) (three_quarters_le_gradRate M)

/-! ## 2. The anchor-shaped inner sum of `D₂(k)` -/

/-- The field indices `l ≥ k`, enumerated by the offset `l − k ∈ ℕ`. -/
def upperScaleEquiv (k : ℤ) : ℕ ≃ {l : ℤ // k ≤ l} where
  toFun p := ⟨k + (p : ℤ), by omega⟩
  invFun l := (l.1 - k).toNat
  left_inv p := by
    show (k + (p : ℤ) - k).toNat = p
    omega
  right_inv l := by
    refine Subtype.ext ?_
    show k + (((l.1 - k).toNat : ℕ) : ℤ) = l.1
    have hl := l.2
    omega

/-- **The inner sum of `D₂(k)`**, formed in `ℝ≥0∞` exactly as the anchor
`annular_decomposition` forms it: `Σ_{l ≥ k} 3^{(2−γ)k}‖∇j_l‖_{W^{1,∞}(□_k)}`. -/
def gradInnerE (M : ABKModel d) (k : ℤ) (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' l : {l : ℤ // k ≤ l},
    ENNReal.ofReal
      (Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * shellW1InfGradNorm k (omega.1 l.1))

/-- The real-valued inner sum; at the samples where the `ℝ≥0∞` sum diverges this
is `0`, which only strengthens every upper-tail statement about it. -/
def gradInner (M : ABKModel d) (k : ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  (gradInnerE M k omega).toReal

/-- The inner sum as a `SeriesTail` weighted series: the weight is constant in
the offset and the atom is the cross-scale gauge. -/
theorem gradInnerE_eq_wsumE (M : ABKModel d) (k : ℤ) (omega : Cutoff.CutoffSample d) :
    gradInnerE M k omega =
      wsumE (fun p (w : Cutoff.CutoffSample d) => shellW1InfGradNorm k (w.1 (k + (p : ℤ))))
        (fun _ => Real.rpow 3 ((2 - M.gamma) * (k : ℝ))) omega := by
  rw [gradInnerE, ← (upperScaleEquiv k).tsum_eq
      (fun l : {l : ℤ // k ≤ l} =>
        ENNReal.ofReal
          (Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * shellW1InfGradNorm k (omega.1 l.1))),
    wsumE]
  rfl

/-! ## 3. The majorant layer series -/

def gradWeight (M : ABKModel d) (p : ℕ) : ℝ := (3 : ℝ) ^ (-((1 - M.gamma) * (p : ℝ)))

theorem gradWeight_pos (M : ABKModel d) (p : ℕ) : 0 < gradWeight M p :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem gradWeight_nonneg (M : ABKModel d) (p : ℕ) : 0 ≤ gradWeight M p :=
  (gradWeight_pos M p).le

/-- **The Step-2 majorant series at scale `k`**: the geometrically weighted sum
of the layer brackets at their own scales, from `k` upwards.  This is the
right-hand side of the manuscript's rearranged display. -/
def gradSeries (M : ABKModel d) (k : ℤ) : Cutoff.CutoffSample d → ℝ :=
  wsum (fun p => atomG1a M (k + (p : ℤ))) (gradWeight M)

theorem gradSeries_nonneg (M : ABKModel d) (k : ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ gradSeries M k omega := wsum_nonneg _ _ omega

/-- The majorant series in the real `tsum` spelling consumed by the window
arithmetic of `Algsuperdiff.Probability.WindowRearrange`. -/
theorem gradSeries_eq_tsum (M : ABKModel d) (k : ℤ) (omega : Cutoff.CutoffSample d) :
    gradSeries M k omega =
      ∑' p : ℕ, (3 : ℝ) ^ (-((1 - M.gamma) * (p : ℝ))) * atomG1a M (k + (p : ℤ)) omega :=
  wsum_eq_tsum (fun p w => atomG1a_nonneg M (k + (p : ℤ)) w) (gradWeight_nonneg M) omega

/-- **The pointwise majorization, in `ℝ≥0∞`, unconditional.**  This is the
manuscript's cube comparison summed over the field indices. -/
theorem gradInnerE_le_wsumE (M : ABKModel d) (k : ℤ) (omega : Cutoff.CutoffSample d) :
    gradInnerE M k omega ≤
      wsumE (fun p => atomG1a M (k + (p : ℤ))) (gradWeight M) omega := by
  rw [gradInnerE_eq_wsumE, wsumE, wsumE]
  refine ENNReal.tsum_le_tsum fun p => ENNReal.ofReal_le_ofReal ?_
  have hkl : k ≤ k + (p : ℤ) := by omega
  have hcast : ((k + (p : ℤ) - k : ℤ) : ℝ) = (p : ℝ) := by push_cast; ring
  have hbase := gradCross_le M hkl omega
  rw [hcast] at hbase
  exact hbase

/-- The real form of the majorization, at the samples where the majorant series
converges. -/
theorem gradInner_le_gradSeries (M : ABKModel d) (k : ℤ)
    {omega : Cutoff.CutoffSample d}
    (hfin : wsumE (fun p => atomG1a M (k + (p : ℤ))) (gradWeight M) omega ≠ (⊤ : ℝ≥0∞)) :
    gradInner M k omega ≤ gradSeries M k omega :=
  ENNReal.toReal_mono hfin (gradInnerE_le_wsumE M k omega)

/-! ## 4. Almost sure convergence of the majorant series -/

/-- The per-layer first moment of the Step-2 layer bracket. -/
theorem integral_atomG1a_le (M : ABKModel d) (l : ℤ) :
    ∫ omega, atomG1a M l omega ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      gammaMomentConst 2 * 1 :=
  integral_le_of_isBigOWith_of_nonneg one_pos (atomG1a_nonneg M l)
    (measurable_atomG1a M l) (isBigOWith_atomG1a M l)

theorem integrable_atomG1a (M : ABKModel d) (l : ℤ) :
    Integrable (atomG1a M l) (Cutoff.cutoffSampleLaw M).toMeasure :=
  integrable_of_isBigOWith_of_nonneg one_pos (atomG1a_nonneg M l)
    (measurable_atomG1a M l) (isBigOWith_atomG1a M l)

theorem summable_gradWeight_mul (M : ABKModel d) (a : ℝ) :
    Summable fun p : ℕ => gradWeight M p * a :=
  ((hasSum_threePow_neg (gradRate_pos M)).mul_right a).summable

/-- **The majorant series converges almost surely, at every scale.**  Proved from
the per-layer first moments; the manuscript never states the convergence and
never needs to, because it is automatic. -/
theorem ae_gradSeries_finite (M : ABKModel d) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ k : ℤ,
      wsumE (fun p => atomG1a M (k + (p : ℤ))) (gradWeight M) omega ≠ (⊤ : ℝ≥0∞) := by
  rw [MeasureTheory.ae_all_iff]
  intro k
  have hconst : (0 : ℝ) ≤ gammaMomentConst 2 * 1 := by
    have h := gammaMomentConst_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [h]
  exact ae_wsumE_ne_top (fun p w => atomG1a_nonneg M (k + (p : ℤ)) w)
    (fun p => measurable_atomG1a M (k + (p : ℤ)))
    (fun p => integrable_atomG1a M (k + (p : ℤ))) (gradWeight_nonneg M)
    (fun _ => hconst) (fun p => integral_atomG1a_le M (k + (p : ℤ)))
    (summable_gradWeight_mul M (gammaMomentConst 2 * 1))

/-! ## 5. The Step-2 window rearrangement -/

/-- **The Step-2 window rearrangement.**  At every sample point where the
majorant series converges,

```
Σ_{k=n}^m (inner sum of D₂(k)) ≤ Cgeo ( Σ_{l=n}^m Y_l + Σ_{p≥0} 3^{−(1−γ)p} Y_{m+1+p} )
```

with `Cgeo = geomTailConst (1−γ) = (1 − 3^{−(1−γ)})⁻¹` and `Y_l` the layer
bracket at its own scale. -/
theorem cesaro_gradInner_le (M : ABKModel d) {n m : ℤ} (hnm : n ≤ m)
    {omega : Cutoff.CutoffSample d}
    (hfin : ∀ k : ℤ,
      wsumE (fun p => atomG1a M (k + (p : ℤ))) (gradWeight M) omega ≠ (⊤ : ℝ≥0∞)) :
    ∑ k ∈ Finset.Icc n m, gradInner M k omega ≤
      geomTailConst (1 - M.gamma) *
        ((∑ l ∈ Finset.Icc n m, atomG1a M l omega) + gradSeries M (m + 1) omega) := by
  have hstep : ∑ k ∈ Finset.Icc n m, gradInner M k omega ≤
      ∑ k ∈ Finset.Icc n m, gradSeries M k omega :=
    Finset.sum_le_sum fun k _ => gradInner_le_gradSeries M k (hfin k)
  have hrw : ∀ k : ℤ, gradSeries M k omega =
      ∑' p : ℕ, (3 : ℝ) ^ (-((1 - M.gamma) * (p : ℝ))) * atomG1a M (k + (p : ℤ)) omega :=
    fun k => gradSeries_eq_tsum M k omega
  have hwin := window_geom_tail_rearrange_le (α := 1 - M.gamma) (gradRate_pos M)
    (Y := fun l => atomG1a M l omega) (fun l => atomG1a_nonneg M l omega) hnm
  simp only [← hrw] at hwin
  exact le_trans hstep hwin

/-! ## 6. The `Γ₂` tail of the off-window series -/

/-- **The off-window layer series has a `Γ₂` tail at a constant amplitude**:
`Σ_{l≥m} 3^{(2−γ)(m−l)}Y_l ≤ 𝒪_{Γ₂}(C)`.  This is the `e.Gamma.sigma.triangle`
step of Step 2, at the proved geometric-weight closure
`Algsuperdiff.Probability.weightedTsum_isBigOWith` (L4); no pointwise
summability of the layer series is assumed. -/
theorem isBigOWith_gradSeries (M : ABKModel d) (k : ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) (gradSeries M k)
      (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1)) := by
  have hfun : gradSeries M k =
      fun omega => ∑' p : ℕ,
        (3 : ℝ) ^ (-((1 - M.gamma) * (p : ℝ))) * atomG1a M (k + (p : ℤ)) omega :=
    funext fun omega => gradSeries_eq_tsum M k omega
  rw [hfun]
  exact weightedTsum_isBigOWith (by norm_num) (gradRate_pos M) one_pos
    (fun p w => atomG1a_nonneg M (k + (p : ℤ)) w)
    (fun p => measurable_atomG1a M (k + (p : ℤ)))
    fun p => isBigOWith_atomG1a M (k + (p : ℤ))

/-! ## 7. The Step-2 conclusion -/

/-- The deterministic level of Step 2, in units of the `D₂` prefactor. -/
def stepTwoDetConst : ℝ := geomTailConst (3 / 4) * (gammaMomentConst 2 * 1)

/-- The fluctuation constant of Step 2, in units of the `D₂` prefactor.  Both
constants are absolute numerals: no `γ`, no `s`, no dimension. -/
def stepTwoConst : ℝ :=
  cesaroTailEngineConst *
    (geomTailConst (3 / 4) * 1 +
      geomTailConst (3 / 4) * (gammaTriangleConst 2 * (geomTailConst (3 / 4) * 1)))

theorem stepTwoDetConst_nonneg : 0 ≤ stepTwoDetConst := by
  have h1 : 0 < geomTailConst (3 / 4 : ℝ) := geomTailConst_pos (by norm_num)
  have h2 : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  simp only [stepTwoDetConst]
  positivity

theorem stepTwoConst_pos : 0 < stepTwoConst := by
  have h1 : 0 < geomTailConst (3 / 4 : ℝ) := geomTailConst_pos (by norm_num)
  have h2 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h3 : 0 < cesaroTailEngineConst := cesaroTailEngineConst_pos
  simp only [stepTwoConst]
  positivity

/-- For a window `n < m`, the Cesàro average of the inner sums of `D₂` splits into
a deterministic level and a `Γ₂` fluctuation of scale `stepTwoConst ·
(m−n)^{−1/2}`. -/
theorem exists_stepTwo_kicked (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
      (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          cesaroAvg (fun k => gradInner M k omega) n m ≤ Xdet omega + Xfluc omega) ∧
        (∀ omega, Xdet omega ≤ stepTwoDetConst) ∧
        IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
          (stepTwoConst * (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hnm' : n ≤ m := le_of_lt hnm
  have hCgeo : 0 < geomTailConst (1 - M.gamma) := geomTailConst_pos (gradRate_pos M)
  have hCle : geomTailConst (1 - M.gamma) ≤ geomTailConst (3 / 4) :=
    geomTailConst_gradRate_le M
  have hbpos : 0 < geomTailConst (1 - M.gamma) *
      (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1)) := by
    have h2 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
    positivity
  -- the tail variable of the engine
  set T : Cutoff.CutoffSample d → ℝ :=
    fun omega => geomTailConst (1 - M.gamma) * gradSeries M (m + 1) omega with hTdef
  have hT : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) T
      (geomTailConst (1 - M.gamma) *
        (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1))) := by
    refine IsBigO.const_mul hCgeo.le ?_
    exact isBigO_of_isBigOWith_of_nonneg (gradSeries_nonneg M (m + 1))
      (isBigOWith_gradSeries M (m + 1))
  -- the engine, applied to the majorant Cesàro object
  obtain ⟨Xdet, Xfluc, hdom, hdet, hfluc⟩ :=
    cesaroAvg_isBigO_of_iIndepFun_with_tail
      (P := (Cutoff.cutoffSampleLaw M).toMeasure) (X := fun l => atomG1a M l) (T := T)
      (Dbar := fun omega => geomTailConst (1 - M.gamma) *
        cesaroAvg (fun l => atomG1a M l omega) n m
        + (1 / (((m - n + 1 : ℤ) : ℝ))) * T omega)
      (K := 1) (mu0 := gammaMomentConst 2 * 1) (a := geomTailConst (1 - M.gamma))
      (b := geomTailConst (1 - M.gamma) *
        (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1)))
      one_pos hCgeo.le hbpos.le (iIndepFun_gradLayer M) (fun l => measurable_atomG1a M l)
      (fun l => isBigO_of_isBigOWith_of_nonneg (atomG1a_nonneg M l) (isBigOWith_atomG1a M l))
      (fun l => integral_atomG1a_le M l) hT n m hnm' (fun _ => le_rfl)
  refine ⟨Xdet, Xfluc, ?_, ?_, ?_⟩
  · -- the almost sure domination of the true Cesàro average
    filter_upwards [ae_gradSeries_finite M] with omega hfinite
    have hkey := cesaro_gradInner_le M hnm' hfinite
    have hcard : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) := window_pos hnm'
    have hexp : geomTailConst (1 - M.gamma) *
          ((∑ l ∈ Finset.Icc n m, atomG1a M l omega) + gradSeries M (m + 1) omega)
        = ((m - n + 1 : ℤ) : ℝ) *
            (geomTailConst (1 - M.gamma) * cesaroAvg (fun l => atomG1a M l omega) n m
              + (1 / (((m - n + 1 : ℤ) : ℝ))) * T omega) := by
      rw [hTdef]
      simp only [cesaroAvg]
      field_simp
    have hstep : cesaroAvg (fun k => gradInner M k omega) n m ≤
        geomTailConst (1 - M.gamma) * cesaroAvg (fun l => atomG1a M l omega) n m
          + (1 / (((m - n + 1 : ℤ) : ℝ))) * T omega := by
      have hinv : (0 : ℝ) ≤ 1 / ((m - n + 1 : ℤ) : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hkey hinv
      simp only [cesaroAvg, hTdef]
      calc 1 / ((m - n + 1 : ℤ) : ℝ) * ∑ k ∈ Finset.Icc n m, gradInner M k omega
          ≤ 1 / ((m - n + 1 : ℤ) : ℝ) *
              (geomTailConst (1 - M.gamma) *
                ((∑ l ∈ Finset.Icc n m, atomG1a M l omega) + gradSeries M (m + 1) omega)) :=
            hmul
        _ = geomTailConst (1 - M.gamma) *
              (1 / ((m - n + 1 : ℤ) : ℝ) * ∑ l ∈ Finset.Icc n m, atomG1a M l omega)
            + 1 / ((m - n + 1 : ℤ) : ℝ) *
              (geomTailConst (1 - M.gamma) * gradSeries M (m + 1) omega) := by ring
    exact le_trans hstep (hdom omega)
  · intro omega
    refine le_trans (hdet omega) ?_
    have h2 : 0 ≤ gammaMomentConst 2 * 1 := by
      have h := gammaMomentConst_pos (show (0 : ℝ) < 2 by norm_num)
      linarith only [h]
    simp only [stepTwoDetConst]
    exact mul_le_mul_of_nonneg_right hCle h2
  · refine hfluc.mono_scale ?_
    have hpow : (0 : ℝ) < ((m - n : ℤ) : ℝ) := by
      have : (0 : ℤ) < m - n := by omega
      exact_mod_cast this
    have hle : (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) ≤
        (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
      refine rpow_neg_half_le_rpow_neg_half hpow ?_
      have : ((m - n : ℤ) : ℝ) ≤ ((m - n + 1 : ℤ) : ℝ) := by
        have : (m - n : ℤ) ≤ m - n + 1 := by omega
        exact_mod_cast this
      exact this
    have hApos : 0 ≤ cesaroTailEngineConst *
        (geomTailConst (1 - M.gamma) * 1 +
          geomTailConst (1 - M.gamma) *
            (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1))) := by
      have h2 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
      have h3 : 0 < cesaroTailEngineConst := cesaroTailEngineConst_pos
      positivity
    have hAle : cesaroTailEngineConst *
          (geomTailConst (1 - M.gamma) * 1 +
            geomTailConst (1 - M.gamma) *
              (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1)))
        ≤ stepTwoConst := by
      have h2 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
      have h3 : 0 < cesaroTailEngineConst := cesaroTailEngineConst_pos
      have hstep : geomTailConst (1 - M.gamma) * 1 +
            geomTailConst (1 - M.gamma) *
              (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1))
          ≤ geomTailConst (3 / 4) * 1 +
            geomTailConst (3 / 4) * (gammaTriangleConst 2 * (geomTailConst (3 / 4) * 1)) := by
        have h4 : 0 < geomTailConst (1 - M.gamma) := hCgeo
        have h5 : 0 < geomTailConst (3 / 4 : ℝ) := geomTailConst_pos (by norm_num)
        have hprod : geomTailConst (1 - M.gamma) * geomTailConst (1 - M.gamma)
            ≤ geomTailConst (3 / 4) * geomTailConst (3 / 4) :=
          mul_le_mul hCle hCle h4.le h5.le
        have hT2 : gammaTriangleConst 2 *
              (geomTailConst (1 - M.gamma) * geomTailConst (1 - M.gamma))
            ≤ gammaTriangleConst 2 * (geomTailConst (3 / 4) * geomTailConst (3 / 4)) :=
          mul_le_mul_of_nonneg_left hprod h2.le
        have hL : geomTailConst (1 - M.gamma) * 1 +
              geomTailConst (1 - M.gamma) *
                (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1))
            = geomTailConst (1 - M.gamma) +
              gammaTriangleConst 2 *
                (geomTailConst (1 - M.gamma) * geomTailConst (1 - M.gamma)) := by ring
        have hR : geomTailConst (3 / 4) * 1 +
              geomTailConst (3 / 4) * (gammaTriangleConst 2 * (geomTailConst (3 / 4) * 1))
            = geomTailConst (3 / 4) +
              gammaTriangleConst 2 *
                (geomTailConst (3 / 4) * geomTailConst (3 / 4)) := by ring
        rw [hL, hR]
        linarith only [hCle, hT2]
      simp only [stepTwoConst]
      exact mul_le_mul_of_nonneg_left hstep cesaroTailEngineConst_pos.le
    calc cesaroTailEngineConst *
          (geomTailConst (1 - M.gamma) * 1 +
            geomTailConst (1 - M.gamma) *
              (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1)))
          * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
        ≤ cesaroTailEngineConst *
            (geomTailConst (1 - M.gamma) * 1 +
              geomTailConst (1 - M.gamma) *
                (gammaTriangleConst 2 * (geomTailConst (1 - M.gamma) * 1)))
            * (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hle hApos
      _ ≤ stepTwoConst * (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_right hAle ?_
          exact Real.rpow_nonneg hpow.le _

/-- **`e.D2k.kicked`**, at an arbitrary nonnegative prefactor.  At `pref =
c⋆^{−1/2}s^{−1}γ^{1/2}` — the prefactor the annular decomposition puts in front
of the inner sum — this is the printed display

```
avsum_{k=n}^m D₂(k) ≤ C c⋆^{−1/2}s^{−1}γ^{1/2}
                        + 𝒪_{Γ₂}( C c⋆^{−1/2}s^{−1}γ^{1/2}(m−n)^{−1/2} )
```

with `C = max(stepTwoDetConst, stepTwoConst)`, both absolute numerals.  The
prefactor is kept abstract so that the final stitch may supply it in whatever
spelling the `D`-decomposition delivers. -/
theorem exists_D2k_kicked (M : ABKModel d) {n m : ℤ} (hnm : n < m) {pref : ℝ}
    (hpref : 0 ≤ pref) :
    ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
      (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          cesaroAvg (fun k => pref * gradInner M k omega) n m ≤ Xdet omega + Xfluc omega) ∧
        (∀ omega, Xdet omega ≤ stepTwoDetConst * pref) ∧
        IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
          (stepTwoConst * pref * (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨Xdet, Xfluc, hdom, hdet, hfluc⟩ := exists_stepTwo_kicked M hnm
  refine ⟨fun omega => pref * Xdet omega, fun omega => pref * Xfluc omega, ?_, ?_, ?_⟩
  · filter_upwards [hdom] with omega homega
    rw [cesaroAvg_const_mul]
    calc pref * cesaroAvg (fun k => gradInner M k omega) n m
        ≤ pref * (Xdet omega + Xfluc omega) := mul_le_mul_of_nonneg_left homega hpref
      _ = pref * Xdet omega + pref * Xfluc omega := by ring
  · intro omega
    have := mul_le_mul_of_nonneg_left (hdet omega) hpref
    calc pref * Xdet omega ≤ pref * stepTwoDetConst := this
      _ = stepTwoDetConst * pref := by ring
  · have h := IsBigO.const_mul hpref hfluc
    refine h.mono_scale ?_
    have : pref * (stepTwoConst * (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2))
        = stepTwoConst * pref * (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by ring
    exact le_of_eq this

end

end Algsuperdiff.Section4.Provider.MinimalScale
