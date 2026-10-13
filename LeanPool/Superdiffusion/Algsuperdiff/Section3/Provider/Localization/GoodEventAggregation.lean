/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.AggregationRemainder
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.LambdaGateChain

/-!
# GoodEventAggregation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
# `l.localization.mathcalE`: the v-uniform injection endpoint and the
  good-event grid aggregation

This module delivers two independent things.

## Part 1 --- the loading-uniform null set

The `LambdaGateChain` injection chain delivers the priced display in the shape

```text
∀ v, vecNormSq v ≤ 2 → ∀ᵐ ω, ω ∈ 𝒬(l,l-h,z) → (the priced display) ,
```

so its exceptional set is allowed to depend on the loading direction `v`,
whereas the printed display is pathwise *for every* `|e| = 1`, and an
uncountable union of null sets need not be null.  The consumers that need the
uniform form are the two composed switch endpoints
`SwitchNormalization.breakdownLeg{A,B}_le_of_shom_switch`, whose `hdeep` binder
is literally `∀ v, vecNormSq v ≤ 2 → J(...) ≤ c0` **at a fixed sample**.

No link of the chain is genuinely `v`-dependent in its null set: the whole a.e.
content is the single `v`-free event of `BadEvents.lambda_transfer_ae`, plus the
`v`-free `BadEvents.gradientW1Infinity_incrementUnitCube₂_le_responseGate_ae`
(itself one `filter_upwards` on the same event) and the `v`-free
`LambdaGateChain.inv_lambdaSq_le_of_mem_goodLocalEvent_ae`.  Every step that
consumes a loading vector --- `BadEvents.responseJ_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer`
and the deterministic bridges of `SensitivityBridges` --- is a **pointwise**
statement taking `(p, q)` as ordinary arguments.  The four theorems of Part 1
therefore re-thread only the a.e. structure, moving `∀ p q` (and, in the last of
them, `∀ Q hgap L`) inside the `∀ᵐ`, and consume the pointwise statements
unchanged.

## Part 2 --- the good-event grid aggregation engine

The printed step is *"combining these inequalities, summing over
`z ∈ 3^l ℤ^d ∩ □_m` and applying the triangle inequality"*.  Concretely, from
the per-`(l,z)` display

```text
max_{|e|=1} J(z+□_l, σ_m^{∓1/2}e; a_m) 1_{𝒬(l,l-h,z)}
  ≤ c · max_{|e|=1} J(z+□_l, σ_{l-h}^{∓1/2}e; a_{l-h})
    + b · 3^{4l-2γl}‖k_m-k_{l-h}‖²_{W^{2,∞}(z+□_l)}
    + (the σ-switch remainder at depth j = m-l)
```

one obtains, at the printed weights `c_{2s} 3^{-s(m-l)}` and the printed inner
exponent pair `(d/s, s/d)`,

```text
c_{2s} Σ_{l ≤ m} 3^{-s(m-l)} (⨍_{z} (LHS)^{d/s})^{s/d}
  ≤ c · c_{2s} Σ_l 3^{-s(m-l)} (⨍_z (deep)^{d/s})^{s/d}
    + b · c_{2s} Σ_l 3^{-s(m-l)} (⨍_z (wave)^{d/s})^{s/d}
    + 1024 C_rem γ² (h² + s^{-2} + E⁴|log γ|⁴) .
```

The grid's cardinality enters ONLY through the printed normalization: every
statement below is phrased through `Breakdown.legScaleAverage`, whose
`Book.Ch02.finsetAverageReal` is the printed `⨍`, and no `card` ever appears on
the right-hand side, the printed structure being the average itself.  The grid
is `descendantsAtScale (originCube d m) l`.

The `min`-series lane is not re-derived: the remainder is routed verbatim into
the proved collapse
`AggregationRemainder.localization_remainder_series_le_of_termwise` at the
sibling's own `switchRemainder` carrier, so the cross-file seam is consumed
rather than duplicated.

## What this module does NOT deliver

The **composed** good-event display at the concrete carriers --- i.e. the
instantiation of the engine at `Breakdown.breakdownLeg{A,B}` with the
`σ`-switch and the priced injection substituted for `hstep` --- is not here.
Its three ingredients are, however, all available.

**The per-`(l,z)` carrier bridge is proved.**  The chain from the injection
endpoint's unit-cube carrier `responseJ (cubeDomain (originCube d 0))
(perturbCoeffOn …)` to the switch endpoint's translated carrier `responseJ
(cubeDomain (originCube d R.scale)) ((… (translateCutoffSample …)).coeffOn …)`
is the three-step composition of
`BadEvents.responseJ_perturbCoeffOn_unitRescaledCutoffCoeff`,
`SensitivityBridges.responseJ_cutoffFamily_eq_unitRescaledCutoffCoeff` and
`ResponseTransport.responseJ_cutoffFamily_eq_originCube_translate` (whose
`[NeZero d]` is `Breakdown.neZero_of_abkModel`).  All three are already inside
this module's own import closure, and the chain is an equality needing no
hypothesis beyond `n ≤ L`, which the endpoints below already bind.

**The `hgate` transport is proved.**  The `hgate` binder of
`SwitchNormalization.breakdownLeg{A,B}_le_of_shom_switch` is available at the
switch endpoint's own carrier (`originCube d R.scale`, the translated sample),
for both the primal and the adjoint leg, from
`LambdaGateChain.lambda_gate_chain` composed with the deterministic and
unconditional `BadEvents.lambdaSq_cutoff_translateCutoffSample` and the cube-
and family-polymorphic `SwitchNormalization.sigmaStarInv_gate_of_lambdaGate`
and `…_transpose_gate_of_lambdaGate`.

**The aggregated wave series is a series-level push.**
`MultiscaleEstimate.waveSizesTotalW2` *is* the printed
`c_{2s} Σ_l 3^{-s(m-l)} (⨍_z wave^{d/s})^{s/d}`, phrased through the very
`Breakdown.legScaleAverage` carrier this module aggregates, with its own proved
endpoints (`wave_sizes_bound`); and the per-cube reconciliation of the
injection endpoint's wave leg to it is
`LambdaGateChain.three_zpow_mul_underlineW2Gauge_sq_le_waveGaugeW2_sq`.  Only
the monotonicity and `tsum_le_tsum` push from the per-cube bound to the series
remains.

Every proved carrier is already phrased through `descendantsAtScale`, so no
composition step meets the printed lattice at all.

Given those two scalars, the full composed switch endpoint

```text
breakdownLegA Q (a_L ω) (isotropic σ_m)
  ≤ 8 (3 c_deep + c_wave) + (the two switchRemainder terms)
```

compiles today from this module's Part-1 endpoint plus proved publics only.
This module is the layer directly beneath it.

## The scale gate on `m0` (-bin statement change)

The landmark premise carried by every public below is `mStarStar M < m0`,
**not** the printed `m0 in (mstar, infty) cap Z`.  Nothing else moved: the
premise is forwarded verbatim to the proved `shom_continuity`, no proof step
here consumes it, and no frozen statement changes.

## Hard rules

No `set_option`, no `sorry`, no custom axiom, no `native_decide`, no `#print`;
under 1500 lines; no upstream edit; no tracked file edited.
-/

namespace Algsuperdiff.Section3.Provider.Localization

open _root_.MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book _root_.HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! # Part 1 --- the v-uniform injection endpoint

The three steps (i), bottom up. -/

/-! ## Step A --- the response-`J` sensitivity switch, v-uniform

`BadEvents.responseJ_sensitivity_of_mem_goodLocalEvent_ae` binds `(p, q)`
outside its `∀ᵐ`, but its whole proof is one `filter_upwards` on the v-
`BadEvents.lambda_transfer_ae`, applied to the pointwise public
`…_of_lambdaTransfer`.  Moving `∀ p q` inside the event is therefore free. -/

/-- **The response-`J` sensitivity switch on the good event, uniformly in the
loads.**  On ONE probability-one event (the one of
`BadEvents.lambda_transfer_ae`), simultaneously for every pair of loading
vectors `(p, q)`, the coefficient switch of ABK26 holds in the form used.

This is `BadEvents.responseJ_sensitivity_of_mem_goodLocalEvent_ae` with the two
loading binders moved INSIDE the almost-sure quantifier; the statement is
otherwise character-identical.

Conditional on the caller-supplied `omega ∈ goodLocalEvent M Ccg Q n`, the
manuscript's own indicator, inherited verbatim. -/
theorem responseJ_sensitivity_of_mem_goodLocalEvent_ae_forall_loads (M : ABKModel d)
    (Ccg : ℝ) (Q : TriadicCube d) (n L : ℤ) (hL : n ≤ L) (delta : ℝ)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        ∀ p q : Vec d,
          responseJ (cubeDomain (originCube d 0))
              (perturbCoeffOn (cubeDomain (originCube d 0))
                (unitRescaledCutoffCoeff M Q n omega)
                (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1) p q
            ≤ (1 + delta + responseSensitivityConst d *
                (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
                (unitCubeLambda (3 / 8) (.finite 2)
                  (unitRescaledCutoffCoeff M Q n omega))⁻¹) *
                responseJ (cubeDomain (originCube d 0))
                  (unitRescaledCutoffCoeff M Q n omega) p q +
              responseSensitivityConst d * delta⁻¹ *
                (vecNormSq p * (incrementUnitCube₂ Q n L omega).w1Infinity ^ 2 *
                    (unitCubeLambda (3 / 8) (.finite 2)
                      (unitRescaledCutoffCoeff M Q n omega))⁻¹ +
                  |vecDot p q| *
                      (incrementUnitCube₂ Q n L omega).gradientW1Infinity ^ 2 *
                    (unitCubeLambda (3 / 8) (.finite 2)
                      (unitRescaledCutoffCoeff M Q n omega))⁻¹ ^ 2) := by
  filter_upwards [lambda_transfer_ae M Q n] with omega htransfer homega p q
  exact responseJ_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer M Q homega hL
    _ htransfer p q delta hdelta hdelta1

/-! ## Step B --- the composed `delta = 1` endpoint, v-uniform

The second a.e. input of the composed `delta = 1` sensitivity display, namely
`BadEvents.gradientW1Infinity_incrementUnitCube₂_le_responseGate_ae`, is
already v-free, and every remaining ingredient of that proof is deterministic.
The composition below is the proved one, re-threaded with `∀ p q` inside. -/

/-- **The composed `delta = 1` sensitivity endpoint, uniformly in the loads.**

The composed `delta = 1` sensitivity display of `SensitivityBridges`, with the
two loading binders moved INSIDE the almost-sure quantifier.  The event is the
intersection of the two v-free events already used there.

The deterministic ingredients are consumed unchanged: the response gate
(`BadEvents.gradientW1Infinity_incrementUnitCube₂_le_responseGate_ae`), the
`3^{4l}` fingerprints
(`SensitivityBridges.w1Infinity_sq_incrementUnitCube₂_le`,
`…gradientW1Infinity_sq_incrementUnitCube₂_le`), the reciprocal gauge
conversions (`SensitivityBridges.inv_unitCubeLambda_le_inv_lambdaSq_oneEighth`
and its square), the rescale companion
(`SensitivityBridges.responseJ_cutoffFamily_eq_unitRescaledCutoffCoeff`), and
CoarseGraining's `Ch02.responseJ_nonneg`.

Conditional on `omega ∈ goodLocalEvent M Ccg Q n`, inherited verbatim. -/
theorem responseJ_perturb_le_three_mul_responseJ_cube_ae_forall_loads
    (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) (n L : ℤ) (hL : n ≤ L) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        ∀ p q : Vec d,
          responseJ (cubeDomain (originCube d 0))
              (perturbCoeffOn (cubeDomain (originCube d 0))
                (unitRescaledCutoffCoeff M Q n omega)
                (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1) p q ≤
            3 * responseJ (cubeDomain Q)
                ((coefficientCutoffTriadicCoeffFamily M n omega).coeffOn Q) p q +
              responseSensitivityConst d *
                (vecNormSq p *
                    ((3 : ℝ) ^ (4 * Q.scale) *
                      underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2) *
                    (lambdaSq Q (1 / 8) (.finite 2)
                      (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ +
                  |vecDot p q| *
                      ((3 : ℝ) ^ (4 * Q.scale) *
                        underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2) *
                    (lambdaSq Q (1 / 8) (.finite 2)
                      (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ ^ 2) := by
  let : NeZero d := neZero_of_abkModel M
  have hCpos : (0 : ℝ) < responseSensitivityConst d :=
    responseSensitivityConst_pos M.shellPrefix.dimension
  filter_upwards
    [responseJ_sensitivity_of_mem_goodLocalEvent_ae_forall_loads M Ccg Q n L hL 1
      (by norm_num) le_rfl,
      gradientW1Infinity_incrementUnitCube₂_le_responseGate_ae M Ccg Q n L hL]
    with omega hswitch hgate homega p q
  have hsens := hswitch homega p q
  have hG := hgate homega
  have hlampos : (0 : ℝ) < unitCubeLambda (3 / 8) (.finite 2)
      (unitRescaledCutoffCoeff M Q n omega) := by
    rw [unitCubeLambda_unitRescaledCutoffCoeff]
    exact lambdaSq_pos Q (coefficientCutoffTriadicCoeffFamily M n omega)
      (by norm_num) (by norm_num)
  have hinvnn : (0 : ℝ) ≤ (unitCubeLambda (3 / 8) (.finite 2)
      (unitRescaledCutoffCoeff M Q n omega))⁻¹ := inv_nonneg.2 hlampos.le
  have hJ0 : (0 : ℝ) ≤ responseJ (cubeDomain (originCube d 0))
      (unitRescaledCutoffCoeff M Q n omega) p q :=
    responseJ_nonneg _ _ p q
  have hT : (0 : ℝ) ≤ (3 : ℝ) ^ (4 * Q.scale) *
      underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2 := by positivity
  -- The response gate collapses the switch's leading factor to `3`.
  have hlead : 1 + 1 + responseSensitivityConst d *
        (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
        (unitCubeLambda (3 / 8) (.finite 2)
          (unitRescaledCutoffCoeff M Q n omega))⁻¹ ≤ 3 := by
    have hCG : responseSensitivityConst d *
        (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
        unitCubeLambda (3 / 8) (.finite 2)
          (unitRescaledCutoffCoeff M Q n omega) := by
      have hstep := mul_le_mul_of_nonneg_left hG hCpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hCpos.ne', one_mul] at hstep
    have hstep := mul_le_mul_of_nonneg_right hCG hinvnn
    rw [mul_inv_cancel₀ hlampos.ne'] at hstep
    linarith
  have hfactor : (1 + 1 + responseSensitivityConst d *
        (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
        (unitCubeLambda (3 / 8) (.finite 2)
          (unitRescaledCutoffCoeff M Q n omega))⁻¹) *
        responseJ (cubeDomain (originCube d 0))
          (unitRescaledCutoffCoeff M Q n omega) p q ≤
      3 * responseJ (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q n omega) p q :=
    mul_le_mul_of_nonneg_right hlead hJ0
  -- The `3^{4l}` fingerprint and the reciprocal gauge conversion price the two
  -- remainder terms.
  have hzeroth : vecNormSq p * (incrementUnitCube₂ Q n L omega).w1Infinity ^ 2 *
        (unitCubeLambda (3 / 8) (.finite 2)
          (unitRescaledCutoffCoeff M Q n omega))⁻¹ ≤
      vecNormSq p *
          ((3 : ℝ) ^ (4 * Q.scale) *
            underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2) *
        (lambdaSq Q (1 / 8) (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (w1Infinity_sq_incrementUnitCube₂_le Q n L omega)
        (vecNormSq_nonneg p))
      (inv_unitCubeLambda_le_inv_lambdaSq_oneEighth M Q n omega) hinvnn
      (mul_nonneg (vecNormSq_nonneg p) hT)
  have hfirst : |vecDot p q| *
          (incrementUnitCube₂ Q n L omega).gradientW1Infinity ^ 2 *
        (unitCubeLambda (3 / 8) (.finite 2)
          (unitRescaledCutoffCoeff M Q n omega))⁻¹ ^ 2 ≤
      |vecDot p q| *
          ((3 : ℝ) ^ (4 * Q.scale) *
            underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2) *
        (lambdaSq Q (1 / 8) (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ ^ 2 :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left
        (gradientW1Infinity_sq_incrementUnitCube₂_le Q n L omega)
        (abs_nonneg (vecDot p q)))
      (inv_unitCubeLambda_sq_le_inv_lambdaSq_sq_oneEighth M Q n omega)
      (pow_nonneg hinvnn 2) (mul_nonneg (abs_nonneg (vecDot p q)) hT)
  have hrem : responseSensitivityConst d * (1 : ℝ)⁻¹ *
        (vecNormSq p * (incrementUnitCube₂ Q n L omega).w1Infinity ^ 2 *
            (unitCubeLambda (3 / 8) (.finite 2)
              (unitRescaledCutoffCoeff M Q n omega))⁻¹ +
          |vecDot p q| *
              (incrementUnitCube₂ Q n L omega).gradientW1Infinity ^ 2 *
            (unitCubeLambda (3 / 8) (.finite 2)
              (unitRescaledCutoffCoeff M Q n omega))⁻¹ ^ 2) ≤
      responseSensitivityConst d *
        (vecNormSq p *
            ((3 : ℝ) ^ (4 * Q.scale) *
              underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2) *
            (lambdaSq Q (1 / 8) (.finite 2)
              (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ +
          |vecDot p q| *
              ((3 : ℝ) ^ (4 * Q.scale) *
                underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2) *
            (lambdaSq Q (1 / 8) (.finite 2)
              (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ ^ 2) := by
    rw [inv_one, mul_one]
    exact mul_le_mul_of_nonneg_left (add_le_add hzeroth hfirst) hCpos.le
  rw [responseJ_cutoffFamily_eq_unitRescaledCutoffCoeff M n Q p q omega]
  exact hsens.trans (add_le_add hfactor hrem)

/-! ## Step C --- the priced injection endpoint, v-uniform -/

/-- **The per-`(l,z)` priced injection display, uniformly in the loads**.

The priced injection display of `LambdaGateChain` with `∀ v, vecNormSq v ≤ 2`
moved INSIDE the almost-sure quantifier: on ONE probability-one event,
simultaneously for every loading direction, the printed display holds.  The
premise list, the witness `C` (the `l.shom.continuity` constant) and the four
explicit constants `3`, `324`, `16 Ccg + 8 Ccg²`, `c⋆^{-1} γ 3^{4l-2γl}` are
inherited character-for-character; nothing is weakened and nothing is added.

This is the form the composed switch endpoints
`SwitchNormalization.breakdownLeg{A,B}_le_of_shom_switch` need for their
`hdeep` binder, which quantifies over the loading ball at a fixed sample.

Conditional on `omega ∈ goodLocalEvent M Ccg Q (Q.scale - hgap)`, `0 < Ccg` and
the displayed scale premises, all inherited verbatim. -/
theorem responseJ_injection_priced_ae_forall_loads (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ (Q : TriadicCube d) (hgap : ℕ) (L : ℤ),
            Q.scale - (hgap : ℤ) ≤ L → Q.scale - (hgap : ℤ) ≤ m0 →
            M.gamma * (hgap : ℝ) ≤ 1 →
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ goodLocalEvent M Ccg Q (Q.scale - (hgap : ℤ)) →
                  ∀ v : Vec d, vecNormSq v ≤ 2 →
                    Ch02.responseJ (Ch02.cubeDomain (originCube d 0))
                        (perturbCoeffOn (Ch02.cubeDomain (originCube d 0))
                          (unitRescaledCutoffCoeff M Q (Q.scale - (hgap : ℤ)) omega)
                          (incrementUnitCube₂ Q (Q.scale - (hgap : ℤ)) L
                            omega).toLInfSkewMatrixFieldOn 1)
                        (Observable.inverseSqrtLoad
                          (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
                        (Observable.sqrtLoad
                          (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) ≤
                      3 * Ch02.responseJ (Ch02.cubeDomain Q)
                          ((coefficientCutoffTriadicCoeffFamily M
                            (Q.scale - (hgap : ℤ)) omega).coeffOn Q)
                          (Observable.inverseSqrtLoad
                            (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
                          (Observable.sqrtLoad
                            (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) +
                        324 * responseSensitivityConst d *
                          (16 * Ccg + 8 * Ccg ^ 2) *
                          ((Disorder.cstar M)⁻¹ * M.gamma *
                            (3 : ℝ) ^ (4 * (Q.scale : ℝ) -
                              2 * M.gamma * (Q.scale : ℝ))) *
                          underlineW2Gauge Q
                            (shellIncrement omega.1 (Q.scale - (hgap : ℤ)) L) ^ 2 := by
  obtain ⟨C, hC0, hcont⟩ := shom_continuity d
  refine ⟨C, hC0, ?_⟩
  intro M m0 E hm0 hstate hCE hgammaE Ccg hCcg Q hgap L hnL hnm0 hgh
  let : NeZero d := neZero_of_abkModel M
  set n : ℤ := Q.scale - (hgap : ℤ) with hndef
  have hnQ : n ≤ Q.scale := by rw [hndef]; omega
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le one_pos hE1
  have hgamma1 : M.gamma ≤ 1 := by
    have hinv : ((E : ℝ))⁻¹ ≤ 1 := by rw [inv_le_one₀ hE0]; exact hE1
    have h0 : (0 : ℝ) ≤ ((E : ℝ))⁻¹ := (inv_pos.2 hE0).le
    refine le_trans hgammaE ?_
    calc ((E : ℝ)⁻¹) ^ 10 ≤ (1 : ℝ) ^ 10 := pow_le_pow_left₀ h0 hinv 10
      _ = 1 := one_pow 10
  obtain ⟨hquarter, -, -, -, -⟩ :=
    hcont M m0 E hm0 hstate hCE hgammaE n (n - 1) (by omega) hnm0
  have hsigp : (0 : ℝ) < ((Annealed.sigmaBar M (n - 1) : ℝ)) :=
    (Annealed.sigmaBar M (n - 1)).2
  have hsign : (0 : ℝ) < ((Annealed.sigmaBar M n : ℝ)) := (Annealed.sigmaBar M n).2
  have hquart : ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
      4 * ((Annealed.sigmaBar M (n - 1) : ℝ))⁻¹ := by
    have hpos4 : (0 : ℝ) < 1 / 4 * ((Annealed.sigmaBar M (n - 1) : ℝ)) := by
      positivity
    refine (inv_anti₀ hpos4 hquarter).trans (le_of_eq ?_)
    field_simp
  have hpre := inv_sq_sigmaBar_mul_three_zpow_le_prefactor M hstate Q.scale hgap
    (by omega) hgamma1 hgh
  rw [← hndef] at hpre
  have hCresp : (0 : ℝ) < responseSensitivityConst d :=
    responseSensitivityConst_pos M.shellPrefix.dimension
  filter_upwards [responseJ_perturb_le_three_mul_responseJ_cube_ae_forall_loads M
      Ccg Q n L hnL,
    inv_lambdaSq_le_of_mem_goodLocalEvent_ae M hCcg Q hnQ]
    with omega hend hell homega v hv
  set S : ℝ := ((Annealed.sigmaBar M (n - 1) : ℝ))⁻¹ with hS
  set W : ℝ := underlineW2Gauge Q (shellIncrement omega.1 n L) with hW
  set G : ℝ := (3 : ℝ) ^ (4 * Q.scale) with hG
  set Lam : ℝ := (Ch02.lambdaSq Q (1 / 8) (Ch02.MultiscaleExponent.finite 2)
    (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ with hLam
  have hS0 : (0 : ℝ) < S := inv_pos.2 hsigp
  have hW0 : (0 : ℝ) ≤ W := underlineW2Gauge_nonneg _ _
  have hG0 : (0 : ℝ) < G := zpow_pos (by norm_num) _
  have hLam0 : (0 : ℝ) ≤ Lam :=
    inv_nonneg.2 (Ch02.lambdaSq_nonneg Q _ (by norm_num) (by norm_num))
  have hLamS : Lam ≤ 2 * Ccg * S := hell homega
  have hp : vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v) ≤
      8 * S := by
    rw [vecNormSq_inverseSqrtLoad_eq]
    have h1 : ((Annealed.sigmaBar M n : ℝ))⁻¹ * vecNormSq v ≤
        ((Annealed.sigmaBar M n : ℝ))⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left hv (inv_pos.2 hsign).le
    nlinarith [hquart, h1]
  have hpq : |vecDot (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v)
      (Observable.sqrtLoad (Annealed.sigmaBar M n) v)| ≤ 2 := by
    rw [vecDot_inverseSqrtLoad_sqrtLoad, abs_of_nonneg (vecNormSq_nonneg v)]
    exact hv
  have hcore := injection_remainder_bound
    (Cresp := responseSensitivityConst d) (Ccg := Ccg) (S := S) (G := G) (W := W)
    (Lam := Lam)
    (A := vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v))
    (B := |vecDot (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v)
      (Observable.sqrtLoad (Annealed.sigmaBar M n) v)|)
    (P := 324 * (Disorder.cstar M)⁻¹ * M.gamma *
      (3 : ℝ) ^ (4 * (Q.scale : ℝ) - 2 * M.gamma * (Q.scale : ℝ)))
    hCresp.le hCcg.le hS0.le hG0.le hLam0 hLamS hp hpq hpre
  linarith [hend homega
    (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v)
    (Observable.sqrtLoad (Annealed.sigmaBar M n) v), hcore]

/-! ## Step D --- one null set for the whole grid

The previous endpoint still produces ONE null set per `(Q, hgap, L)`.  Part 2's
consumer entry point `geometricDiscount_mul_gridScaleSeries_good_le` fixes
`omega` and demands the per-`(j, R)` estimate for descendant cube, so the
z-aggregation needs the cube/gap/scale-uniform form as well.  It is available
at zero mathematical cost: `TriadicCube d` is countable, so three
`MeasureTheory.ae_all_iff` rewrites move `∀ Q hgap L` outside the almost-sure
quantifier, and the three scale premises are discharged by case analysis (when
one of them fails the conclusion is vacuous). -/

/-- **The priced injection display on ONE null set, uniformly in the cube, the gap,
the coefficient scale AND the load** (as read by the z-aggregation).

`responseJ_injection_priced_ae_forall_loads` with `∀ Q hgap L` and their three
scale premises ALSO moved inside the `∀ᵐ`: on one probability-one event,
simultaneously for every triadic cube, every gap, every coefficient scale and
every loading direction, the printed display holds.  Nothing is weakened: the
premise list, the witness `C` and the four constants are those of the endpoint
above, and instantiating this form at a fixed `(Q, hgap, L)` recovers it.

This is what the grid aggregation needs, because
`geometricDiscount_mul_gridScaleSeries_good_le`'s `hstep` binder quantifies
over all descendants at a fixed sample.

Conditional on `omega ∈ goodLocalEvent M Ccg Q (Q.scale - hgap)` and `0 < Ccg`,
both inherited verbatim. -/
theorem responseJ_injection_priced_ae_forall_cubes_and_loads (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            ∀ (Q : TriadicCube d) (hgap : ℕ) (L : ℤ),
              Q.scale - (hgap : ℤ) ≤ L → Q.scale - (hgap : ℤ) ≤ m0 →
              M.gamma * (hgap : ℝ) ≤ 1 →
                omega ∈ goodLocalEvent M Ccg Q (Q.scale - (hgap : ℤ)) →
                  ∀ v : Vec d, vecNormSq v ≤ 2 →
                    Ch02.responseJ (Ch02.cubeDomain (originCube d 0))
                        (perturbCoeffOn (Ch02.cubeDomain (originCube d 0))
                          (unitRescaledCutoffCoeff M Q (Q.scale - (hgap : ℤ)) omega)
                          (incrementUnitCube₂ Q (Q.scale - (hgap : ℤ)) L
                            omega).toLInfSkewMatrixFieldOn 1)
                        (Observable.inverseSqrtLoad
                          (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
                        (Observable.sqrtLoad
                          (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) ≤
                      3 * Ch02.responseJ (Ch02.cubeDomain Q)
                          ((coefficientCutoffTriadicCoeffFamily M
                            (Q.scale - (hgap : ℤ)) omega).coeffOn Q)
                          (Observable.inverseSqrtLoad
                            (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
                          (Observable.sqrtLoad
                            (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) +
                        324 * responseSensitivityConst d *
                          (16 * Ccg + 8 * Ccg ^ 2) *
                          ((Disorder.cstar M)⁻¹ * M.gamma *
                            (3 : ℝ) ^ (4 * (Q.scale : ℝ) -
                              2 * M.gamma * (Q.scale : ℝ))) *
                          underlineW2Gauge Q
                            (shellIncrement omega.1 (Q.scale - (hgap : ℤ)) L) ^ 2 := by
  obtain ⟨C, hC0, hmain⟩ := responseJ_injection_priced_ae_forall_loads d
  refine ⟨C, hC0, ?_⟩
  intro M m0 E hm0 hstate hCE hgammaE Ccg hCcg
  rw [MeasureTheory.ae_all_iff]
  intro Q
  rw [MeasureTheory.ae_all_iff]
  intro hgap
  rw [MeasureTheory.ae_all_iff]
  intro L
  by_cases hnL : Q.scale - (hgap : ℤ) ≤ L
  · by_cases hnm0 : Q.scale - (hgap : ℤ) ≤ m0
    · by_cases hgh : M.gamma * (hgap : ℝ) ≤ 1
      · filter_upwards [hmain M m0 E hm0 hstate hCE hgammaE Ccg hCcg Q hgap L
          hnL hnm0 hgh] with omega homega
        exact fun _ _ _ => homega
      · exact Filter.Eventually.of_forall fun _ _ _ h => absurd h hgh
    · exact Filter.Eventually.of_forall fun _ _ h _ => absurd h hnm0
  · exact Filter.Eventually.of_forall fun _ h _ _ => absurd h hnL

/-! # Part 2 --- the good-event grid aggregation engine

Everything below is gauge-free and carrier-free: no diffusivity, no threshold,
no coefficient family occurs.  The only development-specific object is the
remainder carrier `AggregationRemainder.switchRemainder`, at which the remainder
collapse is consumed. -/

/-! ## The per-scale step (grid Minkowski)

`Breakdown.legScaleAverage Q k s leg` is the printed
`(⨍_{z ∈ 3^k ℤ^d ∩ Q} leg(z+□_k)^{d/s})^{s/d}`.  For `s ≤ 1 ≤ d` the inner
exponent `d/s` is at least one, so the power mean is subadditive; it is also
degree-one homogeneous, and the power mean of a constant is at most that
constant (with equality off the empty grid). -/

/-- **The three-term reinjection at one scale.**  A per-cube estimate

```text
leg(z+□_k) ≤ c · deep(z+□_k) + b · wave(z+□_k) + rem
```

valid on the whole grid passes through the printed `L^{d/s}` average with
unchanged multiplicative constants and an unchanged additive remainder.  Two applications of
Minkowski, two of homogeneity, one constant lane.

This is the printed *"summing over `z ∈ 3^l ℤ^d ∩ □_m` and applying the
triangle inequality"*, at one localization scale.  The grid's cardinality
enters only through the average's own normalization. -/
theorem legScaleAverage_le_three_term (Q : TriadicCube d) (k : ℤ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hd : d ≠ 0)
    {leg deep wave : TriadicCube d → ℝ} {c b rem : ℝ}
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hrem : 0 ≤ rem)
    (hleg : ∀ R ∈ descendantsAtScale Q k, 0 ≤ leg R)
    (hdeep : ∀ R ∈ descendantsAtScale Q k, 0 ≤ deep R)
    (hwave : ∀ R ∈ descendantsAtScale Q k, 0 ≤ wave R)
    (hsplit : ∀ R ∈ descendantsAtScale Q k,
      leg R ≤ c * deep R + b * wave R + rem) :
    legScaleAverage Q k s leg ≤
      c * legScaleAverage Q k s deep + b * legScaleAverage Q k s wave + rem := by
  have hcd : ∀ R ∈ descendantsAtScale Q k, 0 ≤ c * deep R := fun R hR =>
    mul_nonneg hc (hdeep R hR)
  have hbw : ∀ R ∈ descendantsAtScale Q k, 0 ≤ b * wave R := fun R hR =>
    mul_nonneg hb (hwave R hR)
  have htail : ∀ R ∈ descendantsAtScale Q k, 0 ≤ b * wave R + rem := by
    intro R hR
    have := hbw R hR
    linarith
  have hstep1 : legScaleAverage Q k s leg ≤
      legScaleAverage Q k s (fun R => c * deep R) +
        legScaleAverage Q k s (fun R => b * wave R + rem) :=
    legScaleAverage_le_add Q k hs hs1 hd hcd htail hleg
      (fun R hR => by have := hsplit R hR; linarith)
  have hstep2 : legScaleAverage Q k s (fun R => b * wave R + rem) ≤
      legScaleAverage Q k s (fun R => b * wave R) +
        legScaleAverage Q k s (fun _ => rem) :=
    legScaleAverage_le_add Q k hs hs1 hd hbw (fun _ _ => hrem) htail
      (fun _ _ => le_rfl)
  have hconst : legScaleAverage Q k s (fun _ => rem) ≤ rem :=
    legScaleAverage_le_const Q k hs hrem (fun _ _ => hrem) (fun _ _ => le_rfl) hd
  rw [legScaleAverage_smul Q k hs hd hc hdeep] at hstep1
  rw [legScaleAverage_smul Q k hs hd hb hwave] at hstep2
  linarith

/-- **The printed spelling of the good part.**  The manuscript writes the indicator
INSIDE the `d/s`-th power, `(⨍_z (max_e J)^{d/s} 1_{𝒬(l,l-h,z)})^{s/d}`; the
statements above truncate the leg first.  No sign hypothesis on the leg is
needed. -/
theorem legScaleAverage_indicator_eq {Omega : Type*} (Q : TriadicCube d) (k : ℤ)
    {s : ℝ} (hs : 0 < s) (hd : d ≠ 0) {leg : TriadicCube d → ℝ}
    (B : TriadicCube d → Set Omega) (omega : Omega) :
    legScaleAverage Q k s
        (fun R => leg R * (B R).indicator (fun _ => (1 : ℝ)) omega) =
      Real.rpow
        (Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (leg R) ((d : ℝ) / s) *
            (B R).indicator (fun _ => (1 : ℝ)) omega))
        (s / (d : ℝ)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hP : (d : ℝ) / s ≠ 0 := ne_of_gt (div_pos hdR hs)
  have hfun : ∀ R ∈ descendantsAtScale Q k,
      Real.rpow (leg R * (B R).indicator (fun _ => (1 : ℝ)) omega) ((d : ℝ) / s) =
        Real.rpow (leg R) ((d : ℝ) / s) *
          (B R).indicator (fun _ => (1 : ℝ)) omega := by
    intro R _
    by_cases hmem : omega ∈ B R
    · rw [Set.indicator_of_mem hmem, mul_one, mul_one]
    · rw [Set.indicator_of_notMem hmem, mul_zero, mul_zero]
      exact Real.zero_rpow hP
  have havg :
      Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (leg R * (B R).indicator (fun _ => (1 : ℝ)) omega)
            ((d : ℝ) / s)) =
        Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (leg R) ((d : ℝ) / s) *
            (B R).indicator (fun _ => (1 : ℝ)) omega) := by
    unfold Book.Ch02.finsetAverageReal
    rw [Finset.sum_congr rfl hfun]
  show Real.rpow
      (Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
        (fun R => Real.rpow (leg R * (B R).indicator (fun _ => (1 : ℝ)) omega)
          ((d : ℝ) / s))) (s / (d : ℝ)) = _
  rw [havg]

/-! ## The `l`-sum

`Breakdown.breakdownLegSum` carries ONE leg for all scales, which is what the
printed left-hand side needs (`a_m` and `σ_m` do not move).  The right-hand
sides of the good-event aggregation are genuinely scale-indexed --- `a_{l-h}`,
`σ_{l-h}` and `3^{4l-2γl}‖k_m-k_{l-h}‖²` all move with `l` --- so the sum
below is taken over a per-scale of legs.  On a constant family the two agree by
`rfl`. -/

/-- The printed weighted grid sum `Σ_{l ≤ m} 3^{-s(m-l)} (⨍_z leg_l(z+□_l)^{d/s})^{s/d}`
of a per-scale leg family, reindexed by the depth `j = m - l ∈ ℕ`. -/
def gridScaleSeries (m : ℤ) (s : ℝ) (leg : ℕ → TriadicCube d → ℝ) : ℝ :=
  ∑' j : ℕ,
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      legScaleAverage (originCube d m) (m - (j : ℤ)) s (leg j)

/-- A weighted grid sum of a nonnegative leg family is nonnegative. -/
theorem gridScaleSeries_nonneg (m : ℤ) (s : ℝ) {leg : ℕ → TriadicCube d → ℝ}
    (hleg : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ leg j R) :
    0 ≤ gridScaleSeries m s leg :=
  tsum_nonneg fun j =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (legScaleAverage_nonneg _ _ _ (hleg j))

/-- **The named producer of the `Summable` caller obligations below.**  A
uniform descendant bound `D` on the whole leg family makes the weighted grid
series summable, by domination against the bare geometric series.

This is the per-scale-family analogue of the proved
`Breakdown.summable_breakdownLegSum_terms`, and it carries the same `[NeZero
d]` binder, which the consumers themselves do not. -/
theorem summable_gridScaleSeries_terms [NeZero d] (m : ℤ) {s : ℝ} (hs : 0 < s)
    {leg : ℕ → TriadicCube d → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hleg0 : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ leg j R)
    (hlegle : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      leg j R ≤ D) :
    Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (leg j)) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    ((Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hs).mul_right D)
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (legScaleAverage_nonneg _ _ _ (hleg0 j))
  · exact mul_le_mul_of_nonneg_left
      (legScaleAverage_le_const (originCube d m) (m - (j : ℤ)) hs hD (hleg0 j)
        (hlegle j) (NeZero.ne d))
      (Real.rpow_nonneg (by norm_num) _)

/-- **The three-term reinjection of the whole `l`-sum.**  The per-scale estimate
of `legScaleAverage_le_three_term`, summed against the printed weights
`3^{-s(m-l)}`.

A: the four `Summable` binders are caller obligations (a divergent `tsum` is
`0` in Lean); the producer of the first three is
`summable_gridScaleSeries_terms`. -/
theorem gridScaleSeries_le_three_term (m : ℤ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hd : d ≠ 0) {good deep wave : ℕ → TriadicCube d → ℝ} {rem : ℕ → ℝ} {c b : ℝ}
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hrem : ∀ j : ℕ, 0 ≤ rem j)
    (hgood : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ good j R)
    (hdeep : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ deep j R)
    (hwave : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ wave j R)
    (hstep : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      good j R ≤ c * deep j R + b * wave j R + rem j)
    (hsumGood : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (good j)))
    (hsumDeep : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (deep j)))
    (hsumWave : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (wave j)))
    (hsumRem : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) * rem j)) :
    gridScaleSeries m s good ≤
      c * gridScaleSeries m s deep + b * gridScaleSeries m s wave +
        ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * rem j := by
  have hw : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) := fun _ =>
    Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ j : ℕ,
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          legScaleAverage (originCube d m) (m - (j : ℤ)) s (good j) ≤
        (c * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              legScaleAverage (originCube d m) (m - (j : ℤ)) s (deep j)) +
            b * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              legScaleAverage (originCube d m) (m - (j : ℤ)) s (wave j))) +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * rem j := by
    intro j
    have hscale := legScaleAverage_le_three_term (originCube d m) (m - (j : ℤ)) hs
      hs1 hd hc hb (hrem j) (hgood j) (hdeep j) (hwave j) (hstep j)
    calc Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          legScaleAverage (originCube d m) (m - (j : ℤ)) s (good j)
        ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (c * legScaleAverage (originCube d m) (m - (j : ℤ)) s (deep j) +
              b * legScaleAverage (originCube d m) (m - (j : ℤ)) s (wave j) +
              rem j) := mul_le_mul_of_nonneg_left hscale (hw j)
      _ = (c * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              legScaleAverage (originCube d m) (m - (j : ℤ)) s (deep j)) +
            b * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              legScaleAverage (originCube d m) (m - (j : ℤ)) s (wave j))) +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * rem j := by ring
  have hsumA := hsumDeep.mul_left c
  have hsumB := hsumWave.mul_left b
  have hsumRHS := (hsumA.add hsumB).add hsumRem
  have hle := hsumGood.tsum_le_tsum hterm hsumRHS
  rw [(hsumA.add hsumB).tsum_add hsumRem, hsumA.tsum_add hsumB,
    hsumDeep.tsum_mul_left c, hsumWave.tsum_mul_left b] at hle
  exact hle

/-! ## The composed good-event aggregation

The remainder lane is routed into the proved remainder collapse at the sibling's
own `switchRemainder` carrier, so that the cross-file seam
(`AggregationRemainder.switchRemainder_eq_of_int_gap`) is the ONLY place where
the `σ`-switch remainder is reshaped. -/

/-- **The good-event aggregation at the printed weights.**  With the per-`(l,z)`
reinjection estimate available at every depth, at a per-cube remainder dominated
by `C_rem ·` the corrected `σ`-switch remainder, the whole printed left-hand
side collapses to

```text
c · (c_{2s} Σ_l 3^{-s(m-l)} (⨍_z deep^{d/s})^{s/d})
  + b · (c_{2s} Σ_l 3^{-s(m-l)} (⨍_z wave^{d/s})^{s/d})
  + 1024 C_rem γ² (h² + s^{-2} + E⁴|log γ|⁴) .
```

The last summand is the fifth term of `e.localization.mathcalE.estimate`; its
`1024` is the proved absolute constant of
`AggregationRemainder.localization_remainder_series_le_of_termwise`, and the
caller's own `C_rem` passes through multiplicatively.

A: the three `Summable` binders, as above.  The remainder lane's summability is
discharged internally. -/
theorem geometricDiscount_mul_gridScaleSeries_le (m : ℤ) {s gam Eval : ℝ} {h : ℕ}
    {c b Crem : ℝ} (hgam : 0 < gam) (hsgam : 8 * gam ≤ s) (hs1 : s ≤ 1)
    (hgh : gam * (h : ℝ) ≤ 1) (hd : d ≠ 0) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hCrem : 0 ≤ Crem) {good deep wave : ℕ → TriadicCube d → ℝ}
    (hgood : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ good j R)
    (hdeep : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ deep j R)
    (hwave : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ wave j R)
    (hstep : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      good j R ≤ c * deep j R + b * wave j R +
        Crem * switchRemainder gam Eval h j)
    (hsumGood : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (good j)))
    (hsumDeep : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (deep j)))
    (hsumWave : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (wave j))) :
    Book.Ch02.geometricDiscount s 2 * gridScaleSeries m s good ≤
      c * (Book.Ch02.geometricDiscount s 2 * gridScaleSeries m s deep) +
        b * (Book.Ch02.geometricDiscount s 2 * gridScaleSeries m s wave) +
        1024 * Crem * gam ^ 2 *
          ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + Eval ^ 4 * |Real.log gam| ^ 4) := by
  have hs : 0 < s := lt_of_lt_of_le (by linarith) hsgam
  have hrem : ∀ j : ℕ, 0 ≤ Crem * switchRemainder gam Eval h j := fun j =>
    mul_nonneg hCrem (switchRemainder_nonneg gam Eval h j)
  have hbase := summable_weighted_switchRemainder (E := Eval) hgam hsgam hs1 hgh
  have hsumRem : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (Crem * switchRemainder gam Eval h j)) := by
    refine (hbase.mul_left Crem).congr fun j => ?_
    ring
  have hseries := gridScaleSeries_le_three_term m hs hs1 hd hc hb hrem hgood hdeep
    hwave hstep hsumGood hsumDeep hsumWave hsumRem
  have hc2 : (0 : ℝ) ≤ Book.Ch02.geometricDiscount s 2 :=
    geometricDiscount_two_nonneg hs.le
  have hT5 := localization_remainder_series_le_of_termwise (E := Eval) (C := Crem)
    (f := fun j : ℕ => Crem * switchRemainder gam Eval h j) hgam hsgam hs1 hgh
    hCrem hrem (fun _ => le_rfl)
  have hmul := mul_le_mul_of_nonneg_left hseries hc2
  nlinarith [hmul, hT5, hc2]

/-- **The consumer entry point of the good lane.**  The composed aggregation with
the manuscript's indicator in place: the per-`(l,z)` estimate is assumed only ON
the good event `𝒬(l,l-h,z)`, and the left-hand side is the printed good part.

Together with `legScaleAverage_indicator_eq` (which puts the indicator back
inside the `d/s`-th power) this is the printed display at the abstract legs;
the assembly supplies the legs, the constants `c`, `b`, `C_rem` and the
per-`(l,z)` estimate. -/
theorem geometricDiscount_mul_gridScaleSeries_good_le {Omega : Type*} (m : ℤ)
    {s gam Eval : ℝ} {h : ℕ} {c b Crem : ℝ} (hgam : 0 < gam) (hsgam : 8 * gam ≤ s)
    (hs1 : s ≤ 1) (hgh : gam * (h : ℝ) ≤ 1) (hd : d ≠ 0) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hCrem : 0 ≤ Crem) {leg deep wave : ℕ → TriadicCube d → ℝ}
    (B : ℕ → TriadicCube d → Set Omega) (omega : Omega)
    (hleg : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ leg j R)
    (hdeep : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ deep j R)
    (hwave : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      0 ≤ wave j R)
    (hstep : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      omega ∈ B j R →
        leg j R ≤ c * deep j R + b * wave j R +
          Crem * switchRemainder gam Eval h j)
    (hsumGood : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => leg j R * (B j R).indicator (fun _ => (1 : ℝ)) omega)))
    (hsumDeep : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (deep j)))
    (hsumWave : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (wave j))) :
    Book.Ch02.geometricDiscount s 2 *
        gridScaleSeries m s
          (fun j R => leg j R * (B j R).indicator (fun _ => (1 : ℝ)) omega) ≤
      c * (Book.Ch02.geometricDiscount s 2 * gridScaleSeries m s deep) +
        b * (Book.Ch02.geometricDiscount s 2 * gridScaleSeries m s wave) +
        1024 * Crem * gam ^ 2 *
          ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + Eval ^ 4 * |Real.log gam| ^ 4) := by
  refine geometricDiscount_mul_gridScaleSeries_le m hgam hsgam hs1 hgh hd hc hb
    hCrem ?_ hdeep hwave ?_ hsumGood hsumDeep hsumWave
  · intro j R hR
    by_cases hmem : omega ∈ B j R
    · rw [Set.indicator_of_mem hmem, mul_one]
      exact hleg j R hR
    · rw [Set.indicator_of_notMem hmem, mul_zero]
  · intro j R hR
    by_cases hmem : omega ∈ B j R
    · rw [Set.indicator_of_mem hmem, mul_one]
      exact hstep j R hR hmem
    · rw [Set.indicator_of_notMem hmem, mul_zero]
      have h1 := mul_nonneg hc (hdeep j R hR)
      have h2 := mul_nonneg hb (hwave j R hR)
      have h3 := mul_nonneg hCrem (switchRemainder_nonneg gam Eval h j)
      linarith

end

end Algsuperdiff.Section3.Provider.Localization
