/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.Breakdown
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementDerivativeBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.TranslatedLargeCubeW1Inf
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# WaveSizes

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the derivative half of the wave-size sum `e.wave.sizes`

Local provider for the second of the three displays that the proof of ABK26's
Proposition `p.multiscale.estimate` reduces to, namely `e.wave.sizes`.

The display bounds the weighted scale sum of the grid power means of the
squared *wave sizes* -- the size of the layers `k_m - k_{l-h}` that the
localization step injects on each cube `z + cu_l` -- by a `Gamma_1` tail at
amplitude `s^{-2} eps^{-C}`.

This is a *provider endpoint only*.  It is not a source node, not a frozen
declaration, and it does not close `p.multiscale.estimate`.

## What this module carries, and what it does NOT

The printed display carries the volume-normalized Sobolev norm `‖k_m -
k_{l-h}‖_{W^{2,∞}(z + cu_l)}`.  **At `p = ∞` that object is a maximum, not a
sum**: at `p = ∞` on a cube of side `3^l` (`|U|^{-1/d}` is `3^{-l}`), iterated
to second order, gives all norms on `z+cu_l` in `L∞`, `3^{2l}‖f‖_{W^{2,∞}} =
max{‖f‖, 3^l‖∇f‖, 3^{2l}‖∇²f‖}`.  This module and its sibling work with the
three-order **sum** `‖f‖ + 3^l‖∇f‖ + 3^{2l}‖∇²f‖`, which *dominates* that
maximum (nonnegative legs) and is at most `3` times it, so every bound proved
against the sum bounds the printed maximum: nothing is over-claimed.  An
earlier version joined the two with `=`; that equation was false and is
withdrawn.  "The three-order object" below means the sum.

This module carries the **derivative half only**, i.e. the last two terms,
under the name `waveGauge`:

`waveGauge l m h z = 3^l Σ_{k ∈ (l-h, m]} ‖∇ j_k‖_{L∞(z+cu_l)}
   + 3^{2l} Σ_{k ∈ (l-h, m]} ‖∇² j_k‖_{L∞(z+cu_l)}`,

built from the proved layer gauges `Stream.localCubeDerivNorm` and
`Stream.localCubeSecondDerivNorm` read at the base point `z` through the frozen
translation action `ShellField.translate z`.

The zeroth-order `L∞` leg, the **extended carrier** `waveGaugeW2` that adds it,
the zeroth-order fidelity statement, the integer cutoff,
and the headline `wave_sizes_bound` all live in the sibling module
`Provider/MultiscaleEstimate/WaveSizesZeroth.lean`, which imports this one.
Every estimate below is therefore a *derivative-half* estimate and is named or
documented as such.

**The zeroth-order term is load-bearing; it is not an omission the source
sanctions.**  An earlier version of this docstring claimed the contrary, on the
ground that the Section 2.4 sensitivity input consumes only `‖∇h‖_{W^{1,∞}}`.
That claim was false and is withdrawn (and the adjudication recorded with it).
The frozen remainder of `Frozen/Section24/ResponseJSensitivity.lean` is

`C δ⁻¹ (vecNormSq p * h.w1Infinity ^ 2 * λ⁻¹
        + |vecDot p q| * h.gradientW1Infinity ^ 2 * λ⁻¹ ^ 2)`,

and `UnitCubeSkewW2Infinity.w1Infinity`
(`Frozen/Section24/UnitCubeSkewW2Infinity/W1Infinity.lean`) is
`max{‖∇h‖_{L∞(□₀)}, ‖h‖_{L∞(□₀)}}`: it *contains* the zeroth-order `L∞` term,
at the coefficient `vecNormSq p`, which at the wave call site (`p =
shom_{l-h}^{-1/2} e`) is `|shom_{l-h}^{-1/2}e|² > 0`.  That remainder is
consumed verbatim at `Provider/BadEvents/GoodLocalEvents.lean`
(`responseJ_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer`).  Only
`gradientW1Infinity = max{‖∇²h‖_{L∞}, ‖∇h‖_{L∞}}` is derivative-only, and it is
the sensitivity *gate*, not the remainder.  The printed `e.J.sensitivity.apppp`
merges both remainders into the single `3^{4l}‖·‖²_{W^{2,∞}}` object, which is
exactly why the wave display is stated at the full `W^{2,∞}` norm.

## Main definitions

* `layerWeight`: the observation-scale reweighting `max{3^{l-k}, 3^{2(l-k)}}`.
* `waveGauge`: the scale-`l` normalized *derivative* gauge of the missing
  layers on a translated cube (the derivative half of the printed norm).
* `waveAmp`, `waveGridConst`: the constants, all explicit.

## Main results

* `three_rpow_split`: the printed exponent split `½s(m-l) ≥ ¼s(m-l) + 2γ(m-l)`.
  Reusable development arithmetic, together with
  `half_le_one_sub_three_rpow_neg` (the geometric-gap bound) and
  `isBigOWith_gammaSigma_of_eq_zero` (the empty-range degenerate case).
* `isBigOWith_gammaSigma_waveGauge`: the per-cube `Gamma_2` estimate, uniform in
  the base point and *free of the scale gap* `m - l`.
* `measurable_waveGauge`: the measurability interface of the carrier.

## The grid/lattice identification, asserted not proved

The printed display sums over the lattice points `z ∈ 3^l Z^d ∩ cu_m` and reads
each summand on `z + cu_l`.  This file realizes that index set as the finite
family of triadic descendants `descendantsAtScale (originCube d m) l`, with
`z:= cubeCenter R` for `R` a descendant.  This is the **development
convention** inherited from the docstring of `Localization.legScaleAverage`
(`Provider/Localization/Breakdown.lean`), where the same identification is made
for `e.mathcal.E.breakdown`; it is *asserted*, not proved, and no declaration
in this file depends on it being a bijection.

```
theorem cubeCenter_injOn_descendantsAtScale (Q : TriadicCube d) (k : ℤ) :
    Set.InjOn cubeCenter ↑(descendantsAtScale Q k)

theorem cubeCenter_image_descendantsAtScale_eq_lattice (Q : TriadicCube d)
    {k : ℤ} (hk : k ≤ Q.scale) :
    (fun R => cubeCenter R) '' ↑(descendantsAtScale Q k)
      = {z : Vec d | (∀ i, ∃ p : ℤ, z i = (3 : ℝ) ^ k * (p : ℝ))
          ∧ z ∈ cubeSet Q}
```

Until they are proved the identification is a *reading* of the display, and any
downstream statement that needs the printed lattice literally must supply them.
What *is* proved here is that `cubeCenter R = triadicCubeShift R` holds by
definitional unfolding, so the cube `R` and the translated cube
`cubeCenter R + cu_{R.scale}` are the same set
(`openCubeSet_eq_translateSet_originCube_of_triadicCube`); that identity, and
not the lattice enumeration, is what the estimates below use.

## Deviations from the printed proof, all disclosed

1. **Per-layer, not summed, stream input.**  The printed proof applies the
   *summed* display `e.W.1.inf.bound` as a black box.  That display is stated
   at the *own-scale* normalization `3^k, 3^{2k}`, while the wave gauge needs
   the *observation-scale* normalization `3^l, 3^{2l}`; converting costs the
   factor `3^{2(l-k)} ≤ 3^{2h}` on every layer, including the layers `k > l`
   where the true weight `3^{l-k}` is a *decay*.  Routed that way the per-scale
   amplitude grows like `(m-l)^2` (through `min{γ^{-1}, m-l+h}^2`) and the
   `l`-sum proves at `s^{-3}`, one power worse than the printed `s^{-2}`; this
   is finding (3).  This file therefore applies the *per-layer* proved estimate
   `isBigOWith_gammaSigma_largeCubeDerivGauge_translate` with the honest weight
   `max{3^{l-k}, 3^{2(l-k)}}`.  The layers `k > l` then sum geometrically to a
   dimensional constant, the per-scale amplitude is *independent of the scale
   gap* `m-l`, and the `l`-sum is `s^{-1} ≤ s^{-2}`.
2. **The comparator for the summed input is the translated summed gauge, not the
   frozen display.**  The comparator of the carrier at a base point is
   `Σ_{k ∈ (l-h,m]} largeCubeDerivGauge l k (translate z (ω k))`, whose `Γ₂`
   estimate is `Stream.isBigOWith_gammaSigma_largeCubeDerivGaugeSum_translate`
   (`Provider/Stream/TranslatedLargeCubeW1Inf.lean`).  The frozen
   `Frozen.Section3.stream_derivative_sum_bound` is **untranslated** (no base
   point, binder `n ≤ min m l`), is **not imported by this module**, and its own
   internal input is the untranslated
   `Stream.isBigOWith_gammaSigma_largeCubeDerivGauge`
   (`Provider/Stream/LargeCubeW1Inf.lean`).  The honest comparator for the
   printed route at a base point is therefore the translated summed statement,
   and that is what is cited.  An earlier version of this docstring named the
   frozen declaration instead; that naming was inaccurate and is withdrawn.
3. **Grid power mean by the maximum lemma.**  The printed proof passes the
   per-cube `Gamma_1` bound through the power mean `(⨍_z (·)^{d/s})^{s/d}`
   silently.  Here the passage is paid honestly: by
   `Localization.legScaleAverage_le_const` the power mean is at most the grid
   maximum, and the grid maximum of `Gamma_2` variables at a common amplitude
   costs the factor `(3 max{1, log N})^{1/2}` of the proved maximum lemma
   (ABK26 `l.maximums.Gamma.s`, in the strengthened `N = 1`-inclusive form
   disclosed above), i.e. a factor linear in `m-l` after squaring.
4. **The `l`-sum is stated at `s^{-1}`, the printed form at `s^{-2}`.**  On the
   derivative half the route above is strictly sharper than the printed
   amplitude; the printed form follows because `s ≤ 1`.  The *full* carrier
   does not enjoy this: the zeroth-order leg has a genuinely quadratic base and
   proves at exactly the printed `s^{-2}` (`WaveSizesZeroth.lean`).

## References

* ABK26, `e.wave.sizes`.
* ABK26, `e.J.sensitivity.apppp` (the consumer shape).
* ABK26, `e.W.1.inf.bound`.
* ABK26, `l.Gamma.sigma.triangle`.
* ABK26, `l.maximums.Gamma.s`.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.IndependentSums
open _root_.Algsuperdiff.Frozen.Assumptions
open _root_.Algsuperdiff.Section3.Cutoff
open _root_.Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## Elementary real arithmetic

All of this section is abstract-real: no model, no measure, no cube. -/

/-- `log 3 > 1`. -/
private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  have h := Real.exp_one_lt_d9
  linarith

/-- `√x ≤ x` above one. -/
private theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have h : Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq (by linarith)] at h

/-- For `0 < a ≤ 1` the geometric gap `1 - 3^{-a}` is at least `a / 2`.  Reusable
development arithmetic; also consumed by `WaveSizesZeroth.lean`. -/
theorem half_le_one_sub_three_rpow_neg {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a / 2 ≤ 1 - (3 : ℝ) ^ (-a) := by
  have hlog : (1 : ℝ) < Real.log 3 := one_lt_log_three
  have hexp : (3 : ℝ) ^ (-a) = Real.exp (-a * Real.log 3) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hmono : Real.exp (-a * Real.log 3) ≤ Real.exp (-a) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hlin : Real.exp (-a) ≤ (1 + a)⁻¹ := by
    have h1 : (0 : ℝ) < 1 + a := by linarith
    have h2 : (1 : ℝ) + a ≤ Real.exp a := by
      have := Real.add_one_le_exp a
      linarith
    have h3 : Real.exp (-a) = (Real.exp a)⁻¹ := by rw [Real.exp_neg]
    rw [h3]
    exact inv_anti₀ h1 h2
  have hkey : (1 + a)⁻¹ ≤ 1 - a / 2 := by
    have h1 : (0 : ℝ) < 1 + a := by linarith
    rw [inv_le_iff_one_le_mul₀ h1]
    nlinarith
  rw [hexp]
  linarith

/-- **The exponent split of the printed proof**: since `s ≥ 8γ`, `3^{2γ j} 3^{-s j}
≤ 3^{-(3/4) s j}`, so a quarter of the geometric weight absorbs the `γ`-drift. -/
theorem three_rpow_split {s gamma : ℝ} (hsg : 8 * gamma ≤ s) (j : ℕ) :
    (3 : ℝ) ^ (-s * (j : ℝ)) * (3 : ℝ) ^ (2 * gamma * (j : ℝ)) ≤
      (3 : ℝ) ^ (-(3 / 4 * s) * (j : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

/-- The integer power of `3` read as a real power. -/
private theorem three_zpow_eq_rpow (a : ℤ) : (3 : ℝ) ^ a = (3 : ℝ) ^ ((a : ℝ)) :=
  (Real.rpow_intCast 3 a).symm

/-! ## The wave carrier -/

/-- The observation-scale weight that converts the own-scale layer gauge
`3^k‖∇j_k‖_{L∞} + 3^{2k}‖∇²j_k‖_{L∞}` into the scale-`l` normalized gauge
`3^l‖∇j_k‖_{L∞} + 3^{2l}‖∇²j_k‖_{L∞}`.  It is a *decay* above the observation
scale (`k > l`) and a *loss* below it (`k ≤ l`). -/
def layerWeight (l k : ℤ) : ℝ := max ((3 : ℝ) ^ (l - k)) ((3 : ℝ) ^ (2 * (l - k)))

theorem layerWeight_pos (l k : ℤ) : 0 < layerWeight l k :=
  lt_of_lt_of_le (zpow_pos (by norm_num : (0 : ℝ) < 3) (l - k)) (le_max_left _ _)

theorem layerWeight_nonneg (l k : ℤ) : 0 ≤ layerWeight l k := (layerWeight_pos l k).le

/-- **The wave carrier.**  The scale-`l` normalized derivative gauge of the
missing layers `k_m - k_{l-h}` on the translated cube `z + cu_l`:
`3^l Σ_{k ∈ (l-h,m]} ‖∇ j_k‖_{L∞(z+cu_l)}
   + 3^{2l} Σ_{k ∈ (l-h,m]} ‖∇² j_k‖_{L∞(z+cu_l)}`.
By the triangle inequality this dominates the derivative part of
`3^{2l}‖k_m - k_{l-h}‖_{W^{2,∞}(z+cu_l)}`; see the module docstring for the
carrier adjudication. -/
def waveGauge (l m : ℤ) (h : ℕ) (z : Vec d) (omega : ShellSeq d) : ℝ :=
  ∑ k ∈ Finset.Ioc (l - (h : ℤ)) m,
    ((3 : ℝ) ^ l * localCubeDerivNorm l (ShellField.translate z (omega k)) +
      (3 : ℝ) ^ (2 * l) * localCubeSecondDerivNorm l (ShellField.translate z (omega k)))

theorem waveGauge_nonneg (l m : ℤ) (h : ℕ) (z : Vec d) (omega : ShellSeq d) :
    0 ≤ waveGauge l m h z omega := by
  refine Finset.sum_nonneg fun k _ => add_nonneg ?_ ?_
  · exact mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) l).le
      (localCubeDerivNorm_nonneg l _)
  · exact mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) (2 * l)).le
      (localCubeSecondDerivNorm_nonneg l _)

theorem measurable_waveGauge (l m : ℤ) (h : ℕ) (z : Vec d) :
    Measurable (fun omega : ShellSeq d => waveGauge l m h z omega) := by
  refine Finset.measurable_sum _ fun k _ => Measurable.add ?_ ?_
  · exact measurable_const.mul
      (((measurable_localCubeDerivNorm l).comp
        (ShellField.measurable_translate z)).comp (measurable_pi_apply k))
  · exact measurable_const.mul
      (((measurable_localCubeSecondDerivNorm l).comp
        (ShellField.measurable_translate z)).comp (measurable_pi_apply k))

/-- Each summand of the wave carrier is the own-scale layer gauge of
`e.W.1.inf.bound` reweighted by `layerWeight`. -/
theorem waveGauge_term_le (l k : ℤ) (j : ShellField d) :
    (3 : ℝ) ^ l * localCubeDerivNorm l j + (3 : ℝ) ^ (2 * l) * localCubeSecondDerivNorm l j ≤
      layerWeight l k * largeCubeDerivGauge l k j := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hD1 : 0 ≤ localCubeDerivNorm l j := localCubeDerivNorm_nonneg l j
  have hD2 : 0 ≤ localCubeSecondDerivNorm l j := localCubeSecondDerivNorm_nonneg l j
  have h1 : (3 : ℝ) ^ l ≤ layerWeight l k * (3 : ℝ) ^ k := by
    have hsplit : (3 : ℝ) ^ l = (3 : ℝ) ^ (l - k) * (3 : ℝ) ^ k := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring_nf
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_pos h3 k).le
  have h2 : (3 : ℝ) ^ (2 * l) ≤ layerWeight l k * (3 : ℝ) ^ (2 * k) := by
    have hsplit : (3 : ℝ) ^ (2 * l) = (3 : ℝ) ^ (2 * (l - k)) * (3 : ℝ) ^ (2 * k) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring_nf
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_pos h3 (2 * k)).le
  have hgauge : layerWeight l k * largeCubeDerivGauge l k j =
      layerWeight l k * (3 : ℝ) ^ k * localCubeDerivNorm l j +
        layerWeight l k * (3 : ℝ) ^ (2 * k) * localCubeSecondDerivNorm l j := by
    rw [largeCubeDerivGauge]
    ring
  rw [hgauge]
  exact add_le_add (mul_le_mul_of_nonneg_right h1 hD1)
    (mul_le_mul_of_nonneg_right h2 hD2)

/-! ## The per-cube `Gamma_2` estimate -/

/-- The per-layer `Γ₂` amplitude of a wave-carrier summand: the proved per-layer
estimate `isBigOWith_gammaSigma_largeCubeDerivGauge_translate` at `n = k-1`,
reweighted to the observation scale. -/
def layerAmp (M : ABKModel d) (l k : ℤ) : ℝ :=
  layerWeight l k *
    (shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (k : ℝ)))

private theorem layerAmp_pos (M : ABKModel d) (l k : ℤ) : 0 < layerAmp M l k := by
  have h1 : (0 : ℝ) < layerWeight l k := layerWeight_pos l k
  have h2 : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
  have h3 : (1 : ℝ) ≤ Real.sqrt (max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ))) := by
    have hle := Real.sqrt_le_sqrt (le_max_left (1 : ℝ) ((l : ℝ) - ((k - 1 : ℤ) : ℝ)))
    rwa [Real.sqrt_one] at hle
  have h4 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h5 : (0 : ℝ) < Real.sqrt (max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ))) := by linarith
  rw [layerAmp]
  positivity

/-- The layer amplitudes below the observation scale: at most `h` terms, each
at most `3^{2h} C h 3^{γl}`. -/
private theorem sum_layerAmp_low_le (M : ABKModel d) (l : ℤ) (h : ℕ) :
    ∑ k ∈ Finset.Ioc (l - (h : ℤ)) l, layerAmp M l k ≤
      shellW1InfConst d * ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h)) *
        (3 : ℝ) ^ (M.gamma * (l : ℝ)) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hC : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
  have hgl : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hbound : ∀ k ∈ Finset.Ioc (l - (h : ℤ)) l,
      layerAmp M l k ≤ (3 : ℝ) ^ (2 * h) *
        (shellW1InfConst d * (h : ℝ) * (3 : ℝ) ^ (M.gamma * (l : ℝ))) := by
    intro k hk
    obtain ⟨hklow, hkhigh⟩ := Finset.mem_Ioc.mp hk
    have hh1 : 1 ≤ h := by omega
    have hweight : layerWeight l k ≤ (3 : ℝ) ^ (2 * h) := by
      have hone : (1 : ℝ) ≤ 3 := by norm_num
      have hA : (3 : ℝ) ^ (l - k) ≤ (3 : ℝ) ^ ((2 * h : ℕ) : ℤ) :=
        zpow_le_zpow_right₀ hone (by omega)
      have hB : (3 : ℝ) ^ (2 * (l - k)) ≤ (3 : ℝ) ^ ((2 * h : ℕ) : ℤ) :=
        zpow_le_zpow_right₀ hone (by omega)
      rw [zpow_natCast] at hA hB
      exact max_le hA hB
    have hmax1 : (1 : ℝ) ≤ max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ)) := le_max_left _ _
    have hmaxh : max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ)) ≤ (h : ℝ) := by
      refine max_le ?_ ?_
      · exact_mod_cast Nat.one_le_cast.2 hh1
      · have hz : (l : ℤ) - (k - 1) ≤ (h : ℤ) := by omega
        have hzr : ((l : ℤ) : ℝ) - (((k - 1 : ℤ)) : ℝ) ≤ ((h : ℕ) : ℝ) := by
          exact_mod_cast hz
        exact hzr
    have hsqrt : Real.sqrt (max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ))) ≤ (h : ℝ) :=
      (sqrt_le_self_of_one_le hmax1).trans hmaxh
    have hrpow : (3 : ℝ) ^ (M.gamma * (k : ℝ)) ≤ (3 : ℝ) ^ (M.gamma * (l : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hkl : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkhigh
      nlinarith
    have hinner : shellW1InfConst d *
        Real.sqrt (max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ))) * (3 : ℝ) ^ (M.gamma * (k : ℝ)) ≤
        shellW1InfConst d * (h : ℝ) * (3 : ℝ) ^ (M.gamma * (l : ℝ)) := by
      have hrp0 : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (k : ℝ)) := (Real.rpow_pos_of_pos
        (by norm_num) _).le
      have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
      calc shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (k : ℝ))
          ≤ shellW1InfConst d * (h : ℝ) * (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt hC.le) hrp0
        _ ≤ shellW1InfConst d * (h : ℝ) * (3 : ℝ) ^ (M.gamma * (l : ℝ)) :=
            mul_le_mul_of_nonneg_left hrpow (by positivity)
    have hinner0 : (0 : ℝ) ≤ shellW1InfConst d *
        Real.sqrt (max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ))) * (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
      have hsq0 : (0 : ℝ) ≤ Real.sqrt (max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ))) :=
        Real.sqrt_nonneg _
      have hrp0 : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (k : ℝ)) := (Real.rpow_pos_of_pos
        (by norm_num) _).le
      positivity
    rw [layerAmp]
    exact mul_le_mul hweight hinner hinner0 (by positivity)
  have hcard : ((Finset.Ioc (l - (h : ℤ)) l).card : ℝ) = (h : ℝ) := by
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (Int.card_Ioc_of_le (l - (h : ℤ)) l (by omega))
    push_cast at hz
    linarith [hz]
  have hsum := Finset.sum_le_card_nsmul (Finset.Ioc (l - (h : ℤ)) l)
    (fun k => layerAmp M l k)
    ((3 : ℝ) ^ (2 * h) * (shellW1InfConst d * (h : ℝ) * (3 : ℝ) ^ (M.gamma * (l : ℝ))))
    hbound
  rw [nsmul_eq_mul, hcard] at hsum
  refine hsum.trans (le_of_eq ?_)
  ring

/-- The layer amplitudes above the observation scale sum geometrically: the
weight `3^{l-k}` decays, so the total is a dimensional constant times
`3^{γl}`, with no dependence on the scale gap `m - l`. -/
private theorem sum_layerAmp_high_le (M : ABKModel d) {l m : ℤ} (hlm : l ≤ m) :
    ∑ k ∈ Finset.Ioc l m, layerAmp M l k ≤
      shellW1InfConst d * (3 : ℝ) ^ (M.gamma * (l : ℝ)) := by
  have hrewrite : ∀ k ∈ Finset.Ioc l m,
      layerAmp M l k =
        shellW1InfConst d * (3 : ℝ) ^ ((l : ℝ)) *
          Real.rpow 3 ((M.gamma - 1) * (k : ℝ)) := by
    intro k hk
    obtain ⟨hklow, _⟩ := Finset.mem_Ioc.mp hk
    have hweight : layerWeight l k = (3 : ℝ) ^ (l - k) := by
      refine max_eq_left ?_
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
    have hmax : max 1 ((l : ℝ) - ((k - 1 : ℤ) : ℝ)) = 1 := by
      refine max_eq_left ?_
      have hkl : (l : ℤ) - (k - 1) ≤ 0 := by omega
      have hklr : ((l : ℤ) : ℝ) - (((k - 1 : ℤ)) : ℝ) ≤ 0 := by exact_mod_cast hkl
      linarith
    have hL : (3 : ℝ) ^ (((l - k : ℤ) : ℝ)) * (3 : ℝ) ^ (M.gamma * (k : ℝ)) =
        (3 : ℝ) ^ ((l : ℝ) + (M.gamma - 1) * (k : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      push_cast
      ring_nf
    have hR : (3 : ℝ) ^ ((l : ℝ)) * (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ)) =
        (3 : ℝ) ^ ((l : ℝ) + (M.gamma - 1) * (k : ℝ)) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    rw [layerAmp, hweight, hmax, Real.sqrt_one, three_zpow_eq_rpow (l - k)]
    change (3 : ℝ) ^ (((l - k : ℤ) : ℝ)) *
        (shellW1InfConst d * 1 * (3 : ℝ) ^ (M.gamma * (k : ℝ))) =
      shellW1InfConst d * (3 : ℝ) ^ ((l : ℝ)) * (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ))
    calc (3 : ℝ) ^ (((l - k : ℤ) : ℝ)) *
          (shellW1InfConst d * 1 * (3 : ℝ) ^ (M.gamma * (k : ℝ)))
        = shellW1InfConst d *
            ((3 : ℝ) ^ (((l - k : ℤ) : ℝ)) * (3 : ℝ) ^ (M.gamma * (k : ℝ))) := by ring
      _ = shellW1InfConst d * (3 : ℝ) ^ ((l : ℝ) + (M.gamma - 1) * (k : ℝ)) := by rw [hL]
      _ = shellW1InfConst d *
            ((3 : ℝ) ^ ((l : ℝ)) * (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ))) := by rw [hR]
      _ = shellW1InfConst d * (3 : ℝ) ^ ((l : ℝ)) *
            (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ)) := by ring
  rw [Finset.sum_congr rfl hrewrite, ← Finset.mul_sum]
  have hgeo := sum_Ioc_rpow_gamma_sub_one_le (gamma := M.gamma)
    M.shellPrefix.gamma_le_quarter (n := l) (m := m) hlm
  have hCpos : (0 : ℝ) ≤ shellW1InfConst d * (3 : ℝ) ^ ((l : ℝ)) := by
    have h1 : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
    have h2 : (0 : ℝ) < (3 : ℝ) ^ ((l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine (mul_le_mul_of_nonneg_left hgeo hCpos).trans (le_of_eq ?_)
  change shellW1InfConst d * (3 : ℝ) ^ ((l : ℝ)) * (3 : ℝ) ^ ((M.gamma - 1) * (l : ℝ)) =
    shellW1InfConst d * (3 : ℝ) ^ (M.gamma * (l : ℝ))
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring_nf

/-- The total per-layer amplitude of the wave carrier. -/
private theorem sum_layerAmp_le (M : ABKModel d) {l m : ℤ} (hlm : l ≤ m) (h : ℕ) :
    ∑ k ∈ Finset.Ioc (l - (h : ℤ)) m, layerAmp M l k ≤
      shellW1InfConst d * ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1) *
        (3 : ℝ) ^ (M.gamma * (l : ℝ)) := by
  have hdisj : Disjoint (Finset.Ioc (l - (h : ℤ)) l) (Finset.Ioc l m) := by
    refine Finset.disjoint_left.2 fun k hk hk' => ?_
    have h1 := (Finset.mem_Ioc.mp hk).2
    have h2 := (Finset.mem_Ioc.mp hk').1
    omega
  have hunion : Finset.Ioc (l - (h : ℤ)) l ∪ Finset.Ioc l m =
      Finset.Ioc (l - (h : ℤ)) m := Finset.Ioc_union_Ioc_eq_Ioc (by omega) hlm
  rw [← hunion, Finset.sum_union hdisj]
  have hlow := sum_layerAmp_low_le M l h
  have hhigh := sum_layerAmp_high_le M hlm
  have hcomb : shellW1InfConst d * ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h)) *
        (3 : ℝ) ^ (M.gamma * (l : ℝ)) + shellW1InfConst d * (3 : ℝ) ^ (M.gamma * (l : ℝ)) =
      shellW1InfConst d * ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1) *
        (3 : ℝ) ^ (M.gamma * (l : ℝ)) := by ring
  linarith

/-- The identically zero random variable satisfies every nonnegative
weak-Orlicz upper bound.  Used for the empty layer range `h = 0`, `l = m`, here
and in `WaveSizesZeroth.lean`. -/
theorem isBigOWith_gammaSigma_of_eq_zero {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {X : Omega → ℝ} {sigma A : ℝ}
    (hA : 0 ≤ A) (hX : ∀ omega, X omega = 0) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) X A := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hAt : (0 : ℝ) ≤ A * t := mul_nonneg hA ht0
  have hset : IndependentSums.upperTailEvent X (A * t) = (∅ : Set Omega) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, hX omega,
      Set.mem_empty_iff_false, iff_false, not_lt]
    exact hAt
  rw [hset, measureReal_empty]
  have h1 : (1 : ℝ) ≤ IndependentSums.gammaSigma sigma t :=
    IndependentSums.one_le_gammaSigma ht0
  exact inv_nonneg.2 (by linarith)

/-- The cutoff-dependent amplitude of the per-cube wave estimate.  It is
independent of the scale `l` and of the scale gap `m - l`. -/
def waveAmp (d : ℕ) (h : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    (shellW1InfConst d * ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1))

theorem waveAmp_pos (d h : ℕ) : 0 < waveAmp d h := by
  have h1 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h2 : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (2 * h) := by positivity
  have h4 : (0 : ℝ) ≤ (h : ℝ) ^ 2 := by positivity
  rw [waveAmp]
  have h5 : (0 : ℝ) < (h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1 := by nlinarith
  positivity

theorem waveAmp_nonneg (d h : ℕ) : 0 ≤ waveAmp d h := (waveAmp_pos d h).le

/-- **The per-cube `Γ₂` estimate for the wave carrier.**  On every translated
cube `z + cu_l` with `l ≤ m` and every integer cutoff `h`,

`3^l‖∇(k_m-k_{l-h})‖_{L∞(z+cu_l)} + 3^{2l}‖∇²(k_m-k_{l-h})‖_{L∞(z+cu_l)}
   ≤ O_{Γ₂}(C(d) (h² 3^{2h} + 1) 3^{γl})`,

uniformly in the base point `z` and *with no dependence on the scale gap
`m - l`*.  This is ABK26's `e.W.1.inf.bound` input, applied per layer at the
observation-scale normalization. -/
theorem isBigOWith_gammaSigma_waveGauge (M : ABKModel d) {l m : ℤ} (hlm : l ≤ m)
    (h : ℕ) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => waveGauge l m h z omega)
      (waveAmp d h * (3 : ℝ) ^ (M.gamma * (l : ℝ))) := by
  have hgl : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hamp : (0 : ℝ) ≤ waveAmp d h * (3 : ℝ) ^ (M.gamma * (l : ℝ)) :=
    mul_nonneg (waveAmp_nonneg d h) hgl.le
  rcases Finset.eq_empty_or_nonempty (Finset.Ioc (l - (h : ℤ)) m) with hempty | hne
  · refine isBigOWith_gammaSigma_of_eq_zero hamp ?_
    intro omega
    rw [waveGauge, hempty, Finset.sum_empty]
  · have hnonneg : ∀ (k : ℤ) (omega : ShellSeq d),
        0 ≤ (3 : ℝ) ^ l * localCubeDerivNorm l (ShellField.translate z (omega k)) +
          (3 : ℝ) ^ (2 * l) *
            localCubeSecondDerivNorm l (ShellField.translate z (omega k)) := by
      intro k omega
      refine add_nonneg (mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) l).le
        (localCubeDerivNorm_nonneg l _)) ?_
      exact mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) (2 * l)).le
        (localCubeSecondDerivNorm_nonneg l _)
    have hmeas : ∀ k : ℤ, Measurable (fun omega : ShellSeq d =>
        (3 : ℝ) ^ l * localCubeDerivNorm l (ShellField.translate z (omega k)) +
          (3 : ℝ) ^ (2 * l) *
            localCubeSecondDerivNorm l (ShellField.translate z (omega k))) := by
      intro k
      refine Measurable.add ?_ ?_
      · exact measurable_const.mul
          (((measurable_localCubeDerivNorm l).comp
            (ShellField.measurable_translate z)).comp (measurable_pi_apply k))
      · exact measurable_const.mul
          (((measurable_localCubeSecondDerivNorm l).comp
            (ShellField.measurable_translate z)).comp (measurable_pi_apply k))
    have hbigO : ∀ k ∈ Finset.Ioc (l - (h : ℤ)) m,
        IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d =>
            (3 : ℝ) ^ l * localCubeDerivNorm l (ShellField.translate z (omega k)) +
              (3 : ℝ) ^ (2 * l) *
                localCubeSecondDerivNorm l (ShellField.translate z (omega k)))
          (layerAmp M l k) := by
      intro k _
      have hlayer := isBigOWith_gammaSigma_largeCubeDerivGauge_translate M
        (l := l) (n := k - 1) (k := k) (by omega) z
      have hmul := hlayer.const_mul (layerWeight_nonneg l k)
      have hterm : IndependentSums.IsBigOWith M.P.toMeasure
          (IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d =>
            (3 : ℝ) ^ l * localCubeDerivNorm l (ShellField.translate z (omega k)) +
              (3 : ℝ) ^ (2 * l) *
                localCubeSecondDerivNorm l (ShellField.translate z (omega k)))
          (layerAmp M l k) :=
        hmul.of_le fun omega => waveGauge_term_le l k (ShellField.translate z (omega k))
      exact (Orlicz.isBigOWith_iff_isBigO_of_nonneg (hnonneg k)).1 hterm
    have hfinite := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (Finset.Ioc (l - (h : ℤ)) m)
      (X := fun k omega =>
        (3 : ℝ) ^ l * localCubeDerivNorm l (ShellField.translate z (omega k)) +
          (3 : ℝ) ^ (2 * l) *
            localCubeSecondDerivNorm l (ShellField.translate z (omega k)))
      (a := fun k : ℤ => layerAmp M l k) (σ := 2) (by norm_num) hne
      (fun k _ => layerAmp_pos M l k) hbigO (fun k _ => hmeas k)
    have hwith : IndependentSums.IsBigOWith M.P.toMeasure
        (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d => waveGauge l m h z omega)
        (IndependentSums.gammaTriangleConst 2 *
          ∑ k ∈ Finset.Ioc (l - (h : ℤ)) m, layerAmp M l k) :=
      (Orlicz.isBigOWith_iff_isBigO_of_nonneg
        (fun omega => waveGauge_nonneg l m h z omega)).2 hfinite
    refine hwith.mono_scale ?_
    have hsum := sum_layerAmp_le M hlm h
    have htri : (0 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos.le
    calc IndependentSums.gammaTriangleConst 2 *
          ∑ k ∈ Finset.Ioc (l - (h : ℤ)) m, layerAmp M l k
        ≤ IndependentSums.gammaTriangleConst 2 *
            (shellW1InfConst d * ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1) *
              (3 : ℝ) ^ (M.gamma * (l : ℝ))) := mul_le_mul_of_nonneg_left hsum htri
      _ = waveAmp d h * (3 : ℝ) ^ (M.gamma * (l : ℝ)) := by rw [waveAmp]; ring

/-! ## The grid maximum -/

/-- The scale-`m-j` grid of `cu_m` is nonempty. -/
theorem waveGrid_nonempty (m : ℤ) (j : ℕ) :
    (descendantsAtScale (originCube d m) (m - (j : ℤ))).Nonempty :=
  descendantsAtScale_nonempty (originCube d m) (by change m - (j : ℤ) ≤ m; omega)

/-- The dimensional constant of the grid maximum, from ABK26's
`l.maximums.Gamma.s`. -/
def waveGridConst (d : ℕ) : ℝ := 3 * (1 + (d : ℝ) * Real.log 3)

theorem waveGridConst_pos (d : ℕ) : 0 < waveGridConst d := by
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [waveGridConst]
  positivity

/-- The grid-maximum penalty of `l.maximums.Gamma.s` is at most `waveGridConst d *
(1 + j)`.  Stated in the `N = 1`-inclusive form `3 max{1, log N}` of the proved
maximum lemma; see the disclosure of the `l.maximums.Gamma.s` strengthening in
the module docstring. -/
theorem three_mul_max_one_log_card_waveGrid_le (m : ℤ) (j : ℕ) :
    3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ)) ≤
      waveGridConst d * (1 + (j : ℝ)) := by
  have hk : m - (j : ℤ) ≤ (originCube d m).scale := by change m - (j : ℤ) ≤ m; omega
  have hcard := ErrorComparison.card_descendantsAtScale_eq_rpow (originCube d m) hk
  have hdepth : Int.toNat ((originCube d m).scale - (m - (j : ℤ))) = j := by
    have hred : (originCube d m).scale - (m - (j : ℤ)) = (j : ℤ) := by
      change m - (m - (j : ℤ)) = (j : ℤ)
      ring
    rw [hred, Int.toNat_natCast]
  rw [hdepth] at hcard
  have hlog : Real.log
      (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ) =
      (d : ℝ) * (j : ℝ) * Real.log 3 := by
    rw [hcard]
    change Real.log ((3 : ℝ) ^ ((d : ℝ) * (j : ℝ))) = (d : ℝ) * (j : ℝ) * Real.log 3
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hdl : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := mul_nonneg hd hlog3.le
  rw [hlog]
  have hmax : max 1 ((d : ℝ) * (j : ℝ) * Real.log 3) ≤
      (1 + (d : ℝ) * Real.log 3) * (1 + (j : ℝ)) := by
    refine max_le ?_ ?_
    · nlinarith [mul_nonneg hdl hj]
    · nlinarith [mul_nonneg hdl hj]
  rw [waveGridConst]
  nlinarith

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
