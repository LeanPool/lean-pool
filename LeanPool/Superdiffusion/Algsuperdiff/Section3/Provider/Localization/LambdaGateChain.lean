/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.SensitivityBridges
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ShomContinuity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.SwitchNormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.LambdaSensitivityTwin
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpGlobalFrame
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.WaveSizesZeroth

/-!
# LambdaGateChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the `lambda`-gate chain, the wave bridge and the injection prefactor

ABK26: the good-event coefficient-switch chain of `l.localization.mathcalE`, and
the injection display `e.J.sensitivity.apppp`.

## 1. The `lambda`-gate chain

The printed chain is

```
|s_{m,*}^{-1}(z+cu_l)| 1_Q <= lambda_{1/8,2}^{-1}(z+cu_l; a_m) 1_Q
                           <= 2 lambda_{1/8,2}^{-1}(z+cu_l; a_{l-h}) 1_Q
                           <= C shom_{l-h}^{-1} ,
```

with `Q = Q(l,l-h,z)` the good local event.  This module produces the composed
last two steps at an explicit dimension-only-times-`Ccg` level:

```
shom_{l-h} lambda_{1/8,2}^{-1}(z+cu_l; a_m) <= 48 Ccg ,   almost surely on Q .
```

Constant accounting, term by term (each factor is proved separately below):

* the **middle** step contributes `2`
  (`inv_lambdaSq_le_two_mul_inv_lambdaSq_of_mem_goodLocalEvent_ae`): the proved
  `Multiscale.lambdaSq_inv_le_of_mem_goodLocalEvent_ae`
  (`Provider/Multiscale/LambdaSensitivityTwin.lean`) already states the frozen
  `lambda`-sensitivity switch on the good event **at the manuscript's own
  carrier** `lambda_{s,q}(z+cu_l; a_L)`, with the explicit leading factor `1 +
  C_lam ||grad(k_m - k_{l-h})||_{W1inf} lambda_{3/8,2}^{-1}`; the good event's
  own sensitivity clause -- in the proved discharged form
  `BadEvents.gradientW1Infinity_incrementUnitCube₂_le_lambdaGate_ae` -- bounds
  that second summand by `1`.  So the printed `2` is exact, not an
  over-estimate.  Only that collapse is new here; the carrier work is consumed,
  not redone;
* the good event's **ellipticity clause** contributes `2 Ccg`
  (`inv_lambdaSq_le_of_mem_goodLocalEvent_ae`): `goodLocalThreshold` is
  `(1/2) Ccg^{-1} 3^{-(1/2)(n-m)_+} shom_{n-1}` and at `n = l-h <= l = Q.scale`
  the positive part vanishes, so the clause reads
  `(1/2) Ccg^{-1} shom_{l-h-1} <= lambda_{1/8,2}(z+cu_l; a_{l-h})`;

`2 * (2 Ccg) * 12 = 48 Ccg`, which is dimension-only times the caller's `Ccg`.
The gate is delivered at the `lambda`-carrier form `lambda_gate_chain`, which is
exactly the `hgate` binder of
`Provider/Localization/SwitchNormalization.lean`'s `_of_lambdaGate` bridges, at
`s = 1/8`, `q = 2`, `sn = shom_{l-h}`, `Cev = 48 Ccg`.

## 2. The wave bridge

`three_zpow_mul_underlineW2Gauge_le_waveGaugeW2` proves

```
3^{2l} ||k_m - k_{l-h}||_{W-underline^{2,infinity}(z+cu_l)}
  <= waveGaugeW2 m h (z+cu_l) omega ,
```

i.e. `3 ^ (2 * Q.scale) * underlineW2Gauge Q (shellIncrement omega (Q.scale-h)
m) <= MultiscaleEstimate.waveGaugeW2 m h Q omega`, **at the constant `1`**.
Three apparent obstacles all dissolve at the carriers as proved:

* SUM versus MAX: `waveGaugeW2` is `cubeSupBound + waveGauge`, and `waveGauge` is
  itself a SUM over the missing layers of `3^l ||grad j_k|| + 3^{2l} ||grad^2
  j_k||`, so each of the three `max`-entries of `3^{2l} underlineW2Gauge` is
  dominated by the corresponding part of the sum, the other part being
  nonnegative;
* pointwise-versus-suprema: NOT needed.  `waveGauge`'s summands are already at
  the suprema (`Stream.localCubeDerivNorm`, `Stream.localCubeSecondDerivNorm` are
  the exact `L-infinity` norms), so a pointwise fidelity statement is not the
  route; the route is layer
  subadditivity, `Stream.localCube(Second)DerivNorm_sum_le`, applied to
  `shellIncrement = ShellField.sum (Ioc (l-h) m)`;
* the base points `cubeBasePoint Q`, `cubeCenter Q`, `triadicCubeShift Q` are
  the same function by `rfl` (all three identifications are already proved as
  `BadEvents.cubeBasePoint_eq_triadicCubeShift` and the wave lane's own private
  `cubeCenter_eq_triadicCubeShift`).

The zeroth-order entry goes through the proved exact-`L-infinity` identity
`Stream.streamIncrementLinftyNorm_eq_localCubeControl` and the wave lane's
`streamIncrementLinftyNorm_le_waveGaugeW2`.

## 3. The injection prefactor (justified)

`inv_sq_sigmaBar_mul_three_zpow_le_prefactor` is the step the manuscript
performs "using `e.shom.h.bounds` from the induction hypothesis and `h cgamma
<= 1`":

```
shom_{l-h-1}^{-2} 3^{4l} <= 324 cstar^{-1} cgamma 3^{4l - 2 cgamma l} .
```

The printed exponent arithmetic is used verbatim: the lower branch of
`e.shom.h.bounds` (`inductionState`'s first conjunct) at the index `j = l-h-1`
gives `shom_j^2 >= (1/4) cstar cgamma^{-1} 3^{2 cgamma j}`, hence `shom_j^{-2}
<= 4 cstar^{-1} cgamma 3^{-2 cgamma j}` and `3^{-2 cgamma j} = 3^{-2 cgamma l}
3^{2 cgamma h} 3^{2 cgamma} <= 81. 3^{-2 cgamma l}` under `cgamma h <= 1` and
`cgamma <= 1`.  The manuscript performs the identical inversion in-source
(`shom_n^{-2} <= 4 cstar^{-1} cgamma 3^{-2 cgamma n}`).  The constant `4 . 81 =
324` is the honest one; the manuscript writes `C`.

## The scale gate on `m0`

The landmark premise carried by every statement below is `mStarStar M < m0`,
**not** the printed `m0 in (mstar, infty) cap Z`.  Nothing else moved: the
premise is forwarded verbatim to `Provider.Localization.shom_continuity`, no
proof step here consumes it, and no frozen statement changes --
`Algsuperdiff.Frozen.Section3.diffusivity_asymptotics` keeps the printed
`mStar M < m0` and reaches the weaker-gated chain a fortiori through
`Provider.Scales.mStarStar_le_mStar`.

## Related statements elsewhere

`SwitchNormalization.sigmaStarInv_gate_of_lambdaGate` is the one-cube ordering
step (through CoarseGraining's
`Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv`) that converts this file's
gate into the matrix-norm gate the switch consumes; it takes that gate as a
hypothesis, so there is no cycle and it is not invoked here.

`Multiscale.SharpGlobalFrame.sigmaBar_inv_le_growth_branch` is the one-scale
inversion of the lower branch of `e.shom.h.bounds`, on the identical premise
list (`inductionState M m0 E`, `j <= m0`), concluding
`shom_j^{-1} <= 2 sqrt(cstar^{-1} cgamma) 3^{-cgamma j}` -- whose square is
exactly the `hinv0` step of `inv_sq_sigmaBar_mul_three_zpow_le_prefactor`, and
it is consumed there rather than re-proved.

`MultiscaleEstimate.WaveSizesZeroth.streamIncrementLinftyNorm_le_waveGaugeW2`,
the wave lane's own zeroth-order fidelity statement against the same
three-order object, is consumed below.

## References

* ABK26, `l.localization.mathcalE` and its `lambda`-gate;
  `e.J.sensitivity.apppp`; `e.shom.h.bounds` inside `d.mathcalS.def`; the
  manuscript's own in-source twin of the prefactor inversion;
  `e.good.local.events`; `l.shom.continuity`.
-/

namespace Algsuperdiff.Section3.Provider.Localization

open _root_.MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book _root_.HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.MultiscaleEstimate
open Algsuperdiff.Section3.Provider.Stream
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Nonzero dimension, from the paper-wide assumption `2 <= d` stored in the
model. -/
private theorem neZero_of_model_lambdaGate (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-! ## 1. The middle step: the coefficient switch `a_m -> a_{l-h}`

On the good event `Q(l,l-h,z)` the frozen Section 2.4 `lambda`-sensitivity
engine moves the coefficient at a cost of exactly the printed factor `2`. -/

/-- **The middle step of the printed `lambda`-gate chain**.

Almost surely on the good local event `Q(l,n,z)`, for every admissible exponent
pair in the frozen engine's own window `0 < s <= 1/2`,

```
lambda_{s,q}^{-1}(z+cu_l; a_L) 1_Q <= 2 lambda_{s,q}^{-1}(z+cu_l; a_n) 1_Q .
```

The printed constant `2` is exact: the engine's leading factor is
`1 + C_lam ||grad(k_L-k_n)||_{W1inf} lambda_{3/8,2}^{-1}(z+cu_l;a_n)` and the
good event's sensitivity clause -- discharged, at the frozen `3/8` carrier, by
`BadEvents.gradientW1Infinity_incrementUnitCube₂_le_lambdaGate_ae` -- caps the
second summand by `1`.

A: the conclusion holds under the caller-supplied membership `omega ∈
goodLocalEvent M Ccg Q n`, which is the manuscript's own indicator
`1_{Q(l,l-h,z)}`. -/
theorem inv_lambdaSq_le_two_mul_inv_lambdaSq_of_mem_goodLocalEvent_ae
    (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) {n L : ℤ} (hnL : n ≤ L)
    {s : ℝ} {q : Ch02.MultiscaleExponent} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (hq : q.IsAdmissible) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        (Ch02.lambdaSq Q s q (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ ≤
          2 * (Ch02.lambdaSq Q s q
            (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ := by
  let : NeZero d := neZero_of_model_lambdaGate M
  filter_upwards
    [Algsuperdiff.Section3.Provider.Multiscale.lambdaSq_inv_le_of_mem_goodLocalEvent_ae
      M.shellPrefix.dimension M Ccg Q hnL s q hs hs2 hq,
    gradientW1Infinity_incrementUnitCube₂_le_lambdaGate_ae M Ccg Q n L hnL]
    with omega hsens hgrad homega
  have hC0 : (0 : ℝ) < lambdaSensitivityConst d :=
    lambdaSensitivityConst_pos M.shellPrefix.dimension
  have hLam0 : (0 : ℝ) < Ch02.lambdaSq Q (3 / 8) (Ch02.MultiscaleExponent.finite 2)
      (coefficientCutoffTriadicCoeffFamily M n omega) :=
    Ch02.lambdaSq_pos Q _ (by norm_num) (by norm_num)
  have hbracket : lambdaSensitivityConst d *
      (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
      (Ch02.lambdaSq Q (3 / 8) (Ch02.MultiscaleExponent.finite 2)
        (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ ≤ 1 := by
    have hg := hgrad homega
    rw [unitCubeLambda_unitRescaledCutoffCoeff M Q n (3 / 8)
      (Ch02.MultiscaleExponent.finite 2) omega] at hg
    have hstep := mul_le_mul_of_nonneg_left hg hC0.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC0), one_mul] at hstep
    have hfin := mul_le_mul_of_nonneg_right hstep (inv_nonneg.2 hLam0.le)
    rwa [mul_inv_cancel₀ (ne_of_gt hLam0)] at hfin
  have hinvn : (0 : ℝ) ≤ (Ch02.lambdaSq Q s q
      (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ :=
    inv_nonneg.2 (Ch02.lambdaSq_nonneg Q _ hs hq)
  refine (hsens homega).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hinvn

/-! ## 2. The last step: the good event's coarse-ellipticity clause

The gate opens through `e.good.local.events`. -/

/-- At or below the cube's own scale the printed positive part `(n-m)_+` vanishes.
(The proved `BadEvents.scaleGapPos_of_lt` covers only the strict branch; the
boundary `n = Q.scale` is inside the localization regime and is needed here.) -/
theorem scaleGapPos_eq_zero_of_le {m n : ℤ} (h : n ≤ m) :
    scaleGapPos m n = 0 := by
  have hc : ((n : ℝ)) ≤ (m : ℝ) := by exact_mod_cast h
  exact max_eq_right (by linarith)

/-- **The last step of the printed `lambda`-gate chain**.

Almost surely on the good local event `Q(l,n,z)` with `n <= l = Q.scale`, the
coarse-ellipticity clause of `e.good.local.events` clamps the inverse multiscale
ellipticity of `a_n` at the event's own comparator `shom_{n-1}`:

```
lambda_{1/8,2}^{-1}(z+cu_l; a_n) 1_Q <= 2 Ccg shom_{n-1}^{-1} .
```

The `3^{-(1/4)(n-m)_+}` weight of the event and the `3^{-(1/2)(n-m)_+}` weight of
`goodLocalThreshold` both collapse to `1` in this regime, so the level is exactly
the reciprocal of the threshold's own `(1/2) Ccg^{-1}`.

A: on the caller-supplied `omega ∈ goodLocalEvent M Ccg Q n` and `0 < Ccg`. -/
theorem inv_lambdaSq_le_of_mem_goodLocalEvent_ae (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        (Ch02.lambdaSq Q (1 / 8) (Ch02.MultiscaleExponent.finite 2)
            (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ ≤
          2 * Ccg * ((Annealed.sigmaBar M (n - 1) : ℝ))⁻¹ := by
  filter_upwards [cubeLowerEllipticity_ae_eq_literal M Q n (1 / 8) (by norm_num)
    exponentTwo] with omega hae homega
  have hsig : (0 : ℝ) < ((Annealed.sigmaBar M (n - 1) : ℝ)) :=
    (Annealed.sigmaBar M (n - 1)).2
  have hclause := ((mem_goodLocalEvent_iff M Ccg Q n omega).1 homega).2
  rw [goodLocalThreshold, scaleGapPos_eq_zero_of_le hn] at hclause
  rw [show (-(1 / 2 : ℝ) * 0) = 0 by ring, show (-(1 / 4 : ℝ) * 0) = 0 by ring,
    Real.rpow_zero, mul_one, one_mul] at hclause
  rw [hae, cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, exponentTwo_val] at hclause
  have hpos : (0 : ℝ) < 1 / 2 * Ccg⁻¹ *
      ((Annealed.sigmaBar M (n - 1) : ℝ)) := by positivity
  refine (inv_anti₀ hpos hclause).trans (le_of_eq ?_)
  field_simp

/-! ## 3. The composed gate, in both consumer spellings

 The chain, end to end.  The premise list is `l.shom.continuity`'s own, which is
 where the
`shom_{n-1} -> shom_n` passage comes from. -/

/-- **The composed `lambda`-gate**, at the printed carrier `lambda_{1/8,2}(z+cu_l;
a_L)` and the deep comparator `shom_n` (`n = l-h` at the intended instance).

On the `l.shom.continuity` premise list, for every coarse-ellipticity constant
`Ccg > 0`, every localization cube `Q` of scale `l`, every cutoff pair
`n <= L` with `n <= l` and `n <= m0`, almost surely on `Q(l,n,z)`:

```
shom_n lambda_{1/8,2}^{-1}(z+cu_l; a_L) <= 48 Ccg .
```

The level `48 Ccg` is dimension-only times the caller's `Ccg`; the three factors
are `2` (the middle step), `2 Ccg` (the event's ellipticity clause at
`shom_{n-1}`) and `12` (`shom_continuity`'s fourth conjunct at the adjacent pair,
whose side condition `cgamma <= 1` comes from the root's own
`cgamma <= (E^{-1})^{10}`).

This is exactly the `hgate` binder of
`Provider/Localization/SwitchNormalization.lean`'s `_of_lambdaGate` bridges, at
`s = 1/8`, `q = 2`, `sn = shom_n`, `Cev = 48 Ccg`.

A on `omega ∈ goodLocalEvent M Ccg Q n` and `0 < Ccg`; a proved local Provider
theorem, no node status. -/
theorem lambda_gate_chain (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ (Q : TriadicCube d) (n L : ℤ), n ≤ L → n ≤ Q.scale → n ≤ m0 →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ goodLocalEvent M Ccg Q n →
                (Annealed.sigmaBar M n : ℝ) *
                    (Ch02.lambdaSq Q (1 / 8) (Ch02.MultiscaleExponent.finite 2)
                      (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ ≤
                  48 * Ccg := by
  obtain ⟨C, hC0, hcont⟩ := shom_continuity d
  refine ⟨C, hC0, ?_⟩
  intro M m0 E hm0 hstate hCE hgammaE Ccg hCcg Q n L hnL hnQ hnm0
  let : NeZero d := neZero_of_model_lambdaGate M
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le one_pos hE1
  have hgamma1 : M.gamma ≤ 1 := by
    have hinv : ((E : ℝ))⁻¹ ≤ 1 := by rw [inv_le_one₀ hE0]; exact hE1
    have h0 : (0 : ℝ) ≤ ((E : ℝ))⁻¹ := (inv_pos.2 hE0).le
    refine le_trans hgammaE ?_
    calc ((E : ℝ)⁻¹) ^ 10 ≤ (1 : ℝ) ^ 10 := pow_le_pow_left₀ h0 hinv 10
      _ = 1 := one_pow 10
  obtain ⟨-, -, -, hshort, -⟩ :=
    hcont M m0 E hm0 hstate hCE hgammaE n (n - 1) (by omega) hnm0
  have hgap : M.gamma * ((n : ℝ) - ((n - 1 : ℤ) : ℝ)) ≤ 1 := by
    push_cast
    simpa using hgamma1
  have hratio := hshort hgap
  have hsigp : (0 : ℝ) < ((Annealed.sigmaBar M (n - 1) : ℝ)) :=
    (Annealed.sigmaBar M (n - 1)).2
  have hsign : (0 : ℝ) < ((Annealed.sigmaBar M n : ℝ)) := (Annealed.sigmaBar M n).2
  have hpass : ((Annealed.sigmaBar M (n - 1) : ℝ))⁻¹ ≤
      12 * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_right hratio (inv_nonneg.2 hsign.le)
    have hid : ((Annealed.sigmaBar M n : ℝ) *
        ((Annealed.sigmaBar M (n - 1) : ℝ))⁻¹) *
        ((Annealed.sigmaBar M n : ℝ))⁻¹ =
        ((Annealed.sigmaBar M (n - 1) : ℝ))⁻¹ := by field_simp
    rwa [hid] at hstep
  filter_upwards [inv_lambdaSq_le_two_mul_inv_lambdaSq_of_mem_goodLocalEvent_ae
      M Ccg Q hnL (s := 1 / 8) (q := Ch02.MultiscaleExponent.finite 2) (by norm_num)
      (by norm_num) (by norm_num),
    inv_lambdaSq_le_of_mem_goodLocalEvent_ae M hCcg Q hnQ]
    with omega hmid hell homega
  have h1 := hmid homega
  have h2 := hell homega
  have hfinal : (Ch02.lambdaSq Q (1 / 8) (Ch02.MultiscaleExponent.finite 2)
      (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ ≤
      48 * Ccg * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
    nlinarith [h1, h2, hpass, hCcg.le]
  have hmul := mul_le_mul_of_nonneg_left hfinal hsign.le
  calc (Annealed.sigmaBar M n : ℝ) *
        (Ch02.lambdaSq Q (1 / 8) (Ch02.MultiscaleExponent.finite 2)
          (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹
      ≤ (Annealed.sigmaBar M n : ℝ) *
        (48 * Ccg * ((Annealed.sigmaBar M n : ℝ))⁻¹) := hmul
    _ = 48 * Ccg := by field_simp

/-! ## 4. The wave bridge -/

/-- Translating the whole shell sequence translates the finite increment. -/
private theorem shellIncrement_translateSequence_gate (z : Vec d) (n L : ℤ)
    (omega : ShellSeq d) :
    shellIncrement (ShellField.translateSequence z omega) n L =
      ShellField.translate z (shellIncrement omega n L) := by
  rw [shellIncrement, shellIncrement, ShellField.translate_sum]
  rfl

/-- At the localization cube `Q` of scale `l` and the missing-layer range `(l-h,
m]`,

```
3^{2l} ||k_m - k_{l-h}||_{W-underline^{2,infinity}(z+cu_l)}
  <= waveGaugeW2 m h (z+cu_l) omega ,
```

**at the honest constant `1`** -- no dimension factor is needed.

The three legs, in the order they appear in `underlineW2Gauge`'s `max`: `3^{2l}
||grad^2||` and `3^l ||grad||` are dominated by the corresponding halves of
`waveGauge`'s per-layer sum after layer subadditivity of the exact `L-infinity`
gauges (`Stream.localCubeSecondDerivNorm_sum_le`,
`Stream.localCubeDerivNorm_sum_le`, applied to `shellIncrement = ShellField.sum
(Ioc (l-h) m)`), the other half of each summand being nonnegative; the
zeroth-order leg `||.||_{L-infinity}` is the proved exact identity
`Stream.streamIncrementLinftyNorm_eq_localCubeControl` composed with the wave
lane's own `streamIncrementLinftyNorm_le_waveGaugeW2`.  The base points
`cubeBasePoint Q` and `cubeCenter Q` are the same function by `rfl`. -/
theorem three_zpow_mul_underlineW2Gauge_le_waveGaugeW2 (Q : TriadicCube d) (m : ℤ)
    (h : ℕ) (omega : ShellSeq d) :
    (3 : ℝ) ^ (2 * Q.scale) *
        underlineW2Gauge Q (shellIncrement omega (Q.scale - (h : ℤ)) m) ≤
      waveGaugeW2 m h Q omega := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have h32 : (0 : ℝ) < (3 : ℝ) ^ (2 * Q.scale) := zpow_pos (by norm_num) _
  have hsq : (3 : ℝ) ^ (2 * Q.scale) = (3 : ℝ) ^ Q.scale * (3 : ℝ) ^ Q.scale := by
    rw [two_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  set z : Vec d := cubeBasePoint Q with hz
  set s : Finset ℤ := Finset.Ioc (Q.scale - (h : ℤ)) m with hs
  set inc : ShellField d := shellIncrement omega (Q.scale - (h : ℤ)) m with hinc
  have htr : ShellField.translate z inc =
      ShellField.sum s (fun k => ShellField.translate z (omega k)) := by
    rw [hinc, shellIncrement, ShellField.translate_sum]
  have hwave : waveGauge Q.scale m h z omega =
      ∑ k ∈ s, ((3 : ℝ) ^ Q.scale *
          localCubeDerivNorm Q.scale (ShellField.translate z (omega k)) +
        (3 : ℝ) ^ (2 * Q.scale) *
          localCubeSecondDerivNorm Q.scale (ShellField.translate z (omega k))) := rfl
  have hcube : (0 : ℝ) ≤ cubeSupBound Q (Q.scale - (h : ℤ)) m omega :=
    cubeSupBound_nonneg _ _ _ _
  have hwaveLe : waveGauge Q.scale m h z omega ≤ waveGaugeW2 m h Q omega := by
    rw [waveGaugeW2]
    have hz' : waveGauge Q.scale m h (cubeCenter Q) omega =
        waveGauge Q.scale m h z omega := rfl
    rw [hz']
    linarith
  have hDsum : localCubeDerivNorm Q.scale (ShellField.translate z inc) ≤
      ∑ k ∈ s, localCubeDerivNorm Q.scale (ShellField.translate z (omega k)) := by
    rw [htr]
    exact localCubeDerivNorm_sum_le Q.scale s _
  have hSDsum : localCubeSecondDerivNorm Q.scale (ShellField.translate z inc) ≤
      ∑ k ∈ s, localCubeSecondDerivNorm Q.scale
        (ShellField.translate z (omega k)) := by
    rw [htr]
    exact localCubeSecondDerivNorm_sum_le Q.scale s _
  have hDterm : (3 : ℝ) ^ Q.scale *
      localCubeDerivNorm Q.scale (ShellField.translate z inc) ≤
      waveGauge Q.scale m h z omega := by
    rw [hwave, Finset.sum_add_distrib]
    have hsecond : (0 : ℝ) ≤ ∑ k ∈ s, (3 : ℝ) ^ (2 * Q.scale) *
        localCubeSecondDerivNorm Q.scale (ShellField.translate z (omega k)) :=
      Finset.sum_nonneg fun _ _ =>
        mul_nonneg h32.le (localCubeSecondDerivNorm_nonneg _ _)
    have hstep := mul_le_mul_of_nonneg_left hDsum h3.le
    rw [Finset.mul_sum] at hstep
    linarith
  have hSDterm : (3 : ℝ) ^ (2 * Q.scale) *
      localCubeSecondDerivNorm Q.scale (ShellField.translate z inc) ≤
      waveGauge Q.scale m h z omega := by
    rw [hwave, Finset.sum_add_distrib]
    have hfirst : (0 : ℝ) ≤ ∑ k ∈ s, (3 : ℝ) ^ Q.scale *
        localCubeDerivNorm Q.scale (ShellField.translate z (omega k)) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg h3.le (localCubeDerivNorm_nonneg _ _)
    have hstep := mul_le_mul_of_nonneg_left hSDsum h32.le
    rw [Finset.mul_sum] at hstep
    linarith
  have hCterm : localCubeControl Q.scale (ShellField.translate z inc) ≤
      waveGaugeW2 m h Q omega := by
    have hid : localCubeControl Q.scale (ShellField.translate z inc) =
        streamIncrementLinftyNorm Q.scale (Q.scale - (h : ℤ)) m
          (ShellField.translateSequence z omega) := by
      rw [streamIncrementLinftyNorm_eq_localCubeControl,
        shellIncrement_translateSequence_gate]
    rw [hid]
    exact streamIncrementLinftyNorm_le_waveGaugeW2 m h Q omega
  rw [underlineW2Gauge, mul_max_of_nonneg _ _ h32.le, mul_max_of_nonneg _ _ h32.le]
  refine max_le (hSDterm.trans hwaveLe) (max_le ?_ ?_)
  · have hrw : (3 : ℝ) ^ (2 * Q.scale) *
        (((3 : ℝ) ^ Q.scale)⁻¹ *
          localCubeDerivNorm Q.scale (ShellField.translate z inc)) =
        (3 : ℝ) ^ Q.scale *
          localCubeDerivNorm Q.scale (ShellField.translate z inc) := by
      rw [hsq]; field_simp
    rw [hrw]
    exact hDterm.trans hwaveLe
  · have hrw : (3 : ℝ) ^ (2 * Q.scale) *
        ((((3 : ℝ) ^ Q.scale)⁻¹) ^ 2 *
          localCubeControl Q.scale (ShellField.translate z inc)) =
        localCubeControl Q.scale (ShellField.translate z inc) := by
      rw [hsq]; field_simp
    rw [hrw]
    exact hCterm

/-- **The wave bridge, squared** -- the form the injection remainder meets, since
the frozen sensitivity engine's remainder carries the squares of the two gate
quantities (the `3^{4l}` fingerprint). -/
theorem three_zpow_mul_underlineW2Gauge_sq_le_waveGaugeW2_sq (Q : TriadicCube d)
    (m : ℤ) (h : ℕ) (omega : ShellSeq d) :
    (3 : ℝ) ^ (4 * Q.scale) *
        underlineW2Gauge Q (shellIncrement omega (Q.scale - (h : ℤ)) m) ^ 2 ≤
      waveGaugeW2 m h Q omega ^ 2 := by
  have hbase := three_zpow_mul_underlineW2Gauge_le_waveGaugeW2 Q m h omega
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * Q.scale) *
      underlineW2Gauge Q (shellIncrement omega (Q.scale - (h : ℤ)) m) :=
    mul_nonneg (zpow_pos (by norm_num) _).le (underlineW2Gauge_nonneg _ _)
  have hsq : (3 : ℝ) ^ (4 * Q.scale) = ((3 : ℝ) ^ (2 * Q.scale)) ^ 2 := by
    rw [show (4 : ℤ) * Q.scale = 2 * Q.scale + 2 * Q.scale by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), sq]
  rw [hsq, ← mul_pow]
  exact pow_le_pow_left₀ hnn hbase 2

/-! ## 5. The injection prefactor

Justified by `e.shom.h.bounds` and `h cgamma <= 1`. -/

/-- **The injection prefactor.**

From the lower branch of `e.shom.h.bounds` (the first conjunct of
`inductionState`) at the index `j = l-h-1`, together with `cgamma h <= 1` and
`cgamma <= 1`:

```
shom_{l-h-1}^{-2} 3^{4l} <= 324 cstar^{-1} cgamma 3^{4l - 2 cgamma l} .
```

Exponent arithmetic, verbatim: `shom_j^2 >= (1/4) cstar cgamma^{-1} 3^{2 cgamma
j}` gives `shom_j^{-2} <= 4 cstar^{-1} cgamma 3^{-2 cgamma j}`, and `-2 cgamma
j = -2 cgamma l + 2 cgamma h + 2 cgamma` with `3^{2 cgamma h} 3^{2 cgamma} <=
3^2. 3^2 = 81`.  The manuscript performs the identical inversion in-source. The
honest constant is `4 . 81 = 324`; the manuscript writes `C`.

Only the exponent split `-2 cgamma j = -2 cgamma l + 2 cgamma h + 2 cgamma` is
new here. -/
theorem inv_sq_sigmaBar_mul_three_zpow_le_prefactor (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (l : ℤ) (h : ℕ) (hj : l - (h : ℤ) - 1 ≤ m0) (hgamma1 : M.gamma ≤ 1)
    (hgh : M.gamma * (h : ℝ) ≤ 1) :
    ((Annealed.sigmaBar M (l - (h : ℤ) - 1) : ℝ))⁻¹ ^ 2 * (3 : ℝ) ^ (4 * l) ≤
      324 * (Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (4 * (l : ℝ) - 2 * M.gamma * (l : ℝ)) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  set j : ℤ := l - (h : ℤ) - 1 with hjdef
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M j : ℝ) := (Annealed.sigmaBar M j).2
  -- the proved one-scale inversion `Multiscale.sigmaBar_inv_le_growth_branch`
  have hinv0 : ((Annealed.sigmaBar M j : ℝ))⁻¹ ^ 2 ≤
      4 * (Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) := by
    have hgrowth :=
      Algsuperdiff.Section3.Provider.Multiscale.sigmaBar_inv_le_growth_branch M hstate hj
    have hstep := pow_le_pow_left₀ (inv_nonneg.2 hsig.le) hgrowth 2
    refine hstep.trans (le_of_eq ?_)
    have hcg : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * M.gamma := by positivity
    rw [mul_pow, mul_pow, Real.sq_sqrt hcg,
      ← Real.rpow_natCast ((3 : ℝ) ^ (-(M.gamma * (j : ℝ)))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast
    ring_nf
  have hjcast : (j : ℝ) = (l : ℝ) - (h : ℝ) - 1 := by rw [hjdef]; push_cast; ring
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ (-(2 * M.gamma * (l : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hsplit : (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) ≤
      81 * (3 : ℝ) ^ (-(2 * M.gamma * (l : ℝ))) := by
    rw [hjcast, show -(2 * M.gamma * ((l : ℝ) - (h : ℝ) - 1)) =
        -(2 * M.gamma * (l : ℝ)) + (2 * M.gamma * (h : ℝ) + 2 * M.gamma) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hb : (3 : ℝ) ^ (2 * M.gamma * (h : ℝ) + 2 * M.gamma) ≤ 81 := by
      have hle : 2 * M.gamma * (h : ℝ) + 2 * M.gamma ≤ 4 := by linarith
      refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle) ?_
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    nlinarith [hb, hLpos]
  have hzpow : (3 : ℝ) ^ (4 * l) = (3 : ℝ) ^ (4 * (l : ℝ)) := by
    rw [← Real.rpow_intCast 3 (4 * l)]
    congr 1
    push_cast
    ring
  have hmerge : (3 : ℝ) ^ (-(2 * M.gamma * (l : ℝ))) * (3 : ℝ) ^ (4 * (l : ℝ)) =
      (3 : ℝ) ^ (4 * (l : ℝ) - 2 * M.gamma * (l : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hpow0 : (0 : ℝ) < (3 : ℝ) ^ (4 * (l : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgeq : (0 : ℝ) ≤ 4 * (Disorder.cstar M)⁻¹ * M.gamma := by positivity
  rw [hzpow]
  calc ((Annealed.sigmaBar M j : ℝ))⁻¹ ^ 2 * (3 : ℝ) ^ (4 * (l : ℝ))
      ≤ (4 * (Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ)))) * (3 : ℝ) ^ (4 * (l : ℝ)) :=
        mul_le_mul_of_nonneg_right hinv0 hpow0.le
    _ ≤ (4 * (Disorder.cstar M)⁻¹ * M.gamma *
          (81 * (3 : ℝ) ^ (-(2 * M.gamma * (l : ℝ))))) * (3 : ℝ) ^ (4 * (l : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsplit hgeq) hpow0.le
    _ = 324 * (Disorder.cstar M)⁻¹ * M.gamma *
          ((3 : ℝ) ^ (-(2 * M.gamma * (l : ℝ))) * (3 : ℝ) ^ (4 * (l : ℝ))) := by ring
    _ = 324 * (Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (4 * (l : ℝ) - 2 * M.gamma * (l : ℝ)) := by rw [hmerge]

/-! ### The manuscript's loading identities -/

/-- `|shom^{-1/2} v|^2 = shom^{-1} |v|^2`. -/
theorem vecNormSq_inverseSqrtLoad_eq (sigma : Observable.PositiveScalar)
    (v : Vec d) :
    vecNormSq (Observable.inverseSqrtLoad sigma v) = (sigma : ℝ)⁻¹ * vecNormSq v := by
  rw [Observable.inverseSqrtLoad, vecNormSq_smul, ← Real.sqrt_inv,
    Real.sq_sqrt (inv_nonneg.mpr sigma.2.le)]

/-- `shom^{-1/2} v . shom^{1/2} v = |v|^2`: the manuscript's paired loading is
normalized. -/
theorem vecDot_inverseSqrtLoad_sqrtLoad (sigma : Observable.PositiveScalar)
    (v : Vec d) :
    vecDot (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) =
      vecNormSq v := by
  have hs : (0 : ℝ) < Real.sqrt (sigma : ℝ) := Real.sqrt_pos.2 sigma.2
  rw [Observable.inverseSqrtLoad, Observable.sqrtLoad, vecDot_smul_left,
    vecDot_smul_right, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), one_mul]
  rfl

/-- The abstract-real core of the injection pricing: the two remainder terms of
the frozen `delta = 1` endpoint, gated at `Lam <= 2 Ccg S` with the loading data
`A <= 8 S`, `B <= 2`, and the prefactor substitution `S^2 G <= P`. -/
theorem injection_remainder_bound {Cresp Ccg S G W Lam A B P : ℝ}
    (hCresp : 0 ≤ Cresp) (hCcg : 0 ≤ Ccg) (hS : 0 ≤ S) (hG : 0 ≤ G)
    (hLam0 : 0 ≤ Lam) (hLamS : Lam ≤ 2 * Ccg * S) (hA : A ≤ 8 * S) (hB : B ≤ 2)
    (hP : S ^ 2 * G ≤ P) :
    Cresp * (A * (G * W ^ 2) * Lam + B * (G * W ^ 2) * Lam ^ 2) ≤
      Cresp * ((16 * Ccg + 8 * Ccg ^ 2) * P * W ^ 2) := by
  have hGW : (0 : ℝ) ≤ G * W ^ 2 := by positivity
  have h1 : A * (G * W ^ 2) * Lam ≤ 16 * Ccg * (S ^ 2 * (G * W ^ 2)) := by
    have hx : A * (G * W ^ 2) ≤ 8 * S * (G * W ^ 2) :=
      mul_le_mul_of_nonneg_right hA hGW
    have hy := mul_le_mul hx hLamS hLam0 (by positivity)
    nlinarith [hy]
  have h2 : B * (G * W ^ 2) * Lam ^ 2 ≤ 8 * Ccg ^ 2 * (S ^ 2 * (G * W ^ 2)) := by
    have hsq : Lam ^ 2 ≤ (2 * Ccg * S) ^ 2 := pow_le_pow_left₀ hLam0 hLamS 2
    have hx : B * (G * W ^ 2) ≤ 2 * (G * W ^ 2) :=
      mul_le_mul_of_nonneg_right hB hGW
    have hy := mul_le_mul hx hsq (by positivity) (by positivity)
    nlinarith [hy]
  have hKnn : (0 : ℝ) ≤ 16 * Ccg + 8 * Ccg ^ 2 := by positivity
  have h3 : (16 * Ccg + 8 * Ccg ^ 2) * (S ^ 2 * G) * W ^ 2 ≤
      (16 * Ccg + 8 * Ccg ^ 2) * P * W ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_left hP hKnn
    nlinarith [hstep, sq_nonneg W]
  have hsum : A * (G * W ^ 2) * Lam + B * (G * W ^ 2) * Lam ^ 2 ≤
      (16 * Ccg + 8 * Ccg ^ 2) * P * W ^ 2 := by nlinarith [h1, h2, h3]
  exact mul_le_mul_of_nonneg_left hsum hCresp

end

end Algsuperdiff.Section3.Provider.Localization
