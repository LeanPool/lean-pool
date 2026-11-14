/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionData
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.LayerMass

/-!
# ConclusionKtotEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `Ktot` pricing at the honest layer envelope

```
cubeSupBound □ □.scale L ω  ≤  (1+k)^{1/2} ρ_k A t ,
ρ_k = (3 max{1, log #𝒲(□_m,k)})^{1/2} ,   A = whitneyWaveCubeScale M L ,
```

on a set of outer measure at least `1 − 2 e^{−t²}`
(`one_sub_le_measureReal_forall_cubeSupBound_le`), while
`ConclusionKtot.goodCellForm_le_ktotConst_mul_layerQuantity_ae` consumes a
single real `Swave`.  That module's "What is not proved" paragraph names the
exact three-step local instantiation; this module performs it.

## 1. The logarithm of the proved layer-mass count

`LayerMass.card_whitneyLayer_le` is `#𝒲(□_m,k) ≤ 2d (3^{d−1})^{k−1}(3^d)^{1+h_k}`.
Collapsing `2d ≤ 3^d` (`two_mul_le_three_pow`, all `d`) puts it in the single
power form `#𝒲(□_m,k) ≤ 3^{d(2+k+h_k)}` (`card_whitneyLayer_le_pow`), so

```
3 max{1, log #𝒲(□_m,k)}  ≤  whitneyLayerLogConst d . (1 + k + h_k) ,
whitneyLayerLogConst d = 3 (1 + 2 d log 3) ,
```

which is `three_mul_max_one_log_card_whitneyLayer_le`, and therefore
`ρ_k² ≤ C(d)(1 + k + h_k)` (`whitneyWaveLayerPenalty_sq_le`).  The route is the
one already used for the covering family in
`Provider/Stream/LargeCubeLinfty.lean`
(`three_mul_max_one_log_card_subcubeShifts_le`, constant `largeCubeLogConst`);
the empty layer `k = 0` is covered because `log 0 = 0` there.

## 2. The absorption, over abstract reals

The amplification `(1+k) ρ_k²` is polynomial while the payload of
`ConclusionCompetitor.toReal_tsum_simplexPartition_cutoff_two_leg_le_payload`
is geometric in `k + h_k`, so a polynomial-vs-exponential trade discharges this
local pricing mismatch at an arbitrarily small exponent loss.  The core is
stated over abstract reals with the exponential kept as an atom `A`:

```
0 < c , 0 ≤ s , (1 + c s)² ≤ A   ⟹   (1 + s)² ≤ (1 + c⁻¹)² A ,
```

`sq_one_add_le_mul`, whose only content is `1 + s ≤ (1+c⁻¹)(1+cs)`
(`one_add_le_mul`).  The atom is supplied once, at `c = ε log 3 / 2`, by
`sq_one_add_le_three_rpow` (`(1 + u)² ≤ (e^u)² = 3^{εs}`), giving

```
(1+x)(1+x+y)  ≤  layerAbsorptionConst ε . 3^{ε(x+y)} ,
layerAbsorptionConst ε = (1 + 2 (ε log 3)^{-1})² ,
```

for all `x, y ≥ 0` (`one_add_mul_le_layerAbsorptionConst_mul`).  The constant is
the honest one produced by that route; nothing here optimizes it.

## 3. The good leg at the raised exponent

Feeding the envelope `Sc k = whitneyWaveLayerScale M m h k L . t` makes the
layer constant `k`-dependent through `Sup²` only, and steps 1--2 price exactly
that dependence:

```
max{osc_m, Sc k}²  ≤  ktotEnvelopeSup M m L ε t² . 3^{ε(k+h_k)} ,
ktotEnvelopeSup M m L ε t
    = (osc_m² + C(d) C_ε (whitneyWaveCubeScale M L)² t²)^{1/2} ,
```

(`sq_max_oscThreshold_whitneyWaveLayerScale_le`), and `ktotConst` is affine in
`Sup²` with nonnegative coefficients (`ktotConst_le_mul`), so the whole layer
constant is at most `ktotConst(ktotEnvelopeSup) . 3^{ε(k+h_k)}` and the payload
exponent rises from `2γ` to `2γ + ε`.
`goodCellForm_le_ktotEnvelopeConst_mul_layerQuantity_ae` is the conclusion in
the exact `hgood` binder body of
`ConclusionCompetitor.toReal_tsum_simplexPartition_cutoff_two_leg_le_payload`
at

```
Ktot := ktotConst M m i 3 (ktotEnvelopeSup M m L ε t) p q ,
γ    := 2 M.gamma + ε ,
```

and `one_sub_le_measureReal_goodCellForm_le_ktotEnvelopeConst_mul` discharges
its envelope antecedent against `ConclusionData`'s aggregation: the `hgood`
body holds on a set of outer measure at least `1 − 2 (Γ₂ t)^{-1}`.

The payload's remaining data at this `Ktot` are already proved elsewhere: `hγ0:
0 ≤ 2 M.gamma + ε` is immediate from `M.shellPrefix.gamma_pos` and `ε > 0`, and
`hK : 0 ≤ Ktot` is `ConclusionKtot.ktotConst_nonneg hd M m i (0 ≤ 3) _ p q`.
Neither is restated here, because nothing here invokes the payload.

## Conditional consumer gate (audit-28 A2- pattern)

The payload's own window is `hγ : 4 γ ≤ 1 − b` (the layer-series summability
condition of `ConclusionAssembly`, carried unchanged by
`LayerUniform.toReal_tsum_simplexPartition_two_leg_le_payload` and by
`ConclusionCompetitor.toReal_tsum_simplexPartition_cutoff_two_leg_le_payload`).
At the instantiation above it reads

```
8 M.gamma + 4 ε  ≤  1 − b ,
```

which is NOT implied by the standing `γ ≤ 1/4` gate and is NOT a binder of
anything below (nothing here invokes the payload).  It is the composer's gate,
recorded here exactly as `ConclusionKtot` records its own `8 M.gamma ≤ 1 − b`
tightening: the factor `2` is the price of the squared-gauge pricing and the
`4 ε` is the price of this module's absorption.  Both have wide room under the
induction's own admissibility `M.gamma ≤ E^{-5}`, and `ε` is free, so the
composer chooses `ε` after `b`; no statement below assumes any relation between
`ε`, `b` and `M.gamma`.

## What is *not* proved

* **No constant `Swave`**, and no claim that one exists: `ConclusionData`'s
  analysis is unchanged and nothing here re-opens it.  The envelope is carried
  as an antecedent of the almost-sure statements below; it is never replaced by
  a constant.
* **The concluding assembly is NOT run.**  Nothing below invokes the
  concluding payload of `ConclusionRoot`; the parameter window above is
  recorded, not discharged, and the collar leg, the mass data and the
  `hBadDens` datum are untouched.
* **No `3^{−3k/4}` per-layer weight** (blocks it, and the amplification is paid
  by the union bound of `ConclusionData` and by this module's `ε`, never by a
  layer weight).
* **The constants are not optimized.**  `whitneyLayerLogConst d = 3(1+2d log 3)`
  and `layerAbsorptionConst ε = (1 + 2(ε log 3)^{-1})²` are the honest outputs of
  the two routes above; the manuscript's own `C(d)`, `C_ε` are not claimed to be
  these.
* **No new probabilistic input.**  The only almost-sure statement consumed is
  the base pricing
  `ConclusionCompetitor.goodCellForm_le_stepOneLayerMajorant_ae`; the layer
  envelope itself is carried as an antecedent rather than discharged here.  No
  independence and no measurability of the good event is used or needed.

## Main definitions

* `Algsuperdiff.Section3.Provider.Multiscale.whitneyLayerLogConst`
* `Algsuperdiff.Section3.Provider.Multiscale.layerAbsorptionConst`
* `Algsuperdiff.Section3.Provider.Multiscale.ktotEnvelopeSup`

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.three_mul_max_one_log_card_whitneyLayer_le`
* `Algsuperdiff.Section3.Provider.Multiscale.whitneyWaveLayerPenalty_sq_le`
* `Algsuperdiff.Section3.Provider.Multiscale.one_add_mul_le_layerAbsorptionConst_mul`
* `Algsuperdiff.Section3.Provider.Multiscale.sq_max_oscThreshold_whitneyWaveLayerScale_le`
* `Algsuperdiff.Section3.Provider.Multiscale.goodCellForm_le_ktotConst_mul_layerScale_ae`
* `Algsuperdiff.Section3.Provider.Multiscale.`
  `goodCellForm_le_ktotEnvelopeConst_mul_layerQuantity_ae`

## References

* ABK26, `p.bfA.multiscalebound` Step 1 (majorant) and Step 3; `e.hn.def`
  and `e.hn.gap` (label-line convention; the inequality prints on the
  following line; the printed reference is garbled); the Whitney layers;
  `e.km.kn.Linfty`; `l.maximums.Gamma.s`.
* `Provider/Multiscale/ConclusionData.lean` (the envelope and its aggregation),
  `Provider/Multiscale/ConclusionKtot.lean` (the pricing and `ktotConst`),
  `Provider/Multiscale/LayerMass.lean` (the layer count),
  `Provider/Multiscale/ConclusionCompetitor.lean` (the `hgood` consumer),
  `Provider/Stream/LargeCubeLinfty.lean` (the covering-count precedent).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Step 1: the logarithm of the proved layer count -/

/-- `2 d ≤ 3^d`, for every `d`. -/
theorem two_mul_le_three_pow (d : ℕ) : 2 * d ≤ 3 ^ d := by
  induction d with
  | zero => norm_num
  | succ n ih =>
      have h1 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      omega

/-- **The proved layer count in single-power form.**
`LayerMass.card_whitneyLayer_le` with `2d ≤ 3^d`, `3^{d−1} ≤ 3^d` and `k − 1 ≤
k`. -/
theorem card_whitneyLayer_le_pow (m : ℤ) (hn : ℕ → ℕ) (k : ℕ) :
    (whitneyLayer (d := d) m hn k).card ≤ 3 ^ (d * (2 + k + hn k)) := by
  refine le_trans (card_whitneyLayer_le m hn k) ?_
  have h1 : 2 * d ≤ 3 ^ d := two_mul_le_three_pow d
  have h2 : (3 ^ (d - 1)) ^ (k - 1) ≤ (3 ^ d) ^ k :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (k - 1)
      |>.trans (Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num)) (by omega))
  calc 2 * d * (3 ^ (d - 1)) ^ (k - 1) * (3 ^ d) ^ (1 + hn k)
      ≤ 3 ^ d * (3 ^ d) ^ k * (3 ^ d) ^ (1 + hn k) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) le_rfl
    _ = 3 ^ (d + d * k + d * (1 + hn k)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    _ = 3 ^ (d * (2 + k + hn k)) := by
        congr 1
        ring

/-- The log-cardinality constant of a Whitney layer, `3(1 + 2 d log 3)`. -/
def whitneyLayerLogConst (d : ℕ) : ℝ := 3 * (1 + 2 * (d : ℝ) * Real.log 3)

theorem whitneyLayerLogConst_pos (d : ℕ) : 0 < whitneyLayerLogConst d := by
  have h : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 := by
    have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  rw [whitneyLayerLogConst]
  linarith

/-- **Step (i).**  The `l.maximums.Gamma.s` penalty base of the layer `𝒲(□_m,k)`
is at most `C(d) (1 + k + h_k)`.  Layer `0` is empty and `log 0 = 0`, so the
bound is trivial there. -/
theorem three_mul_max_one_log_card_whitneyLayer_le (m : ℤ) (hn : ℕ → ℕ) (k : ℕ) :
    3 * max 1 (Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ)) ≤
      whitneyLayerLogConst d * (1 + (k : ℝ) + (hn k : ℝ)) := by
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hhR : (0 : ℝ) ≤ (hn k : ℝ) := Nat.cast_nonneg _
  have hcard := card_whitneyLayer_le_pow (d := d) m hn k
  have hlogle : Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ) ≤
      2 * (d : ℝ) * Real.log 3 * (1 + (k : ℝ) + (hn k : ℝ)) := by
    have hbound : Real.log ((3 ^ (d * (2 + k + hn k)) : ℕ) : ℝ) =
        ((d : ℝ) * (2 + (k : ℝ) + (hn k : ℝ))) * Real.log 3 := by
      have hc : ((3 ^ (d * (2 + k + hn k)) : ℕ) : ℝ) = (3 : ℝ) ^ (d * (2 + k + hn k)) := by
        norm_cast
      rw [hc, Real.log_pow]
      push_cast
      ring
    have hstep : Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ) ≤
        Real.log ((3 ^ (d * (2 + k + hn k)) : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (whitneyLayer (d := d) m hn k).card with hz | hpos
      · rw [hz]
        have h0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
        rw [h0, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast Nat.one_le_pow _ _ (by norm_num))
      · refine Real.log_le_log (by exact_mod_cast hpos) ?_
        exact_mod_cast hcard
    refine le_trans hstep (le_of_eq_of_le hbound ?_)
    have hdkh : (0 : ℝ) ≤ (d : ℝ) * ((k : ℝ) + (hn k : ℝ)) := by positivity
    have hmul : (d : ℝ) * (2 + (k : ℝ) + (hn k : ℝ)) ≤
        2 * (d : ℝ) * (1 + (k : ℝ) + (hn k : ℝ)) := by linarith [hdkh]
    calc ((d : ℝ) * (2 + (k : ℝ) + (hn k : ℝ))) * Real.log 3
        ≤ (2 * (d : ℝ) * (1 + (k : ℝ) + (hn k : ℝ))) * Real.log 3 :=
          mul_le_mul_of_nonneg_right hmul hlog3
      _ = 2 * (d : ℝ) * Real.log 3 * (1 + (k : ℝ) + (hn k : ℝ)) := by ring
  have hX : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 := by positivity
  have hXY : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 * (1 + (k : ℝ) + (hn k : ℝ)) :=
    mul_nonneg hX (by linarith)
  have hexp : (1 + 2 * (d : ℝ) * Real.log 3) * (1 + (k : ℝ) + (hn k : ℝ)) =
      (1 + (k : ℝ) + (hn k : ℝ)) + 2 * (d : ℝ) * Real.log 3 * (1 + (k : ℝ) + (hn k : ℝ)) := by
    ring
  have hmax : max 1 (Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ)) ≤
      (1 + 2 * (d : ℝ) * Real.log 3) * (1 + (k : ℝ) + (hn k : ℝ)) := by
    rw [hexp]
    exact max_le (by linarith) (by linarith)
  have hfin : 3 * ((1 + 2 * (d : ℝ) * Real.log 3) * (1 + (k : ℝ) + (hn k : ℝ))) =
      whitneyLayerLogConst d * (1 + (k : ℝ) + (hn k : ℝ)) := by
    rw [whitneyLayerLogConst]
    ring
  linarith [hfin, hmax]

/-- **Step (i), squared.**  `ρ_k² ≤ C(d)(1 + k + h_k)` for the finset-sup Orlicz
penalty `ρ_k = whitneyWaveLayerPenalty d m h k`. -/
theorem whitneyWaveLayerPenalty_sq_le (m : ℤ) (hn : ℕ → ℕ) (k : ℕ) :
    whitneyWaveLayerPenalty d m hn k ^ 2 ≤
      whitneyLayerLogConst d * (1 + (k : ℝ) + (hn k : ℝ)) := by
  have hbase : (0 : ℝ) ≤ 3 * max 1 (Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ max 1 (Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ)) :=
      le_max_left _ _
    linarith
  have hrpow : (3 * max 1 (Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ)))
      ^ ((2 : ℝ)⁻¹) =
      Real.sqrt (3 * max 1 (Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ))) := by
    rw [Real.sqrt_eq_rpow, one_div]
  have hsq : whitneyWaveLayerPenalty d m hn k ^ 2 =
      3 * max 1 (Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ)) := by
    rw [whitneyWaveLayerPenalty, hrpow, Real.sq_sqrt hbase]
  rw [hsq]
  exact three_mul_max_one_log_card_whitneyLayer_le m hn k

/-! ## Step 2: the absorption, over abstract reals -/

/-- **The absorption core, degree one.**  `1 + s ≤ (1 + c⁻¹)(1 + c s)`. -/
theorem one_add_le_mul (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) :
    1 + s ≤ (1 + c⁻¹) * (1 + c * s) := by
  have hci : (0 : ℝ) < c⁻¹ := inv_pos.2 hc
  have hcs : (0 : ℝ) ≤ c * s := mul_nonneg hc.le hs
  have hcancel : c⁻¹ * (c * s) = s := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
  have hid : (1 + c⁻¹) * (1 + c * s) = 1 + c * s + c⁻¹ + c⁻¹ * (c * s) := by ring
  rw [hid, hcancel]
  linarith

/-- **The absorption core, squared, with the exponential kept as an ATOM.**  No
`rpow`, no `exp`: only the abstract inequality `(1 + c s)² ≤ A` enters. -/
theorem sq_one_add_le_mul {c s A : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hA : (1 + c * s) ^ 2 ≤ A) : (1 + s) ^ 2 ≤ (1 + c⁻¹) ^ 2 * A := by
  have h1 := one_add_le_mul c s hc hs
  have h0 : (0 : ℝ) ≤ 1 + s := by linarith
  have hsq : (1 + s) * (1 + s) ≤ ((1 + c⁻¹) * (1 + c * s)) * ((1 + c⁻¹) * (1 + c * s)) :=
    mul_le_mul h1 h1 h0 (le_trans h0 h1)
  have hfac : (0 : ℝ) ≤ (1 + c⁻¹) ^ 2 := sq_nonneg _
  calc (1 + s) ^ 2 = (1 + s) * (1 + s) := by ring
    _ ≤ ((1 + c⁻¹) * (1 + c * s)) * ((1 + c⁻¹) * (1 + c * s)) := hsq
    _ = (1 + c⁻¹) ^ 2 * (1 + c * s) ^ 2 := by ring
    _ ≤ (1 + c⁻¹) ^ 2 * A := mul_le_mul_of_nonneg_left hA hfac

/-- **The atom, supplied once.**  `(1 + (ε log 3 / 2) s)² ≤ 3^{ε s}` for
`s ≥ 0`: the square of `1 + u ≤ e^u` at `u = ε s log 3 / 2`. -/
theorem sq_one_add_le_three_rpow {eps s : ℝ} (heps : 0 < eps) (hs : 0 ≤ s) :
    (1 + eps * Real.log 3 / 2 * s) ^ 2 ≤ (3 : ℝ) ^ (eps * s) := by
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set u : ℝ := eps * Real.log 3 / 2 * s with hu
  have hu0 : (0 : ℝ) ≤ u := by
    rw [hu]; positivity
  have hexp : (3 : ℝ) ^ (eps * s) = Real.exp u * Real.exp u := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add, hu]
    congr 1
    ring
  have hle : 1 + u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have h0 : (0 : ℝ) ≤ 1 + u := by linarith
  calc (1 + u) ^ 2 = (1 + u) * (1 + u) := by ring
    _ ≤ Real.exp u * Real.exp u := mul_le_mul hle hle h0 (Real.exp_nonneg u)
    _ = (3 : ℝ) ^ (eps * s) := hexp.symm

/-- The absorption constant `C_ε = (1 + 2(ε log 3)^{-1})²`. -/
def layerAbsorptionConst (eps : ℝ) : ℝ := (1 + (eps * Real.log 3 / 2)⁻¹) ^ 2

theorem layerAbsorptionConst_nonneg (eps : ℝ) : 0 ≤ layerAbsorptionConst eps :=
  sq_nonneg _

/-- **Step (ii).**  `(1+x)(1+x+y) ≤ C_ε 3^{ε(x+y)}` for every `ε > 0` and every
`x, y ≥ 0`: polynomial against exponential, at the honest `C_ε`. -/
theorem one_add_mul_le_layerAbsorptionConst_mul {eps x y : ℝ} (heps : 0 < eps)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1 + x) * (1 + x + y) ≤ layerAbsorptionConst eps * (3 : ℝ) ^ (eps * (x + y)) := by
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) < eps * Real.log 3 / 2 := by positivity
  have hs : (0 : ℝ) ≤ x + y := by linarith
  have hatom := sq_one_add_le_three_rpow (eps := eps) (s := x + y) heps hs
  have hcore := sq_one_add_le_mul (c := eps * Real.log 3 / 2) (s := x + y) hc hs hatom
  have hprod : (1 + x) * (1 + x + y) ≤ (1 + (x + y)) ^ 2 := by
    have h1 : (1 : ℝ) + x ≤ 1 + x + y := by linarith
    have h2 : (0 : ℝ) ≤ 1 + x + y := by linarith
    calc (1 + x) * (1 + x + y) ≤ (1 + x + y) * (1 + x + y) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (1 + (x + y)) ^ 2 := by ring
  calc (1 + x) * (1 + x + y) ≤ (1 + (x + y)) ^ 2 := hprod
    _ ≤ (1 + (eps * Real.log 3 / 2)⁻¹) ^ 2 * (3 : ℝ) ^ (eps * (x + y)) := hcore
    _ = layerAbsorptionConst eps * (3 : ℝ) ^ (eps * (x + y)) := by rw [layerAbsorptionConst]

/-! ## Step 3: the layer envelope, priced into the exponent -/

theorem whitneyWaveCubeScale_nonneg (hd : 2 ≤ d) (M : ABKModel d) (L : ℤ) :
    0 ≤ whitneyWaveCubeScale M L := by
  have hpen : (0 : ℝ) ≤ (3 * max 1 (Real.log ((7 ^ d : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  have hC : (0 : ℝ) ≤ streamLinftyConst d := (streamLinftyConst_pos (by omega)).le
  have hg : (0 : ℝ) ≤ Real.sqrt M.gamma⁻¹ := Real.sqrt_nonneg _
  have hK : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (L : ℝ)) := Real.rpow_nonneg (by norm_num) _
  rw [whitneyWaveCubeScale]
  exact mul_nonneg hpen (mul_nonneg (mul_nonneg hC hg) hK)

theorem whitneyWaveLayerScale_nonneg (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ)
    (k : ℕ) (L : ℤ) : 0 ≤ whitneyWaveLayerScale M m hn k L := by
  have hpen : (0 : ℝ) ≤ whitneyWaveLayerPenalty d m hn k := by
    rw [whitneyWaveLayerPenalty]
    exact Real.rpow_nonneg (by positivity) _
  rw [whitneyWaveLayerScale]
  exact mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg hpen (whitneyWaveCubeScale_nonneg hd M L))

/-- **The layer-free gauge bound the raised-exponent pricing runs at.**  The
root oscillation threshold and the whole layer envelope, combined in one
constant: `Sup₀² = osc_m² + C(d) C_ε A² t²`. -/
def ktotEnvelopeSup (M : ABKModel d) (m L : ℤ) (eps t : ℝ) : ℝ :=
  Real.sqrt (oscThreshold M m ^ 2 +
    whitneyLayerLogConst d * layerAbsorptionConst eps * whitneyWaveCubeScale M L ^ 2 * t ^ 2)


theorem sq_ktotEnvelopeSup (M : ABKModel d) (m L : ℤ) (eps t : ℝ) :
    ktotEnvelopeSup M m L eps t ^ 2 =
      oscThreshold M m ^ 2 +
        whitneyLayerLogConst d * layerAbsorptionConst eps *
          whitneyWaveCubeScale M L ^ 2 * t ^ 2 := by
  refine Real.sq_sqrt ?_
  have h1 : (0 : ℝ) ≤ whitneyLayerLogConst d := (whitneyLayerLogConst_pos d).le
  have h2 : (0 : ℝ) ≤ layerAbsorptionConst eps := layerAbsorptionConst_nonneg eps
  have h3 : (0 : ℝ) ≤ oscThreshold M m ^ 2 := sq_nonneg _
  have h4 : (0 : ℝ) ≤ whitneyLayerLogConst d * layerAbsorptionConst eps *
      whitneyWaveCubeScale M L ^ 2 * t ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg h1 h2) (sq_nonneg _)) (sq_nonneg _)
  linarith

/-- **Steps (i) and (ii), composed on the proved envelope.**  The squared gauge
bound the layer-`k` pricing sees is the layer-free `Sup₀²` times exactly one
factor `3^{ε(k+h_k)}`. -/
theorem sq_max_oscThreshold_whitneyWaveLayerScale_le (M : ABKModel d) (m : ℤ)
    (hn : ℕ → ℕ) (k : ℕ) (L : ℤ) {eps t : ℝ} (heps : 0 < eps) :
    max (oscThreshold M m) (whitneyWaveLayerScale M m hn k L * t) ^ 2 ≤
      ktotEnvelopeSup M m L eps t ^ 2 *
        (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hhR : (0 : ℝ) ≤ (hn k : ℝ) := Nat.cast_nonneg _
  have hE : (1 : ℝ) ≤ (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hE0 : (0 : ℝ) ≤ (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) := by linarith
  -- the envelope square, expanded
  have hnk : (0 : ℝ) ≤ 1 + (k : ℝ) := by linarith
  have hscalesq : (whitneyWaveLayerScale M m hn k L * t) ^ 2 =
      (1 + (k : ℝ)) *
        (whitneyWaveLayerPenalty d m hn k ^ 2 * (whitneyWaveCubeScale M L ^ 2 * t ^ 2)) := by
    rw [whitneyWaveLayerScale]
    have hsq : Real.sqrt (1 + (k : ℝ)) ^ 2 = 1 + (k : ℝ) := Real.sq_sqrt hnk
    calc (Real.sqrt (1 + (k : ℝ)) *
            (whitneyWaveLayerPenalty d m hn k * whitneyWaveCubeScale M L) * t) ^ 2
        = Real.sqrt (1 + (k : ℝ)) ^ 2 *
            (whitneyWaveLayerPenalty d m hn k ^ 2 * (whitneyWaveCubeScale M L ^ 2 * t ^ 2)) := by
          ring
      _ = (1 + (k : ℝ)) *
            (whitneyWaveLayerPenalty d m hn k ^ 2 *
              (whitneyWaveCubeScale M L ^ 2 * t ^ 2)) := by rw [hsq]
  have hAt : (0 : ℝ) ≤ whitneyWaveCubeScale M L ^ 2 * t ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpen := whitneyWaveLayerPenalty_sq_le (d := d) m hn k
  have hstep1 : (whitneyWaveLayerScale M m hn k L * t) ^ 2 ≤
      (1 + (k : ℝ)) *
        (whitneyLayerLogConst d * (1 + (k : ℝ) + (hn k : ℝ)) *
          (whitneyWaveCubeScale M L ^ 2 * t ^ 2)) := by
    rw [hscalesq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpen hAt) hnk
  have habs := one_add_mul_le_layerAbsorptionConst_mul (eps := eps) (x := (k : ℝ))
    (y := (hn k : ℝ)) heps hkR hhR
  have hCA : (0 : ℝ) ≤ whitneyLayerLogConst d * (whitneyWaveCubeScale M L ^ 2 * t ^ 2) :=
    mul_nonneg (whitneyLayerLogConst_pos d).le hAt
  have hstep2 : (1 + (k : ℝ)) *
      (whitneyLayerLogConst d * (1 + (k : ℝ) + (hn k : ℝ)) *
        (whitneyWaveCubeScale M L ^ 2 * t ^ 2)) ≤
      whitneyLayerLogConst d * layerAbsorptionConst eps *
        whitneyWaveCubeScale M L ^ 2 * t ^ 2 *
        (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left habs hCA
    calc (1 + (k : ℝ)) *
          (whitneyLayerLogConst d * (1 + (k : ℝ) + (hn k : ℝ)) *
            (whitneyWaveCubeScale M L ^ 2 * t ^ 2))
        = whitneyLayerLogConst d * (whitneyWaveCubeScale M L ^ 2 * t ^ 2) *
            ((1 + (k : ℝ)) * (1 + (k : ℝ) + (hn k : ℝ))) := by ring
      _ ≤ whitneyLayerLogConst d * (whitneyWaveCubeScale M L ^ 2 * t ^ 2) *
            (layerAbsorptionConst eps *
              (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ)))) := h
      _ = whitneyLayerLogConst d * layerAbsorptionConst eps *
            whitneyWaveCubeScale M L ^ 2 * t ^ 2 *
            (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) := by ring
  have hosc : oscThreshold M m ^ 2 ≤
      oscThreshold M m ^ 2 * (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) :=
    le_mul_of_one_le_right (sq_nonneg _) hE
  have hmax : max (oscThreshold M m) (whitneyWaveLayerScale M m hn k L * t) ^ 2 ≤
      oscThreshold M m ^ 2 + (whitneyWaveLayerScale M m hn k L * t) ^ 2 := by
    rcases le_total (oscThreshold M m) (whitneyWaveLayerScale M m hn k L * t) with h | h
    · rw [max_eq_right h]
      linarith [sq_nonneg (oscThreshold M m)]
    · rw [max_eq_left h]
      linarith [sq_nonneg (whitneyWaveLayerScale M m hn k L * t)]
  rw [sq_ktotEnvelopeSup]
  have hsum : (oscThreshold M m ^ 2 +
      whitneyLayerLogConst d * layerAbsorptionConst eps *
        whitneyWaveCubeScale M L ^ 2 * t ^ 2) *
      (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) =
      oscThreshold M m ^ 2 * (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) +
        whitneyLayerLogConst d * layerAbsorptionConst eps *
          whitneyWaveCubeScale M L ^ 2 * t ^ 2 *
          (3 : ℝ) ^ (eps * ((k : ℝ) + (hn k : ℝ))) := by ring
  rw [hsum]
  linarith [hmax, hosc, hstep1, hstep2]

/-- The affine core of the layer-constant comparison: `ktotConst` is affine in
`Sup²` with nonnegative coefficients. -/
private theorem affine_sq_le_mul {c1 c2 kap S1 S2 Eatom : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hkap : 0 ≤ kap) (hE : 1 ≤ Eatom) (hsq : S1 ^ 2 ≤ S2 ^ 2 * Eatom) :
    c1 * (1 + kap * S1 ^ 2) + c2 ≤ (c1 * (1 + kap * S2 ^ 2) + c2) * Eatom := by
  have h1 : c1 * (kap * S1 ^ 2) ≤ c1 * (kap * (S2 ^ 2 * Eatom)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hkap) hc1
  have h2 : c1 ≤ c1 * Eatom := le_mul_of_one_le_right hc1 hE
  have h3 : c2 ≤ c2 * Eatom := le_mul_of_one_le_right hc2 hE
  linarith [h1, h2, h3]

/-- **The layer constant at a dominated gauge.**  If the layer's own squared
gauge bound is at most `S2²` times an atom `Eatom ≥ 1`, then the layer constant
is at most the layer-free one times that atom. -/
theorem ktotConst_le_mul (hd : 2 ≤ d) (M : ABKModel d) (m i : ℤ) {Cw : ℝ} (hCw : 0 ≤ Cw)
    {S1 S2 Eatom : ℝ} (hE : 1 ≤ Eatom) (hsq : S1 ^ 2 ≤ S2 ^ 2 * Eatom) (p q : Vec d) :
    ktotConst M m i Cw S1 p q ≤ ktotConst M m i Cw S2 p q * Eatom := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hA : (0 : ℝ) ≤ simplexCrudeConst d (1 / 4) := simplexCrudeConst_nonneg d (by norm_num)
  have hBL : (0 : ℝ) ≤ bigLambdaSensitivityConst d := (bigLambdaSensitivityConst_pos hd).le
  have hcs : (0 : ℝ) ≤ (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    inv_nonneg.2 (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
  have hX : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hY : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (m : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hP : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hQ : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hkap : (0 : ℝ) ≤ 8 * bigLambdaSensitivityConst d *
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
      (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hcs) hg.le) hX
  have hc1 : (0 : ℝ) ≤ 640 * simplexCrudeConst d (1 / 4) * Cw * vecNormSq p :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hCw) hP
  have hc2 : (0 : ℝ) ≤ 320 * simplexCrudeConst d (1 / 4) * Cw *
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (m : ℝ))) * vecNormSq q :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hCw) hY) hQ
  have h := affine_sq_le_mul hc1 hc2 hkap hE hsq
  rw [ktotConst, ktotConst]
  linarith [h]

/-! ## The good leg at the layer envelope -/

/-- **The good leg priced against a layer-dependent gauge bound.**
`ConclusionKtot.goodCellForm_le_ktotConst_mul_ae` with its single real `Swave`
replaced by a sequence `Sc` read at the cube's own layer.  The proof is the
consumed one: the pricing `stepOneLayerMajorant_le_ktotConst_mul` is per-cube,
and a layer cube's gauge bound is used only at its own layer index. -/
theorem goodCellForm_le_ktotConst_mul_layerScale_ae (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) (hn : ℕ → ℕ)
    {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0) {L : ℤ} (hmL : m ≤ L) (p q : Vec d)
    {Cw : ℝ} {Sc : ℕ → ℝ} (hSc0 : ∀ n : ℕ, 0 ≤ Sc n) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
          Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) ≤ Cw) →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
          cubeSupBound Q Q.scale L omega.1 ≤ Sc n) →
      ∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
        ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
          goodCellForm M m hn L omega
              ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
              (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q) T ≤
            ktotConst M m i Cw (max (oscThreshold M m) (Sc n)) p q *
              (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (hn n : ℝ))) := by
  classical
  filter_upwards [goodCellForm_le_stepOneLayerMajorant_ae hd M hS m hn hmi hi]
    with omega hbase hCw hSwave n Q hQ T hT
  have hscale : Q.scale = m - (n : ℤ) - (hn n : ℤ) := scale_eq_of_mem_whitneyLayer hQ
  have hQm : Q.scale ≤ m := by rw [hscale]; omega
  have hQL : Q.scale ≤ L := le_trans hQm hmL
  have hCw0 : (0 : ℝ) ≤ Cw :=
    le_trans (multiscaleDescendantWeight_nonneg Q (simplexScale m hn n) (1 / 4))
      (hCw n Q hQ)
  have hSup0 : (0 : ℝ) ≤ max (oscThreshold M m) (Sc n) :=
    le_trans (hSc0 n) (le_max_right _ _)
  by_cases hbad : Q ∈ badFamily M m hn omega
  · have hcube : whitneyCubeOf m hn T = Q :=
      whitneyCubeOf_of_mem_whitneySimplexCells hQ hT
    have hzero : notBadIndicator M m hn omega T = 0 :=
      notBadIndicator_of_bad (by rw [hcube]; exact hbad)
    rw [goodCellForm, hzero, mul_zero]
    exact mul_nonneg (ktotConst_nonneg hd M m i hCw0 _ p q)
      (Real.rpow_nonneg (by norm_num) _)
  · have hnb : omega ∉ BadEvents.bad M Q := fun h => hbad ⟨⟨n, hQ⟩, h⟩
    have hosc : omega ∉ badOsc M Q := fun h => hnb (Or.inl h)
    have hw : (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ≤
        max (oscThreshold M m) (Sc n) :=
      le_trans (w1Infinity_incrementUnitCube₂_le_max_oscThreshold M Q hosc hQL)
        (max_le_max (oscThreshold_mono M hQm) (hSwave n Q hQ))
    exact le_trans (hbase n Q hQ L hQL T hT p q)
      (stepOneLayerMajorant_le_ktotConst_mul hd M m hn n i L omega hQ p q
        (hCw n Q hQ) hSup0 hw)

/-- **Step (iii): the `hgood` binder body at the raised exponent `2γ + ε`.** The
good leg, at the honest layer envelope of `ConclusionData` and at the
descendant weight `Cw := 3`, is bounded by a layer-free constant times
`3^{(2γ+ε)(k+h_k)}`.  See the module docstring for the composer's gate `8
M.gamma + 4 ε ≤ 1 − b`. -/
theorem goodCellForm_le_ktotEnvelopeConst_mul_layerQuantity_ae (hd : 2 ≤ d) (M : ABKModel d)
    {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hs k₀ : ℕ) {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0)
    {L : ℤ} (hmL : m ≤ L) (p q : Vec d) {eps : ℝ} (heps : 0 < eps) {t : ℝ}
    (ht0 : 0 ≤ t) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
          cubeSupBound Q Q.scale L omega.1 ≤
            whitneyWaveLayerScale M m (whitneyScaleSeq b hs k₀) n L * t) →
      ∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
        ∀ T ∈ whitneySimplexCells (d := d) m (whitneyScaleSeq b hs k₀) n Q,
          goodCellForm M m (whitneyScaleSeq b hs k₀) L omega
              ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
              (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q) T ≤
            ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q *
              (3 : ℝ) ^ ((2 * M.gamma + eps) * layerQuantity b hs k₀ n) := by
  have hSc0 : ∀ n : ℕ, 0 ≤ whitneyWaveLayerScale M m (whitneyScaleSeq b hs k₀) n L * t :=
    fun n => mul_nonneg
      (whitneyWaveLayerScale_nonneg hd M m (whitneyScaleSeq b hs k₀) n L) ht0
  filter_upwards [goodCellForm_le_ktotConst_mul_layerScale_ae hd M hS m
    (whitneyScaleSeq b hs k₀) hmi hi hmL p q (Cw := 3) hSc0] with omega hbase hSwave n Q hQ T hT
  have hstep := hbase (multiscaleDescendantWeight_whitneyScaleSeq_le_three hb0 hb hs k₀ m)
    hSwave n Q hQ T hT
  have hkR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hhR : (0 : ℝ) ≤ ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE : (1 : ℝ) ≤ (3 : ℝ) ^ (eps * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ))) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hsq := sq_max_oscThreshold_whitneyWaveLayerScale_le M m (whitneyScaleSeq b hs k₀) n L
    (eps := eps) (t := t) heps
  have hconst := ktotConst_le_mul hd M m i (Cw := 3) (by norm_num) hE hsq p q
  have hZ : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hmerge : (3 : ℝ) ^ (eps * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ))) *
      (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ))) =
      (3 : ℝ) ^ ((2 * M.gamma + eps) * layerQuantity b hs k₀ n) := by
    rw [← Real.rpow_add (by norm_num), layerQuantity]
    congr 1
    ring
  calc goodCellForm M m (whitneyScaleSeq b hs k₀) L omega
          ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
          (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q) T
      ≤ ktotConst M m i 3
          (max (oscThreshold M m)
            (whitneyWaveLayerScale M m (whitneyScaleSeq b hs k₀) n L * t)) p q *
          (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ))) := hstep
    _ ≤ ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q *
          (3 : ℝ) ^ (eps * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ))) *
          (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right hconst hZ
    _ = ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q *
          ((3 : ℝ) ^ (eps * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ))) *
            (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ)))) := by
          ring
    _ = ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q *
          (3 : ℝ) ^ ((2 * M.gamma + eps) * layerQuantity b hs k₀ n) := by rw [hmerge]


end

end Algsuperdiff.Section3.Provider.Multiscale
