/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionKtot
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam3

/-!
# ConclusionData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Local providers for three named data of the `p.bfA.multiscalebound` conclusion

`Provider/Multiscale/ConclusionKtot.lean` and
`Provider/Multiscale/ConclusionSeam3.lean` land the two remaining analytic
inputs of the concluding assembly and leave exactly three data open, named
in their own docstrings: the descendant-weight bound `Cw`, the transported wave
gauge bound `Swave`, and the seam-3 shell envelope `hA`.  This module proves
local Provider results for two of those A antecedents and replaces the third by
the strongest statement its own route supports.  It does not close the source
conclusion or any fraction of it.

## 1. The local `Cw = 3` result

On `𝒲(□_m,k)` one has `□.scale = m − k − h_k` and
`simplexScale m h k = m − (k+1) − h_{k+1}`, so

```
multiscaleDescendantWeight □ (simplexScale m h k) (1/4)
    = 3^{2·(1/4)·(1 + h_{k+1} − h_k)} = 3^{(1 + h_{k+1} − h_k)/2} .
```

`multiscaleDescendantWeight_eq_of_mem_whitneyLayer` is this identity.  The gap
step of `e.hn.gap` ((the label line — the development convention, restored),
`h_{k+1} ≤ h_k + 1`) is proved for the Whitney sequence as
`Whitney.whitneyScaleSeq_succ_le` (`b ≤ 1/8`), so the exponent is at most `1`
and the weight at most `3^1 = 3`, uniformly over the layers and over the cubes
of a layer.  `ConclusionKtot`'s docstring records that `e.SW.def`'s `hstep`
binder carried by `Provider/Whitney/SimplexPartition.lean` is the opposite
inequality `h_k ≤ h_{k+1} + 1` and therefore does not discharge this; the gap
lemma used here is a different, proved statement about the sequence itself,
read in the same direction.
`multiscaleDescendantWeight_whitneyScaleSeq_le_three` is literally the `hCw` binder
of `ConclusionKtot.goodCellForm_le_ktotConst_mul_layerQuantity_ae` at `Cw :=
3`, and `goodCellForm_le_ktotConst_three_mul_layerQuantity_ae` is that consumer
with the datum discharged --- so the fit is machine-checked, not asserted.

## 2. The local `hA` envelope

`streamIncrementLpMassScale M p n m` depends on `n` only through `min{γ^{-1/2},
(m−n)^{1/2}}` inside `streamPointScale`, which is ANTITONE in `n`: a deeper
shell index can only enlarge the `e.kmn.bounds` scale, and the growth saturates
at the `γ`-entry.  `streamPointScale_le_of_le` and
`streamIncrementLpMassScale_le_of_le` record this, and
`seamLayerScale_le_of_le` is the resulting envelope over `h ≤ H` in the exact
shape of the `hA` binder of
`ConclusionSeam3.measureReal_upperTailEvent_seamLayerObject_hsep_le`: the
common scale is the proved deterministic-index scale read at the D index `h =
H`, so it is not a new constant and carries no new hypothesis.
`measureReal_upperTailEvent_seamLayerObject_hsep_envelope_le` is the seam-3
conclusion with that datum discharged; it has no interface datum left.

## 3. `Swave` (no constant; an honest layer envelope only)

`ConclusionKtot` prices the transported gauge `Stream.cubeSupBound` inside ONE
layer at `Γ₂`, at the scale

```
ρ_k · A ,    ρ_k = (3 max{1, log #𝒲(□_m,k)})^{1/2} ,
A   = (3 max{1, log 7^d})^{1/2} · C_d · γ^{-1/2} · 3^{γL} ,
```

and asks for a single real `Swave` dominating the gauge on ALL layers at once.
Two facts about the proved inputs bear on that request, and both are proved or
computed here rather than asserted.

* The per-cube amplitude is layer-free.  At `n = □.scale` the covering family of
  `e.km.kn.Linfty` has `(subcubeShifts d n n).card = 7^d` members at every
  scale (`card_subcubeShifts_self`; `subcubeRadius n n = 3`), and
  `min{γ^{-1/2}, (L − □.scale)^{1/2}} ≤ γ^{-1/2}` caps the only other
  scale-dependent factor.  `whitneyWaveCubeScale` is the resulting layer-free
  amplitude and
  `isBigOWith_gammaSigma_two_layerSup_cubeSupBound_whitneyWaveCubeScale` is the
  layer maximum at it.
* The penalty `ρ_k` is NOT bounded in `k`.  The layers are the literal infinite
  family (`whitneyPartition` is a `Set`, not a `Finset`); every layer `k ≥ 1`
  is nonempty and `#𝒲(□_m,k)` grows with `k`, so the `Γ₂` scales of the layer
  maxima are unbounded.  This module therefore does NOT produce a constant
  `Swave`, and nothing below claims one exists.

What IS produced is the all-layer aggregation with the amplification the union
bound actually pays.  `measureReal_exists_cubeSupBound_gt_le`: for every
`t ≥ 1`,

```
P[ ∃ k, ∃ □ ∈ 𝒲(□_m,k) :  the dominating gauge cubeSupBound (≥ ‖k_L − k_{□.scale}‖_{L^∞(□)}; audit
#29 F-11) > (1+k)^{1/2} ρ_k A t ]
      ≤ 2 e^{−t²} = 2 (Γ₂ t)^{-1} ,
```

because the `k`-th piece costs `exp(−(1+k)t²)` and the geometric series is at
most `2 e^{−t²}` for `t ≥ 1` (`exp 1 ≥ 2`).  Only monotonicity, finite
subadditivity and continuity from below are used: no independence, no
measurability of the union and no identification across samples (discipline is
inherited unchanged, since every per-layer estimate is the proved one).
`one_sub_le_measureReal_forall_ cubeSupBound_le` is the complementary reading,
which is the `hSwave` binder of the good leg with its single constant replaced
by the layer envelope `whitneyWaveLayerScale M m h k L · t`, on an event of
probability at least `1 − 2 e^{−t²}`.

The amplification is in `k` (`(1+k)^{1/2} ρ_k`, with `ρ_k² = 3 max{1, log
#𝒲(□_m,k)}`), while the payload of
`ConclusionRoot.tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload` reads
its two legs at the geometric weight `3^{γ · layerQuantity}` in `k + h_k`; the
remaining distance is therefore an arithmetic re-absorption, spelled out in
"What is not proved".

## What is *not* proved

* **No constant `Swave`, and no claim that one exists.**  The obstruction above
  is an analysis of the proved scales, not a theorem: this module proves no
  lower bound on any layer maximum and asserts no divergence.  What it does
  assert is that the route through the proved per-layer `Γ₂` estimates cannot
  produce one, which is why the consumer's binder is the thing that must move.
* **The good leg is NOT restated at the layer envelope.**  Feeding
  `whitneyWaveLayerScale` into `stepOneLayerMajorant_le_ktotConst_mul` makes
  the constant `k`-dependent through `Sup²`, so the payload exponent must rise
  from `2γ` to `2γ + ε`.  That needs (i) the logarithm of the already proved
  cardinality bound `LayerMass.card_whitneyLayer_le` (`#𝒲(□_m,k) ≤
  2d·(3^{d−1})^{k−1}·(3^d)^{1+h_k}`, giving `ρ_k² ≤ C(d)·(1 + k + h_k)`), (ii)
  the elementary `(1+k)·(1+k+h_k) ≤ C_ε 3^{ε(k+h_k)}`, and (iii) a restatement
  of the good leg at the raised exponent, with the parameter window
  `4(2γ+ε) ≤ 1 − b`.  None of the three is done in this module; all three are
  carried out in `ConclusionKtotEnvelope.lean`, whose endpoint is
  `goodCellForm_le_ktotEnvelopeConst_mul_layerQuantity_ae`.
* **No monotonicity of `streamIncrementLpMassScale` in `p`, `m` or the cube**,
  and no re-basing onto the cube-averaged `L⁴` norm: only the shell-index
  direction is proved, which is all `hA` needs.

## Main definitions

* `Algsuperdiff.Section3.Provider.Multiscale.whitneyWaveCubeScale`
* `Algsuperdiff.Section3.Provider.Multiscale.whitneyWaveLayerPenalty`
* `Algsuperdiff.Section3.Provider.Multiscale.whitneyWaveLayerScale`

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.multiscaleDescendantWeight_whitneyScaleSeq_le_three`
* `Algsuperdiff.Section3.Provider.Multiscale.card_subcubeShifts_self`
* `Algsuperdiff.Section3.Provider.Multiscale.`
  `isBigOWith_gammaSigma_two_layerSup_cubeSupBound_whitneyWaveCubeScale`
* `Algsuperdiff.Section3.Provider.Multiscale.measureReal_exists_cubeSupBound_gt_le`

## References

* ABK26, `p.bfA.multiscalebound` Step 1 (majorant) and Step 3; `e.hn.def` /
  `e.hn.gap`; `e.SW.def`; `e.km.kn.Linfty`; `e.kmn.bounds`;
  `l.maximums.Gamma.s`; `e.hsep.tails`.
* `Provider/Multiscale/ConclusionKtot.lean` and
  `Provider/Multiscale/ConclusionSeam3.lean` (the two consumers),
  `Provider/Whitney/BadSetDefinitions.lean` (the Whitney sequence and layers),
  `Provider/Stream/IncrementLp.lean` (the `e.kmn.bounds` scale),
  `Provider/Stream/WaveTranslation.lean` (the transported gauge).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## `Cw`: the descendant weight along the Whitney layers -/

/-- **The descendant weight of a layer cube is `3^{(1 + h_{k+1} − h_k)/2}`.**
On `𝒲(□_m,k)` one has `□.scale = m − k − h_k` and the simplex scale is
`m − (k+1) − h_{k+1}`, so the exponent of
`Ch02.multiscaleDescendantWeight □ (simplexScale m h k) (1/4)` is
`2·(1/4)·(1 + h_{k+1} − h_k)`. -/
theorem multiscaleDescendantWeight_eq_of_mem_whitneyLayer (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer (d := d) m hn n) :
    Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) =
      (3 : ℝ) ^ ((1 + (hn (n + 1) : ℝ) - (hn n : ℝ)) / 2) := by
  rw [Ch02.multiscaleDescendantWeight, scale_eq_of_mem_whitneyLayer hQ, simplexScale]
  congr 1
  push_cast
  ring

/-- **The uniform bound `Cw = 3`.**  With the `e.hn.gap` step `h_{k+1} ≤ h_k + 1`
the exponent is at most `1`, so the descendant weight of every layer cube is at
most `3^{(1+1)/2} = 3`. -/
theorem multiscaleDescendantWeight_le_three_of_mem_whitneyLayer (m : ℤ) (hn : ℕ → ℕ)
    (n : ℕ) (hgap : hn (n + 1) ≤ hn n + 1) {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer (d := d) m hn n) :
    Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) ≤ 3 := by
  rw [multiscaleDescendantWeight_eq_of_mem_whitneyLayer m hn n hQ]
  have hgapR : (hn (n + 1) : ℝ) ≤ (hn n : ℝ) + 1 := by exact_mod_cast hgap
  have hexp : (1 + (hn (n + 1) : ℝ) - (hn n : ℝ)) / 2 ≤ 1 := by linarith
  calc (3 : ℝ) ^ ((1 + (hn (n + 1) : ℝ) - (hn n : ℝ)) / 2)
      ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 3 := Real.rpow_one 3

/-- **`Cw := 3`, in the exact binder shape the good leg's descendant-weight
hypothesis has** (the `hCw` binder of
`ConclusionKtotEnvelope.goodCellForm_le_ktotConst_mul_layerScale_ae`).  The
Whitney sequence
`h_k = ⌈b(1−b)⁻¹k⌉ + h_hat_sep + k₀` satisfies `e.hn.gap` for `b ≤ 1/8`
(`whitneyScaleSeq_succ_le`), so its descendant weights are bounded by `3`
uniformly over the layers and over the cubes of each layer. -/
theorem multiscaleDescendantWeight_whitneyScaleSeq_le_three {b : ℝ} (hb0 : 0 < b)
    (hb : b ≤ 1 / 8) (hs k₀ : ℕ) (m : ℤ) :
    ∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
      Ch02.multiscaleDescendantWeight Q
        (simplexScale m (whitneyScaleSeq b hs k₀) n) (1 / 4) ≤ 3 :=
  fun n _ hQ =>
    multiscaleDescendantWeight_le_three_of_mem_whitneyLayer m (whitneyScaleSeq b hs k₀) n
      (whitneyScaleSeq_succ_le hb0 hb hs k₀ n) hQ


/-! ## `hA`: the shell-index envelope of the seam-3 scales -/


/-! ## `Swave`: the transported wave gauge, aggregated over all layers -/

/-- The covering family of a cube at its OWN scale has `7^d` members, at every
scale: `subcubeRadius n n = 3`. -/
theorem card_subcubeShifts_self (d : ℕ) (n : ℤ) :
    (subcubeShifts d n n).card = 7 ^ d := by
  rw [card_subcubeShifts, subcubeRadius]
  norm_num

/-- **The layer-free per-cube amplitude of the transported wave gauge.**  The
amplitude of `Stream.isBigOWith_gammaSigma_cubeSupBound_cutoffLaw` at
`n = □.scale`, with the covering count evaluated (`7^d`, independent of the
scale) and the `min` capped by its `γ`-entry, so that nothing depends on the
layer. -/
def whitneyWaveCubeScale (M : ABKModel d) (L : ℤ) : ℝ :=
  (3 * max 1 (Real.log ((7 ^ d : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
    (streamLinftyConst d * Real.sqrt M.gamma⁻¹ * (3 : ℝ) ^ (M.gamma * (L : ℝ)))

/-- The `l.maximums.Gamma.s` penalty of the layer `𝒲(□_m,k)`. -/
def whitneyWaveLayerPenalty (d : ℕ) (m : ℤ) (hn : ℕ → ℕ) (k : ℕ) : ℝ :=
  (3 * max 1 (Real.log (((whitneyLayer (d := d) m hn k).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹

/-- **The honest layer envelope of the wave gauge.**  The `Γ₂` scale of the
layer-`k` maximum, amplified by `(1+k)^{1/2}`; the amplification is what makes
the countable aggregation over the layers summable. -/
def whitneyWaveLayerScale (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (k : ℕ) (L : ℤ) : ℝ :=
  Real.sqrt (1 + (k : ℝ)) * (whitneyWaveLayerPenalty d m hn k * whitneyWaveCubeScale M L)

/-- The layer maximum of the transported gauge at the layer-free amplitude: the covering
count is evaluated and the `min` is capped, so only the log-cardinality penalty
of the layer remains `k`-dependent. -/
theorem isBigOWith_gammaSigma_two_layerSup_cubeSupBound_whitneyWaveCubeScale (hd : 2 ≤ d)
    (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) {n : ℕ}
    (hne : (whitneyLayer (d := d) m hn n).Nonempty) {L : ℤ}
    (hL : m - (n : ℤ) - (hn n : ℤ) < L) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : CutoffSample d =>
        (whitneyLayer (d := d) m hn n).sup' hne fun Q =>
          cubeSupBound Q (m - (n : ℤ) - (hn n : ℤ)) L omega.1)
      (whitneyWaveLayerPenalty d m hn n * whitneyWaveCubeScale M L) := by
  refine (isBigOWith_gammaSigma_two_layerSup_cubeSupBound_cutoffLaw hd M m hn hne
    hL).mono_scale ?_
  have hpen : (0 : ℝ) ≤ (3 * max 1 (Real.log (((whitneyLayer (d := d) m hn n).card : ℕ) : ℝ)))
      ^ (2 : ℝ)⁻¹ := Real.rpow_nonneg (by positivity) _
  have hpen7 : (0 : ℝ) ≤ (3 * max 1 (Real.log ((7 ^ d : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  have hC : (0 : ℝ) ≤ streamLinftyConst d := (streamLinftyConst_pos (by omega)).le
  have hK : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (L : ℝ)) := Real.rpow_nonneg (by norm_num) _
  rw [whitneyWaveLayerPenalty, whitneyWaveCubeScale, card_subcubeShifts_self]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hpen7) hpen
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hC) hK

/-- **The wave gauge over ALL layers, priced.**  For every `t ≥ 1`, the probability
that SOME Whitney cube of SOME layer violates its own layer envelope at level `t` is at
most `2 e^{-t²}`:

```
P[ ∃ k, ∃ □ ∈ 𝒲(□_m,k),  the dominating gauge cubeSupBound (≥ ‖k_L − k_{□.scale}‖_{L^∞(□)}) >
(1+k)^{1/2} ρ_k A t ]
      ≤ 2 (Γ₂ t)^{-1} ,
```

with `ρ_k = (3 max{1, log #𝒲(□_m,k)})^{1/2}` the layer penalty of
`l.maximums.Gamma.s` and `A = whitneyWaveCubeScale M L` the layer-free per-cube
amplitude of `e.km.kn.Linfty`.  The `(1+k)^{1/2}` amplification is exactly what
makes the countable union over the layers summable: the `k`-th piece costs
`e^{-(1+k)t²}` and the geometric series is bounded by `2 e^{-t²}` for `t ≥ 1`.
No independence and no measurability of the union is used: the estimate is a
countable union bound over the proved per-layer maxima. -/
theorem measureReal_exists_cubeSupBound_gt_le (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ)
    (hn : ℕ → ℕ) {L : ℤ} (hmL : m ≤ L) {t : ℝ} (ht : 1 ≤ t) :
    (cutoffSampleLaw M).toMeasure.real
        {omega : CutoffSample d | ∃ k : ℕ, ∃ Q ∈ whitneyLayer (d := d) m hn k,
          whitneyWaveLayerScale M m hn k L * t < cubeSupBound Q Q.scale L omega.1} ≤
      2 * (IndependentSums.gammaSigma 2 t)⁻¹ := by
  classical
  set q : ℝ := Real.exp (-(t ^ 2)) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; exact Real.exp_pos _
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hq2 : q ≤ 1 / 2 := by
    have h1 : Real.exp (-(t ^ 2)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h3 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h4 : (Real.exp 1)⁻¹ * Real.exp 1 = 1 := inv_mul_cancel₀ (ne_of_gt h3)
    have h5 : (0 : ℝ) < (Real.exp 1)⁻¹ := inv_pos.2 h3
    rw [h2] at h1
    rw [hqdef]
    nlinarith [h1, h4, h5, hexp1]
  have hqgamma : (IndependentSums.gammaSigma 2 t)⁻¹ = q := by
    simp only [IndependentSums.gammaSigma, hqdef]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← Real.exp_neg]
  set E : ℕ → Set (CutoffSample d) := fun k =>
    {omega : CutoffSample d | ∃ Q ∈ whitneyLayer (d := d) m hn k,
      whitneyWaveLayerScale M m hn k L * t < cubeSupBound Q Q.scale L omega.1} with hEdef
  have hEk : ∀ k : ℕ, (cutoffSampleLaw M).toMeasure.real (E k) ≤ q ^ (k + 1) := by
    intro k
    have hnn : (0 : ℝ) ≤ 1 + (k : ℝ) := by positivity
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + (k : ℝ)) := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + (k : ℝ) by
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith)
      rwa [Real.sqrt_one] at h
    have hpow : (IndependentSums.gammaSigma 2 (Real.sqrt (1 + (k : ℝ)) * t))⁻¹ =
        q ^ (k + 1) := by
      have hsq : (Real.sqrt (1 + (k : ℝ)) * t) ^ (2 : ℝ) = (1 + (k : ℝ)) * t ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow,
          Real.sq_sqrt hnn]
      simp only [IndependentSums.gammaSigma]
      rw [hsq, ← Real.exp_neg, hqdef, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    by_cases hne : (whitneyLayer (d := d) m hn k).Nonempty
    · have hk1 : 1 ≤ k := by
        obtain ⟨Q, hQ⟩ := hne
        exact (mem_whitneyLayer_iff.mp hQ).1
      have hscaleL : m - (k : ℤ) - (hn k : ℤ) < L := by
        have hh : (0 : ℤ) ≤ (hn k : ℤ) := Int.natCast_nonneg _
        have hkZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
        omega
      have hs1 : (1 : ℝ) ≤ Real.sqrt (1 + (k : ℝ)) * t := by nlinarith [hsqrt1, ht]
      have hbase := isBigOWith_gammaSigma_two_layerSup_cubeSupBound_whitneyWaveCubeScale hd M m hn
        hne hscaleL hs1
      have hprod : whitneyWaveLayerScale M m hn k L * t =
          whitneyWaveLayerPenalty d m hn k * whitneyWaveCubeScale M L *
            (Real.sqrt (1 + (k : ℝ)) * t) := by
        rw [whitneyWaveLayerScale]
        ring
      have hEeq : E k = IndependentSums.upperTailEvent
          (fun omega : CutoffSample d =>
            (whitneyLayer (d := d) m hn k).sup' hne fun Q =>
              cubeSupBound Q (m - (k : ℤ) - (hn k : ℤ)) L omega.1)
          (whitneyWaveLayerPenalty d m hn k * whitneyWaveCubeScale M L *
            (Real.sqrt (1 + (k : ℝ)) * t)) := by
        ext omega
        simp only [hEdef, Set.mem_ofPred_eq, IndependentSums.mem_upperTailEvent,
          Finset.lt_sup'_iff, hprod]
        constructor
        · rintro ⟨Q, hQ, hlt⟩
          exact ⟨Q, hQ, by rwa [scale_eq_of_mem_whitneyLayer hQ] at hlt⟩
        · rintro ⟨Q, hQ, hlt⟩
          exact ⟨Q, hQ, by rwa [scale_eq_of_mem_whitneyLayer hQ]⟩
      rw [hEeq, ← hpow]
      exact hbase
    · have hempty : E k = (∅ : Set (CutoffSample d)) := by
        ext omega
        simp only [hEdef, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨Q, hQ, -⟩
        exact hne ⟨Q, hQ⟩
      rw [hempty, measureReal_empty]
      positivity
  have hgeom : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), q ^ k ≤ (1 - q)⁻¹ := by
    intro N
    have hsum := (summable_geometric_of_lt_one hq0.le (by linarith)).sum_le_tsum
      (Finset.range (N + 1)) fun i _ => pow_nonneg hq0.le i
    rwa [tsum_geometric_of_lt_one hq0.le (by linarith)] at hsum
  have hinv2 : (1 - q)⁻¹ ≤ 2 := by
    have hpos : (0 : ℝ) < 1 - q := by linarith
    have h4 : (1 - q)⁻¹ * (1 - q) = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    have h5 : (0 : ℝ) < (1 - q)⁻¹ := inv_pos.2 hpos
    nlinarith [h4, h5, hpos]
  have hfin : ∀ N : ℕ, (cutoffSampleLaw M).toMeasure.real
      (⋃ k ∈ Finset.range (N + 1), E k) ≤ 2 * q := by
    intro N
    calc (cutoffSampleLaw M).toMeasure.real (⋃ k ∈ Finset.range (N + 1), E k)
        ≤ ∑ k ∈ Finset.range (N + 1), (cutoffSampleLaw M).toMeasure.real (E k) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range (N + 1), q ^ (k + 1) :=
          Finset.sum_le_sum fun k _ => hEk k
      _ = q * ∑ k ∈ Finset.range (N + 1), q ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ q * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left (hgeom N) hq0.le
      _ ≤ 2 * q := by nlinarith [hinv2, hq0]
  have hmono : Monotone fun N : ℕ => ⋃ k ∈ Finset.range (N + 1), E k := by
    intro N N' hNN' x hx
    simp only [Set.mem_iUnion, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, hxk⟩ := hx
    exact ⟨k, by omega, hxk⟩
  have hunion : (⋃ N : ℕ, ⋃ k ∈ Finset.range (N + 1), E k) = ⋃ k, E k := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨_, k, _, hxk⟩
      exact ⟨k, hxk⟩
    · rintro ⟨k, hxk⟩
      exact ⟨k, k, by omega, hxk⟩
  have hb : ∀ N : ℕ, (cutoffSampleLaw M).toMeasure (⋃ k ∈ Finset.range (N + 1), E k) ≤
      ENNReal.ofReal (2 * q) := fun N =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 (hfin N)
  have hmeasure : (cutoffSampleLaw M).toMeasure (⋃ k, E k) ≤ ENNReal.ofReal (2 * q) := by
    rw [← hunion, hmono.measure_iUnion]
    exact iSup_le hb
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal (by positivity)] at htoReal
  have hset : {omega : CutoffSample d | ∃ k : ℕ, ∃ Q ∈ whitneyLayer (d := d) m hn k,
      whitneyWaveLayerScale M m hn k L * t < cubeSupBound Q Q.scale L omega.1} = ⋃ k, E k := by
    ext omega
    simp only [hEdef, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset, hqgamma]
  exact htoReal


end

end Algsuperdiff.Section3.Provider.Multiscale
