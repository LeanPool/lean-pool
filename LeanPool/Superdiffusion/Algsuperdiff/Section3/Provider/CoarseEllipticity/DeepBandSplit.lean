/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveThirdTerm
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.WaveBandMean

/-!
# DeepBandSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `k₀`-deep band mean split, at the proved volume-normalized `L^p` carrier

`WaveBandMean.lean` supplies the arithmetic half of that resolution (the mean's
size, and its absorption into the frozen `Ccg`).  This module supplies the
**carrier half**: on the repository's own volume-normalized `L^p` increment
norm it puts the deterministic head of the split in closed form, and names the
amplitude at which that head enters the `waveBandMean` shape.

## The split

For the wave increment `k_L - k_ell` on the origin cube `cu_l`, split at the
band anchor `a = ell + k₀`:

```
  ‖k_L − k_ell‖_{L^p(cu_l)}
      ≤ head(ell, a)^{1/p}                        (deterministic: a NUMBER)
        + ‖k_L − k_a‖_{L^p(cu_l)}                 (the re-indexed wave term)
        + tail(ell, a)^{1/p},                      𝒪_{Γ₂}(gainScale^{1/p}) .
```

Both inputs are proved here and are consumed unchanged:

* the head-plus-gain estimate
  `Provider.Stream.streamIncrementLpNorm_head_tail_gain` (`e.kl.bounds.large`,
  corrected), whose head `streamIncrementLpMassHead` is the deterministic
  `(C(d) p)^{p/2} A^{p/2}` and whose tail is `Γ₂` at
  `streamIncrementLpGainScale`.

## Both ingredients of the split are available here

Both are present at this volume-normalized carrier:

* the sharp Minkowski at constant `1` for the volume-normalized carrier is
  `streamIncrementLpNorm_add_le`;

## What is proved here

* `streamIncrementLpMassHead_rpow_inv` --- the head's `p`-th root in closed form,
  `C_mom · streamPointScale · p^{1/2}`.
* `deepBandAmplitude` --- the resulting `C(d, p)` amplitude of the band mean.
  It is **not** a bare numeral: at this repository's carrier the head's constant
  is a genuine `C(d, p)`, and the frozen `Ccg` is dimension-only, so this is
  exactly the class the deterministic slot admits.
* `deepBandAmplitude_nonneg` --- that amplitude is nonnegative, which is what
  the `waveBandMean` arithmetic of `WaveBandMean.lean` asks of it.

## References

* ABK26, `e.kl.bounds.large`; `e.km.kn.Lp`; the `L⁴(cu)` triangle; the Step-3
  endpoint terms.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream

variable {d : ℕ}

/-! ## 1. The deterministic head, in closed form -/

/-- The `p`-th root of the corrected head of `e.kl.bounds.large`.  The head is
literally a `p`-th power, so its root is the base. -/
theorem streamIncrementLpMassHead_rpow_inv (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) :
    streamIncrementLpMassHead M p n m ^ p⁻¹ =
      IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
        p ^ ((2 : ℝ)⁻¹) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hbase : (0 : ℝ) ≤ IndependentSums.gammaMomentConst 2 *
      streamPointScale M n m * p ^ ((2 : ℝ)⁻¹) :=
    (mul_pos (mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
      (streamPointScale_pos M hnm)) (Real.rpow_pos_of_pos hp0 _)).le
  rw [streamIncrementLpMassHead, ← Real.rpow_mul hbase, mul_inv_cancel₀ hp0.ne',
    Real.rpow_one]

/-! ## 2. The band amplitude and the wave-band mean bound -/

/-- The `C(d, p)` amplitude of the deep-band deterministic mean at the proved
volume-normalized `L^p` carrier: the head's constant, with the point-scale's
own dimensional factors. -/
noncomputable def deepBandAmplitude (d : ℕ) (p : ℝ) : ℝ :=
  IndependentSums.gammaMomentConst 2 *
    (IndependentSums.gammaTriangleConst 2 *
      ((d : ℝ) ^ 2 * geometricConcentrationConst)) * p ^ ((2 : ℝ)⁻¹)

theorem deepBandAmplitude_nonneg (d : ℕ) {p : ℝ} (hp : 0 < p) :
    0 ≤ deepBandAmplitude d p := by
  rw [deepBandAmplitude]
  have h1 : (0 : ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have h2 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h3 : (0 : ℝ) < geometricConcentrationConst := geometricConcentrationConst_pos
  have h4 : (0 : ℝ) < p ^ ((2 : ℝ)⁻¹) := Real.rpow_pos_of_pos hp _
  positivity


/-! ## 3. The assembled split -/


end Algsuperdiff.Section3.Provider.CoarseEllipticity
