/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.ObservableSwapPayoff

/-!
# GridDomination

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The gap-`0` fold behind `hgrid`

`Provider/CoarseEllipticity/LowerLeg.lean` retains one conditional analytic
input called `hgrid` --- the domination of the leg's target observable by a
**weighted series of per-scale triadic grid maxima**, in one of the two shapes

```
hgrid : forall omega, X omega <= sum_k mass * gridWeight rho k * G k omega        (upper leg)
hgrid : forall omega, forall L >= L0, X L omega <= sum_k mass * gridWeight rho k * G k omega  (lower)
```

The deterministic content behind such a binder --- `Lambda_{s,2}` and
`lambda_{s,2}^{-1}` *are* weighted grid series, gap-`0` term included --- is the
subject of `Provider/CoarseEllipticity/LambdaGridBridge.lean`.  This module
supplies the one piece of arithmetic that separates what such a bridge displays
from the shape a consumer accepts: the two index ranges do not match, and the
mismatch is a single extra summand.

## The gap-`0` fold, and why it is free

The source series runs over `k <= m` while `gridWeight` covers the gaps `>= 1`
of the proof's own binder `n <= m-1`.  The bridge therefore displays the
gap-`0` summand `mass * (top-scale maximum)` separately, and the consumers'
right-hand side has no slot for it.  It is folded into the series here: for any
`ctop` with `1 <= ctop * sum_k gridWeight rho k`,

```
mass * T + sum_k mass * gridWeight rho k * u k
  <= sum_k mass * gridWeight rho k * (ctop * T + u k)
```

(`top_add_gridSum_le_gridSum`).  At the source's own data the fold is **exact**,
not lossy: `sum_k gridWeight (2s) k = 3^{-2s} (1 - 3^{-2s})^{-1}`, so the
canonical `ctop = 3^{2s}` (`one_le_rpow_mul_tsum_gridWeight`) reproduces the
gap-`0` term with the multiplier `mass * ctop * sum_k gridWeight (2s) k = 1` at
`mass = c_{s,2} = 1 - 3^{-2s}`.  Since `s <= 1` on the frozen window,
`ctop <= 9`: the fold costs a dimension-free bounded factor and no pole.

## What is proved here

* `one_le_rpow_mul_tsum_gridWeight`, `top_add_gridSum_le_gridSum` --- the fold,
  model-free: neither statement mentions a coefficient field, a cutoff sample
  or a probability measure, and both are `forall`-quantified with no
  almost-everywhere hypothesis used or produced.

## Why the fold is stated at an arbitrary majorizing family

`top_add_gridSum_le_gridSum` does not name a grid family: it asks only for some
`G` with `ctop * T + u k <= G k` at every gap `k`.  That generality is what the
two legs need, and they need it differently.

The upper leg's target is read at a **single** cutoff index, so there a
majorant may be built from the sample alone and no binder survives.

The lower leg's target is the whole family `{X L}_{L >= m-1}` with an
`L`-**free** right-hand side (that is what a single witness for
`Probability.IsLowerIntegerFamilyOrlicz` means), while any grid family built
from the coefficient cutoff `Cutoff.coefficientCutoff M.nu L omega` reads the
index `L`.  The `L`-uniformity is therefore an obligation on the caller, who
must exhibit an `L`-free family `G` majorizing the folded grid maxima at every
`L >= L0`.  What that obligation amounts to is the analytic requirement that
the block estimate `p.bfA.multiscalebound` be uniform in the cutoff index,
which is how the source uses it.

## What is *not* claimed here

No on-grid domination of an actual observable is proved here, and no block
estimate, no `e.maxy.bound` lift and no base case is claimed.  In particular
`hsplit` --- the per-scale split of the grid maxima into a deterministic
constant and the `Gamma` lanes --- is untouched.  The two legs themselves are
delivered downstream by the superposed-flux pre-split route, as
`superposedFlux_coarse_ellipticity_lower_leg` and
`superposedFlux_coarse_ellipticity_upper_leg`.

## References

* ABK26, coarse-grained ellipticity constants, (the definition and the
  normalizer `c_{sq}`); `p.cg.ellipticity.bounds`, statement, proof from
  `p.bfA.multiscalebound` (the grid maximum and the summation).
* `Provider/BadEvents/ObservableSwapPayoff.lean` (the observables at the
  translated cutoff samples),
  `Provider/CoarseEllipticity/LambdaGridBridge.lean` (the deterministic bridge
  and the `q = 2` weight arithmetic), `.../GridWeights.lean` (`gridWeight`,
  `gridSupAbs`), `.../LowerLeg.lean` (the `hgrid` consumer).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The gap-`0` fold -/

/-- The canonical fold constant.  `ctop = 3^{rho}` covers the gap-`0` term
against the whole grid series, because the series already contains the gap-`1`
weight `3^{-rho}`. -/
theorem one_le_rpow_mul_tsum_gridWeight {rho : ℝ} (hrho : 0 < rho) :
    1 ≤ (3 : ℝ) ^ rho * ∑' k : ℕ, gridWeight rho k := by
  have hsum := gridWeight_summable hrho
  have hhead : gridWeight rho 0 ≤ ∑' k : ℕ, gridWeight rho k :=
    hsum.le_tsum 0 fun j _ => gridWeight_nonneg rho j
  have hzero : gridWeight rho 0 = (3 : ℝ) ^ (-rho) := by
    rw [gridWeight]
    norm_num
  have hinv : (3 : ℝ) ^ rho * (3 : ℝ) ^ (-rho) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hpos : (0 : ℝ) < (3 : ℝ) ^ rho := Real.rpow_pos_of_pos (by norm_num) _
  calc (1 : ℝ) = (3 : ℝ) ^ rho * (3 : ℝ) ^ (-rho) := hinv.symm
    _ = (3 : ℝ) ^ rho * gridWeight rho 0 := by rw [hzero]
    _ ≤ (3 : ℝ) ^ rho * ∑' k : ℕ, gridWeight rho k :=
        mul_le_mul_of_nonneg_left hhead hpos.le

/-- **The gap-`0` fold.**  The source's series carries a gap-`0` summand `mass * T`
outside the `gridWeight` family (against the proof's binder `n <= m-1`).  Any
family `G` majorizing `ctop * T + u k` at every scale absorbs it, provided
`ctop` covers the gap-`0` term against the total weight.

The inequality is proved by comparison inside the series, so the only
summability needed is that of the majorizing series itself: the two smaller
series are summable by domination. -/
theorem top_add_gridSum_le_gridSum {rho mass ctop T : ℝ} {u G : ℕ → ℝ}
    (hrho : 0 < rho) (hmass : 0 ≤ mass) (hT : 0 ≤ T) (hu : ∀ k, 0 ≤ u k)
    (hctop : 1 ≤ ctop * ∑' k : ℕ, gridWeight rho k)
    (hG : ∀ k, ctop * T + u k ≤ G k)
    (hGsum : Summable fun k : ℕ => mass * gridWeight rho k * G k) :
    mass * T + ∑' k : ℕ, mass * gridWeight rho k * u k
      ≤ ∑' k : ℕ, mass * gridWeight rho k * G k := by
  have hwsum : Summable (gridWeight rho) := gridWeight_summable hrho
  have hwnn : ∀ k, 0 ≤ mass * gridWeight rho k := fun k =>
    mul_nonneg hmass (gridWeight_nonneg rho k)
  have htsumw : (0 : ℝ) ≤ ∑' k : ℕ, gridWeight rho k :=
    tsum_nonneg fun k => gridWeight_nonneg rho k
  have hctop0 : 0 ≤ ctop := by
    by_contra hneg
    push Not at hneg
    have hle : ctop * ∑' k : ℕ, gridWeight rho k ≤ 0 * ∑' k : ℕ, gridWeight rho k :=
      mul_le_mul_of_nonneg_right hneg.le htsumw
    rw [zero_mul] at hle
    linarith
  have hcTnn : 0 ≤ ctop * T := mul_nonneg hctop0 hT
  have hmidle : ∀ k, mass * gridWeight rho k * (ctop * T + u k)
      ≤ mass * gridWeight rho k * G k := fun k =>
    mul_le_mul_of_nonneg_left (hG k) (hwnn k)
  have hmidnn : ∀ k, 0 ≤ mass * gridWeight rho k * (ctop * T + u k) := fun k =>
    mul_nonneg (hwnn k) (add_nonneg hcTnn (hu k))
  have hmidsum : Summable fun k : ℕ => mass * gridWeight rho k * (ctop * T + u k) :=
    Summable.of_nonneg_of_le hmidnn hmidle hGsum
  have husum : Summable fun k : ℕ => mass * gridWeight rho k * u k := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hwnn k) (hu k))
      (fun k => ?_) hmidsum
    exact mul_le_mul_of_nonneg_left (by linarith) (hwnn k)
  have hheadsum : Summable fun k : ℕ => mass * ctop * T * gridWeight rho k :=
    hwsum.mul_left _
  have hmidtsum : ∑' k : ℕ, mass * gridWeight rho k * (ctop * T + u k)
      = mass * ctop * T * (∑' k : ℕ, gridWeight rho k)
        + ∑' k : ℕ, mass * gridWeight rho k * u k := by
    rw [tsum_congr (fun k => by ring :
        ∀ k : ℕ, mass * gridWeight rho k * (ctop * T + u k)
          = mass * ctop * T * gridWeight rho k + mass * gridWeight rho k * u k),
      hheadsum.tsum_add husum, tsum_mul_left]
  have hkey : mass * T ≤ mass * ctop * T * ∑' k : ℕ, gridWeight rho k := by
    have hstep : mass * T * 1 ≤ mass * T * (ctop * ∑' k : ℕ, gridWeight rho k) :=
      mul_le_mul_of_nonneg_left hctop (mul_nonneg hmass hT)
    calc mass * T = mass * T * 1 := by ring
      _ ≤ mass * T * (ctop * ∑' k : ℕ, gridWeight rho k) := hstep
      _ = mass * ctop * T * ∑' k : ℕ, gridWeight rho k := by ring
  calc mass * T + ∑' k : ℕ, mass * gridWeight rho k * u k
      ≤ ∑' k : ℕ, mass * gridWeight rho k * (ctop * T + u k) := by
        rw [hmidtsum]; linarith
    _ ≤ ∑' k : ℕ, mass * gridWeight rho k * G k :=
        hmidsum.tsum_le_tsum hmidle hGsum

/-! ## 2. Summability of the grid tail series at the ruled exponent -/


/-! ## 3. The scaled observables as a top term plus a weighted grid series -/


/-! ## 4. `hgrid` at the canonical grid family -/


/-! ## 5. `hgrid` against an arbitrary majorizing grid family -/


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
