/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveThirdTerm

/-!
# WaveThirdTermSquared

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The squared three-term display: what Step 3 consumes

Step 2 of `p.bfA.multiscalebound` proves `e.wave.influence.bound` in its
printed three-term form (`WaveThirdTerm.wave_influence_bound_three_terms`), an
inequality for the **unsquared** amplitude

```
gamma^{1/2} 3^{-gamma ell} || k_L - k_{ell - hsep} ||_{Lbar^4(cu_lout)}
  <=  waveHeadTerm + waveUpperTerm + waveTailTerm .
```

Step 3's `|b_L|` branch consumes the **square** of that quantity,

```
gamma . 3^{-2 gamma ell} . || k_L - k_{n-k-h_k} ||^2_{Lbar^4(cu)} ,
```

after the manuscript's own Cauchy--Schwarz/Hölder step
`(avsum gamma^2 3^{-4 gamma ell} |.|^4)^{1/2} <= avsum gamma 3^{-2 gamma ell}
||.||^2_{Lbar^4}`.  Squaring a *sum* of three terms is not free: the cross terms
have to be paid for.  This module proves the squared display.

## The cross terms

The manuscript writes the three-term bound and then squares it silently.  The
honest cost is the elementary

```
(a + b + c)^2  <=  3 (a^2 + b^2 + c^2)      (a, b, c real) ,
```

i.e. Cauchy--Schwarz on `(1,1,1)`; the factor `3` is sharp (equality at
`a = b = c`).  `three_mul_sq_add_sq_add_sq_le` below is that inequality, proved
as an abstract real fact.  No sharper split is available for a general triple,
and none is needed: the three squared legs are then priced separately.

## The three squared legs

* **head**: deterministic, and the square *collapses in closed form*.  The
  proved `waveHeadTerm_le` gives `head <= C(d) gamma^{1/2} hsep^{1/2}`, so
  `head^2 <= C(d)^2 gamma hsep` --- literally the manuscript's first term
  `cgamma hsep`, with an explicit dimensional constant.  (The square of the
  *minimum* `min{gamma^{-1/2}, hsep^{1/2}}` carried by `waveL4Head` is even
  smaller; the printed `gamma hsep` is what the consumer asks for and is what
  is proved.)
* **upper**: the `r = 2` instance of `e.powerofGammasigma`
  (`Orlicz.ProductPower.isBigOWith_gammaSigma_sq_iff_of_nonneg`) at the proved
  `Gamma_2` leg.  `Gamma_2` at scale `K` gives `Gamma_{2/2} = Gamma_1` at scale
  `K^2` --- the printed *index* `Gamma_1` exactly.  The statement below carries
  `waveUpperScale ^ 2` verbatim and claims nothing more.  The direction check
  the seam needs survives: squaring *divides* the Orlicz index, it does not
  multiply it.
* **tail**: the same `r = 2` instance at the proved `Gamma_{2
  sigma_2/(2+sigma_2)}` leg, giving `Gamma_{sigma_2/(2+sigma_2)}` at scale
  `waveTailGainScale^2`, which carries `3^{-(d/4)(lout-ell)}` --- the square of
  the proved `3^{-(d/8)(lout-ell)}`, computed correctly here.  The printed gain
  is `C 3^{-(d/10) k_0}` --- a different exponent constant at a different argument
  --- so the identification with the printed gain is the consumer's to make, not
  established in this file.  The printed index is `Gamma_{(1+sigma)^{-1}}`: the
  two agree at `sigma_2 = 2/sigma`, since `sigma_2/(2+sigma_2) = 1/(1 +
  2/sigma_2)`.  `sigma_2 > 0` is free, so the printed index is attainable;
  nothing below fixes it.

## What is *not* proved

The instantiation `ell = n - k - h_k + hsep` (the manuscript's own `ell`), the
cube average `avsum_{cu in W(cu_n,k)}` in front of the display, and the Hölder
step that produced the square are the consumer's; this module squares the
*pointwise* display only.

## References

* ABK26, `p.bfA.multiscalebound`, Step 2 and Step 3's `|b_L|` branch;
  `e.powerofGammasigma`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## The cross terms -/


theorem sq_le_sq_of_le_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by nlinarith [hx, hxy]

/-! ## Nonnegativity of the two Orlicz scales -/


theorem waveTailGainScale_nonneg (d : ℕ) (b sigma sigma2 : ℝ) (lout ell : ℤ) :
    0 ≤ waveTailGainScale d b sigma sigma2 lout ell := by
  have hK : (0 : ℝ) < hsepAmplitude sigma b := by rw [hsepAmplitude]; positivity
  have hser : (0 : ℝ) ≤
      ∑' i : ℕ, truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i :=
    tsum_nonneg fun i => (truncationIndicatorScale_pos hK i).le
  have hgain : (0 : ℝ) ≤ streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) :=
    Real.rpow_nonneg (streamIncrementLpGainConst_pos d _).le _
  have hhead : (0 : ℝ) ≤ waveL4HeadConst d := waveL4HeadConst_nonneg d
  have htri : (0 : ℝ) ≤
      IndependentSums.gammaTriangleConst (2 * sigma2 / (2 + sigma2)) :=
    IndependentSums.gammaTriangleConst_pos.le
  have hprod : (0 : ℝ) ≤ HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [waveTailGainScale]
  positivity

/-! ## The squared amplitude -/


/-- **The squared head, in closed form**: `head^2 <= C(d)^2 gamma hsep`, the
manuscript's first term `cgamma hsep` with an explicit dimensional constant. -/
theorem waveHeadTerm_sq_le (M : ABKModel d) (m : ℤ) (E b : ℝ) (ell : ℤ)
    (omega : CutoffSample d) :
    waveHeadTerm M m E b ell omega ^ 2 ≤
      waveL4HeadConst d ^ 2 * (M.gamma * (hsep M m E b omega : ℝ)) := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hh : (0 : ℝ) ≤ (hsep M m E b omega : ℝ) := Nat.cast_nonneg _
  have hsq := sq_le_sq_of_le_of_nonneg (waveHeadTerm_nonneg M m E b ell omega)
    (waveHeadTerm_le M m E b ell omega)
  refine hsq.trans (le_of_eq ?_)
  have h1 : Real.sqrt M.gamma ^ 2 = M.gamma := Real.sq_sqrt hg.le
  have h2 : Real.sqrt ((hsep M m E b omega : ℝ)) ^ 2 = (hsep M m E b omega : ℝ) :=
    Real.sq_sqrt hh
  calc (waveL4HeadConst d *
        (Real.sqrt M.gamma * Real.sqrt ((hsep M m E b omega : ℝ)))) ^ 2
      = waveL4HeadConst d ^ 2 *
        (Real.sqrt M.gamma ^ 2 * Real.sqrt ((hsep M m E b omega : ℝ)) ^ 2) := by ring
    _ = waveL4HeadConst d ^ 2 * (M.gamma * (hsep M m E b omega : ℝ)) := by rw [h1, h2]

/-! ## The two squared Orlicz legs -/


/-! ## The packaged squared display -/


end

end Algsuperdiff.Section3.Provider.Multiscale
