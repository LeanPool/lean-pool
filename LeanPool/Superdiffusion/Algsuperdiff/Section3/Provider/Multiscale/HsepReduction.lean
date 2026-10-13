/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveOscillations

/-!
# HsepReduction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `3^{gamma hsep}` reduction: the Orlicz half

Step 3 of `p.bfA.multiscalebound` (ABK26) reduces the prefactor `3^{gamma
hsep}` to `2 + (something of size exp(-c gamma^{-1}))`.

```
3^{gamma hsep}  <=  1 + 3 gamma hsep 1_{gamma hsep <= 3^{-4}}
                       + 3^{gamma hsep} 1_{gamma hsep > 3^{-4}}
                <=  2 + 3^{gamma hsep} 1_{gamma hsep > 3^{-4}}
                <=  2 + O_{Gamma_4}(1) . O_{Gamma_4}(exp(-c gamma^{-1})) .
```

The **deterministic** half is proved:
`ConclusionArithmetic.three_rpow_le_two_add_indicator`.  This module proves the
**Orlicz** half, i.e. the last line, at explicit exponents and an explicit
scale, out of the three ingredients names:

* `e.hsep.tails` for the `O(1)` factor, at the proved amplitude
  (`Percolation.isBigOWith_gammaSigma_three_rpow_hsep_of_gates`, which controls
  `3^{b hsep}` at `Gamma_{1-sigma}`); the passage from `3^{gamma hsep}` to `3^{b
  hsep}` is's own `gamma <= b` step, proved as
  `ConclusionAssembly.three_rpow_gamma_hsep_le_three_rpow_b_hsep`;
* `e.indc.O.sigma` for the indicator
  (`WaveOscillationsCore.isBigOWith_gammaSigma_indicator_natLt` at the event
  `{i < hsep}`), applied at the **integer threshold** `i = floor((81
  gamma)^{-1})`, which is exactly the discretization of `{gamma hsep >
  3^{-4}}`:'s own computation `P[gamma hsep > 3^{-4}] <= exp(-exp(3^{-4} b
  gamma^{-1}))` is this event's tail, and the resulting scale `(K 3^{-b
  floor((81 gamma)^{-1})})^{(1-sigma)/sigma_2}` is the advertised `exp(-c
  gamma^{-1})` size;
* `e.multGammasig` for the product
  (`Orlicz.ProductPower.isBigOWith_gammaSigma_mul_of_nonneg`, carrying
  CoarseGraining's explicit `gammaProductConst`).

## Exponent bookkeeping

prints `Gamma_4` on both factors and on the product.  At this repository's
proved amplitude index the input is `Gamma_{1-sigma}` with `sigma > 0`, i.e.
`sigma_1 < 1`, so what is proved is

```
Gamma_tau ,   tau = (1-sigma) sigma_2 / ((1-sigma) + sigma_2)
```

on the product.  `sigma_2 > 0` is free, so `tau` can be made any value below `1
- sigma`; the manuscript's "upon relabelling `sigma`" is exactly this freedom.
Neither `Gamma_4` nor `Gamma_2` is attainable from a `Gamma_{1-sigma}` input
with `sigma > 0`; nothing below claims either.

## What is *not* proved

The final numerical comparison "`(K 3^{-b floor((81
gamma)^{-1})})^{(1-sigma)/sigma_2} <= C exp(-c gamma^{-1})`" is not proved: the
scale is carried in the exact closed form above, which is *stronger* than any
`exp(-c gamma^{-1})` claim and avoids inventing a `c`.  A consumer that wants
the printed shape can bound `floor((81 gamma)^{-1}) >= (81 gamma)^{-1} - 1`.

## References

* ABK26, `p.bfA.multiscalebound`, Step 3; `e.hsep.tails`; `e.indc.O.sigma`;
  `e.multGammasig`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-! ## Monotonicity of the weak-Orlicz bound -/

/-- A pointwise-smaller variable inherits the `Gamma_sigma` bound at the same
scale: the upper-tail events are nested.  (CoarseGraining carries `mono_scale`;
this is the missing `mono` in the *function* argument.) -/
theorem isBigOWith_gammaSigma_of_le {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {X Y : Omega → ℝ} {K sig : ℝ}
    (hle : ∀ omega, X omega ≤ Y omega)
    (hY : IsBigOWith mu (gammaSigma sig) Y K) :
    IsBigOWith mu (gammaSigma sig) X K := by
  rw [isBigOWith_gammaSigma_iff] at hY ⊢
  intro t ht
  refine le_trans (measureReal_mono ?_ (measure_ne_top mu _)) (hY ht)
  intro omega homega
  rw [mem_upperTailEvent] at homega ⊢
  exact lt_of_lt_of_le homega (hle omega)

/-! ## The `O(1)` factor: `3^{gamma hsep}` at `Gamma_{1-sigma}` -/

theorem hsepAmplitude_pos (sigma b : ℝ) : 0 < hsepAmplitude sigma b := by
  rw [hsepAmplitude]
  positivity

/-- **`e.hsep.tails` read at the Step-3 prefactor** ('s `O_{Gamma_4}(1)` factor).
Under `gamma <= b`, the prefactor `3^{gamma hsep}` inherits the proved
`Gamma_{1-sigma}` bound of `3^{b hsep}` at the same amplitude. -/
theorem isBigOWith_gammaSigma_three_rpow_gamma_hsep_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma b gam : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) (hgammab : gam ≤ b) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 - sigma))
      (fun omega => (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)))
      (hsepAmplitude sigma b) :=
  isBigOWith_gammaSigma_of_le
    (fun omega => three_rpow_gamma_hsep_le_three_rpow_b_hsep hgammab omega)
    (isBigOWith_gammaSigma_three_rpow_hsep_of_gates M hd hE hS hsigma0 hsigma hb0 hb1
      hEexp hE4 hunit hgamma20 hinvSq hEb hgamma)


/-! ## The indicator factor: `e.indc.O.sigma` at the threshold -/

/-- The threshold event, discretized: `gamma hsep > 3^{-4}` forces `hsep > (81
gamma)^{-1}`, hence `floor((81 gamma)^{-1}) < hsep`. -/
theorem indicator_gamma_hsep_gt_le_indicator_natLt (M : ABKModel d) {m : ℤ}
    {E b gam : ℝ} (hgam : 0 < gam) (omega : CutoffSample d) :
    (if (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ) then (1 : ℝ) else 0) ≤
      {omega : CutoffSample d | ⌊(81 * gam)⁻¹⌋₊ < hsep M m E b omega}.indicator
        (fun _ => (1 : ℝ)) omega := by
  classical
  by_cases hcase : (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ)
  · have hmem : omega ∈
        {omega : CutoffSample d | ⌊(81 * gam)⁻¹⌋₊ < hsep M m E b omega} := by
      have hlt : (81 * gam)⁻¹ < (hsep M m E b omega : ℝ) := by
        have h81 : (0 : ℝ) < 81 * gam := by linarith
        have hinv : (0 : ℝ) < (81 * gam)⁻¹ := inv_pos.2 h81
        have hmul : (81 * gam) * (81 * gam)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h81)
        nlinarith [hcase, h81, hinv, hmul]
      have hfloor : ((⌊(81 * gam)⁻¹⌋₊ : ℕ) : ℝ) ≤ (81 * gam)⁻¹ :=
        Nat.floor_le (by positivity)
      have : ((⌊(81 * gam)⁻¹⌋₊ : ℕ) : ℝ) < ((hsep M m E b omega : ℕ) : ℝ) := by
        linarith
      exact_mod_cast this
    rw [ite_eq_left hcase, Set.indicator_of_mem hmem]
  · rw [ite_eq_right hcase]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) omega

/-- **`e.indc.O.sigma`'s indicator**.  The indicator `1_{gamma hsep
> 3^{-4}}` is `O_{Gamma_{sigma_2}}` at the scale

```
  (K 3^{-b floor((81 gamma)^{-1})})^{(1-sigma)/sigma_2} ,
  K = hsepAmplitude sigma b ,
```

which is's own `exp(-c gamma^{-1})` size (the exponent is linear in
`gamma^{-1}`).  The free exponent `sigma_2 > 0` is `e.indc.O.sigma`'s own `t =
1/sigma_2`. -/
theorem isBigOWith_gammaSigma_indicator_gamma_hsep_gt_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma sigma2 b gam : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hsigma2 : 0 < sigma2)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) (hgam : 0 < gam) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma sigma2)
      (fun omega =>
        if (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ) then (1 : ℝ) else 0)
      (truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b)
        ⌊(81 * gam)⁻¹⌋₊) :=
  isBigOWith_gammaSigma_of_le
    (fun omega => indicator_gamma_hsep_gt_le_indicator_natLt M hgam omega)
    (isBigOWith_gammaSigma_indicator_natLt hb0 hsigma2 (by linarith)
      (hsepAmplitude_pos sigma b)
      (isBigOWith_gammaSigma_three_rpow_hsep_of_gates M hd hE hS hsigma0 hsigma hb0 hb1
        hEexp hE4 hunit hgamma20 hinvSq hEb hgamma) ⌊(81 * gam)⁻¹⌋₊)


/-! ## The product: `e.multGammasig` -/

/-- **The Orlicz half's display.**  The random summand's corrected inequality is
`Gamma_tau` with `tau = (1-sigma) sigma_2/((1-sigma) + sigma_2)` at the explicit
scale

```
  gammaProductConst (1-sigma) sigma_2 . hsepAmplitude sigma b
    . (hsepAmplitude sigma b . 3^{-b floor((81 gamma)^{-1})})^{(1-sigma)/sigma_2} .
``` -/
theorem isBigOWith_gammaSigma_three_rpow_gamma_hsep_mul_indicator_of_gates
    (M : ABKModel d)
    {m : ℤ} {E sigma sigma2 b gam : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hsigma2 : 0 < sigma2)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) (hgam : 0 < gam) (hgammab : gam ≤ b) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) * sigma2 / ((1 - sigma) + sigma2)))
      (fun omega => (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) *
        (if (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ) then (1 : ℝ) else 0))
      (HCPolySupport.Book.Ch04.gammaProductConst (1 - sigma) sigma2 *
        hsepAmplitude sigma b *
        truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b)
          ⌊(81 * gam)⁻¹⌋₊) := by
  classical
  refine Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_mul_of_nonneg
    (by linarith) hsigma2 (hsepAmplitude_pos sigma b).le
    (truncationIndicatorScale_pos (hsepAmplitude_pos sigma b) _).le
    (fun omega => Real.rpow_nonneg (by norm_num) _) (fun omega => ?_)
    (isBigOWith_gammaSigma_three_rpow_gamma_hsep_of_gates M hd hE hS hsigma0 hsigma
      hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgamma hgammab)
    (isBigOWith_gammaSigma_indicator_gamma_hsep_gt_of_gates M hd hE hS hsigma0 hsigma
      hsigma2 hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgamma hgam)
  by_cases hcase : (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ)
  · rw [ite_eq_left hcase]; norm_num
  · rw [ite_eq_right hcase]


/-- **The Step 3 display, both halves.**  Pointwise the prefactor is `<= 2 + Z`,
and `Z` is `Gamma_tau` at the explicit `exp(-c gamma^{-1})`-sized scale:

```
3^{gamma hsep}  <=  2 + 3^{gamma hsep} 1_{gamma hsep > 3^{-4}} ,
3^{gamma hsep} 1_{gamma hsep > 3^{-4}}
    <=  O_{Gamma_tau}( C . K . (K 3^{-b floor((81 gamma)^{-1})})^{(1-sigma)/sigma_2} ) .
```

The first line is `ConclusionArithmetic.three_rpow_le_two_add_indicator`
(ABK26's own deterministic split, at `3 . 3^{-4} < 1`); the second is
`isBigOWith_gammaSigma_three_rpow_gamma_hsep_mul_indicator`.  Together they are
exactly the corrected display of ABK26, with the printed `O_{Gamma_4}(exp(-c
gamma^{-1}))` summand of the right-hand side removed as ABK26 requires. -/
theorem three_rpow_gamma_hsep_le_two_add_orlicz_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma sigma2 b gam : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hsigma2 : 0 < sigma2)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) (hgam : 0 < gam) (hgammab : gam ≤ b) :
    (∀ omega : CutoffSample d,
        (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) ≤
          2 + (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) *
            (if (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ) then (1 : ℝ) else 0)) ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) * sigma2 / ((1 - sigma) + sigma2)))
        (fun omega => (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) *
          (if (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ) then (1 : ℝ) else 0))
        (HCPolySupport.Book.Ch04.gammaProductConst (1 - sigma) sigma2 *
          hsepAmplitude sigma b *
          truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b)
            ⌊(81 * gam)⁻¹⌋₊) := by
  classical
  refine ⟨fun omega => ?_,
    isBigOWith_gammaSigma_three_rpow_gamma_hsep_mul_indicator_of_gates M hd hE hS
      hsigma0 hsigma hsigma2 hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgamma hgam
      hgammab⟩
  have hx : (0 : ℝ) ≤ gam * (hsep M m E b omega : ℝ) :=
    mul_nonneg hgam.le (Nat.cast_nonneg _)
  have hdet := three_rpow_le_two_add_indicator hx
  by_cases hcase : (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ)
  · rw [ite_eq_left hcase] at hdet ⊢
    linarith [hdet]
  · rw [ite_eq_right hcase] at hdet ⊢
    linarith [hdet]


end

end Algsuperdiff.Section3.Provider.Multiscale
