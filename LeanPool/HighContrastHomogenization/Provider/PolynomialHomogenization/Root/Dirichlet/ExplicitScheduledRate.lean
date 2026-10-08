/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FluxConstantSlotSplit
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.UniformFluxScheduledRateExtraction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.ExplicitScheduledRate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (δ), the core: the scheduled rate at an **explicit** `C₀`

the flux scheduled rate at the witness
(`UniformFluxScheduledRateExtraction:36`) selects its constant as `A.toReal`,
where

```
A = ofReal outputFactor * ofReal Cdual *
      ((Cbesov² · ofReal Kflux)^(1/2) · hardyConstant^(1/2) +
       (Cbesov² · ofReal Kflux)^(1/2) · hardyConstant^(1/2))
```

and hides it behind an `∃`.  Because the witness is opaque, the module can only
conclude `∃ C₀, 0 ≤ C₀ s ρ Rad ∧ …` with `C₀` bound *inside* `∀ abar U s ρ Rad`
— which is exactly the defect the restated Dirichlet clause forbids.

This module repeats that proof **with the head named and bounded**:
`scheduledRateHead` is `A`, and `rowConvertedFluxScheduledRateAtWitness_of_head_le`
delivers `RowConvertedFluxScheduledRateAtWitness d C₀ …` for **any** `C₀`
dominating the head.  `scheduledRateHead_le_ofReal` then converts a real-valued
bound on the four factors into that domination, so a law-free `C₀` can be built
from the `ρ`-paid output factor, the flux slot split, that module (the
energy collapse) and the uniform Hardy constant.

The Hardy-top premise is **not** needed here: it served only to know `A ≠ ⊤` so that
`A.toReal` could be formed.  With the head bounded rather than reified, the
hypothesis drops.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The head of the scheduled rate: module the `A` premise, named. -/
@[expose]
noncomputable def scheduledRateHead (d : ℕ) (outputFactor Cdual Kflux : ℝ)
    (hardyConstant : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal outputFactor * ENNReal.ofReal Cdual *
    (((fractionalDualToBesovConstant d ^ (2 : ℕ) *
            ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
          hardyConstant ^ (1 / 2 : ℝ)) +
      ((fractionalDualToBesovConstant d ^ (2 : ℕ) *
            ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
        hardyConstant ^ (1 / 2 : ℝ)))

/-- **(δ), the core.**  The converted flux rate holds at **any** `C₀` that
dominates the scheduled head — in particular at a law-free one. -/
theorem rowConvertedFluxScheduledRateAtWitness_of_head_le
    {g kappaRate Cdual : ℝ}
    {capFlux hardyConstant boundaryEnergy : ℝ≥0∞}
    {s rho Rad epsilon Xval outputFactor : ℝ}
    {C₀ : ℝ → ℝ → ℝ → ℝ}
    (hbase : 0 ≤ epsilon * Xval)
    (hBoundaryTop : boundaryEnergy ≠ ⊤)
    {Kflux : ℝ} (hKflux : 0 ≤ Kflux)
    (hFlux : capFlux ≤
      ENNReal.ofReal (Kflux * (epsilon * Xval) ^ (2 * kappaRate)) *
        boundaryEnergy)
    (hC₀ : 0 ≤ C₀ s rho Rad)
    (hhead : scheduledRateHead d outputFactor Cdual Kflux hardyConstant ≤
      ENNReal.ofReal (C₀ s rho Rad)) :
    RowConvertedFluxScheduledRateAtWitness d C₀ g kappaRate Cdual capFlux
      hardyConstant boundaryEnergy s rho Rad epsilon Xval outputFactor := by
  let D : ℝ≥0∞ := (fractionalDualToBesovConstant d) ^ (2 : ℕ)
  let rate : ℝ := (epsilon * Xval) ^ kappaRate
  let rateE : ℝ≥0∞ := ENNReal.ofReal rate
  have hrate : 0 ≤ rate := Real.rpow_nonneg hbase _
  have hpower : rate ^ 2 = (epsilon * Xval) ^ (2 * kappaRate) := by
    dsimp only [rate]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    congr 1
    ring_nf
  have hfluxRewrite :
      ENNReal.ofReal (Kflux * (epsilon * Xval) ^ (2 * kappaRate)) =
        ENNReal.ofReal Kflux * rateE ^ (2 : ℕ) := by
    rw [← hpower, ENNReal.ofReal_mul hKflux, ENNReal.ofReal_pow hrate]
  have hFlux' : capFlux ≤
      (ENNReal.ofReal Kflux * rateE ^ (2 : ℕ)) * boundaryEnergy := by
    simpa only [hfluxRewrite] using hFlux
  have hcapTop : capFlux ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hBoundaryTop) hFlux'
  have hroot : (D * capFlux) ^ (1 / 2 : ℝ) ≤
      ((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) * rateE) *
        boundaryEnergy ^ (1 / 2 : ℝ) := by
    have hinside : D * capFlux ≤
        ((D * ENNReal.ofReal Kflux) * rateE ^ (2 : ℕ)) * boundaryEnergy := by
      calc
        D * capFlux ≤ D *
            ((ENNReal.ofReal Kflux * rateE ^ (2 : ℕ)) * boundaryEnergy) :=
          mul_le_mul_right hFlux' D
        _ = ((D * ENNReal.ofReal Kflux) * rateE ^ (2 : ℕ)) *
            boundaryEnergy := by ac_rfl
    refine (ENNReal.rpow_le_rpow hinside (by norm_num)).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ)),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    have hrateRoot : (rateE ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = rateE := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hrateRoot]
  have hTwoRow : ruledScheduledTwoRowCap d hardyConstant capFlux ≤
      (((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
          hardyConstant ^ (1 / 2 : ℝ)) +
        ((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
          hardyConstant ^ (1 / 2 : ℝ))) * rateE *
            boundaryEnergy ^ (1 / 2 : ℝ) := by
    unfold ruledScheduledTwoRowCap
    dsimp only [D]
    calc
      (D * capFlux) ^ (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ) +
          (D * capFlux) ^ (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ) ≤
        (((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) * rateE) *
            boundaryEnergy ^ (1 / 2 : ℝ)) * hardyConstant ^ (1 / 2 : ℝ) +
          (((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) * rateE) *
            boundaryEnergy ^ (1 / 2 : ℝ)) * hardyConstant ^ (1 / 2 : ℝ) :=
          add_le_add
            (mul_le_mul_of_nonneg_right hroot (zero_le))
            (mul_le_mul_of_nonneg_right hroot (zero_le))
      _ = (((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
              hardyConstant ^ (1 / 2 : ℝ)) +
            ((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
              hardyConstant ^ (1 / 2 : ℝ))) * rateE *
          boundaryEnergy ^ (1 / 2 : ℝ) := by ring
  refine ⟨hcapTop, ?_⟩
  calc
    ENNReal.ofReal outputFactor *
        (ENNReal.ofReal Cdual *
          ruledScheduledTwoRowCap d hardyConstant capFlux) ≤
      scheduledRateHead d outputFactor Cdual Kflux hardyConstant * rateE *
        boundaryEnergy ^ (1 / 2 : ℝ) := by
        calc
          ENNReal.ofReal outputFactor *
              (ENNReal.ofReal Cdual *
                ruledScheduledTwoRowCap d hardyConstant capFlux) ≤
            ENNReal.ofReal outputFactor *
              (ENNReal.ofReal Cdual *
                ((((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
                      hardyConstant ^ (1 / 2 : ℝ)) +
                    ((D * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
                      hardyConstant ^ (1 / 2 : ℝ))) * rateE *
                    boundaryEnergy ^ (1 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hTwoRow (zero_le)) (zero_le)
          _ = scheduledRateHead d outputFactor Cdual Kflux hardyConstant *
              rateE * boundaryEnergy ^ (1 / 2 : ℝ) := by
            rw [scheduledRateHead]
            dsimp only [D]
            ac_rfl
    _ ≤ ENNReal.ofReal (C₀ s rho Rad) * rateE *
        boundaryEnergy ^ (1 / 2 : ℝ) :=
      mul_le_mul' (mul_le_mul' hhead le_rfl) le_rfl
    _ = ENNReal.ofReal (C₀ s rho Rad * (epsilon * Xval) ^ kappaRate) *
        boundaryEnergy ^ (1 / 2 : ℝ) := by
      dsimp only [rateE, rate]
      rw [ENNReal.ofReal_mul hC₀]

/-! ## The real-valued bridge -/

/-- **The head, bounded in real terms.**  All four factors of the scheduled head
are real (the Hardy constant through any real dominating it), so a law-free `C₀`
built from the modules named above dominates it. -/
theorem scheduledRateHead_le_ofReal (d : ℕ)
    {outputFactor Cdual Kflux hardyReal : ℝ}
    (hout : 0 ≤ outputFactor) (hCdual : 0 ≤ Cdual) (hKflux : 0 ≤ Kflux)
    (hhardyReal : 0 ≤ hardyReal)
    {hardyConstant : ℝ≥0∞} (hhardy : hardyConstant ≤ ENNReal.ofReal hardyReal) :
    scheduledRateHead d outputFactor Cdual Kflux hardyConstant ≤
      ENNReal.ofReal (outputFactor * Cdual *
        (2 * ((fractionalDualToBesovConstant d).toReal *
          (Real.sqrt Kflux * Real.sqrt hardyReal)))) := by
  set Cb : ℝ≥0∞ := fractionalDualToBesovConstant d with hCb
  have hCbTop : Cb ≠ ⊤ :=
    (fractionalDualToBesovConstant_lt_top d).ne
  have hCb0 : (0 : ℝ) ≤ Cb.toReal := ENNReal.toReal_nonneg
  have hsqK : (0 : ℝ) ≤ Real.sqrt Kflux := Real.sqrt_nonneg _
  have hsqH : (0 : ℝ) ≤ Real.sqrt hardyReal := Real.sqrt_nonneg _
  -- the flux root
  have hpow : (Cb ^ (2 : ℕ) * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Cb.toReal * Real.sqrt Kflux) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    have hcb : (Cb ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = Cb := by
      rw [← ENNReal.rpow_natCast Cb 2, ← ENNReal.rpow_mul]
      norm_num
    have hk : (ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt Kflux) := by
      rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hKflux (by norm_num)]
    rw [hcb, hk, ENNReal.ofReal_mul hCb0, ENNReal.ofReal_toReal hCbTop]
  -- the hardy root
  have hhroot : hardyConstant ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt hardyReal) := by
    refine (ENNReal.rpow_le_rpow hhardy (by norm_num)).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hhardyReal
      (by norm_num)]
  have hterm : (Cb ^ (2 : ℕ) * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
      hardyConstant ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Cb.toReal * (Real.sqrt Kflux * Real.sqrt hardyReal)) := by
    rw [hpow]
    refine (mul_le_mul_of_nonneg_left hhroot (zero_le)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (mul_nonneg hCb0 hsqK)]
    congr 1
    ring
  have hsum : ((Cb ^ (2 : ℕ) * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
        hardyConstant ^ (1 / 2 : ℝ)) +
      ((Cb ^ (2 : ℕ) * ENNReal.ofReal Kflux) ^ (1 / 2 : ℝ) *
        hardyConstant ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (2 * (Cb.toReal *
        (Real.sqrt Kflux * Real.sqrt hardyReal))) := by
    refine (add_le_add hterm hterm).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add
      (mul_nonneg hCb0 (mul_nonneg hsqK hsqH))
      (mul_nonneg hCb0 (mul_nonneg hsqK hsqH))]
    congr 1
    ring
  rw [scheduledRateHead, ← hCb]
  refine (mul_le_mul_of_nonneg_left hsum (zero_le)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hout, ← ENNReal.ofReal_mul (mul_nonneg hout hCdual)]

end

end RowSupply
end HighContrast
end HCPolySupport
