/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamRepin

/-!
# HomSeamSqrtTwoChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The level pairing at the re-pinned base `s/8`, absorbing the `√2`

## What moves

`HomSpineResidueLevel`'s pairing chain is stated at `EthmB(m)`'s PRINTED base
`⟨homS M, hs⟩` and takes both `𝓔`-dominations at constant one.  The re-pin
moves the base to `s' = s/8` (`HomSeamRepin.homSeamBase`) and delivers the
SECOND domination at `√2`, because the order step
`𝓔_{s/16,∞,2} ≤ √2 · 𝓔_{s/32,∞,2}` costs exactly the ratio of the two geometric
normalizations.  This file carries the two consequences:

* the gap pairing at a general domination constant `K ≥ 1`
  (`ofReal_gapLeg_le_of_const`), the constant entering as `K²` — the
  `ofReal_one_add_sq_le_of_const` is the whole of it;
The base re-pin is FREE on the first leg: `ofReal_firstLeg_le` returns the
constant `c · C_en0 · s'`, and `s' = s/8 ≤ s`, so the leg constant
already covers it.  The `√2` is the only genuine cost, and it is a factor `2`.

## Slot-agnosticism (and why the chain stops here)

Every theorem below takes the two error slots as BARE nonnegative reals `E1`,
`E2`.  It is therefore valid at the slots
(the pinned slots at the uncut `a_L`) and equally at the
print-accurate slots (`HomSeamFluxCoefficient.recutPinnedE1Flux/E2Flux`, at
`ã_{L,m}`).  The chain deliberately stops before the `a_L` lane's `hlevel`,
which names the pinned `𝓔₁` slot and so fixes the coefficient: see `HomSeamFluxCoefficient`'s module
disclosure for why
the `a_L`-sided domination is not available and what the print-accurate
re-instantiation costs.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The gap pairing at a general domination constant -/

/-- The abstract shape of the gap pairing when the domination carries a
constant `K ≥ 1`: the constant enters squared, and nothing else changes. -/
private theorem ofReal_gapLeg_core_of_const {c gap Kg Cgap g5 E2 K : ℝ} (Ecar : ℝ≥0∞)
    (hc : 0 ≤ c) (hKg : 0 ≤ Kg) (hCgap : 0 < Cgap) (hg5 : 0 ≤ g5) (hE2 : 0 ≤ E2)
    (hK : 1 ≤ K) (hgap : gap ≤ Kg * g5)
    (hdom : ENNReal.ofReal E2 ≤ ENNReal.ofReal K * Ecar) :
    ENNReal.ofReal (c * gap * (1 + E2 ^ (2 : ℕ))) ≤
      ENNReal.ofReal (c * K ^ (2 : ℕ) * Kg / Cgap) *
        (ENNReal.ofReal (Cgap * g5) * (1 + Ecar ^ (2 : ℝ))) := by
  have hsq : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := pow_nonneg hE2 2
  have hone : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by linarith only [hsq]
  have hK0 : (0 : ℝ) ≤ K := by linarith only [hK]
  have hKsq : (0 : ℝ) ≤ K ^ (2 : ℕ) := pow_nonneg hK0 2
  have hstep : c * gap * (1 + E2 ^ (2 : ℕ)) ≤ c * (Kg * g5) * (1 + E2 ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hc) hone
  have hcK : (0 : ℝ) ≤ c * Kg / Cgap := div_nonneg (mul_nonneg hc hKg) hCgap.le
  have hCg5 : (0 : ℝ) ≤ Cgap * g5 := mul_nonneg hCgap.le hg5
  have hsplit : c * (Kg * g5) * (1 + E2 ^ (2 : ℕ)) =
      c * Kg / Cgap * (Cgap * g5) * (1 + E2 ^ (2 : ℕ)) := by
    field_simp
  have hprod : ENNReal.ofReal (c * Kg / Cgap * (Cgap * g5) * (1 + E2 ^ (2 : ℕ))) =
      ENNReal.ofReal (c * Kg / Cgap) *
        (ENNReal.ofReal (Cgap * g5) * ENNReal.ofReal (1 + E2 ^ (2 : ℕ))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hcK hCg5), ENNReal.ofReal_mul hcK, mul_assoc]
  have hconst : ENNReal.ofReal (c * Kg / Cgap) * ENNReal.ofReal (K ^ (2 : ℕ)) =
      ENNReal.ofReal (c * K ^ (2 : ℕ) * Kg / Cgap) := by
    rw [← ENNReal.ofReal_mul hcK]
    congr 1
    field_simp
  calc ENNReal.ofReal (c * gap * (1 + E2 ^ (2 : ℕ)))
      ≤ ENNReal.ofReal (c * (Kg * g5) * (1 + E2 ^ (2 : ℕ))) :=
        ENNReal.ofReal_le_ofReal hstep
    _ = ENNReal.ofReal (c * Kg / Cgap) *
          (ENNReal.ofReal (Cgap * g5) * ENNReal.ofReal (1 + E2 ^ (2 : ℕ))) := by
        rw [hsplit, hprod]
    _ ≤ ENNReal.ofReal (c * Kg / Cgap) *
          (ENNReal.ofReal (Cgap * g5) *
            (ENNReal.ofReal (K ^ (2 : ℕ)) * (1 + Ecar ^ (2 : ℝ)))) :=
        mul_le_mul' le_rfl
          (mul_le_mul' le_rfl (ofReal_one_add_sq_le_of_const hE2 hK hdom))
    _ = ENNReal.ofReal (c * K ^ (2 : ℕ) * Kg / Cgap) *
          (ENNReal.ofReal (Cgap * g5) * (1 + Ecar ^ (2 : ℝ))) := by
        rw [← hconst]; ring

/-- **THE SECOND PAIRING AT A GENERAL DOMINATION CONSTANT.**

`HomSpineResiduePairing`'s gap pairing with the domination weakened from
constant one to constant `K ≥ 1`.  The pairing constant picks up exactly `K²`;
the mesoscale gap absorption `homGapAbsorbAt` is untouched. -/
theorem ofReal_gapLeg_le_of_const (M : ABKModel d) {Cgap : ℝ} (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {c E2 s2 K : ℝ}
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hc : 0 ≤ c) (hE2 : 0 ≤ E2) (hs2 : 5 < 10 * s2 * Real.log 3) (hK : 1 ≤ K)
    (hdom : ENNReal.ofReal E2 ≤
      ENNReal.ofReal K *
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homQuarterOf s) omega) :
    ENNReal.ofReal
        (c *
            (homS M ^ (-(9 / 2) : ℝ) *
              (3 : ℝ) ^ (s2 * (((homN M m : ℤ)) : ℝ) - s2 * (m : ℝ))) *
          (1 + E2 ^ (2 : ℕ))) ≤
      ENNReal.ofReal (c * K ^ (2 : ℕ) * homGapConstAt s2 / Cgap) *
        ethmBGap M Cgap m (homN M m) s omega := by
  have hgap := homGapAbsorbAt (M := M) hlog hgamma1 m hs2
  have hexp : (3 : ℝ) ^ (s2 * (((homN M m : ℤ)) : ℝ) - s2 * (m : ℝ)) =
      (3 : ℝ) ^ (s2 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) := by
    congr 1
    ring
  rw [hexp, ethmBGap]
  exact ofReal_gapLeg_core_of_const _ hc (homGapConstAt_nonneg hs2) hCgap
    (pow_nonneg M.shellPrefix.gamma_pos.le 5) hE2 hK hgap hdom

/-! ## 2. The level leg at the re-pinned base -/

/-- `(√2)² = 2`: the exact cost of the order step in the pairing constant. -/
theorem sqrtTwo_sq : (Real.sqrt 2) ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)

theorem one_le_sqrtTwo : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  simpa only [Real.sqrt_one] using h

end

end Algsuperdiff.Section4.Provider.Homogenization
