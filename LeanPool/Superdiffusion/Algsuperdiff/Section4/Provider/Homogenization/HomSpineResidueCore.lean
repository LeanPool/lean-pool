/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueLevel

/-!
# HomSpineResidueCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The re-cut core, produced: all twelve conjuncts at the corrected pin

## What this file supplies

`HomSpineInstallPins` installs the twelve-conjunct core of the §4.5 bundle.
All twelve conjuncts are available at the corrected numeral pin `p = 4d`,
`s = |log γ|⁻¹`, `s₂ = 49/100`, `j_n = ⌈10|log γ|⌉`, from one per-`ω` supplier
and a frame condition on `K_abs`:

| conjunct | where it comes from |
|:-- |:-- |
| `0 < j_n`, the guard, the window, `0 ≤ C_w` | the numeral pin (proved here) |
| `spineClauseConst … ≤ K_abs` | `hKabs`, a frame condition on the free `K_abs` |
| `0 ≤ E_B`, `ofReal E_B ≤ EthmB(m)` | the real cut of `EthmB(m)` (proved here) |
| the MULTISCALE clause | the supplier (the coarse-graining input) |
| `0 ≤ S`, the partial sums | the supplier |
| `hlevel`, `hlevelDual` | `HomSpineResidueLevel` (the `EthmB(m)` pairing) |

So the residual bill of Theorem B's §4.5 spine is exactly that supplier plus
`hfin` and `hKabs`.

## The residual bill, itemized

The supplier asks, for each `L ≥ m` and each printed elliptic pair, for

1. the energy partial-sum slot `S` with the printed bound `hSbound` at the
   Step-2 constant shape `C · 3^{(1-α)X_m}(1 + 𝓔_{1/4})` — **this is the
   Theorem-C item**;
2. the MULTISCALE coarse-graining clause at `Gen:= printedLocalEnergy`;
3. the two `𝓔`-dominations — **the carrier seam**, disclosed in
   `HomSpineResiduePairing` and NOT dischargeable at the current pins.

`hfin` is the a.e. finiteness of the `[0,∞]` carrier, which
`HomSpineFinalWitness` already derives from the `p = 1` moment.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 3. The numeral pin, checked -/

/-- The printed mesoscale depth is positive (`⌈10|log γ|⌉ ≥ 40`). -/
theorem homK_pos {M : ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|) : 0 < homK M := by
  have h := homK_ge M
  have h40 : (40 : ℝ) ≤ (homK M : ℝ) := by linarith only [h, hlog]
  by_contra hcon
  push Not at hcon
  have hzero : homK M = 0 := Nat.le_zero.mp hcon
  rw [hzero] at h40
  norm_num at h40

/-- `d / (4d) = 1/4`: the printed exponent's own quotient. -/
theorem recutExponent_quotient (d : ℕ) (hd1 : 1 ≤ d) :
    (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hdR]
  rw [recutExponent_toReal d hd1]
  field_simp

/-- The corrected pin absorbs the mesoscale gap at the `γ⁵` rate. -/
theorem recutOrderTop_gapExponent :
    5 < 10 * (recutOrderTop : FractionalOrder).1 * Real.log 3 := by
  rw [recutOrderTop_val]
  exact gapExponent_holds_at_fortyNineHundredths

end

end Algsuperdiff.Section4.Provider.Homogenization
