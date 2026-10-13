/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineInstallData

/-!
# HomSpineInstallPins

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The INSTALLED bundle: the four dominations discharged at the printed carriers

## What this file supplies

The re-cut bundle's four slot dominations are PINNABLE but were not
INSTALLED.  This file installs them: the §4.5 bundle core is
`HomSpineRecutClose`'s re-cut bundle with

* the abstract slots `Ccg, 𝓔₁, 𝓔₂, D_g` REPLACED by the printed carriers' own
  `toReal` (`recutPinnedDg` and its three siblings);
* the four dominations, the four sign conditions and the two pin equations
  DELETED — they are discharged by `HomSpineRecutSupport`'s `_dominates_self`
  corollaries at exactly those values;
* the order frame reduced to the two conditions that are not numerals: the
  bundle's own guard `s + d/p ≤ 1/2` and the window `7s/8 < s₂`.

What survives is the genuinely content-bearing core:

```text
  { the MULTISCALE clause, hS, hlevel, hlevelDual, hEB/hdom, (jn, s, Cw, S, EB, Fflux) }.
```

The installation is general in `(p, s₂)` and is instantiated at the
printed exponent `p = 4d` and the CORRECTED window pin `s₂ = 49/100`
(`HomSpineInstallData` machine-checks that the `s₂ = 3/8` cannot absorb the
forcing leg at the `γ⁵` rate and that `49/100` can).
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The display pin, as `FractionalOrder`s -/

/-- The display pin's low order `s₁′ = s/8` (the sharp choice). -/
def recutOrderLow (s : FractionalOrder) : FractionalOrder :=
  ⟨s.1 / 8, by have h := s.2.1; linarith only [h], by have h := s.2.2; linarith only [h]⟩

@[simp] theorem recutOrderLow_val (s : FractionalOrder) : (recutOrderLow s).1 = s.1 / 8 := rfl

/-- The display pin's dual order `s′ = 7s/8` (the sharp choice: the carrier
comparison's weight hypothesis holds with EQUALITY there). -/
def recutOrderDual (s : FractionalOrder) : FractionalOrder :=
  ⟨7 * s.1 / 8, by have h := s.2.1; linarith only [h],
    by have h := s.2.2; linarith only [h]⟩

@[simp] theorem recutOrderDual_val (s : FractionalOrder) :
    (recutOrderDual s).1 = 7 * s.1 / 8 := rfl

/-- **The CORRECTED window pin** `s₂ = 49/100`.  The earlier value `s₂ = 3/8` is
inside the membership band at `p = 4d` but fails the gap absorption's
exponent condition (`HomSpineInstallData` machine-checks the failure).
`49/100` is inside the band AND absorbs at the `γ⁵` rate. -/
def recutOrderTop : FractionalOrder := ⟨49 / 100, by norm_num, by norm_num⟩

@[simp] theorem recutOrderTop_val : (recutOrderTop : FractionalOrder).1 = 49 / 100 := rfl

/-! ## 2. The four printed carriers, at their own `toReal` -/

/-- The `D_g` slot, pinned to the printed positive-Besov overlap seminorm. -/
def recutPinnedDg (m : ℤ) (s2 : FractionalOrder) (p : FiniteLpExponent)
    (g : Vec d → Vec d) : ℝ :=
  (ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g).toReal

theorem recutPinnedDg_nonneg [NeZero d] (m : ℤ) (s2 : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d) : 0 ≤ recutPinnedDg m s2 p g :=
  ENNReal.toReal_nonneg

/-! ## 5. The installation at the printed numeral pin -/

/-- The corrected numeral pin is inside the membership band at `p = 4d`. -/
theorem recutOrderTop_window (d : ℕ) (hd1 : 1 ≤ d) :
    (recutOrderTop : FractionalOrder).1 < 1 / 2 ∧
      1 / 2 - (d : ℝ) / (recutExponent d hd1).exponent.toReal <
        (recutOrderTop : FractionalOrder).1 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hdR]
  have hquot : (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 := by
    rw [recutExponent_toReal d hd1]
    field_simp
  refine ⟨by norm_num, ?_⟩
  rw [recutOrderTop_val, hquot]
  norm_num

end

end Algsuperdiff.Section4.Provider.Homogenization
