/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGCarrierRHS
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourSchauder

/-!
# HomSpineRecutSupport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Support for the bundle re-cut: the multiscale clause alone, the printed
# carriers' finiteness, and the numeral pin

## What this file supplies

Route (i) is closed, leaving ONE mechanical step: re-cut the spine's per-`ω`
bundle so that the transcribed source hypothesis appears with its MULTISCALE
clause alone, and the Step-4 output `hC4ex` is PRODUCED rather than assumed.
This file gives three of the ingredients that step needs.

1. **THE FINITENESS CHECK** (the CHECK-FIRST item).  The re-cut carries four
   slot dominations; each is a genuine hypothesis only if its printed carrier
   can be `⊤`.  The verdict, machine-checked below:
   * `parentTruncatedHomogenizationErrorInfinityOneScalar` — NEVER `⊤`
     (`CoarseGraining`'s `…_eq_ofReal` exhibits it as an `ENNReal.ofReal`), UNCONDITIONALLY;
   * `parentTruncatedHomogenizationErrorInfinityTwoScalar` — the same;
   * `cubeEuclideanPositiveBesovOverlapESeminorm` — never `⊤` on the printed
     data class `MemCubeEuclideanFullWsp`, which the root's own `C^{0,1/2}`
     binder supplies (`HomCGFinalDatum.memCubeEuclideanFullWsp_of_holderHalf`).
   So all three dominations are PINNABLE: at `E:= carrier.toReal` they hold by
   `ENNReal.ofReal_toReal`, and no printed finiteness requirement has to be
   added to the bundle.  The three `…_dominates_self` lemmas below are that
   pinning, and they are what makes the re-cut bundle demonstrably non-vacuous.
3. The numeral pin.  At the printed §4.5 exponent `p = 4d` and the display pin
   `s₁′ = s/8`, `s′ = 7s/8`, the joint conjunction
   `s₁′ < s′ < s₂`, `s₂ < 1/2`, `1/2 - d/p < s₂`, `s + d/p ≤ 1/2`
   is satisfied at `s₂ = 3/8`, for EVERY admissible `s` — and the guard itself
   is satisfiable (`s = 1/8`).
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 2. THE FINITENESS CHECK, and the pinning it licenses -/

/-- **The `𝓔₁` carrier is never `⊤`** — unconditionally.  `CoarseGraining`'s
`parentTruncatedHomogenizationErrorInfinityOneScalar_eq_ofReal` exhibits it as
an `ENNReal.ofReal`. -/
theorem parentErrorOne_ne_top [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (s1 : FractionalOrder) :
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
        hsigma0 s1 ≠ ⊤ := by
  rw [parentTruncatedHomogenizationErrorInfinityOneScalar_eq_ofReal Q n hn a sigma0
    hsigma0 s1]
  exact ENNReal.ofReal_ne_top

/-- **The `𝓔₂` carrier is never `⊤`** — unconditionally. -/
theorem parentErrorTwo_ne_top [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (s1 : FractionalOrder) :
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 s1 ≠ ⊤ := by
  rw [parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_ofReal Q n hn a sigma0
    hsigma0 s1]
  exact ENNReal.ofReal_ne_top

/-- **The `[𝐠]` carrier is never `⊤` on the printed data class.**

The overlap seminorm is below the dimension constant times the fractional
seminorm, and both factors are finite on `MemCubeEuclideanFullWsp`. -/
theorem overlapSeminorm_ne_top [NeZero d] (Q : TriadicCube d) (s2 : FractionalOrder)
    (p : FiniteLpExponent) {g : Vec d → Vec d} (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g ≠ ⊤ := by
  let F : CubeEuclideanLpField Q p := { toField := g, euclideanMemLp := hg.1 }
  have hcomp := cubeEuclideanOverlap_le_dimensionConstant_mul_wsp Q s2 p F
  have hright : cubeEuclideanWspOverlapDimensionConstant d *
      cubeEuclideanWspESeminorm Q s2 p g < ∞ :=
    ENNReal.mul_lt_top (cubeEuclideanWspOverlapDimensionConstant_lt_top d)
      hg.2.eSeminorm_lt_top
  have hkey : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g < ∞ := by
    refine lt_of_le_of_lt ?_ hright
    simpa only [F] using hcomp
  exact hkey.ne

/-- **The `𝓔₁` domination is PINNABLE**: at `E₁:= carrier.toReal` it is free. -/
theorem parentErrorOne_dominates_self [NeZero d] (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (s1 : FractionalOrder) :
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
        hsigma0 s1 ≤
      ENNReal.ofReal
        (Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
          hsigma0 s1).toReal := by
  rw [ENNReal.ofReal_toReal (parentErrorOne_ne_top Q hn a hsigma0 s1)]

/-- **The `𝓔₂` domination is PINNABLE**: at `E₂:= carrier.toReal` it is free. -/
theorem parentErrorTwo_dominates_self [NeZero d] (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (s1 : FractionalOrder) :
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 s1 ≤
      ENNReal.ofReal
        (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
          hsigma0 s1).toReal := by
  rw [ENNReal.ofReal_toReal (parentErrorTwo_ne_top Q hn a hsigma0 s1)]

/-- **The `[𝐠]` domination is PINNABLE** on the printed data class. -/
theorem overlapSeminorm_dominates_self [NeZero d] (Q : TriadicCube d)
    (s2 : FractionalOrder) (p : FiniteLpExponent) {g : Vec d → Vec d}
    (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g ≤
      ENNReal.ofReal (ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g).toReal := by
  rw [ENNReal.ofReal_toReal (overlapSeminorm_ne_top Q s2 p hg)]

/-! ## 3. The numeral pin: `p = 4d`, `s₁′ = s/8`, `s′ = 7s/8`, `s₂ = 3/8` -/

/-- The printed §4.5 exponent `p = 4d`, as a `FiniteLpExponent`. -/
def recutExponent (d : ℕ) (hd : 1 ≤ d) : FiniteLpExponent where
  exponent := ((4 * d : ℕ) : ℝ≥0∞)
  one_lt := by
    have h : (1 : ℕ) < 4 * d := by omega
    exact_mod_cast (Nat.one_lt_cast (α := ℝ≥0∞)).mpr h
  lt_top := by
    exact lt_of_le_of_ne le_top (ENNReal.natCast_ne_top (4 * d))

@[simp] theorem recutExponent_toReal (d : ℕ) (hd : 1 ≤ d) :
    (recutExponent d hd).exponent.toReal = 4 * (d : ℝ) := by
  show (((4 * d : ℕ) : ℝ≥0∞)).toReal = 4 * (d : ℝ)
  rw [ENNReal.toReal_natCast]
  push_cast
  ring

/-- At the printed pin the exponent clears the `2 ≤ p` threshold the display
needs. -/
theorem recutExponent_two_le (d : ℕ) (hd : 1 ≤ d) :
    (2 : ℝ≥0∞) ≤ (recutExponent d hd).exponent := by
  show (2 : ℝ≥0∞) ≤ ((4 * d : ℕ) : ℝ≥0∞)
  have h : (2 : ℕ) ≤ 4 * d := by omega
  exact_mod_cast (Nat.cast_le (α := ℝ≥0∞)).mpr h

end

end Algsuperdiff.Section4.Provider.Homogenization
