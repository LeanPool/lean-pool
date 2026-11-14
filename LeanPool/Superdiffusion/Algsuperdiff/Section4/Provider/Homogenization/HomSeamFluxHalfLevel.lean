/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxHalfPin

/-!
# HomSeamFluxHalfLevel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hlevelDual` at the Schauder provenance `α = 1/2`

## What this file supplies

`HomSeamFluxFreeCcg`'s `hlevelDual` at a free `Ccg`, with the Hölder gauge of
the Step-4 test moved from `α = s` to `α = 1/2`, the dual order `s′ = 7s/8`
UNCHANGED.  Nothing in the pairing chain notices: `HomSpineInstallArith`'s
`hlevelDual_of_energyBound` is already general in `α` (its `s` slot enters only
through `cgTestConstBase d s s′ t` and the matching scale power), and
`cgTestConst_mul_rpow_originCube` — the dual-order cancellation — is stated at
general `α` too.

The visible change is the scale power on the right: at `α = s` the display
carried `3^{sm}`; at `α = 1/2` it carries the print's own `3^{m/2}` bracket
(the printed display's Schauder weight `3^{m(1/2-s)}` composed with the
display's `3^{s′m}`).  In symbols, `cgTestConst` supplies the single factor
`3^{m(α-s′)}`, so

```text
  cgTestConst □_m α s′ p′ · 3^{s′m}  =  cgTestConstBase d α s′ p′ · 3^{αm},
```

and at `α = 1/2` the right side is `K_test · 3^{m/2}`.

## Why this is the print's reading

The Step-4 pairing tests against `∇v`, the gradient of the constant-coefficient
comparator, and the ONLY regularity the print has for it is the `C^{0,1/2}`
Schauder estimate (the same estimate whose constant
`HomSchauderUniform.stepFourSchauderConstU` already interpolates through).
Reading the dual bound at order `1/2` rather than at order `s` therefore costs
nothing at the consumption site — `∇v` is in the smaller test class — while it
removes the only closing order gap in the test-class conversion.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The Schauder gauge order -/

/-- The print's Step-4 Hölder gauge, `α = 1/2`, as a `FractionalOrder`. -/
def recutOrderHalf : FractionalOrder := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp] theorem recutOrderHalf_val : (recutOrderHalf : FractionalOrder).1 = 1 / 2 := rfl

/-- The conversion window at the re-pin: the order gap `1/2 - 7s/8` is positive
for every base order `s ≤ 1/4`, at every finite dual exponent. -/
theorem cgOrderWindow_half (p : FiniteLpExponent) {s : ℝ} (hquarter : s ≤ 1 / 4) :
    0 < (1 / 2 - 7 * s / 8) * p.conjugate.exponent.toReal :=
  mul_pos (by linarith only [hquarter]) (finiteLpExponent_toReal_pos p.conjugate)

/-! ## 2. `hlevelDual` at `α = 1/2` -/

/-- **`hlevelDual` AT THE SCHAUDER PROVENANCE `α = 1/2`, A FREE `Ccg`, THE `ã`
COEFFICIENT AND THE BASE `s/8`.**

`HomSeamFluxFreeCcg`'s `hlevelDual` at a free `Ccg`, with the test's Hölder
gauge re-pinned.  Two hypotheses of the sibling are GONE (`1 ≤ d` and the
guard `s + d/p ≤ 1/2`): they were needed only to place the closing order gap
`α - s′ = s/8` inside the Gagliardo window, and the fixed gap `1/2 - 7s/8` is
inside it for free. -/
theorem hlevelDualHalfFluxAt_of_seam [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (p : FiniteLpExponent) (s2 : FractionalOrder) {g : Vec d → Vec d}
    {Ccg Kg Kh KhInf S Cen0 Ktest : ℝ} (hCcg0 : 0 ≤ Ccg) (hs : 0 < homS M)
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hss2 : homS M < s2.1) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (hs2gap : 5 < 10 * s2.1 * Real.log 3)
    (hKtest : Ktest =
      cgTestConstBase d (1 / 2) (7 * homS M / 8) p.conjugate.exponent.toReal)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKhInf0 : 0 ≤ KhInf) (hKh0 : 0 ≤ Kh) (hCen0 : 0 ≤ Cen0)
    (hjn : (originCube d m).scale - (jn : ℤ) = homN M m)
    (hSbound : S ≤ Cen0 * recutEnergyFactor M Y m omega *
      energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hdom1 : ENNReal.ofReal
        (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog)) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homHalf (homSeamBase M hs)) omega)
    (hdom2 : ENNReal.ofReal
        (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog)) ≤
      ENNReal.ofReal (Real.sqrt 2) *
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          (homQuarterOf (homSeamBase M hs)) omega)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤) :
    cgTestConst d (originCube d m) (1 / 2)
        (7 * (recutOrderBase M hlog).1 / 8) p.conjugate.exponent.toReal *
        (Real.rpow 3 (7 * (recutOrderBase M hlog).1 / 8 * (m : ℝ)) *
          coarseGrainingFinitePRHS Ccg
            (7 * (recutOrderBase M hlog).1 / 8) s2.1 sigmaBarM
            (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog))
            (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog))
            (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ))) ≤
      Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) *
        (sigmaBarM *
          (2 * pairCwOf d Ccg p s2 Cgap Cen0 (homS M) Ktest *
              (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal *
            dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)) := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  obtain ⟨hlo2, _hhi2⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d s2 p :=
    cgOverlapDataConst_nonneg d s2 p hlo2
  have hE10 : (0 : ℝ) ≤ recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE1Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hE20 : (0 : ℝ) ≤ recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE2Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hlodual : 0 < (1 / 2 - 7 * homS M / 8) * p.conjugate.exponent.toReal :=
    cgOrderWindow_half p (homS_le_quarter hlog)
  have hKtest0 : (0 : ℝ) ≤ Ktest := by
    rw [hKtest]; exact cgTestConstBase_nonneg d hlodual
  refine hlevelDual_of_energyBound (Cdata := cgOverlapDataConst d s2 p)
    (Cen := Cen0 * recutEnergyFactor M Y m omega)
    (Cw := 2 * pairCwOf d Ccg p s2 Cgap Cen0 (homS M) Ktest)
    (EB := (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal)
    hsig (by simp only [recutOrderBase_val]; linarith only [hs])
    (by simp only [recutOrderBase_val]; linarith only [hss2, hs])
    (by simpa only [recutOrderBase_val] using hlodual)
    hCcg0 hE10 hE20 hKg0 hKhInf0 hKh0
    (mul_nonneg hCen0 (recutEnergyFactor_nonneg M Y m omega)) hCdata0 hSbound
    (overlapSeminorm_toReal_le m s2 p hKg0 hs2lt hs2gt hKg) le_rfl le_rfl ?_
  refine seamSplitOf_of_seam M Y m omega p s2 (Ccg := Ccg)
    (sbase := homS M) (kappa := Ktest) (theta := 7 / 8) (Cen0 := Cen0) (Ktest := Ktest)
    hCcg0 hs rfl hlog hgamma1 hCgap hKtest0 (by norm_num) hCen0 hE10 hE20 hCdata0
    (by linarith only [hss2, hs]) hs2gap ?_ ?_ ?_ hdom1 hdom2 hfin
  · rw [pairCwOf]
    have h1 := pairCwLegOf_nonneg d p s2 (Ccg := Ccg)
      (sbase := homS M) (kappa := 1) (theta := 1) hCcg0 hCgap hCen0 hs zero_le_one one_pos
      (by linarith only [hss2]) hCdata0 hs2gap
    linarith only [h1]
  · refine le_of_eq ?_
    simp only [recutOrderBase_val]
    rw [← hKtest]
    ring
  · rw [hjn]
    refine le_of_eq ?_
    simp only [recutOrderBase_val]
    rw [← hKtest, show (7 * homS M / 8 : ℝ) = 7 / 8 * homS M from by ring,
      show (3 : ℝ) ^ (s2.1 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) =
        (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)) from by
      congr 1
      ring]

end

end Algsuperdiff.Section4.Provider.Homogenization
