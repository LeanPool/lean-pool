/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxLane
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxLevelChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueCore

/-!
# HomSeamFluxFreeCcg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `ã` core and its supply with the `Ccg` slot FREED

## Why this file exists

The `ã` core, its supply and its producer were stated at the
PINNED coarse-graining constant `recutPinnedCcgFlux d p = (cgDualBoundConstFlux d
p).toReal`, and so were the two level lemmas they consume —
even though `HomSeamFluxLevelChain`'s own pairing chain (`seamSplitOf_of_seam`)
is already stated at a FREE `Ccg`.  A clause producer that delivers its own
constant `Ccg₀` therefore cannot enter the chain without a detour.

This file removes the detour: every statement below carries `Ccg` as a bare
real, constrained only by

```text
  0 ≤ Ccg                                  (the pairing chain's own use), and
  cgDualBoundConstFlux d p ≤ ofReal Ccg    (the bundle's own conjunct).
```

Both are monotone UP in `Ccg`, so a clause produced at any `Ccg₀` composes at
`max Ccg₀ (recutPinnedCcgFlux d p)`; at `Ccg = recutPinnedCcgFlux d p` the
statements are the pinned ones, with the second hypothesis discharged
by `cgDualBoundConstFlux_dominates_self`.

NOTHING mathematical changes.  The proofs use the pinned constant only through
its nonnegativity and through that one domination; both are hypotheses here.
In particular this file makes NO claim about which constant the multiscale
clause can actually be produced at.

## Disclosure

The lane's pairing constant is LINEAR in `Ccg` (both legs of
`pairCwOf` are), so a `Ccg` that grows with the model grows `C_w` — and hence
`K_abs` — by the same factor.  Freeing the slot does not make a model-dependent
`Ccg` free of charge; it only makes the entry point honest.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 2. The two level conditions at a free `Ccg` -/

/-- **`hlevel` AT A FREE `Ccg`, THE `ã` COEFFICIENT AND THE BASE `s/8`.**

The seam's `hlevel` with the coarse-graining
constant freed; the proof uses the pinned constant only
through its nonnegativity. -/
theorem hlevelFluxAt_of_seam [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (p : FiniteLpExponent) (s2 : FractionalOrder) {g : Vec d → Vec d}
    {Ccg Kg Kh KhInf S Cen0 Ktest : ℝ} (hCcg0 : 0 ≤ Ccg) (hs : 0 < homS M)
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hss2 : homS M < s2.1) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (hs2gap : 5 < 10 * s2.1 * Real.log 3) (hKtest0 : 0 ≤ Ktest)
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
    coarseGrainingFinitePRHS Ccg (recutOrderBase M hlog).1 s2.1
        sigmaBarM (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog))
        (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog))
        (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (2 * pairCwOf d Ccg p s2 Cgap Cen0 (homS M) Ktest *
            (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal *
          dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  obtain ⟨hlo, _hhi⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d s2 p := cgOverlapDataConst_nonneg d s2 p hlo
  have hE10 : (0 : ℝ) ≤ recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE1Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hE20 : (0 : ℝ) ≤ recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE2Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  refine hlevel_of_energyBound (Cdata := cgOverlapDataConst d s2 p)
    (Cen := Cen0 * recutEnergyFactor M Y m omega)
    (Cw := 2 * pairCwOf d Ccg p s2 Cgap Cen0 (homS M) Ktest)
    (EB := (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal)
    hsig (recutOrderBase M hlog).2.1 (by simpa only [recutOrderBase_val] using hss2)
    hCcg0 hE10 hE20 hKg0 hKhInf0 hKh0
    (mul_nonneg hCen0 (recutEnergyFactor_nonneg M Y m omega)) hCdata0 hSbound
    (overlapSeminorm_toReal_le m s2 p hKg0 hs2lt hs2gt hKg) le_rfl le_rfl ?_
  refine seamSplitOf_of_seam M Y m omega p s2 (Ccg := Ccg)
    (sbase := homS M) (kappa := 1) (theta := 1) (Cen0 := Cen0) (Ktest := Ktest)
    hCcg0 hs rfl hlog hgamma1 hCgap zero_le_one one_pos hCen0 hE10 hE20 hCdata0
    (by linarith only [hss2]) hs2gap ?_ ?_ ?_ hdom1 hdom2 hfin
  · rw [pairCwOf]
    have h2 := pairCwLegOf_nonneg d p s2 (Ccg := Ccg)
      (sbase := homS M) (kappa := Ktest) (theta := 7 / 8) hCcg0 hCgap hCen0 hs hKtest0
      (by norm_num) (by linarith only [hss2, hs]) hCdata0 hs2gap
    linarith only [h2]
  · refine le_of_eq ?_
    simp only [recutOrderBase_val]
    ring
  · rw [hjn]
    refine le_of_eq ?_
    simp only [recutOrderBase_val, one_mul]
    rw [show (3 : ℝ) ^ (s2.1 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) =
        (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)) from by
      congr 1
      ring]

/-! ## 3. The two monotonicity steps that make `max` compose -/

/-- The printed right-hand side is monotone UP in the coarse-graining constant,
at the signs the bundle's own conjuncts carry. -/
theorem coarseGrainingFinitePRHS_mono_ccg {Ccg Ccg' s s2 sigma E1 E2 Dg S : ℝ} (n : ℤ)
    (hCcg : Ccg ≤ Ccg') (hs : 0 < s) (hss2 : s < s2) (hE1 : 0 ≤ E1) (hDg : 0 ≤ Dg)
    (hS : 0 ≤ S) :
    coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S n ≤
      coarseGrainingFinitePRHS Ccg' s s2 sigma E1 E2 Dg S n := by
  have hsinv : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hspow : (0 : ℝ) ≤ s ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hs.le _
  have hwin : (0 : ℝ) ≤ (s2 - s)⁻¹ := inv_nonneg.mpr (by linarith only [hss2])
  have hE2sq : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by
    have h2 : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := sq_nonneg E2
    linarith only [h2]
  have hthree : (0 : ℝ) ≤ (3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hDg
  have hA : (0 : ℝ) ≤ s⁻¹ * Real.sqrt sigma * E1 * S :=
    mul_nonneg (mul_nonneg (mul_nonneg hsinv (Real.sqrt_nonneg _)) hE1) hS
  have hB : (0 : ℝ) ≤ s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
      ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) :=
    mul_nonneg (mul_nonneg (mul_nonneg hspow hwin) hE2sq) hthree
  have h1 : Ccg * s⁻¹ * Real.sqrt sigma * E1 * S ≤
      Ccg' * s⁻¹ * Real.sqrt sigma * E1 * S := by
    calc Ccg * s⁻¹ * Real.sqrt sigma * E1 * S
        = Ccg * (s⁻¹ * Real.sqrt sigma * E1 * S) := by ring
      _ ≤ Ccg' * (s⁻¹ * Real.sqrt sigma * E1 * S) := mul_le_mul_of_nonneg_right hCcg hA
      _ = Ccg' * s⁻¹ * Real.sqrt sigma * E1 * S := by ring
  have h2 : Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
        ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) ≤
      Ccg' * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
        ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) := by
    calc Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
          ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)
        = Ccg * (s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
            ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)) := by ring
      _ ≤ Ccg' * (s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
            ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)) := mul_le_mul_of_nonneg_right hCcg hB
      _ = Ccg' * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
            ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) := by ring
  rw [coarseGrainingFinitePRHS, coarseGrainingFinitePRHS]
  linarith only [h1, h2]

/-- The bundle's own `Ccg` conjunct at any constant above the pin: this is what
makes `max Ccg₀ (recutPinnedCcgFlux d p)` an admissible entry point. -/
theorem cgDualBoundConstFlux_le_ofReal_of_pinned_le (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp2 : (2 : ℝ≥0∞) ≤ p.exponent) {Ccg : ℝ}
    (hCcg : recutPinnedCcgFlux d p ≤ Ccg) :
    cgDualBoundConstFlux d p ≤ ENNReal.ofReal Ccg :=
  le_trans (cgDualBoundConstFlux_dominates_self d hd p hp2)
    (ENNReal.ofReal_le_ofReal hCcg)

end

end Algsuperdiff.Section4.Provider.Homogenization
