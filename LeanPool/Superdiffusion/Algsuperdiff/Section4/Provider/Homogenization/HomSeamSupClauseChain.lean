/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradSpine
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormRethread

/-!
# HomSeamSupClauseChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The seam chain re-cut at the SUP-form multiscale clause

## Why the clause slot moves

Step 3 is realized at the fixed exponent `p = 4d`, and the
object the route actually produces is the manuscript's own sup-over-depths
clause (`HomSpineSupFormClause.CoarseGrainingSupMultiscale`), supplied by
`HomSpineSupFormClause` from the single-depth grid/smooth-dual comparison.  The seam chain consumes
the `ℓ^p` clause instead.

The swap is FREE at the point of consumption:
`HomSpineSupFormRethread.spineClauseC3_of_supMultiscale` produces clause (C3)
from the sup clause at IDENTICAL constants.  This file
carries that measurement through the five carriers of the seam chain:

```text
  RecutCoreSupplyFluxEnergySupGrad          RecutCoreSupplyFluxAtSupGrad
  SpineDatumRecutCoreFluxAtHalfSupGrad      SpineDatumCoarseGrainingRecutFluxHalfSupGrad
  HomSpineClauseSupplierAtGrad              (unchanged -- the clause is gone by then)
```

Every declaration is the strict re-cut of its original: the fourth
conjunct's `ℓ^p`-over-depths multiscale clause becomes
`CoarseGrainingSupMultiscale`, and NOTHING else changes -- not a binder, not a
constant, not an order.  `.toSup` gives the regression (`ℓ^p ⇒ sup`), so
nothing that was provable before becomes unprovable after.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The energy residue and the supply, at the sup clause -/

/-- The gradient-threaded energy residue with the multiscale
conjunct re-cut at the print's own sup-over-depths aggregation. -/
def RecutCoreSupplyFluxEnergySupGrad (M : ABKModel d)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (Cen0 : ℝ)
    (hd1 : 1 ≤ d) (hlog : 4 ≤ |Real.log M.gamma|)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => ((Annealed.sigmaBar M m : ℝ)) • (1 : Mat d))
        (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
      ∃ (S : ℝ) (Fflux : Vec d → Vec d),
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m)
              (recutExponent d hd1).exponent.toReal (homS M - homS M / 4) (homK M) N
              (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) ≤
            S) ∧
        S ≤ Cen0 * recutEnergyFactor M Y m omega *
            energyBracket ((Annealed.sigmaBar M m : ℝ))
              (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingSupMultiscale (originCube d m) (homK M)
            (recutPinnedCcgFlux d (recutExponent d hd1)) (homS M) (homS M / 4)
            (recutOrderTop : FractionalOrder).1 (recutExponent d hd1).exponent.toReal
            ((Annealed.sigmaBar M m : ℝ))
            (recutPinnedE1Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedE2Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedDg m recutOrderTop (recutExponent d hd1) g)
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux)

/-- The gradient-threaded core supply, at the sup clause. -/
def RecutCoreSupplyFluxAtSupGrad (M : ABKModel d)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (Cen0 Ccg : ℝ)
    (hd1 : 1 ≤ d) (hlog : 4 ≤ |Real.log M.gamma|)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => ((Annealed.sigmaBar M m : ℝ)) • (1 : Mat d))
        (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
      ∃ (S : ℝ) (Fflux : Vec d → Vec d),
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m)
              (recutExponent d hd1).exponent.toReal (homS M - homS M / 4) (homK M) N
              (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) ≤
            S) ∧
        S ≤ Cen0 * recutEnergyFactor M Y m omega *
            energyBracket ((Annealed.sigmaBar M m : ℝ))
              (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingSupMultiscale (originCube d m) (homK M)
            Ccg (homS M) (homS M / 4)
            (recutOrderTop : FractionalOrder).1 (recutExponent d hd1).exponent.toReal
            ((Annealed.sigmaBar M m : ℝ))
            (recutPinnedE1Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedE2Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedDg m recutOrderTop (recutExponent d hd1) g)
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux) ∧
        FluxCorrectedParentIdentification M m (homK M) omega

/-! ## 2. The twelve-conjunct core, at the sup clause -/

/-- The gradient-threaded twelve-conjunct core, at the sup clause. -/
def SpineDatumRecutCoreFluxAtHalfSupGrad (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (sb : {s : ℝ // 0 < s})
    (sigmaBarM : ℝ) (hsig : 0 < sigmaBarM) (Kabs Ccg : ℝ)
    (p : FiniteLpExponent) (s2 : FractionalOrder)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
      ∃ (jn : ℕ) (Cw S EB : ℝ) (s : FractionalOrder) (Fflux : Vec d → Vec d),
        0 < jn ∧ s.1 + (d : ℝ) / p.exponent.toReal ≤ 1 / 2 ∧
        7 * s.1 / 8 < s2.1 ∧ 0 ≤ Cw ∧
        spineClauseConst d s.1 p.exponent.toReal Cw (stepFourSchauderConstU d) ≤ Kabs ∧
        0 ≤ EB ∧
        ENNReal.ofReal EB ≤ ethmB M Cgap Y m (homN M m) sb omega ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingSupMultiscale (originCube d m) jn Ccg
            s.1 (s.1 / 4) s2.1 p.exponent.toReal sigmaBarM
            (recutPinnedE1Flux M L omega m jn hsig s)
            (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g)
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux) ∧
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
            (s.1 - s.1 / 4) jn N
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) ≤
              S) ∧
        coarseGrainingFinitePRHS Ccg s.1 s2.1 sigmaBarM
            (recutPinnedE1Flux M L omega m jn hsig s)
            (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g) S
            ((originCube d m).scale - (jn : ℤ)) ≤
          sigmaBarM *
            (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        cgTestConst d (originCube d m) (1 / 2) (7 * s.1 / 8)
            p.conjugate.exponent.toReal *
            (Real.rpow 3 (7 * s.1 / 8 * (m : ℝ)) *
              coarseGrainingFinitePRHS Ccg (7 * s.1 / 8) s2.1
                sigmaBarM (recutPinnedE1Flux M L omega m jn hsig s)
                (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g) S
                ((originCube d m).scale - (jn : ℤ))) ≤
          Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) *
            (sigmaBarM *
              (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))

/-- The gradient-threaded re-cut bundle, at the sup
clause. -/
def SpineDatumCoarseGrainingRecutFluxHalfSupGrad (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (sb : {s : ℝ // 0 < s})
    (sigmaBarM : ℝ) (hsig : 0 < sigmaBarM) (Kabs : ℝ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
      ∃ (jn : ℕ) (Cw Ccg E1 E2 Dg S EB : ℝ) (p : FiniteLpExponent)
        (s s1' s' s2 : FractionalOrder) (Fflux : Vec d → Vec d),
        0 < jn ∧ s.1 + (d : ℝ) / p.exponent.toReal ≤ 1 / 2 ∧ 0 ≤ Cw ∧
        spineClauseConst d s.1 p.exponent.toReal Cw (stepFourSchauderConstU d) ≤ Kabs ∧
        0 ≤ EB ∧
        ENNReal.ofReal EB ≤ ethmB M Cgap Y m (homN M m) sb omega ∧
        s1'.1 = s.1 / 8 ∧ s'.1 = 7 * s.1 / 8 ∧
        s'.1 < s2.1 ∧ s2.1 < 1 / 2 ∧
        1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1 ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingSupMultiscale (originCube d m) jn Ccg s.1 (s.1 / 4) s2.1
            p.exponent.toReal sigmaBarM E1 E2 Dg
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux) ∧
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
            (s.1 - s.1 / 4) jn N
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) ≤
              S) ∧
        coarseGrainingFinitePRHS Ccg s.1 s2.1 sigmaBarM E1 E2 Dg S
            ((originCube d m).scale - (jn : ℤ)) ≤
          sigmaBarM *
            (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        0 ≤ Ccg ∧ 0 ≤ E1 ∧ 0 ≤ E2 ∧ 0 ≤ Dg ∧
        cgDualBoundConstFlux d p ≤ ENNReal.ofReal Ccg ∧
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigmaBarM hsig s1' ≤
          ENNReal.ofReal E1 ∧
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigmaBarM hsig
            (fractionalOrderHalf s1') ≤ ENNReal.ofReal E2 ∧
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg ∧
        cgTestConst d (originCube d m) (1 / 2) s'.1 p.conjugate.exponent.toReal *
            (Real.rpow 3 (s'.1 * (m : ℝ)) *
              coarseGrainingFinitePRHS Ccg s'.1 s2.1 sigmaBarM E1 E2 Dg S
                ((originCube d m).scale - (jn : ℤ))) ≤
          Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) *
            (sigmaBarM *
              (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))

/-! ## 3. The installation, at the sup clause -/

/-- The bundle's installation from the core, at
the sup clause. -/
theorem spineDatumCoarseGrainingRecutFluxAtHalfSupGrad_of_core [NeZero d]
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs Ccg : ℝ} (hsig : 0 < sigmaBarM)
    (p : FiniteLpExponent) (s2 : FractionalOrder) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1) (hCcg0 : 0 ≤ Ccg)
    (hCcgDom : cgDualBoundConstFlux d p ≤ ENNReal.ofReal Ccg)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCoreFluxAtHalfSupGrad M Cgap Y m sb sigmaBarM hsig Kabs Ccg
      p s2 omega) :
    SpineDatumCoarseGrainingRecutFluxHalfSupGrad M Cgap Y m sb sigmaBarM hsig Kabs
      omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  obtain ⟨jn, Cw, S, EB, s, Fflux, hjn0, hguard, hwin, hCw, hKabsC, hEB, hdom,
    hCGm, hS0, hS, hlevel, hlevelDual⟩ :=
    hcore L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hgmem : MemCubeEuclideanFullWsp (originCube d m) s2 p g :=
    memCubeEuclideanFullWsp_of_holderHalf hKg0 hs2lt hs2gt hKg
  refine ⟨jn, Cw, Ccg, recutPinnedE1Flux M L omega m jn hsig s,
    recutPinnedE2Flux M L omega m jn hsig s, recutPinnedDg m s2 p g, S, EB, p, s,
    recutOrderLow s, recutOrderDual s, s2, Fflux, hjn0, hguard, hCw, hKabsC, hEB, hdom,
    rfl, rfl, hwin, hs2lt, hs2gt, hCGm, hS0, hS, hlevel, hCcg0,
    recutPinnedE1Flux_nonneg M L omega m jn hsig s,
    recutPinnedE2Flux_nonneg M L omega m jn hsig s,
    recutPinnedDg_nonneg m s2 p g, hCcgDom, ?_, ?_, ?_, hlevelDual⟩
  · exact parentErrorOne_dominates_self (originCube d m) (recutParentScale m jn)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) hsig (recutOrderLow s)
  · exact parentErrorTwo_dominates_self (originCube d m) (recutParentScale m jn)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) hsig
      (fractionalOrderHalf (recutOrderLow s))
  · exact overlapSeminorm_dominates_self (originCube d m) s2 p hgmem

/-- The same at the numeral pin. -/
theorem spineDatumCoarseGrainingRecutFluxAtHalfSupGrad_of_core_pinned [NeZero d]
    (hd : 2 ≤ d) (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs Ccg : ℝ} (hsig : 0 < sigmaBarM)
    (hCcg0 : 0 ≤ Ccg)
    (hCcgDom : cgDualBoundConstFlux d (recutExponent d (le_trans (by norm_num) hd)) ≤
      ENNReal.ofReal Ccg)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCoreFluxAtHalfSupGrad M Cgap Y m sb sigmaBarM hsig Kabs Ccg
      (recutExponent d (le_trans (by norm_num) hd)) recutOrderTop omega) :
    SpineDatumCoarseGrainingRecutFluxHalfSupGrad M Cgap Y m sb sigmaBarM hsig Kabs
      omega := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨hlt, hgt⟩ := recutOrderTop_window d hd1
  exact spineDatumCoarseGrainingRecutFluxAtHalfSupGrad_of_core M Cgap Y m sb hsig
    (recutExponent d hd1) recutOrderTop hlt hgt hCcg0 hCcgDom omega hcore

/-! ## 4. The producer, at the sup clause -/

/-- The core's producer from the supply, at the sup
clause.  The clause conjunct is a pure pass-through here, so the proof is the
one verbatim. -/
theorem spineDatumRecutCoreFluxAtHalfSupGrad_of_supply [NeZero d] (hd1 : 1 ≤ d)
    (M : ABKModel d) {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (hs : 0 < homS M) {Kabs Cen0 Ccg : ℝ} (hCcg0 : 0 ≤ Ccg)
    (omega : Cutoff.CutoffSample d) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤)
    (hKabs : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
        (recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0) (stepFourSchauderConstU d) ≤ Kabs)
    (hsupply : RecutCoreSupplyFluxAtSupGrad M Y m Cen0 Ccg hd1 hlog omega) :
    SpineDatumRecutCoreFluxAtHalfSupGrad M Cgap Y m (homSeamBase M hs)
      ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 Kabs Ccg
      (recutExponent d hd1) recutOrderTop omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  obtain ⟨S, Fflux, hS0, hS, hSbound, hCGm, hid⟩ :=
    hsupply L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKh0 : (0 : ℝ) ≤ Kh := hKh.nonneg hx0 hy0 hne
  have hcen : cubeCenter (originCube d m) ∈ openCubeSet (originCube d m) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)
  have hKhInf0 : (0 : ℝ) ≤ KhInf :=
    le_trans (norm_nonneg _) (hKhInf (cubeCenter (originCube d m)) hcen)
  have hdom1 := seamDom1Flux_of_identification M m (homK M) omega hs hlog hid L hL
  have hdom2 := seamDom2Flux_of_identification M m (homK M) omega hs hlog hid L hL
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hquot : (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 :=
    recutExponent_quotient d hd1
  have hguard : homS M + (d : ℝ) / (recutExponent d hd1).exponent.toReal ≤ 1 / 2 := by
    rw [hquot]; linarith only [hquarter]
  have hss2 : homS M < (recutOrderTop : FractionalOrder).1 := by
    rw [recutOrderTop_val]; linarith only [hquarter]
  obtain ⟨hs2lt, hs2gt⟩ := recutOrderTop_window d hd1
  have hgapexp := recutOrderTop_gapExponent
  have hKtest0 : (0 : ℝ) ≤ recutKtestHalf d hd1 M := recutKtestHalf_nonneg d hd1 M hlog
  have hCw0 : (0 : ℝ) ≤ recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0 := by
    obtain ⟨hs2lt', hs2gt'⟩ := recutOrderTop_window d hd1
    have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d recutOrderTop (recutExponent d hd1) :=
      cgOverlapDataConst_nonneg d recutOrderTop (recutExponent d hd1)
        (holderHalf_window (p := recutExponent d hd1) hs2lt' hs2gt').1
    have h1 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop (Ccg := Ccg)
      (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M) (kappa := 1) (theta := 1)
      hCcg0 hCgap hCen0 hs zero_le_one one_pos (by linarith only [hss2]) hCdata0 hgapexp
    have h2 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop (Ccg := Ccg)
      (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M)
      (kappa := recutKtestHalf d hd1 M) (theta := 7 / 8) hCcg0 hCgap hCen0 hs hKtest0
      (by norm_num) (by linarith only [hss2, hs]) hCdata0 hgapexp
    rw [recutCwHalfFluxAt, pairCwOf]
    linarith only [h1, h2]
  have hjn : (originCube d m).scale - ((homK M : ℕ) : ℤ) = homN M m := rfl
  refine ⟨homK M, recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0, S,
    (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal, recutOrderBase M hlog,
    Fflux, homK_pos hlog, hguard, ?_, hCw0, hKabs, ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal_le, hCGm, hS0, hS, ?_, ?_⟩
  · simp only [recutOrderBase_val]
    linarith only [hss2, hs]
  · exact hlevelFluxAt_of_seam M L omega m (homK M) (Annealed.sigmaBar M m).2 Y
      (recutExponent d hd1) recutOrderTop hCcg0 hs hlog hgamma1 hCgap hss2 hs2lt hs2gt
      hgapexp hKtest0 hKg hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin
  · exact hlevelDualHalfFluxAt_of_seam M L omega m (homK M) (Annealed.sigmaBar M m).2 Y
      (recutExponent d hd1) recutOrderTop hCcg0 hs hlog hgamma1 hCgap hss2 hs2lt
      hs2gt hgapexp rfl hKg hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin

end

end Algsuperdiff.Section4.Provider.Homogenization
