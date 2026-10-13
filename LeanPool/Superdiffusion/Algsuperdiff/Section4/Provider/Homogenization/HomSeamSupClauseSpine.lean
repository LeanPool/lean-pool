/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradProvider
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamSpineBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamSupClauseChain

/-!
# HomSeamSupClauseSpine

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The clause supplier and the budgeted supply layers, at the SUP-form clause

## What this file supplies

`HomSeamSupClauseChain` re-cut the seam carriers at the sup-form multiscale
clause.  This file carries the re-cut to the spine's clause supplier — the last
place the clause is visible — and re-states the two budgeted supply layers of
the budgeted gradient provider at the sup carriers:

```text
  homSpineClauseSupplierAtGrad_of_datumRecutFluxHalfSupGrad
  SeamEnergySupplyOfRegularityGradSupBudget
  SeamBundleOfRegularityHalfSupGradBudget
```

The supplier's proof is the same, with EXACTLY ONE token changed: clause (C3)
now runs through
`HomSpineSupFormRethread.spineClauseC3_of_supMultiscale`.  Its argument list,
its output constant `96 d² · liftGeomFactor (s + d/p) · C_w` and clause (C4)
are untouched — that is the losslessness measurement, executed.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The clause supplier, from the SUP-form datum -/

/-- **THE SPINE'S CLAUSE SUPPLIER, FROM THE SUP-FORM DATUM.**

The spine's clause supplier at the gradient binder, with
the multiscale conjunct read at the print's own sup aggregation.  Clause (C3)
now runs through `spineClauseC3_of_supMultiscale` at the IDENTICAL constant;
clause (C4) never sees the aggregation at all. -/
theorem homSpineClauseSupplierAtGrad_of_datumRecutFluxHalfSupGrad [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM)
    (omega : Cutoff.CutoffSample d)
    (hcg : SpineDatumCoarseGrainingRecutFluxHalfSupGrad M Cgap Y m sb sigmaBarM hsig Kabs
      omega) :
    HomSpineClauseSupplierAtGrad M Cgap Y m sb sigmaBarM Kabs omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  obtain ⟨jn, Cw, Ccg, E1, E2, Dg, S, EB, p, s, s1', s', s2, Fflux,
    hjn0, hguard, hCw, hKabsC, hEB, hdom, hpin1, hpin2, hs's2, hs2lt, hs2gt,
    hCGm, hS0, hS, hlevel, hCcg0, hE10, hE20, hDg0, hCdom, hE1, hE2, hDg, hlevelDual⟩ :=
    hcg L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hprPos : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  have hs0 : 0 < s.1 := s.2.1
  have hdq : (0 : ℝ) ≤ (d : ℝ) / p.exponent.toReal :=
    div_nonneg (Nat.cast_nonneg d) hprPos.le
  have hsle : s.1 ≤ 1 / 2 := by linarith only [hguard, hdq]
  have hbr : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
    dataBracket_nonneg_of_binders (h := h) (g := g) hsig hKg hKh hKhInf
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hsolFlux : IsDirichletSolutionOn
      (fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField
      (originCube d m) u h g :=
    isDirichletSolutionOn_fluxCorrected_of_cutoff M L m omega hsol
  /- the produced frame, and clause (C3) at the print's own aggregation -/
  obtain ⟨W, G, hWval, hGval, hWout, hw, hwI, hwc, hGI, hGzero⟩ :=
    spineFrame_of_dirichletPair hsol hcomp
  have hC3 := spineClauseC3_of_supMultiscale hprPos hs0 hguard hsig (hCGm G hGval) hS
    hlevel hWval hWout hw hwI hwc hGI hGzero
  /- the produced duality legs at `ã`, read at the SCHAUDER gau -/
  have hp2 : (2 : ℝ≥0∞) ≤ p.exponent := two_le_exponent_of_guard hd1 hs0 hguard
  have hspecC := Classical.choose_spec (exists_weakNegDualBounds_of_fluxPair d hd p hp2)
  rw [← cgDualBoundConstFlux_eq d hd p hp2] at hspecC
  obtain ⟨_hCtop, hlegs⟩ := hspecC
  have hlo : 0 < ((recutOrderHalf : FractionalOrder).1 - s'.1) *
      p.conjugate.exponent.toReal := by
    rw [recutOrderHalf_val, hpin2]
    exact mul_pos (by linarith only [hsle, hs0]) (finiteLpExponent_toReal_pos p.conjugate)
  have hhi : ((recutOrderHalf : FractionalOrder).1 - s'.1) *
      p.conjugate.exponent.toReal < (d : ℝ) := by
    rw [recutOrderHalf_val, hpin2]
    exact cgOrderWindowHi_half hd hs0 hp2
  have hs1s : s1'.1 < s'.1 := by
    rw [hpin1, hpin2]; linarith only [hs0]
  have hsc : (originCube d m).scale = m := rfl
  have hjnZ : (0 : ℤ) < (jn : ℤ) := by exact_mod_cast hjn0
  have hnm : (originCube d m).scale - (jn : ℤ) < m := by
    rw [hsc]; omega
  have hjn : (jn : ℤ) = m - ((originCube d m).scale - (jn : ℤ)) := by
    rw [hsc]; ring
  have hwgap : s.1 - s.1 / 4 ≤ s'.1 - s1'.1 := by
    rw [hpin1, hpin2]; linarith only [hs0]
  have hframe : ∀ v' : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v' h g →
        IntegrableOn (fun x => vecDot (v'.grad x) (sigmaBarM • v'.grad x))
            (openCubeSet (originCube d m)) volume ∧
          IntegrableOn (fun x => vecDot
              (matVecMul
                ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
                (u.grad x)) (v'.grad x)) (openCubeSet (originCube d m)) volume ∧
            (WeakNegDualBoundOn (originCube d m) (1 / 2)
                (Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) * sigmaBarM *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => matVecMul
                  ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
                  (u.grad x) - sigmaBarM • v'.grad x) ∧
              WeakNegDualBoundOn (originCube d m) (1 / 2)
                (Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => u.grad x - v'.grad x)) := by
    intro v' hcomp'
    refine ⟨integrableOn_comparatorEnergy sigmaBarM v',
      integrableOn_crossEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u v',
      ?_⟩
    exact hlegs M L omega m ((originCube d m).scale - (jn : ℤ)) hnm jn s1' s' s2
      recutOrderHalf hs1s hs's2 hlo hhi hjn sigmaBarM hsig g u v' h hsol hcomp' Kg hKg0
      hs2lt hs2gt hKg Ccg E1 E2 Dg S
      (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
      hCcg0 hE10 hE20 hDg0 hS0 hCdom hE1 hE2 hDg (s.1 - s.1 / 4)
      (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
      hwgap
      (printedLocalEnergy_nonneg (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
      (fun _ => le_rfl) hS hlevelDual
  /- clause (C4), at `α = 1/2` and the `s`-FREE Schauder consta -/
  obtain ⟨v', hcomp', hC4⟩ := stepFourEnergyFlux_of_dualBounds_uniform hd
    (by norm_num : (0 : ℝ) < 1 / 2) (le_refl (1 / 2 : ℝ)) M L m
    omega sigmaBarM Kg Kh KhInf Cw EB u h g hsig hCw hEB hbr hKg hKhInf hKh hsolFlux
    (integrableOn_selfEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) hframe
  have hCschNonneg : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
  refine ⟨EB, hEB, hdom, ?_, ?_⟩
  · refine hC3.mono fun x hx => ?_
    refine hx.trans ?_
    have hfac : 96 * (d : ℝ) ^ (2 : ℕ) *
        liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw ≤ Kabs := by
      have h1 : (0 : ℝ) ≤ 2 * Cw * stepFourSchauderConstU d :=
        mul_nonneg (by linarith only [hCw]) hCschNonneg
      rw [spineClauseConst] at hKabsC
      linarith only [h1, hKabsC]
    have hEBbr : (0 : ℝ) ≤
        EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
      mul_nonneg hEB hbr
    calc 96 * (d : ℝ) ^ (2 : ℕ) *
          liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw * EB *
            dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh
        = (96 * (d : ℝ) ^ (2 : ℕ) *
            liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw) *
            (EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
          ring
      _ ≤ Kabs * (EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) :=
          mul_le_mul_of_nonneg_right hfac hEBbr
      _ = Kabs * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
          ring
  · rw [dirichletComparator_energyAverage_eq hsig hcomp hcomp']
    refine hC4.trans ?_
    have hlift : (0 : ℝ) ≤ liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) :=
      liftGeomFactor_nonneg (by linarith only [hguard])
    have hfac : 2 * Cw * stepFourSchauderConstU d ≤ Kabs := by
      have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
        have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
        linarith only [hsq]
      have h2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) *
          liftGeomFactor (s.1 + (d : ℝ) / p.exponent.toReal) * Cw :=
        mul_nonneg (mul_nonneg hd2 hlift) hCw
      rw [spineClauseConst] at hKabsC
      linarith only [h2, hKabsC]
    rw [energyBracket]
    calc 2 * Cw * stepFourSchauderConstU d * EB *
          (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
              Real.sqrt sigmaBarM *
                (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)
        = (2 * Cw * stepFourSchauderConstU d) * (EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)) := by ring
      _ ≤ Kabs * (EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg hEB (sq_nonneg _))
      _ = Kabs * EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ) := by ring

/-! ## 2. The two budgeted supply layers, at the sup carriers -/

/-- The budgeted gradient energy supply at the
sup-form energy residue. -/
def SeamEnergySupplyOfRegularityGradSupBudget (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar gamma0 : ℝ) (Cen0F : ABKModel d → ℝ) (Ctop Creg : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ),
      ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RegularityDisplayAt M Creg (homAlpha M) m X omega) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RecutCoreSupplyFluxEnergySupGrad M
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
            (Cen0F M) hd1 hlog omega

/-- The budgeted gradient seam bundle at the sup-form
datum. -/
def SeamBundleOfRegularityHalfSupGradBudget (d : ℕ) [NeZero d]
    (cstar gamma0 Cgap : ℝ) (KabsF : ABKModel d → ℝ) (Ctop Creg : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hs : 0 < homS M) (m : ℤ),
      ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RegularityDisplayAt M Creg (homAlpha M) m X omega) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          ethmB M Cgap
              (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
              (homN M m) (homSeamBase M hs) omega ≠ ⊤) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          SpineDatumCoarseGrainingRecutFluxHalfSupGrad M Cgap
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
            (homSeamBase M hs) ((Annealed.sigmaBar M m : ℝ))
            (Annealed.sigmaBar M m).2 (KabsF M) omega

end

end Algsuperdiff.Section4.Provider.Homogenization
