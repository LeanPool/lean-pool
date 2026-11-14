/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamCompositionCcg
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthBandBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormMonotone
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGDischargeInstantiation
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalDatum

/-!
# HomSeamProviderFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The datum instantiation: the budgeted sup-clause producer, UNCONDITIONAL

## What this file does

`HomSeamCompositionCcg.generatorRenormalizationShape_of_supClauseProducerAtBudgeted`
reduces the generator-renormalization root's shape — the sup clause for the
coarse-grained flux over the whole depth band, at the budgeted clause constant —
to ONE object, `SupClauseProducerAtBudgeted`.
This file PRODUCES that object, with no hypothesis at all
(`supClauseProducerAtBudgeted_holds`), by instantiating the unconditional
band-input producer at the lane's own data:

* the clause constant is `CcgF M:= max (recutPinnedCcgFlux d p) (produced M)`
  with `produced M = (√d · CA(M) · C(p,d)).toReal` the displayed constant of
  `HomSpineSupFormClauseAt`, at the pin `x₀ = homS M · p'`; the `max` raise is
  `CoarseGrainingSupMultiscale.mono_ccg`, and it discharges the duality pin via
  the `cgDualBoundConstFlux_le_ofReal_of_pinned_le`;
* the budget `CcgF M · GEOM ≤ C_bud · |log γ|` holds at
  `C_bud = 2·recutPinnedCcgFlux d p + √d·K(d,p)·C(p,d)·2`: the produced leg is
  the `seamProducedCcg_le_budget`, the pinned leg is the
  `recut_geomFactor_le_absLog` (`GEOM ≤ 2|log γ|`);
* the supply is produced PER SAMPLE, deterministically (`ae_of_all` shape): the
  Dirichlet pair gives the forced-equation/scalar/`H¹₀` triple at the printed
  coefficient `ã` (`isDirichletSolutionOn_fluxCorrected_of_cutoff` + the
  `HomCGDischargeInstantiation` bridges), the Hölder binder gives
  `𝐠 ∈ W^{s₂,p}` (`memCubeEuclideanFullWsp_of_holderHalf`), the `𝓔`/`D_g`
  slots self-dominate at their own `toReal` pins, the two-sided band pin is
  `recutDepthBandPin`, and the produced clause is transported to the lane's
  slots by `mono_s1` (error order `s/8`, clause slot `s/4`), `mono_ccg`, and
  `congr_grad_of_eqOn`.

`generator_renormalization_provider_final` is the endpoint: the frozen root's
SHAPE at every dimension and every `cstar > 0`, from `{d, cstar, hcstar}` and
nothing else.  The theorem statement itself is neither imported
nor claimed here; its discharge is a separate, audited step.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. THE ONE OBJECT, PRODUCED -/

/-- **THE BUDGETED SUP-CLAUSE PRODUCER HOLDS.**  No hypothesis: the band-input
producer, instantiated at the lane's own data and transported to the lane's
slots. -/
theorem supClauseProducerAtBudgeted_holds (d : ℕ) (cstar : ℝ) :
    SupClauseProducerAtBudgeted d cstar := by
  refine ⟨1, one_pos, fun hd inst => ?_⟩
  have : NeZero d := inst
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨C, hCne, hprod⟩ :=
    exists_coarseGrainingSupMultiscale_of_depthConverseOn_at d hd (recutExponent d hd1)
      (recutExponent_two_le d hd1)
  /- the shared sign fac -/
  have hpin0 : (0 : ℝ) ≤ recutPinnedCcgFlux d (recutExponent d hd1) :=
    recutPinnedCcgFlux_nonneg d (recutExponent d hd1)
  have hsq : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hK0 : (0 : ℝ) ≤ gridDepthPinConst d (recutExponent d hd1) := by
    have h := one_le_gridDepthPinConst d (recutExponent d hd1)
    linarith only [h]
  have hprodCoef0 : (0 : ℝ) ≤
      Real.sqrt d * gridDepthPinConst d (recutExponent d hd1) * C.toReal * 2 := by
    have h1 : (0 : ℝ) ≤ Real.sqrt d * gridDepthPinConst d (recutExponent d hd1) *
        C.toReal :=
      mul_nonneg (mul_nonneg hsq hK0) ENNReal.toReal_nonneg
    linarith only [h1]
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hppos : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by
    rw [recutExponent_toReal]
    linarith only [hdR]
  refine ⟨fun M => max (recutPinnedCcgFlux d (recutExponent d hd1))
      ((ENNReal.ofReal (Real.sqrt d) *
          gridDepthConverseConst (recutExponent d hd1)
            (gridDepthGagliardoConst d (recutExponent d hd1))
            (homS M * (recutExponent d hd1).conjugate.exponent.toReal) * C).toReal),
    2 * recutPinnedCcgFlux d (recutExponent d hd1) +
      Real.sqrt d * gridDepthPinConst d (recutExponent d hd1) * C.toReal * 2,
    ?_, ?_, ?_, ?_, ?_⟩
  /- 1. the budget constant is nonnegati -/
  · linarith only [hpin0, hprodCoef0]
  /- 2. the clause constant is nonnegati -/
  · intro M
    exact le_trans hpin0 (le_max_left _ _)
  /- 3. the duality-leg pin, via the pinned entry poi -/
  · intro M
    exact cgDualBoundConstFlux_le_ofReal_of_pinned_le d hd (recutExponent d hd1)
      (recutExponent_two_le d hd1) (le_max_left _ _)
  /- 4. the budget, leg by leg -/
  · intro M hlog
    have hs : 0 < homS M := homS_pos (by linarith only [hlog])
    have hGEOM0 : (0 : ℝ) ≤ coarseGrainingGeomFactor
        ((recutExponent d hd1).exponent.toReal) (homS M / 4) :=
      coarseGrainingGeomFactor_nonneg hppos (by linarith only [hs])
    have hL0 : (0 : ℝ) ≤ |Real.log M.gamma| := abs_nonneg _
    refine le_trans (le_of_eq (max_mul_of_nonneg _ _ hGEOM0)) (max_le ?_ ?_)
    · /- the pinned leg: `pin · GEOM ≤ pin · 2|log γ| ≤ C_bud |log γ|` -/
      have hgeom := recut_geomFactor_le_absLog hd1 M hlog
      have h1 := mul_le_mul_of_nonneg_left hgeom hpin0
      have h2 : 2 * recutPinnedCcgFlux d (recutExponent d hd1) * |Real.log M.gamma| ≤
          (2 * recutPinnedCcgFlux d (recutExponent d hd1) +
            Real.sqrt d * gridDepthPinConst d (recutExponent d hd1) * C.toReal * 2) *
              |Real.log M.gamma| :=
        mul_le_mul_of_nonneg_right (by linarith only [hprodCoef0]) hL0
      linarith only [h1, h2]
    · /- the produced leg: the machine-checked budg -/
      refine le_trans (seamProducedCcg_le_budget d hd1 C M hlog) ?_
      exact mul_le_mul_of_nonneg_right (by linarith only [hpin0]) hL0
  /- 5. the supply, per sample and deterministical -/
  · intro M _hcs _hgamma hlog m
    refine Filter.Eventually.of_forall fun omega => ?_
    intro L _hL u v _h g Kg _Kh _KhInf hsol hcomp hKg _hKh _hKhInf
    have hs : 0 < homS M := homS_pos (by linarith only [hlog])
    have hr0 : (0 : ℝ) < (recutExponent d hd1).conjugate.exponent.toReal :=
      finiteLpExponent_toReal_pos (recutExponent d hd1).conjugate
    have hxpin : 0 < homS M * (recutExponent d hd1).conjugate.exponent.toReal :=
      mul_pos hs hr0
    /- the Dirichlet legs -/
    have hsolF := isDirichletSolutionOn_fluxCorrected_of_cutoff M L m omega hsol
    have hu := isForcedEquation_of_dirichletSolutionOn
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) hsolF
    have hv := isScalarForcedEquation_of_dirichletSolutionOn hcomp
    have hzero := hasH10Difference_of_dirichletPair hsol hcomp
    /- the forcing datum, from the root's own Hölder bind -/
    obtain ⟨x0, y0, hx0m, hy0m, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
    have hKg0 : (0 : ℝ) ≤ Kg := hKg.nonneg hx0m hy0m hne
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hdR]
    have hquot : (d : ℝ) / (4 * (d : ℝ)) = 1 / 4 := by field_simp
    have hgt : 1 / 2 - (d : ℝ) / (recutExponent d hd1).exponent.toReal <
        (recutOrderTop : FractionalOrder).1 := by
      rw [recutExponent_toReal, recutOrderTop_val, hquot]
      norm_num
    have hg2 : MemCubeEuclideanFullWsp (originCube d m) recutOrderTop
        (recutExponent d hd1) g :=
      memCubeEuclideanFullWsp_of_holderHalf hKg0
        (by rw [recutOrderTop_val]; norm_num) hgt hKg
    /- the order pi -/
    have hs1s : (recutOrderLow (recutOrderBase M hlog)).1 < (recutOrderBase M hlog).1 := by
      rw [recutOrderLow_val, recutOrderBase_val]
      linarith only [hs]
    have hss2 : (recutOrderBase M hlog).1 < (recutOrderTop : FractionalOrder).1 := by
      rw [recutOrderBase_val, recutOrderTop_val]
      have hq := homS_le_quarter hlog
      linarith only [hq]
    /- the three self-dominatio -/
    have hE1 := parentErrorOne_dominates_self (originCube d m)
      (recutParentScale m (homK M)) (fluxCorrectedCoeffOn M L m (originCube d m) omega)
      (Annealed.sigmaBar M m).2 (recutOrderLow (recutOrderBase M hlog))
    have hE2 := parentErrorTwo_dominates_self (originCube d m)
      (recutParentScale m (homK M)) (fluxCorrectedCoeffOn M L m (originCube d m) omega)
      (Annealed.sigmaBar M m).2 (fractionalOrderHalf (recutOrderLow (recutOrderBase M hlog)))
    have hDg := overlapSeminorm_dominates_self (originCube d m) recutOrderTop
      (recutExponent d hd1) hg2
    /- THE PRODUCER, at the lane's own da -/
    have hclause := hprod
      (gridDepthConverseConst (recutExponent d hd1)
        (gridDepthGagliardoConst d (recutExponent d hd1))
        (homS M * (recutExponent d hd1).conjugate.exponent.toReal))
      (gridDepthConverseConst_ne_top (gridDepthGagliardoConst_ne_top d (recutExponent d hd1))
        (homS M * (recutExponent d hd1).conjugate.exponent.toReal))
      (DepthBandPin (recutExponent d hd1)
        (homS M * (recutExponent d hd1).conjugate.exponent.toReal))
      (depthConverseOn_of_bandInput hxpin
        (gridDepthGagliardoBandInput_holds d (recutExponent d hd1)))
      m (homK M) (homK_pos hlog)
      (recutOrderLow (recutOrderBase M hlog)) (recutOrderBase M hlog) recutOrderTop
      hs1s hss2 (recutDepthBandPin hd1 M hlog)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega)
      ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 g u v
      hg2 hu hv hzero
      (recutPinnedE1Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog))
      (recutPinnedE2Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog))
      (recutPinnedDg m recutOrderTop (recutExponent d hd1) g)
      (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
      ((centeredCubeGradientDifferenceL2Field m u v).toField)
      ((centeredCubeFluxDifferenceL2Field m
        (fluxCorrectedCoeffOn M L m (originCube d m) omega)
        ((Annealed.sigmaBar M m : ℝ)) u v).toField)
      (recutPinnedE1Flux_nonneg M L omega m (homK M) (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog))
      (recutPinnedE2Flux_nonneg M L omega m (homK M) (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog))
      (recutPinnedDg_nonneg m recutOrderTop (recutExponent d hd1) g)
      (fun R => printedLocalEnergy_nonneg _ _ R) (fun _ => le_rfl)
      hE1 hE2 hDg rfl rfl
    /- transport to the lane's slots: `s₁` up to `s/4`, `Ccg` up to the maximum -/
    have hle : (recutOrderLow (recutOrderBase M hlog)).1 ≤ homS M / 4 := by
      rw [recutOrderLow_val, recutOrderBase_val]
      linarith only [hs]
    have hstep1 := hclause.mono_s1 hppos.le
      (fun R => printedLocalEnergy_nonneg _ _ R) hle
    have hstep2 := hstep1.mono_ccg
      (le_max_right (recutPinnedCcgFlux d (recutExponent d hd1)) _) hs hss2
      (recutPinnedE1Flux_nonneg M L omega m (homK M) (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog))
      (recutPinnedDg_nonneg m recutOrderTop (recutExponent d hd1) g)
      (fun R => printedLocalEnergy_nonneg _ _ R)
    /- the flux representative is free; the gradient slot serves every `G` -/
    refine ⟨(centeredCubeFluxDifferenceL2Field m
      (fluxCorrectedCoeffOn M L m (originCube d m) omega)
      ((Annealed.sigmaBar M m : ℝ)) u v).toField, fun G hG => ?_⟩
    exact hstep2.congr_grad_of_eqOn fun x hx => (hG x hx).symm

/-! ## 2. THE ENDPOINT -/

/-- **THE PROVIDER, FINAL.**  The frozen root's shape at every
dimension and every `cstar > 0`, from `{d, cstar, hcstar}` and NOTHING else.
The theorem statement is neither imported nor claimed here. -/
theorem generator_renormalization_provider_final (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) : GeneratorRenormalizationShape d cstar :=
  generatorRenormalizationShape_of_supClauseProducerAtBudgeted d cstar hcstar
    (supClauseProducerAtBudgeted_holds d cstar)

end

end Algsuperdiff.Section4.Provider.Homogenization
