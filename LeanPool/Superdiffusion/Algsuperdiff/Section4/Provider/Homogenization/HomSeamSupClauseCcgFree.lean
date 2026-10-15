/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamSupClauseProvider

/-!
# HomSeamSupClauseCcgFree

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Seam supply at a model-dependent clause constant

The clause constant is explicit at each model. This module supplies three
interfaces:

* `RecutCoreSupplyFluxSupClauseAt`: the sup-form clause at a constant `Ccg`;
* `SeamMultiscaleSupClauseSupplyAt`: its almost-sure supply at `CcgF M`;
* `SeamSupplyFluxAtSupGradBudget`: the energy and clause supply, together with
  the flux-corrected parent identification, at that same model-dependent constant.

`seamSupplyFluxAtSupGradBudget_of_supClauseAt` combines a clause supply with
the regularity display. The downstream core in `HomSeamSupClauseChain` already
carries `Ccg` freely, so `seamBundleOfRegularityHalfSupGradBudget_of_supplyAt`
produces the budgeted seam bundle without fixing a numeral for this constant.

The pairing envelope is linear in `Ccg` and affine in `C_en⁰`, as proved by
`recutCwHalfEnvelope_affine`. For positive exponents,
`one_le_coarseGrainingGeomFactor` bounds the energy factor below by one. With
this hypothesis, `seamKabsAt_le_budget` bounds the full constant from the product budget
`Ccg * GEOM ≤ C_bud * L`.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The clause carrier and the supply, at a FREE `Ccg` -/

/-- **THE SUP-FORM CLAUSE CARRIER AT A FREE `Ccg`.**

The sup-form clause carrier of `HomSeamSupClauseProvider` with the numeral pin
`recutPinnedCcgFlux d p` replaced by a parameter.  NOTHING else changes — not a
binder, not an order, not a constant. -/
def RecutCoreSupplyFluxSupClauseAt (M : ABKModel d) (m : ℤ)
    (hd1 : 1 ≤ d) (hlog : 4 ≤ |Real.log M.gamma|) (Ccg : ℝ)
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
      ∃ Fflux : Vec d → Vec d,
        ∀ G : Vec d → Vec d,
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
            G Fflux

/-- The sup-form clause, asked almost surely at every admissible model and
scale, at a MODEL-DEPENDENT constant `CcgF M`. -/
def SeamMultiscaleSupClauseSupplyAt (d : ℕ) (hd1 : 1 ≤ d)
    (cstar gamma0 : ℝ) (CcgF : ABKModel d → ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ),
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        RecutCoreSupplyFluxSupClauseAt M m hd1 hlog (CcgF M) omega

/-! ## 2. The supply layer at `CcgF` -/

/-- The energy and clause supply at a model-dependent constant `CcgF M`,
with the flux-corrected parent identification included in
`RecutCoreSupplyFluxAtSupGrad`. -/
def SeamSupplyFluxAtSupGradBudget (d : ℕ) (hd1 : 1 ≤ d)
    (cstar gamma0 : ℝ) (Cen0F CcgF : ABKModel d → ℝ) (Ctop Creg : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ),
      ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RegularityDisplayAt M Creg (homAlpha M) m X omega) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RecutCoreSupplyFluxAtSupGrad M
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
            (Cen0F M) (CcgF M) hd1 hlog omega

/-- **THE SUPPLY LAYER, FROM THE CLAUSE ALONE.**

The supply layer of `HomSeamSupClauseProvider` at a free `Ccg`, with the flux-corrected parent
identification (already unconditional)
appended so that the output is the `Ccg`-free carrier
`RecutCoreSupplyFluxAtSupGrad`. -/
theorem seamSupplyFluxAtSupGradBudget_of_supClauseAt (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) {gamma0in : ℝ} {CcgF : ABKModel d → ℝ}
    (hg0in : 0 < gamma0in)
    (hclause : SeamMultiscaleSupClauseSupplyAt d hd1 cstar gamma0in CcgF) :
    ∃ gamma0 Ctop : ℝ, 0 < gamma0 ∧ 0 ≤ Ctop ∧
      ∀ Creg : ℝ, 0 < Creg →
        SeamSupplyFluxAtSupGradBudget d hd1 cstar gamma0
          (fun M => Creg * 729 *
            coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
              (homS M / 4))
          CcgF Ctop Creg := by
  obtain ⟨Cstep, hCstep, hslot⟩ := seamEnergySlot_of_regularityDisplayAt d hd1
  obtain ⟨g2, hg2, hcuts⟩ := ae_seam_quarter_errors_ne_top d cstar hcstar
  refine ⟨min gamma0in g2, seamTopScaleConst d Cstep, lt_min hg0in hg2,
    seamTopScaleConst_nonneg d hCstep.le, ?_⟩
  intro Creg hCreg M hcs hgamma hlog m X hXmeas hXfin hXdisp
  have hg_in : M.gamma ≤ gamma0in := le_trans hgamma (min_le_left _ _)
  have hg_2 : M.gamma ≤ g2 := le_trans hgamma (min_le_right _ _)
  have hs : 0 < homS M := homS_pos (by linarith only [hlog])
  have hcutsM := hcuts M hcs hg_2 hs m
  have hclM := hclause M hcs hg_in hlog m
  have hrep1 := ae_forall_fluxCorrectedError_eq_representative M m
    ⟨1 / 4 / 2, half_pos seamQuarterPos⟩
  have hrep2 := ae_forall_fluxCorrectedError_eq_representative M m
    ⟨1 / 4, seamQuarterPos⟩
  filter_upwards [hXdisp, hXfin, hcutsM, hclM, hrep1, hrep2,
    ae_fluxCorrectedParentIdentification M m] with omega hdisp hXne hcut hcl hr1 hr2 hid
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  obtain ⟨Fflux, hCGm⟩ := hcl L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hXne
  obtain ⟨S, hS0, hSpart, hSb⟩ :=
    hslot M m omega hCreg hlog hk.symm hdisp L hL u h g Kg Kh KhInf hsol hKg hKh hKhInf
      hgrad (hr1 ⟨L, hL⟩) (hr2 ⟨L, hL⟩) hcut.1 hcut.2.1 hcut.2.2
  refine ⟨S, Fflux, hS0, hSpart, ?_, hCGm, hid⟩
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : (0 : ℝ) ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hKh0 : (0 : ℝ) ≤ Kh := hKh.nonneg hx0 hy0 hne
  have hcen : cubeCenter (originCube d m) ∈ openCubeSet (originCube d m) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)
  have hKhInf0 : (0 : ℝ) ≤ KhInf :=
    le_trans (norm_nonneg _) (hKhInf (cubeCenter (originCube d m)) hcen)
  have hB : (0 : ℝ) ≤ energyBracket ((Annealed.sigmaBar M m : ℝ))
      (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
    energyBracket_nonneg (Real.rpow_nonneg (by norm_num) _) hKg0 hKhInf0 hKh0
  have hF : (0 : ℝ) ≤ recutEnergyFactor M
      (seamEnlargedY M m (seamTopScaleConst d Cstep)
        (homMinimalScaleFactor (1 - homAlpha M) X)) m omega :=
    recutEnergyFactor_nonneg _ _ _ _
  have hconst := recutEnergySlotConst_le_of_geom hd1 hCreg.le hlog
    (GEOM := coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
      (homS M / 4)) le_rfl
  exact le_trans hSb
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hF) hB)

/-! ## 3. `K_abs` at a free `Ccg`, and its budget -/

/-- The `C_en⁰` slope of the pairing envelope: the envelope is AFFINE in
`C_en⁰` with this slope, at every `Ccg`. -/
def seamCwCen0Slope (d : ℕ) (hd1 : 1 ≤ d) : ℝ :=
  2 * (1 + recutKtestHalfBound d hd1 * (7 / 8 : ℝ)⁻¹)

theorem seamCwCen0Slope_nonneg (d : ℕ) (hd1 : 1 ≤ d) : 0 ≤ seamCwCen0Slope d hd1 := by
  have hKB : (0 : ℝ) ≤ recutKtestHalfBound d hd1 := recutKtestHalfBound_nonneg d hd1
  have h : (0 : ℝ) ≤ recutKtestHalfBound d hd1 * (7 / 8 : ℝ)⁻¹ :=
    mul_nonneg hKB (by norm_num)
  rw [seamCwCen0Slope]
  linarith only [h]

/-- **THE ENVELOPE IS LINEAR IN `Ccg` AND AFFINE IN `C_en⁰`.**  Every one of the
four legs of `recutCwHalfEnvelope` carries `Ccg` exactly once, and only the two
`C_en⁰` legs carry `C_en⁰`. -/
theorem recutCwHalfEnvelope_affine (d : ℕ) (hd1 : 1 ≤ d) (Ccg Cgap Cen0 : ℝ) :
    recutCwHalfEnvelope d hd1 Ccg Cgap Cen0 =
      Ccg * (Cen0 * seamCwCen0Slope d hd1 + recutCwHalfEnvelope d hd1 1 Cgap 0) := by
  rw [recutCwHalfEnvelope, recutCwHalfEnvelope, seamCwCen0Slope]
  ring

/-- **`K_abs` AT A FREE `Ccg`.**  The half-gauge `K_abs`
with the numeral pin freed; at the pin it IS that term. -/
def seamKabsAt (d : ℕ) (hd1 : 1 ≤ d) (Cgap Ccg Cen0 : ℝ) : ℝ :=
  (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
    recutCwHalfEnvelope d hd1 Ccg Cgap Cen0

theorem seamKabsAt_nonneg (d : ℕ) (hd1 : 1 ≤ d) {Cgap Ccg Cen0 : ℝ} (hCcg0 : 0 ≤ Ccg)
    (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0) : 0 ≤ seamKabsAt d hd1 Cgap Ccg Cen0 := by
  have hU : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
  have hd2 : (0 : ℝ) ≤ 288 * (d : ℝ) ^ (2 : ℕ) := by
    have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
    linarith only [hsq]
  exact mul_nonneg (by linarith only [hU, hd2])
    (recutCwHalfEnvelope_nonneg d hd1 hCcg0 hCgap hCen0)

/-- **THE BUDGET AT A FREE `Ccg`.**

`K_abs` is inside `C_abs·L` as soon as the PRODUCT `Ccg·GEOM` is inside
`C_bud·L`.  The energy factor is at least `1`, so the same input also controls
the `Ccg`-only leg: no second budget hypothesis is needed. -/
theorem seamKabsAt_le_budget (d : ℕ) (hd1 : 1 ≤ d) {Cgap : ℝ} (hCgap : 0 < Cgap)
    {Creg Ccg GEOM Cbud L : ℝ} (hCreg : 0 < Creg) (hCcg0 : 0 ≤ Ccg) (hGEOM1 : 1 ≤ GEOM)
    (hbud : Ccg * GEOM ≤ Cbud * L) :
    seamKabsAt d hd1 Cgap Ccg (Creg * 729 * GEOM) ≤
      ((2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
        (Creg * 729 * seamCwCen0Slope d hd1 + recutCwHalfEnvelope d hd1 1 Cgap 0) *
          Cbud) * L := by
  have hU : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
  have hd2 : (0 : ℝ) ≤ 288 * (d : ℝ) ^ (2 : ℕ) := by
    have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
    linarith only [hsq]
  have hUsum : (0 : ℝ) ≤ 2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ) := by
    linarith only [hU, hd2]
  have ha : (0 : ℝ) ≤ seamCwCen0Slope d hd1 := seamCwCen0Slope_nonneg d hd1
  have hb : (0 : ℝ) ≤ recutCwHalfEnvelope d hd1 1 Cgap 0 :=
    recutCwHalfEnvelope_nonneg d hd1 zero_le_one hCgap le_rfl
  have hA0 : (0 : ℝ) ≤ Creg * 729 * seamCwCen0Slope d hd1 :=
    mul_nonneg (by linarith only [hCreg]) ha
  have hcg : Ccg ≤ Cbud * L :=
    le_trans (le_mul_of_one_le_right hCcg0 hGEOM1) hbud
  have h1 : Creg * 729 * seamCwCen0Slope d hd1 * (Ccg * GEOM) ≤
      Creg * 729 * seamCwCen0Slope d hd1 * (Cbud * L) :=
    mul_le_mul_of_nonneg_left hbud hA0
  have h2 : recutCwHalfEnvelope d hd1 1 Cgap 0 * Ccg ≤
      recutCwHalfEnvelope d hd1 1 Cgap 0 * (Cbud * L) :=
    mul_le_mul_of_nonneg_left hcg hb
  have hE : recutCwHalfEnvelope d hd1 Ccg Cgap (Creg * 729 * GEOM) =
      Creg * 729 * seamCwCen0Slope d hd1 * (Ccg * GEOM) +
        recutCwHalfEnvelope d hd1 1 Cgap 0 * Ccg := by
    rw [recutCwHalfEnvelope_affine]
    ring
  have hEle : recutCwHalfEnvelope d hd1 Ccg Cgap (Creg * 729 * GEOM) ≤
      (Creg * 729 * seamCwCen0Slope d hd1 + recutCwHalfEnvelope d hd1 1 Cgap 0) *
        (Cbud * L) := by
    rw [hE]
    linarith only [h1, h2]
  rw [seamKabsAt]
  calc (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
        recutCwHalfEnvelope d hd1 Ccg Cgap (Creg * 729 * GEOM)
      ≤ (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
          ((Creg * 729 * seamCwCen0Slope d hd1 +
            recutCwHalfEnvelope d hd1 1 Cgap 0) * (Cbud * L)) :=
        mul_le_mul_of_nonneg_left hEle hUsum
    _ = ((2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
          (Creg * 729 * seamCwCen0Slope d hd1 + recutCwHalfEnvelope d hd1 1 Cgap 0) *
            Cbud) * L := by ring

/-! ## 4. The bundle, at `CcgF` -/

/-- **THE BUNDLE, AT A MODEL-DEPENDENT CLAUSE CONSTANT.**

The budgeted bundle of `HomSeamSupClauseSpine` with the numeral pin replaced by
`CcgF M`.  The two facts the pin used to
supply — `0 ≤ Ccg` and `C(p,d) ≤ ofReal Ccg` — become hypotheses; every other
step is unchanged, because the whole chain above `RecutCoreSupplyFluxAtSupGrad`
already carries `Ccg` free. -/
theorem seamBundleOfRegularityHalfSupGradBudget_of_supplyAt (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) {cstar gamma0 Cgap Ctop Creg : ℝ} {Cen0F CcgF : ABKModel d → ℝ}
    (hCgap : 0 < Cgap)
    (hCen0 : ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| → 0 ≤ Cen0F M)
    (hCcg0 : ∀ M : ABKModel d, 0 ≤ CcgF M)
    (hCcgDom : ∀ M : ABKModel d,
      cgDualBoundConstFlux d (recutExponent d (le_trans (by norm_num) hd)) ≤
        ENNReal.ofReal (CcgF M))
    (hsupply : SeamSupplyFluxAtSupGradBudget d (le_trans (by norm_num) hd) cstar gamma0
      Cen0F CcgF Ctop Creg) :
    SeamBundleOfRegularityHalfSupGradBudget d cstar (min gamma0 (1 / 81)) Cgap
      (fun M => seamKabsAt d (le_trans (by norm_num) hd) Cgap (CcgF M) (Cen0F M))
      Ctop Creg := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  intro M hcs hgamma hs m X hXmeas hXfin hXdisp hfin
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_s : M.gamma ≤ gamma0 := le_trans hgamma (min_le_left _ _)
  have hg81 : M.gamma ≤ 1 / 81 := le_trans hgamma (min_le_right _ _)
  have hlog : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg81
  have hgamma1 : M.gamma < 1 := by linarith only [hg81]
  have hsupF := hsupply M hcs hg_s hlog m X hXmeas hXfin hXdisp
  have hKabsC : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
      (recutCwHalfFluxAt d hd1 M (CcgF M) Cgap (Cen0F M)) (stepFourSchauderConstU d) ≤
      seamKabsAt d hd1 Cgap (CcgF M) (Cen0F M) :=
    spineClauseConst_le_abs_half d hd1 M (hCcg0 M) hCgap (hCen0 M hlog) hlog
  filter_upwards [hsupF, hfin] with omega hsupplyOmega hfinOmega
  exact spineDatumCoarseGrainingRecutFluxAtHalfSupGrad_of_core_pinned hd M Cgap
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
    (homSeamBase M hs) (Annealed.sigmaBar M m).2 (hCcg0 M) (hCcgDom M) omega
    (spineDatumRecutCoreFluxAtHalfSupGrad_of_supply hd1 M
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m hs (hCcg0 M)
      omega hlog hgamma1 hCgap (hCen0 M hlog) hfinOmega hKabsC hsupplyOmega)

/-! ## 5. The energy factor is at least one -/

/-- The `ℓ^p` depth-aggregation energy factor `(1-3^{-wp})^{-1/p}` is at least
`1`: the base of the power is at least `1`.  This is what lets the ONE budget
hypothesis `Ccg·GEOM ≤ C_bud·L` also control `Ccg` alone. -/
theorem one_le_coarseGrainingGeomFactor {p w : ℝ} (hp : 0 < p) (hw : 0 < w) :
    1 ≤ coarseGrainingGeomFactor p w := by
  have hlt : (3 : ℝ) ^ (-(w * p)) < 1 := three_rpow_neg_lt_one (mul_pos hw hp)
  have hpos0 : (0 : ℝ) < (3 : ℝ) ^ (-(w * p)) := Real.rpow_pos_of_pos (by norm_num) _
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(w * p)) := by linarith only [hlt]
  have hden1 : 1 - (3 : ℝ) ^ (-(w * p)) ≤ 1 := by linarith only [hpos0]
  have hinv : (1 : ℝ) ≤ (1 - (3 : ℝ) ^ (-(w * p)))⁻¹ := by
    have h := inv_anti₀ hden hden1
    rwa [inv_one] at h
  rw [coarseGrainingGeomFactor_def]
  calc (1 : ℝ) = (1 : ℝ) ^ (1 / p) := (Real.one_rpow _).symm
    _ ≤ ((1 - (3 : ℝ) ^ (-(w * p)))⁻¹) ^ (1 / p) :=
        Real.rpow_le_rpow zero_le_one hinv (by positivity)

end

end Algsuperdiff.Section4.Provider.Homogenization
