/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AffineAnnealedCutoffEnergyComponent
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffTerminalEnergyIntegrability
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungCenteredDecomposition
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPartialConstants
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungWeakTop
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungBoundaryNormalization

/-!
# High-contrast homogenization: Provider.Response.PreYoungPrimalAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Primal compact pre-Young assembly

The centered decomposition, weak-product bound, cutoff-energy estimate, and
boundary-row estimates combine into the compact primal response family.  The
finite weak-quantity assumption is confined to the component branch.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Primal boundary-row estimates complete the compact response bound, with
the infinite weak-quantity branch closed algebraically. -/
theorem compact_pre_young_primal_of_row_estimates
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l s t : ℤ} {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l m0))
    (hstat : HCPoly.Frozen.IsStationaryLaw P) (hls : l ≤ s)
    (H : ℕ) (ht : t = s + (H : ℤ))
    (hints : HasFiniteAdaptedMean P (roundedGrid l m0) s)
    (hintt : HasFiniteAdaptedMean P (roundedGrid l m0) t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    {Cpre : ℝ} (hCpre : 1 ≤ Cpre)
    (hcut : 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound ≤ Cpre)
    (hcomponent : preYoungComponentCoefficient d ≤ Cpre)
    (hfour : 4 ≤ Cpre) (hsqrtTwo : Real.sqrt 2 ≤ Cpre)
    (hrows :
      profilePrimalWeakQuantity P m0
          (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (fun a ↦ a.subSkew g hg) p r ≠ ⊤ →
      let hq := Recurrence.posDef_of_isRoundedGrid hgrid
      let X := profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg) p r
      let tau := profilePrimalResponseDefect P hq g hg s t p r
      let EJ := ∫ a, responseJ (adaptedDomain hq t)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P
      let gain := preYoungComponentCoefficient d *
        (3 : ℝ) ^ (-(H : ℝ)) * Real.sqrt EJ
      let cut := adaptedPreYoungCutoff (roundedGrid l m0) hq t
      ENNReal.ofReal
          |vecDot X.2 (profilePrimalCutoffMean P hq t
            (fun a ↦ a.subSkew g hg) cut p r).1| ≤
          ENNReal.ofReal (Real.sqrt (4 * tau) *
            profileSchurLoadFlux
              (profileHattedBlock g (adaptedMean P (roundedGrid l m0) s)) X.2) +
            ENNReal.ofReal gain *
              profilePrimalHattedEarlierRow P (roundedGrid l m0) g s X.1 X.2 ^
                (1 / 2 : ℝ) ∧
        ENNReal.ofReal
          |vecDot X.1 (profilePrimalCutoffMean P hq t
            (fun a ↦ a.subSkew g hg) cut p r).2| ≤
          ENNReal.ofReal (Real.sqrt (4 * tau) *
            profileSchurLoadGradient
              (profileHattedBlock g (adaptedMean P (roundedGrid l m0) s)) X.1) +
            ENNReal.ofReal gain *
              profilePrimalHattedEarlierRow P (roundedGrid l m0) g s X.1 X.2 ^
                (1 / 2 : ℝ)) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let X := profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg) p r
    let tau := profilePrimalResponseDefect P hq g hg s t p r
    let EJ := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P
    let row := profilePrimalHattedEarlierRow P (roundedGrid l m0) g s X.1 X.2
    let weak := profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r
    let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
      (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq t))
        (centeredResponseOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r) i ∂P)
      (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
        ((a.subSkew g hg).coeffOn (adaptedDomain hq t))
        (centeredResponseOptimizer (adaptedDomain hq t)
          (a.subSkew g hg) p r) i ∂P)
    ∀ Cresp, Cpre ≤ Cresp →
      ENNReal.ofReal |Jtilde| ≤
        ENNReal.ofReal Cresp * ENNReal.ofReal (Real.sqrt tau) *
          (ENNReal.ofReal (Real.sqrt tau) +
            ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal Cresp *
          ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
          ENNReal.ofReal (Real.sqrt EJ) *
            (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal Cresp * weak := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let X := profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg) p r
  let tau := profilePrimalResponseDefect P hq g hg s t p r
  let EJ := ∫ a, responseJ (adaptedDomain hq t)
    ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P
  let row := profilePrimalHattedEarlierRow P (roundedGrid l m0) g s X.1 X.2
  let weak := profilePrimalWeakQuantity P m0 hq t
    (fun a ↦ a.subSkew g hg) p r
  let cut := adaptedPreYoungCutoff (roundedGrid l m0) hq t
  let expo := (3 : ℝ) ^ (-(H : ℝ))
  let scaleRoot : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt
    (profileSchurLoad
      (profileHattedBlock g (adaptedMean P (roundedGrid l m0) s)) X.1 X.2))
  let boundaryRow : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) *
    |vecDot X.2 (profilePrimalCutoffMean P hq t
        (fun a ↦ a.subSkew g hg) cut p r).1 +
      vecDot X.1 (profilePrimalCutoffMean P hq t
        (fun a ↦ a.subSkew g hg) cut p r).2|)
  apply compact_pre_young_of_finite_component_bounds hCpre
  · intro hweak
    have hdom := fun a : CoeffSpace d ↦
      cutoffWeightedTerminalEnergy_nonneg_le_two_responseJ
        hq t (a.subSkew g hg) p r
    have hdecomposition0 :=
      ofReal_abs_profilePrimalCenteredResponse_le_cutoff_decomposition_of_domination
        hq hm0 t hintt g hg p r hweak hdom
    have hdivCurl := ofReal_abs_integral_adaptedPreYoungCutoff_primal_le
      (t := t) hm0 hgrid P (fun a ↦ a.subSkew g hg) p r
    have hcutoffIntegrable :=
      integrable_cutoffWeightedTerminalEnergyDefect_subSkew
        hq t hintt g hg p r
    have hs := integrable_responseJ_subSkew_of_finiteAdaptedMean
      hq s hints g hg p r
    have htInt := integrable_responseJ_subSkew_of_finiteAdaptedMean
      hq t hintt g hg p r
    have hscale : t - (H : ℤ) = s := by omega
    have hH : (H : ℤ) = t - s := by omega
    have hcutoffEnergy0 :=
      ofReal_abs_integral_affineSubSkewCutoffEnergyDefect_le_component
        hstat hq hgrid hls H hscale hH g hg p r hs htInt hcutoffIntegrable
    have hrow := hrows hweak
    have hboundary0 :=
      abs_boundaryMean_le_of_four_mul_responseDefect hrow.1 hrow.2
    have hexpo : 0 ≤ expo := Real.rpow_nonneg (by norm_num) _
    have hcomponentNonneg : 0 ≤ preYoungComponentCoefficient d :=
      preYoungComponentCoefficient_nonneg d
    have hboundary : boundaryRow ≤
        ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (Real.sqrt tau) * scaleRoot +
          ENNReal.ofReal (preYoungComponentCoefficient d) *
            ENNReal.ofReal expo * ENNReal.ofReal (Real.sqrt EJ) *
              row ^ (1 / 2 : ℝ) := by
      calc
        boundaryRow ≤
            ENNReal.ofReal (Real.sqrt 2 * Real.sqrt tau *
                Real.sqrt (profileSchurLoad
                  (profileHattedBlock g
                    (adaptedMean P (roundedGrid l m0) s)) X.1 X.2)) +
              ENNReal.ofReal
                  (preYoungComponentCoefficient d * expo * Real.sqrt EJ) *
                row ^ (1 / 2 : ℝ) := by
          simpa only [boundaryRow, cut, X, tau, EJ, row, expo, hq] using hboundary0
        _ = _ := by
          rw [ENNReal.ofReal_mul
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
            ENNReal.ofReal_mul (Real.sqrt_nonneg _),
            ENNReal.ofReal_mul (mul_nonneg hcomponentNonneg hexpo),
            ENNReal.ofReal_mul hcomponentNonneg]
    have hscaleRoot : scaleRoot ≤ row ^ (1 / 2 : ℝ) :=
      sqrt_profileSchurLoad_le_profilePrimalHattedEarlierRow_rpow
        P hq g s X.1 X.2
    refine ⟨ENNReal.ofReal |∫ a, Book.Ch02.average (adaptedDomain hq t)
        (fun x ↦ cut x * ((1 / 2 : ℝ) * vecDot
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x - X.1)
          (matVecMul (((a.subSkew g hg).coeffOn
            (adaptedDomain hq t)).toCoeffField x)
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x) - X.2))) ∂P|,
      ENNReal.ofReal |∫ a, Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        cut x * ((1 / 2 : ℝ) * vecDot
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x)
          (matVecMul (((a.subSkew g hg).coeffOn
            (adaptedDomain hq t)).toCoeffField x)
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)))) -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P|,
      ?_, ?_, ?_, hboundary⟩
    · simpa only [hq, X, cut, boundaryRow] using! hdecomposition0
    · simpa only [hq, X] using hdivCurl
    · rw [rpow_neg_natCast_eq_zpow_neg H]
      simpa only [hq, tau, EJ, cut, expo] using hcutoffEnergy0
  · exact sqrt_profileSchurLoad_le_profilePrimalHattedEarlierRow_rpow
      P (Recurrence.posDef_of_isRoundedGrid hgrid) g s
        (profilePrimalCenter P (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (fun a ↦ a.subSkew g hg) p r).1
        (profilePrimalCenter P (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (fun a ↦ a.subSkew g hg) p r).2
  · exact hfour
  · exact hsqrtTwo
  · exact hcut
  · exact hcomponent
  · exact (preYoungDivCurlCoefficient_le_component d).trans hcomponent

end

end HCPolySupport.HighContrast.Response
