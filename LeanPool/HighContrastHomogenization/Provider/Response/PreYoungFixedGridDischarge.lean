/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridRows

/-!
# High-contrast homogenization: Provider.Response.PreYoungFixedGridDischarge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Unconditional pre-Young response families on a fixed rounded grid

The unconditional pre-Young response families on a fixed rounded grid: the grid is
rounded once at the fixed alignment `l` while the generation window `{s, t}`
moves, and the aligned-cell integrability is drawn from the coarse ellipticity
`e.coarse.ellipticity` instead of the window multiplier, whose coupled
window cannot reach an arbitrary terminal generation from a fixed alignment.
No window, profile, or history premise enters: beyond the grid and window
geometry the hypotheses are stationarity, Dagger, and the finite adapted
means with their block positivity on the window.
-/

namespace HCPolySupport.HighContrast.Response.FixedGrid

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

/-- There is a common dimension-dependent constant for the primal and adjoint
compact pre-Young response families on a fixed rounded grid, with the
aligned-cell integrability supplied by `e.coarse.ellipticity`. -/
theorem exists_pre_young_response_families_of_dagger_fixed_grid
    (d : ℕ) [NeZero d] :
    ∃ Cpre : ℝ, 1 ≤ Cpre ∧
      ∀ {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P],
      ∀ (_hstat : HCPoly.Frozen.IsStationaryLaw P),
      ∀ {gdag : ℝ} {Edag : BlockMat d} {Psidag : ℝ → ℝ} {Kdag : ℝ}
        {Sdag : CoeffSpace d → ℝ},
      ∀ (_hdag : HCPoly.Frozen.CoarseEllipticityDagger
          P gdag Edag Psidag Kdag Sdag),
      ∀ {l : ℤ} {m0 q : Mat d},
      ∀ (_hm0 : m0.PosDef) (_hqeq : q = roundedGrid l m0)
        (hgrid : IsRoundedGrid l q),
      ∀ {s t : ℤ},
      ∀ (_hls : l ≤ s) (H : ℕ) (_ht : t = s + (H : ℤ)),
      ∀ (_hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
        HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k)),
      ((∀ Cresp, Cpre ≤ Cresp →
        ∀ (h0 : {h : Mat d // IsSkewMat h}) (p r : Vec d),
          let hq := Recurrence.posDef_of_isRoundedGrid hgrid
          let X := profilePrimalCenter P hq t
            (fun a ↦ a.subSkew h0 h0.property) p r
          let tau := profilePrimalResponseDefect P hq h0
            h0.property s t p r
          let EJ := ∫ a, responseJ (adaptedDomain hq t)
            ((a.subSkew h0 h0.property).coeffOn
              (adaptedDomain hq t)) p r ∂P
          let row := profilePrimalHattedEarlierRow P q h0 s X.1 X.2
          let weak := profilePrimalWeakQuantity P m0 hq t
            (fun a ↦ a.subSkew h0 h0.property) p r
          let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
            (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
              ((a.subSkew h0 h0.property).coeffOn (adaptedDomain hq t))
              (centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew h0 h0.property) p r) i ∂P)
            (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
              ((a.subSkew h0 h0.property).coeffOn (adaptedDomain hq t))
              (centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew h0 h0.property) p r) i ∂P)
          ENNReal.ofReal |Jtilde| ≤
            ENNReal.ofReal Cresp * ENNReal.ofReal (Real.sqrt tau) *
              (ENNReal.ofReal (Real.sqrt tau) +
                ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal Cresp *
              ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
              ENNReal.ofReal (Real.sqrt EJ) *
                (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal Cresp * weak) ∧
      (∀ Cresp, Cpre ≤ Cresp →
        ∀ (h0 : {h : Mat d // IsSkewMat h}) (p r : Vec d),
          let hq := Recurrence.posDef_of_isRoundedGrid hgrid
          let X := profileAdjointCenter P hq t
            (fun a ↦ a.subSkew h0 h0.property) p r
          let tau := profileAdjointResponseDefect P hq h0
            h0.property s t p r
          let EJ := ∫ a, responseJ (adaptedDomain hq t)
            ((a.subSkew h0 h0.property).transpose.coeffOn
              (adaptedDomain hq t)) p r ∂P
          let row := profileAdjointHattedEarlierRow P q h0 s X.1 X.2
          let weak := profileAdjointWeakQuantity P m0 hq t
            (fun a ↦ a.subSkew h0 h0.property) p r
          let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
            (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
              ((a.subSkew h0 h0.property).transpose.coeffOn
                (adaptedDomain hq t))
              (centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew h0 h0.property) p r) i ∂P)
            (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
              ((a.subSkew h0 h0.property).transpose.coeffOn
                (adaptedDomain hq t))
              (centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew h0 h0.property) p r) i ∂P)
          ENNReal.ofReal |Jtilde| ≤
            ENNReal.ofReal Cresp * ENNReal.ofReal (Real.sqrt tau) *
              (ENNReal.ofReal (Real.sqrt tau) +
                ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal Cresp *
              ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
              ENNReal.ofReal (Real.sqrt EJ) *
                (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal Cresp * weak)) := by
  obtain ⟨Cpre, hCpre, hcut, hcomponent, hfour, hsqrtTwo⟩ :=
    exists_one_le_pre_young_constant d (preYoungComponentCoefficient d)
  refine ⟨Cpre, hCpre, ?_⟩
  intro P _ hstat gdag Edag Psidag Kdag Sdag hdag l m0 q hm0 hqeq hgrid
    s t hls H ht hblocks
  subst q
  have hcells : AlignedCellsIntegrable P (roundedGrid l m0) s t :=
    alignedCellsIntegrable_of_dagger hdag
      (Recurrence.posDef_of_isRoundedGrid hgrid) s t
  have hst : s ≤ t := by omega
  have hints := (hblocks s hls hst).1
  have hlt : l ≤ t := hls.trans hst
  have hintt := (hblocks t hlt le_rfl).1
  constructor
  · intro Cresp hCresp h0 p r
    have hcompact := compact_pre_young_primal_of_row_estimates
      hm0 hgrid hstat hls H ht hints hintt h0 h0.property p r
      hCpre hcut hcomponent hfour hsqrtTwo
      (fun hweak ↦ profile_primal_cutoff_mean_rows_le
        hstat hm0 hgrid hls H ht hcells hblocks
          h0 h0.property p r hweak)
    exact hcompact Cresp hCresp
  · intro Cresp hCresp h0 p r
    have hcompact := compact_pre_young_adjoint_of_row_estimates
      hm0 hgrid hstat hls H ht hints hintt h0 h0.property p r
      hCpre hcut hcomponent hfour hsqrtTwo
      (fun hweak ↦ profile_adjoint_cutoff_mean_rows_le
        hstat hm0 hgrid hls H ht hcells hblocks
          h0 h0.property p r hweak)
    exact hcompact Cresp hCresp

end

end HCPolySupport.HighContrast.Response.FixedGrid
