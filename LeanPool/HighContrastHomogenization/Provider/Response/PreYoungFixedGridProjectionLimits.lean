/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAdjointFluxPhysicalProjectionLimit
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAdjointGradientPhysicalProjectionLimit
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalFluxPhysicalProjectionLimit
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridPrimalProjectedRows
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridAdjointProjectedRows

/-!
# High-contrast homogenization: Provider.Response.PreYoungFixedGridProjectionLimits

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical projection limits, fixed grid

Fixed-rounded-grid sibling of `HCPoly.Provider.Response.PreYoungPrimalPhysicalProjectionLimit`,
`HCPoly.Provider.Response.PreYoungPrimalFluxPhysicalProjectionLimit`,
`HCPoly.Provider.Response.PreYoungAdjointGradientPhysicalProjectionLimit`,
`HCPoly.Provider.Response.PreYoungAdjointFluxPhysicalProjectionLimit`: the grid stays rounded at
the fixed
alignment `l` while the generation window `{s, t}` moves, the aligned-cell
integrability coming from the `AlignedCellsIntegrable` carrier instead of the
window multiplier's carrier equality.  The proof is unchanged apart from the
window bundle replaced by the carrier.
-/

namespace HCPolySupport.HighContrast.Response.FixedGrid

open Book.Ch02 MeasureTheory Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The physical primal cutoff oscillation is controlled by the earlier profile row. -/
theorem of_real_abs_integral_primal_physical_oscillation_le_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    ENNReal.ofReal |∫ a, primalPhysicalOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Qcen a ∂P| ≤
      ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
              Real.sqrt (∫ a, responseJ
                (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                ((a.subSkew g hg).coeffOn
                  (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t))
                p r ∂P)) *
        profilePrimalHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  apply ofReal_abs_integral_le_of_tendsto_of_uniform_bound
    (F := fun n ↦ primalProjectedOscillation
      hq s t g hg p r Qcen (n + 1))
    (f := primalPhysicalOscillation hq s t g hg p r Qcen)
  · intro n
    exact (aestrongly_measurable_primal_projected_oscillation
      (P := P) hq hst g hg p r Qcen (n + 1)).aemeasurable
  · exact integrable_primal_physical_oscillation_of_weak
      hq hm0 hst g hg p r Qcen hweak
  · exact Filter.Eventually.of_forall fun a ↦
      tendsto_primal_projected_oscillation
        hq hst g hg a p r Qcen
  · intro n
    simpa only [hq] using
      lintegral_primal_projected_oscillation_le_row
        hstat hm0 hgrid hls hst hcells hblocks
          g hg p r Pcen Qcen hweak (n + 1)

/-- The physical primal flux cutoff oscillation is controlled by the earlier
profile row. -/
theorem of_real_abs_integral_primal_flux_physical_oscillation_le_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    ENNReal.ofReal |∫ a, primalFluxPhysicalOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Pcen a ∂P| ≤
      ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
              Real.sqrt (∫ a, responseJ
                (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                ((a.subSkew g hg).coeffOn
                  (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t))
                p r ∂P)) *
        profilePrimalHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  apply ofReal_abs_integral_le_of_tendsto_of_uniform_bound
    (F := fun n ↦ primalFluxProjectedOscillation
      hq s t g hg p r Pcen (n + 1))
    (f := primalFluxPhysicalOscillation hq s t g hg p r Pcen)
  · intro n
    exact (aestrongly_measurable_primal_flux_projected_oscillation
      (P := P) hq hst g hg p r Pcen (n + 1)).aemeasurable
  · exact integrable_primal_flux_physical_oscillation_of_weak
      hq hm0 hst g hg p r Pcen hweak
  · exact Filter.Eventually.of_forall fun a ↦
      tendsto_primal_flux_projected_oscillation
        hq hst g hg a p r Pcen
  · intro n
    simpa only [hq] using
      lintegral_primal_flux_projected_oscillation_le_row
        hstat hm0 hgrid hls hst hcells hblocks
          g hg p r Pcen Qcen hweak (n + 1)

/-- The physical adjoint gradient cutoff oscillation is controlled by the
earlier transposed profile row. -/
theorem of_real_abs_integral_adjoint_gradient_physical_oscillation_le_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profileAdjointWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    ENNReal.ofReal |∫ a, adjointGradientPhysicalOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Qcen a ∂P| ≤
      ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
              Real.sqrt (∫ a, responseJ
                (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                ((a.subSkew g hg).transpose.coeffOn
                  (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t))
                p r ∂P)) *
        profileAdjointHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  apply ofReal_abs_integral_le_of_tendsto_of_uniform_bound
    (F := fun n ↦ adjointGradientProjectedOscillation
      hq s t g hg p r Qcen (n + 1))
    (f := adjointGradientPhysicalOscillation hq s t g hg p r Qcen)
  · intro n
    exact (aestrongly_measurable_adjoint_gradient_projected_oscillation
      (P := P) hq hst g hg p r Qcen (n + 1)).aemeasurable
  · exact integrable_adjoint_gradient_physical_oscillation_of_weak
      hq hm0 hst g hg p r Qcen hweak
  · exact Filter.Eventually.of_forall fun a ↦
      tendsto_adjoint_gradient_projected_oscillation
        hq hst g hg a p r Qcen
  · intro n
    simpa only [hq] using
      lintegral_adjoint_gradient_projected_oscillation_le_row
        hstat hm0 hgrid hls hst hcells hblocks
          g hg p r Pcen Qcen hweak (n + 1)

/-- The physical adjoint flux cutoff oscillation is controlled by the earlier
transposed profile row. -/
theorem of_real_abs_integral_adjoint_flux_physical_oscillation_le_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profileAdjointWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    ENNReal.ofReal |∫ a, adjointFluxPhysicalOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Pcen a ∂P| ≤
      ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
              Real.sqrt (∫ a, responseJ
                (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                ((a.subSkew g hg).transpose.coeffOn
                  (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t))
                p r ∂P)) *
        profileAdjointHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  apply ofReal_abs_integral_le_of_tendsto_of_uniform_bound
    (F := fun n ↦ adjointFluxProjectedOscillation
      hq s t g hg p r Pcen (n + 1))
    (f := adjointFluxPhysicalOscillation hq s t g hg p r Pcen)
  · intro n
    exact (aestrongly_measurable_adjoint_flux_projected_oscillation
      (P := P) hq hst g hg p r Pcen (n + 1)).aemeasurable
  · exact integrable_adjoint_flux_physical_oscillation_of_weak
      hq hm0 hst g hg p r Pcen hweak
  · exact Filter.Eventually.of_forall fun a ↦
      tendsto_adjoint_flux_projected_oscillation
        hq hst g hg a p r Pcen
  · intro n
    simpa only [hq] using
      lintegral_adjoint_flux_projected_oscillation_le_row
        hstat hm0 hgrid hls hst hcells hblocks
          g hg p r Pcen Qcen hweak (n + 1)

end

end HCPolySupport.HighContrast.Response.FixedGrid
