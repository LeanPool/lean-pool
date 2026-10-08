/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalPhysicalRow
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungRemainingPhysicalRows
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridProjectionLimits

/-!
# High-contrast homogenization: Provider.Response.PreYoungFixedGridPhysicalRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical cutoff-oscillation rows, fixed grid

Fixed-rounded-grid sibling of `HCPoly.Provider.Response.PreYoungPrimalPhysicalRow`,
`HCPoly.Provider.Response.PreYoungRemainingPhysicalRows`: the grid stays rounded at the fixed
alignment `l` while the generation window `{s, t}` moves, the aligned-cell
integrability coming from the `AlignedCellsIntegrable` carrier instead of the
window multiplier's carrier equality.  The proof is unchanged apart from the
window bundle replaced by the carrier.
-/

namespace HCPolySupport.HighContrast.Response.FixedGrid

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The literal primal gradient-slot cutoff oscillation is controlled by the
all-earlier hatted row. -/
theorem of_real_abs_primal_cutoff_oscillation_row_le
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
    ENNReal.ofReal
        |avsum (alignedIndex q s t) (fun z ↦
          ∑ i, Qcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
            (adaptedPreYoungCutoff q (Recurrence.posDef_of_isRoundedGrid hgrid) t x -
              volumeAverage (adaptedCellAt q s z)
                (adaptedPreYoungCutoff q
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t)) *
              toFullBlockVec
                (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew g hg) p r x)
                (Sum.inl i)) ∂P)| ≤
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
  have hphysical := of_real_abs_integral_primal_physical_oscillation_le_row
    hstat hm0 hgrid hls hst hcells hblocks
      g hg p r Pcen Qcen hweak
  have heq := integral_primal_physical_oscillation_eq_cutoff_row
    (P := P) hq hm0 hst g hg p r Qcen hweak
  rw [heq] at hphysical
  simpa only [hq] using hphysical

/-- The literal primal flux cutoff oscillation is controlled by the
all-earlier primal row. -/
theorem of_real_abs_primal_flux_cutoff_oscillation_row_le
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
    ENNReal.ofReal
        |avsum (alignedIndex q s t) (fun z ↦
          ∑ i, Pcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
            (adaptedPreYoungCutoff q (Recurrence.posDef_of_isRoundedGrid hgrid) t x -
              volumeAverage (adaptedCellAt q s z)
                (adaptedPreYoungCutoff q
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t)) *
              toFullBlockVec
                (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew g hg) p r x)
                (Sum.inr i)) ∂P)| ≤
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
  have hphysical := of_real_abs_integral_primal_flux_physical_oscillation_le_row
    hstat hm0 hgrid hls hst hcells hblocks
      g hg p r Pcen Qcen hweak
  have heq := integral_primal_flux_physical_oscillation_eq_cutoff_row
    (P := P) hq hm0 hst g hg p r Pcen hweak
  rw [heq] at hphysical
  simpa only [hq] using hphysical

/-- The literal adjoint gradient cutoff oscillation is controlled by the
all-earlier adjoint row. -/
theorem of_real_abs_adjoint_gradient_cutoff_oscillation_row_le
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
    ENNReal.ofReal
        |avsum (alignedIndex q s t) (fun z ↦
          ∑ i, Qcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
            (adaptedPreYoungCutoff q (Recurrence.posDef_of_isRoundedGrid hgrid) t x -
              volumeAverage (adaptedCellAt q s z)
                (adaptedPreYoungCutoff q
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t)) *
              toFullBlockVec
                (diagonalWeakAdjointState
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew g hg) p r x)
                (Sum.inl i)) ∂P)| ≤
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
  have hphysical :=
    of_real_abs_integral_adjoint_gradient_physical_oscillation_le_row
      hstat hm0 hgrid hls hst hcells hblocks
        g hg p r Pcen Qcen hweak
  have heq := integral_adjoint_gradient_physical_oscillation_eq_cutoff_row
    (P := P) hq hm0 hst g hg p r Qcen hweak
  rw [heq] at hphysical
  simpa only [hq] using hphysical

/-- The literal adjoint flux cutoff oscillation is controlled by the
all-earlier adjoint row. -/
theorem of_real_abs_adjoint_flux_cutoff_oscillation_row_le
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
    ENNReal.ofReal
        |avsum (alignedIndex q s t) (fun z ↦
          ∑ i, Pcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
            (adaptedPreYoungCutoff q (Recurrence.posDef_of_isRoundedGrid hgrid) t x -
              volumeAverage (adaptedCellAt q s z)
                (adaptedPreYoungCutoff q
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t)) *
              toFullBlockVec
                (diagonalWeakAdjointState
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew g hg) p r x)
                (Sum.inr i)) ∂P)| ≤
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
  have hphysical := of_real_abs_integral_adjoint_flux_physical_oscillation_le_row
    hstat hm0 hgrid hls hst hcells hblocks
      g hg p r Pcen Qcen hweak
  have heq := integral_adjoint_flux_physical_oscillation_eq_cutoff_row
    (P := P) hq hm0 hst g hg p r Pcen hweak
  rw [heq] at hphysical
  simpa only [hq] using hphysical

end

end HCPolySupport.HighContrast.Response.FixedGrid
