/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalFluxProjectionGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalFluxProjectionMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalProjectedRowBound

/-!
# High-contrast homogenization: Provider.Response.PreYoungPrimalFluxProjectedRowBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory _root_.Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-!
# Finite projected primal flux rows

The finite cube projections of the primal flux pairing are integrable, and
their annealed absolute values obey the all-earlier hatted-row estimate.
-/

/-- Finiteness of the primal weak quantity makes every absolute flux-slot
cell pairing integrable over the coefficient law. -/
theorem integrable_abs_primal_flux_cell_pairing_of_weak
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {k t : ℤ} (hkt : k ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    Integrable (fun a : CoeffSpace d ↦
      |vecDot Pcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).2|) P := by
  have hread :=
    (integrable_primal_adaptedFiveTermSplit_readouts
      hq hm0 hkt g hg p r hweak).1
  have hsum : Integrable (fun a : CoeffSpace d ↦
      ∑ i, Pcen i * (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).2 i) P :=
    integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i hi ↦ by
      simpa only [toFullBlockVec] using
        (hread w hw (Sum.inr i)).const_mul (Pcen i)
  simpa only [vecDot, Real.norm_eq_abs] using hsum.norm

/-- Every finite projected primal flux oscillation is almost-everywhere
strongly measurable under the coefficient law. -/
theorem aestrongly_measurable_primal_flux_projected_oscillation
    [NeZero d] {P : Measure (CoeffSpace d)}
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d) (N : ℕ) :
    AEStronglyMeasurable
      (primal_flux_projected_oscillation hq s t g hg p r Pcen N) P := by
  apply (aemeasurable_avsum (alignedIndex q s t) _ ?_).aestronglyMeasurable
  intro z hz
  exact (aestronglyMeasurable_cutoff_projected_primal_flux_pairing_subSkew
    hq hst hz g hg p r Pcen N).aemeasurable

end

end HCPolySupport.HighContrast.Response
