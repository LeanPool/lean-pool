/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAdjointProjectionMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalProjectedRowBound
public import LeanPool.HighContrastHomogenization.Provider.Response.SplitReadoutAdjointIntegrability

/-!
# High-contrast homogenization: Provider.Response.PreYoungAdjointGradientProjectedRowBound

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
# Finite projected adjoint gradient rows

The finite cube projections of the adjoint gradient pairing are integrable,
and their annealed absolute values obey the transposed all-earlier row bound.
-/

/-- Finiteness of the adjoint weak quantity makes every absolute gradient-slot
cell pairing integrable over the coefficient law. -/
theorem integrable_abs_adjoint_gradient_cell_pairing_of_weak
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {k t : ℤ} (hkt : k ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (hweak : profileAdjointWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    Integrable (fun a : CoeffSpace d ↦
      |vecDot Qcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).1|) P := by
  have hread :=
    (integrable_adjoint_adaptedFiveTermSplit_readouts
      hq hm0 hkt g hg p r hweak).1
  have hsum : Integrable (fun a : CoeffSpace d ↦
      ∑ i, Qcen i * (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).1 i) P :=
    integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i hi ↦ by
      simpa only [toFullBlockVec] using
        (hread w hw (Sum.inl i)).const_mul (Qcen i)
  simpa only [vecDot, Real.norm_eq_abs] using hsum.norm

/-- Every finite projected adjoint gradient oscillation is almost-everywhere
strongly measurable under the coefficient law. -/
theorem aestrongly_measurable_adjoint_gradient_projected_oscillation
    [NeZero d] {P : Measure (CoeffSpace d)}
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d) (N : ℕ) :
    AEStronglyMeasurable
      (adjoint_gradient_projected_oscillation hq s t g hg p r Qcen N) P := by
  apply (aemeasurable_avsum (alignedIndex q s t) _ ?_).aestronglyMeasurable
  intro z hz
  exact
    (aestronglyMeasurable_cutoff_projected_adjoint_gradient_pairing_subSkew
      hq hst hz g hg p r Qcen N).aemeasurable

end

end HCPolySupport.HighContrast.Response
