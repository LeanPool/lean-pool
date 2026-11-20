/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusChartL2Operators

/-!
# The canonical half-open fundamental square of the transverse torus

The paper works on the flat unit torus `𝕋³ = ℝ³/ℤ³` with
`y = (x₁, x₂) ∈ 𝕋²` (§1.1), and every
Euclidean statement about the cell placement is read in the fixed coordinate
square `(-1/4, 1/4) × (1/4, 3/4) ⊂ 𝕋²` introduced right after `eq:chart-packing`
(§3.3).  Transporting a Euclidean area to the torus therefore needs
one measure-preserving representative of `𝕋²` in pair coordinates.

This module holds exactly that: the half-open square `(0,1] × (0,1]` and the
statement that `transverseIocRepresentative` is measure preserving from
`transverseMeasure` onto Lebesgue measure restricted to it.  Nothing here
mentions a cell or a scale family.  The declarations live in the namespace
`TorusIocFundamentalBox` and are used by the qualitative velocity file
`Global/TorusGlobalVelocityQualitative.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TorusIocFundamentalBox

/-- The canonical half-open fundamental square in pair coordinates. -/
def pairIocFundamentalBox : Set (ℝ × ℝ) :=
  Set.Ioc (0 : ℝ) (0 + 1) ×ˢ Set.Ioc (0 : ℝ) (0 + 1)

/-- The canonical half-open fundamental square in pair coordinates is measurable, being a product of
two half-open intervals.
-/
theorem measurableSet_pairIocFundamentalBox :
    MeasurableSet pairIocFundamentalBox :=
  measurableSet_Ioc.prod measurableSet_Ioc

/-- Pairing the two raw coordinates transports restricted Lebesgue measure
on the raw fundamental rectangle to restricted product Lebesgue measure on
the pair-coordinate fundamental square. -/
theorem measurePreserving_finTwoArrow_restrict :
    MeasurePreserving (MeasurableEquiv.finTwoArrow :
        (Fin 2 → ℝ) → (ℝ × ℝ))
      (volume.restrict TorusChartL2.rawFundamentalBox)
      (volume.restrict pairIocFundamentalBox) := by
  have h := (volume_preserving_finTwoArrow ℝ).restrict_preimage
    measurableSet_pairIocFundamentalBox
  have hpre :
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → (ℝ × ℝ)) ⁻¹'
          pairIocFundamentalBox = TorusChartL2.rawFundamentalBox := by
    ext x
    simp only [pairIocFundamentalBox, Set.mem_preimage, Set.mem_prod,
      MeasurableEquiv.finTwoArrow_apply,
      TorusChartL2.rawFundamentalBox,
      ScaleFamily.TorusCellPlacement.EuclideanCellSourceCertificate.iocFundamentalBox,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzero, hone⟩ k
      fin_cases k <;> assumption
    · intro h
      exact ⟨h 0, h 1⟩
  rw [hpre] at h
  exact h

/-- The pair-valued canonical torus representative is measure preserving
onto the restricted half-open fundamental square. -/
theorem measurePreserving_transverseIocRepresentative :
    MeasurePreserving transverseIocRepresentative transverseMeasure
      (volume.restrict pairIocFundamentalBox) := by
  have hcomp := measurePreserving_finTwoArrow_restrict.comp
    TorusChartL2.measurePreserving_rawFundamentalRepresentativeVal
  have hfun :
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → (ℝ × ℝ)) ∘
          (fun q : TransverseTorus ↦
            (TorusChartL2.rawFundamentalRepresentative q).1) =
        transverseIocRepresentative := by
    funext q
    ext <;> rfl
  rw [hfun] at hcomp
  exact hcomp

end TorusIocFundamentalBox

end

end FastDynamo
