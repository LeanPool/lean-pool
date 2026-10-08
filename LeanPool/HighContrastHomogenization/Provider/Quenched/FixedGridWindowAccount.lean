/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowScale
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42CanonicalMetric
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Provider.Window.CellGeometry
public import LeanPool.HighContrastHomogenization.Provider.Entry.ScaleAccount
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterCellBounds
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellPositivity
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.MeanOrder
public import LeanPool.HighContrastHomogenization.Provider.ShortHop.PathStep
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds

/-!
# High-contrast homogenization: Provider.Quenched.FixedGridWindowAccount

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fixed-grid response-window account

The canonical metric and its base rounded grid are fixed once and for all.
For every sufficiently late terminal generation, a fresh source window begins
`H` generations earlier and encloses every cell read by the response estimate.
The first admissible terminal generation has a polynomial triadic bound in the
reference aspect ratio and the source growth witness.

The lag `H ≥ 4` is a parameter: the compact pre-Young absorption requires
`(3/2)·Cpre·3^{-H} ≤ 1/4` for the dimension-dependent response constant
`Cpre`, so the printed lag four is admissible only after enlarging `H` to a
dimension-dependent value, all before the law.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Coarse ellipticity makes every adapted mean on a positive grid finite and
positive definite, independently of the source-window cutoff. -/
theorem finite_adaptedMean_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    {q : Mat d} (hq : q.PosDef) (k : ℤ) :
    HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k) := by
  have hmeas : HasMeasurableCoarseBlock P
      (adaptedCellTranslate q k 0) :=
    Transport.hasMeasurableCoarseBlock_adaptedCellTranslate P hq k 0
  have hint0 := Entry.hasIntegrableCoarseBlock_adaptedCellTranslate_of_dagger
    hdag hq hmeas
  have hzero : adaptedCellTranslate q k 0 = adaptedCell q k := by
    simp [adaptedCellTranslate]
  have hint : HasFiniteAdaptedMean P q k := by
    rwa [hzero] at hint0
  exact ⟨hint, Recurrence.blockPosDef_adaptedMean hq k hint⟩

end

end HCPolySupport.HighContrast.Quenched
