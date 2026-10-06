/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CellFamilyAndFluxRow

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.RowSupply.DatumRowAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Datum-row aggregation over the enlarged-margin ruled carrier

The per-cell mismatch between the `L²` price and the fractional-energy weights
is bounded because `ruledCellScale_lt_two_mul_Rad` bounds every selected
Whitney scale by the sandwich radius.

## Route

1. **scale bound** — `physicalFullDualL2Constant d (whitneyCellCube system i) s
   = fullDualL2AmplitudeV2 d s * cubeScaleFactor (whitneyCellCube system i) ^ s`,
   and `cubeScaleFactor (whitneyCellCube system i) = 3 ^ system.scale i < 2 Rad`,
   so every cell constant is under the *uniform* `fullDualL2AmplitudeV2 d s *
   (2 Rad) ^ s`;
2. **disjoint-cell summation** — the selected cells are pairwise disjoint,
   measurable, and exhaust `U` up to a null set, so
   `∑ᵢ ∫⁻_{cellᵢ} |∇h|² = ∫⁻_U |∇h|²`;
3. **volume-weight absorption** — `hsNormSq U s h.grad` carries
   `volume U ^ (-(2s)/d) · eVolumeAverage U |∇h|²`, so the average is recovered
   at the cost of `volume U ^ ((2s)/d)`, a `Rad`-bounded factor that
   `C₀ s rho Rad` absorbs.

None of the three is an oscillation estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem continuous_vecNormSq :
    Continuous (vecNormSq : Vec d → ℝ) := by
  have hrw : (vecNormSq : Vec d → ℝ) = fun x => ∑ i, x i * x i := by
    funext x
    simp [vecNormSq, vecDot]
  rw [hrw]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul (continuous_apply i)

/-- Every selected enlarged-margin Whitney cell has scale bounded by twice
the outer sandwich radius. -/
theorem ruledCellScale_lt_two_mul_Rad [NeZero d]
    {U : Set (Vec d)} {rho Rad : ℝ} (hRad : 0 ≤ Rad)
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpen U) (i : system.CellIndex) :
    (3 : ℝ) ^ system.scale i < 2 * Rad := by
  obtain ⟨z, _hzBuf, hzFrontier⟩ := system.boundaryBuffer_meets_frontier i
  let x : Vec d := standardCellCenter (system.scale i) (system.index i)
  have hxCell : x ∈ system.cell i :=
    Recurrence.standardCellCenter_mem_standardCell _ _
  have hgap := (system.boundaryDistance_compare hU i hxCell).1 z hzFrontier
  have hxU : x ∈ U := system.cell_subset i hxCell
  have hxball : vecNormSq (x - system.center) < Rad ^ 2 :=
    system.outer_ball hxU
  have hclosed : IsClosed
      {y : Vec d | vecNormSq (y - system.center) ≤ Rad ^ 2} :=
    isClosed_le (continuous_vecNormSq.comp
      (continuous_id.sub continuous_const)) continuous_const
  have hUsub : U ⊆ {y : Vec d | vecNormSq (y - system.center) ≤ Rad ^ 2} := by
    intro y hy
    show vecNormSq (y - system.center) ≤ Rad ^ 2
    exact le_of_lt (system.outer_ball hy)
  have hzball : vecNormSq (z - system.center) ≤ Rad ^ 2 :=
    closure_minimal hUsub hclosed (frontier_subset_closure hzFrontier)
  have hsplit : x - z = (x - system.center) - (z - system.center) :=
    (sub_sub_sub_cancel_right x z system.center).symm
  have hsq : vecNormSq (x - z) < (2 * Rad) ^ 2 := by
    rw [hsplit]
    calc
      vecNormSq ((x - system.center) - (z - system.center)) ≤
          2 * (vecNormSq (x - system.center) +
            vecNormSq (z - system.center)) :=
        vecNormSq_sub_le _ _
      _ < 2 * (Rad ^ 2 + Rad ^ 2) := by
        linarith only [hxball, hzball]
      _ = (2 * Rad) ^ 2 := by ring
  have hdist : euclideanDist x z < 2 * Rad := by
    have hnn : 0 ≤ 2 * Rad := by linarith only [hRad]
    have hpow : euclideanDist x z ^ 2 < (2 * Rad) ^ 2 := by
      rw [euclideanDist_sq]
      exact hsq
    exact lt_of_pow_lt_pow_left₀ 2 hnn hpow
  have hscale : (3 : ℝ) ^ system.scale i <
      4 * (3 : ℝ) ^ system.scale i := by
    have hpos : (0 : ℝ) < (3 : ℝ) ^ system.scale i := by positivity
    linarith only [hpos]
  exact hscale.trans (hgap.trans hdist)

/-! ## The uniform cell constant -/

/-! ## The cube-average to lintegral bridge -/

/-! ## The aggregation -/

end

end RowSupply
end HighContrast
end HCPolySupport
