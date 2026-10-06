/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.TriadicDilationResponse
public import LeanPool.HighContrastHomogenization.Provider.Quenched.TriadicRebasedSource

/-!
# High-contrast homogenization: Provider.Quenched.TriadicRebasedDagger

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coarse ellipticity under triadic rebasing

The coarse ellipticity carrier is transported directly through the measurable
coefficient-space dilation.  Both spatial generations shift by the same
integer, so the discount exponent is unchanged.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Dilating both generations preserves membership of a standard-cell center
in the corresponding centered cube. -/
theorem standardCellCenter_add_mem_centeredCube_add (n : ℕ) {m k : ℤ}
    {w : Fin d → ℤ}
    (hcenter : standardCellCenter k w ∈ centeredCube d m) :
    standardCellCenter ((n : ℤ) + k) w ∈ centeredCube d ((n : ℤ) + m) := by
  have hdilated :=
    Book.Ch02.dilateVec_mem_openCubeSet_dilateCube (n : ℤ) hcenter
  have hpoint :
      Book.Ch02.dilateVec (n : ℤ) (standardCellCenter k w) =
        standardCellCenter ((n : ℤ) + k) w := by
    funext i
    simp only [Book.Ch02.dilateVec, Book.Ch02.triadicDilationFactor,
      standardCellCenter, Pi.smul_apply, smul_eq_mul]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hcube :
      Book.Ch02.dilateCube (n : ℤ) (originCube d m) =
        originCube d ((n : ℤ) + m) := by
    simp [Book.Ch02.dilateCube, originCube, add_comm]
  change Book.Ch02.dilateVec (n : ℤ) (standardCellCenter k w) ∈
    openCubeSet (Book.Ch02.dilateCube (n : ℤ) (originCube d m)) at hdilated
  rw [hpoint, hcube] at hdilated
  exact hdilated

private theorem source_le_zpow_add_of_rebased_le (n : ℕ)
    {S : CoeffSpace d → ℝ} {a : CoeffSpace d} {m : ℤ}
    (hsource :
      triadicRebasedSource n S (CoeffSpace.triadicDilation n a) ≤
        (3 : ℝ) ^ m) :
    S a ≤ (3 : ℝ) ^ ((n : ℤ) + m) := by
  let r : ℝ := (3 : ℝ) ^ n
  have hr : 0 < r := by positivity
  calc
    S a = r * (S a / r) := by field_simp
    _ ≤ r * (3 : ℝ) ^ m := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [triadicRebasedSource_triadicDilation, r] using hsource
      · exact hr.le
    _ = (3 : ℝ) ^ ((n : ℤ) + m) := by
      simp only [r, ← zpow_natCast]
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]

end

end HighContrast
end HCPolySupport

namespace HCPoly.Frozen.CoarseEllipticityDagger

open MeasureTheory
open HCPolySupport
open HCPolySupport.IndependentSums
open HCPolySupport.HighContrast

noncomputable section

variable {d : ℕ}

/-- Coarse ellipticity on the frozen coefficient-law carrier is preserved by
triadic rebasing, with the source and gauge expressed in the rebased units. -/
theorem triadicRebased {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdagger : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (n : ℕ) :
    HCPoly.Frozen.CoarseEllipticityDagger
      (triadicRebasedLaw n P) g E (triadicRebasedGauge n Ψ) K
        (triadicRebasedSource n S) := by
  refine
    { g_mem := hdagger.g_mem
      refBlock_isSymm := hdagger.refBlock_isSymm
      refBlock_posDef := hdagger.refBlock_posDef
      gauge_admissible :=
        admissiblePsi_triadicRebasedGauge n hdagger.gauge_admissible
      one_lt_growthWitness := hdagger.one_lt_growthWitness
      gauge_growth := hasPsiGrowth_triadicRebasedGauge n
        hdagger.gauge_admissible hdagger.gauge_growth
      source_measurable :=
        measurable_triadicRebasedSource n hdagger.source_measurable
      source_nonneg := triadicRebasedSource_nonneg n hdagger.source_nonneg
      source_tail := sourceTail_triadicRebasedLaw n
        hdagger.source_measurable hdagger.source_tail
      coarse_bound := ?_ }
  rw [triadicRebasedLaw]
  exact
    ((CoeffSpace.triadicDilationMeasurableEquiv n).measurableEmbedding.ae_map_iff).2 <| by
      filter_upwards [hdagger.coarse_bound] with a ha
      intro m hsource k hk w hcenter
      have hsource' : S a ≤ (3 : ℝ) ^ ((n : ℤ) + m) :=
        source_le_zpow_add_of_rebased_le n hsource
      have hk' : (n : ℤ) + k ≤ (n : ℤ) + m :=
        by simpa only [add_comm] using add_le_add_left hk (n : ℤ)
      have hcenter' :
          standardCellCenter ((n : ℤ) + k) w ∈
            centeredCube d ((n : ℤ) + m) :=
        standardCellCenter_add_mem_centeredCube_add n hcenter
      have hbound := ha ((n : ℤ) + m) hsource'
        ((n : ℤ) + k) hk' w hcenter'
      have hexponent :
          g * ((((n : ℤ) + m : ℤ) : ℝ) -
            (((n : ℤ) + k : ℤ) : ℝ)) =
            g * ((m : ℝ) - (k : ℝ)) := by
        push_cast
        ring
      rw [hexponent] at hbound
      change BlockMatLoewnerLE
        (coarseBlock (standardCell d k w) (CoeffSpace.triadicDilation n a))
        (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E)
      rw [coarseBlock_standardCell_triadicDilation]
      exact hbound

end

end HCPoly.Frozen.CoarseEllipticityDagger
