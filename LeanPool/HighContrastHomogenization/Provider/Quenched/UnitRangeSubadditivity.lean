/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeMeanBlock
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Entry.IdentityCells
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexWhitneyGeometry

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeSubadditivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Subadditivity over the standard aligned cubes

The renormalization argument compares the coarse block of a cell with the
average of the coarse blocks of the cells of an inner generation that subdivide
it.  The prior subadditivity theorem is stated at the cell centred at the origin and in
the adapted dialect; this file reads it in the standard dialect, at the identity
grid, and translates it to an arbitrary aligned parent.

The translation is the sample-level covariance of the coarse block: a translated
cell reads the translated sample.  The inner cells of the translated parent are
the inner cells of the origin parent with their indices shifted by the parent's
index, scaled by the ratio of the two generations, so the index set of the
average is the one already counted by `card_centredIndexFinset`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The origin parent, in the standard dialect -/

/-- **Subadditivity at the centred parent.**  The coarse block of `□_k` is below
the average of the coarse blocks of the scale-`l` standard cubes centred in it. -/
theorem toFullBlockMat_coarseBlock_centeredCube_le_average [NeZero d] {l k : ℤ}
    (hlk : l ≤ k) (a : CoeffSpace d) :
    toFullBlockMat (coarseBlock (centeredCube d k) a) ≤
      ((centredIndexFinset d l k).card : ℝ)⁻¹ •
        ∑ t ∈ centredIndexFinset d l k,
          toFullBlockMat (coarseBlock (standardCell d l t) a) := by
  have hZ : (↑(centredIndexFinset d l k) : Set (Fin d → ℤ))
      = {t : Fin d → ℤ | adaptedCellCenter (1 : Mat d) l t ∈ adaptedCell (1 : Mat d) k} := by
    ext t
    simp only [Finset.mem_coe, Set.mem_ofPred_eq, Entry.adaptedCellCenter_one,
      Initialization.adaptedCell_one]
    exact mem_centredIndexFinset_iff hlk
  have hbase := Recurrence.toFullBlockMat_coarseBlock_adaptedCell_le_average
    (q := (1 : Mat d)) Matrix.PosDef.one hlk hZ a
  rw [Initialization.adaptedCell_one] at hbase
  simpa only [adaptedCellAt_one_eq_openCubeSet_translateCube] using! hbase

/-! ## The translation to an aligned parent -/

/-- The index shift carrying the inner cells of the centred parent to the inner
cells of the aligned parent. -/
@[expose]
def innerShift (k l : ℤ) (w t : Fin d → ℤ) : Fin d → ℤ :=
  fun i => t i + w i * 3 ^ (k - l).toNat

/-- The translation vector of an aligned parent. -/
@[expose]
def parentShift (k : ℤ) (w : Fin d → ℤ) : Fin d → ℤ :=
  fun i => w i * 3 ^ k.toNat

private theorem cast_parentShift {k : ℤ} (hk : 0 ≤ k) (w : Fin d → ℤ) (i : Fin d) :
    ((parentShift k w i : ℤ) : ℝ) = (w i : ℝ) * (3 : ℝ) ^ k := by
  rw [parentShift]
  push_cast
  congr 1
  rw [← zpow_natCast (3 : ℝ) k.toNat, Int.toNat_of_nonneg hk]

/-- **Subadditivity at an aligned parent.**  The coarse block of a standard
aligned cube is below the average of the coarse blocks of the scale-`l` standard
cubes that subdivide it. -/
theorem toFullBlockMat_coarseBlock_standardCell_le_average [NeZero d] {l k : ℤ}
    (hl : 0 ≤ l) (hlk : l ≤ k) (w : Fin d → ℤ) (a : CoeffSpace d) :
    toFullBlockMat (coarseBlock (standardCell d k w) a) ≤
      ((centredIndexFinset d l k).card : ℝ)⁻¹ •
        ∑ t ∈ centredIndexFinset d l k,
          toFullBlockMat (coarseBlock (standardCell d l (innerShift k l w t)) a) := by
  have hk : (0 : ℤ) ≤ k := le_trans hl hlk
  set u : Fin d → ℤ := parentShift k w with hudef
  have hucast : ∀ i, ((u i : ℤ) : ℝ) = (w i : ℝ) * (3 : ℝ) ^ k := by
    intro i
    rw [hudef]
    exact cast_parentShift hk w i
  -- the parent is the translate of the centred parent
  have hparent : standardCell d k w
      = translateSet (Source.AKL.intTranslation u) (centeredCube d k) := by
    rw [← standardCell_zero (d := d) k]
    refine Entry.standardCell_eq_translateSet ?_
    intro i
    rw [hucast i]
    simp
  -- the inner cells transport with the same vector
  have hinner : ∀ t : Fin d → ℤ, standardCell d l (innerShift k l w t)
      = translateSet (Source.AKL.intTranslation u) (standardCell d l t) := by
    intro t
    refine Entry.standardCell_eq_translateSet ?_
    intro i
    have hsplit : (3 : ℝ) ^ ((k - l).toNat : ℕ) * (3 : ℝ) ^ l = (3 : ℝ) ^ k := by
      rw [← zpow_natCast (3 : ℝ) ((k - l).toNat),
        show (((k - l).toNat : ℤ)) = k - l from Int.toNat_of_nonneg (by omega),
        ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      omega
    rw [innerShift, hucast i]
    push_cast
    linear_combination (w i : ℝ) * hsplit
  rw [hparent, Recurrence.coarseBlock_translateSet]
  have hbase := toFullBlockMat_coarseBlock_centeredCube_le_average hlk (translateCoeff u a)
  refine hbase.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hinner t, Recurrence.coarseBlock_translateSet]

end

end Quenched
end HighContrast
end HCPolySupport
