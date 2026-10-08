/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeNormalizedLocality
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeSubadditivity

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeInnerCells

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The inner cells of an aligned parent

The renormalization argument averages the coarse blocks of the scale-`l` cells
that subdivide a scale-`k` cell centred in `□_m`.  Three facts about that family
are needed before the concentration estimate and the subadditivity can be
combined.

Their centres lie in `□_{m+1}`, not necessarily in `□_m`: a parent centred near
the boundary of `□_m` has inner cells centred outside it, so the
coarse-ellipticity datum has to be read one generation higher.  The average of
their coarse blocks is a doubled block in its own right.  And the index map of
the subdivision is injective, so the family may be indexed by the cells
themselves.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The inner cells sit one generation higher -/

/-- **The inner cells of a parent centred in `□_m` are centred in `□_{m+1}`.**
This is why the coarse-ellipticity datum is read at the generation `m + 1` in the
subdivision step. -/
theorem standardCellCenter_innerShift_mem_centeredCube_succ {l k m : ℤ}
    (hlk : l ≤ k) (hkm : k ≤ m) {w t : Fin d → ℤ}
    (hw : standardCellCenter k w ∈ centeredCube d m)
    (ht : standardCellCenter l t ∈ centeredCube d k) :
    standardCellCenter l (innerShift k l w t) ∈ centeredCube d (m + 1) := by
  rw [Recurrence.mem_centeredCube_iff] at hw ht ⊢
  intro i
  obtain ⟨hw1, hw2⟩ := hw i
  obtain ⟨ht1, ht2⟩ := ht i
  have hsplit : (3 : ℝ) ^ ((k - l).toNat : ℕ) * (3 : ℝ) ^ l = (3 : ℝ) ^ k := by
    rw [← zpow_natCast (3 : ℝ) ((k - l).toNat),
      show (((k - l).toNat : ℤ)) = k - l from Int.toNat_of_nonneg (by omega),
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have hval : standardCellCenter l (innerShift k l w t) i
      = standardCellCenter l t i + standardCellCenter k w i := by
    simp only [standardCellCenter, innerShift]
    push_cast
    linear_combination (w i : ℝ) * hsplit
  have hkm3 : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) hkm
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hsucc : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  rw [hval, hsucc]
  constructor
  · linarith only [ht1, hw1, hkm3, h3m]
  · linarith only [ht2, hw2, hkm3, h3m]

/-! ## The average of a family of doubled blocks -/

/-- The average of a finite family of doubled blocks. -/
@[expose]
def avgBlockOf {ι : Type*} (Z : Finset ι) (M : ι → BlockMat d) : BlockMat d where
  upperLeft := Matrix.of fun i j => (Z.card : ℝ)⁻¹ * ∑ t ∈ Z, (M t).upperLeft i j
  upperRight := Matrix.of fun i j => (Z.card : ℝ)⁻¹ * ∑ t ∈ Z, (M t).upperRight i j
  lowerLeft := Matrix.of fun i j => (Z.card : ℝ)⁻¹ * ∑ t ∈ Z, (M t).lowerLeft i j
  lowerRight := Matrix.of fun i j => (Z.card : ℝ)⁻¹ * ∑ t ∈ Z, (M t).lowerRight i j

theorem blockMatEntry_avgBlockOf {ι : Type*} (Z : Finset ι) (M : ι → BlockMat d)
    (α β : BlockCoord d) :
    blockMatEntry (avgBlockOf Z M) α β =
      (Z.card : ℝ)⁻¹ * ∑ t ∈ Z, blockMatEntry (M t) α β := by
  cases α <;> cases β <;> rfl

theorem toFullBlockMat_avgBlockOf {ι : Type*} (Z : Finset ι) (M : ι → BlockMat d) :
    toFullBlockMat (avgBlockOf Z M)
      = (Z.card : ℝ)⁻¹ • ∑ t ∈ Z, toFullBlockMat (M t) := by
  ext α β
  rw [toFullBlockMat_eq_blockMatEntry, blockMatEntry_avgBlockOf, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  congr 1

/-! ## The subdivision index map -/

theorem innerShift_injective (k l : ℤ) (w : Fin d → ℤ) :
    Function.Injective (innerShift (d := d) k l w) := by
  intro t t' h
  funext i
  have hi := congrFun h i
  simp only [innerShift] at hi
  omega

theorem card_image_innerShift (k l : ℤ) (w : Fin d → ℤ) (Z : Finset (Fin d → ℤ)) :
    (Z.image (innerShift k l w)).card = Z.card :=
  Finset.card_image_of_injective Z (innerShift_injective k l w)

theorem avgBlockOf_image_innerShift {k l : ℤ} (w : Fin d → ℤ)
    (Z : Finset (Fin d → ℤ)) (F : (Fin d → ℤ) → BlockMat d) :
    avgBlockOf (Z.image (innerShift k l w)) F
      = avgBlockOf Z fun t => F (innerShift k l w t) := by
  classical
  refine toFullBlockMat_injective ?_
  rw [toFullBlockMat_avgBlockOf, toFullBlockMat_avgBlockOf, card_image_innerShift]
  congr 1
  exact Finset.sum_image fun x _ y _ hxy => innerShift_injective k l w hxy

/-! ## Subadditivity in block form -/

/-- **Subadditivity against the average of the inner cells**, in the Loewner
order of doubled blocks and indexed by the inner cells themselves. -/
theorem blockMatLoewnerLE_coarseBlock_avgBlockOf [NeZero d] {l k : ℤ}
    (hl : 0 ≤ l) (hlk : l ≤ k) (w : Fin d → ℤ) (a : CoeffSpace d) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (avgBlockOf ((centredIndexFinset d l k).image (innerShift k l w))
        fun u => coarseBlock (standardCell d l u) a) := by
  refine blockMatLoewnerLE_of_le ?_
  rw [avgBlockOf_image_innerShift, toFullBlockMat_avgBlockOf]
  exact toFullBlockMat_coarseBlock_standardCell_le_average hl hlk w a

end

end Quenched
end HighContrast
end HCPolySupport
