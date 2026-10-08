/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.FillingExhaustion
public import LeanPool.HighContrastHomogenization.Provider.Transport.TransportMeanDomination

/-!
# High-contrast homogenization: Provider.Entry.AdapterQuadratic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quadratic forms of the weighted sums of a filling

`e.two.grid.whitney.average` is consumed against a majorant of every finite
partial double sum of a filling's rows, and the majorant is presented as a
doubled block.  Its quadratic form has to be resolved into the rows and the
remainder, and the resolution is the same at the pathwise and at the annealed
level.  The four elementary facts that do it are collected here: the passage
from the Loewner order to the quadratic form, the resolution of a weighted double
sum, the positivity of a finite sum of positive blocks, and the split of a
partial sum at an intermediate scale.

Two arithmetic conveniences travel with them: a weighted row against a uniform
bound on its cells, and the mean of an affine function of the source scale.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## Quadratic forms -/

/-- The Loewner order on flattened blocks implies the order of the quadratic
forms. -/
theorem quad_le_of_le {A B : FullBlockMat d} (h : A ≤ B) (x : BlockCoord d → ℝ) :
    x ⬝ᵥ Matrix.mulVec A x ≤ x ⬝ᵥ Matrix.mulVec B x := by
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hx := hPS.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  simp only [star_trivial] at hx
  linarith only [hx]

/-- The quadratic form of a weighted double sum plus a remainder, resolved. -/
theorem blockQuadratic_double_sum (X : BlockVec d) (R : Finset ℤ)
    (Zf : ℤ → Finset (Fin d → ℤ)) (c : ℤ → (Fin d → ℤ) → ℝ)
    (A : ℤ → (Fin d → ℤ) → BlockMat d) (G : BlockMat d) :
    blockVecDot X (blockMatVecMul (ofFullBlockMat
      ((∑ r ∈ R, ∑ w ∈ Zf r, c r w • toFullBlockMat (A r w)) + toFullBlockMat G)) X) =
      (∑ r ∈ R, ∑ w ∈ Zf r, c r w * blockVecDot X (blockMatVecMul (A r w) X)) +
        blockVecDot X (blockMatVecMul G X) := by
  rw [blockVecDot_blockMatVecMul_eq_dotProduct, toFullBlockMat_ofFullBlockMat,
    Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum,
    blockVecDot_blockMatVecMul_eq_dotProduct]
  refine congrArg (· + _) (Finset.sum_congr rfl fun r _ => ?_)
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    blockVecDot_blockMatVecMul_eq_dotProduct]

/-- **The majorant read through its half quadratic form**, resolved into the rows
and the scalar remainder.  This is the shape in which
`e.two.grid.whitney.average` compares its hypothesis. -/
theorem half_blockQuadratic_majorant (X : BlockVec d) (R : Finset ℤ)
    (Zf : ℤ → Finset (Fin d → ℤ)) (c : ℤ → (Fin d → ℤ) → ℝ)
    (A : ℤ → (Fin d → ℤ) → BlockMat d) (cb : ℝ) (G : BlockMat d) :
    1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat
        ((∑ r ∈ R, ∑ w ∈ Zf r, c r w • toFullBlockMat (A r w)) +
          cb • toFullBlockMat G)) X) =
      (∑ r ∈ R, ∑ w ∈ Zf r,
          c r w * (1 / 2 * blockVecDot X (blockMatVecMul (A r w) X))) +
        1 / 2 * (cb * blockVecDot X (blockMatVecMul G X)) := by
  rw [show cb • toFullBlockMat G = toFullBlockMat (blockScale cb G) from
      (toFullBlockMat_blockScale cb G).symm,
    blockQuadratic_double_sum, Sharp.blockVecDot_blockMatVecMul_blockScale, mul_add,
    Finset.mul_sum]
  refine congrArg (· + _) (Finset.sum_congr rfl fun r _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- A finite sum of positive semidefinite flattened blocks is positive
semidefinite. -/
theorem posSemidef_finsetSum {ι : Type*} {s : Finset ι} {A : ι → FullBlockMat d}
    (h : ∀ i ∈ s, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-! ## Splitting a partial sum at an intermediate scale -/

/-- **The printed split of the exhaustion hypothesis.**  A quantity dominating
every partial sum below an intermediate scale, added to the part from that scale
up, dominates every partial sum of the whole family. -/
theorem sum_Icc_le_of_belowStart {jStar n : ℤ} (hjn : jStar ≤ n) {row : ℤ → ℝ}
    {G : ℝ} (hrow0 : ∀ r, 0 ≤ row r) (hG0 : 0 ≤ G)
    (hbelow : ∀ J' : ℤ, ∑ r ∈ Finset.Ico J' jStar, row r ≤ G) (J : ℤ) :
    ∑ r ∈ Finset.Icc J n, row r ≤ (∑ r ∈ Finset.Icc jStar n, row r) + G := by
  rcases le_or_gt jStar J with hle | hlt
  · have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := row) (Finset.Icc_subset_Icc hle (le_refl n)) fun i _ _ => hrow0 i
    linarith only [hmono, hG0]
  · have hdisj : Disjoint (Finset.Ico J jStar) (Finset.Icc jStar n) := by
      refine Finset.disjoint_left.mpr fun i hi hi' => ?_
      rw [Finset.mem_Ico] at hi
      rw [Finset.mem_Icc] at hi'
      omega
    have hsplit : Finset.Icc J n = Finset.Ico J jStar ∪ Finset.Icc jStar n := by
      change Finset.Ico J (n + 1) = Finset.Ico J jStar ∪ Finset.Ico jStar (n + 1)
      exact (Finset.Ico_union_Ico_eq_Ico hlt.le (by omega)).symm
    have hbJ := hbelow J
    rw [hsplit, Finset.sum_union hdisj]
    linarith only [hbJ]

/-! ## A weighted row, and the mean of an affine function -/

/-- A weighted row of a filling, against a uniform bound on its cells. -/
theorem sum_weight_mul_le {ι : Type*} {Z : Finset ι} {V : ι → Set (Vec d)}
    {W : Set (Vec d)} {A : ι → ℝ} {B c : ℝ} (hB0 : 0 ≤ B) (hA : ∀ w ∈ Z, A w ≤ B)
    (hrow : ∑ w ∈ Z, (volume (V w)).toReal / (volume W).toReal ≤ c) :
    ∑ w ∈ Z, (volume (V w)).toReal / (volume W).toReal * A w ≤ c * B := by
  have hth0 : ∀ w : ι, (0 : ℝ) ≤ (volume (V w)).toReal / (volume W).toReal :=
    fun _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  refine le_trans (Finset.sum_le_sum fun w hw =>
    mul_le_mul_of_nonneg_left (hA w hw) (hth0 w)) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hrow hB0

/-- The mean of an affine function of the source scale. -/
theorem integral_affine {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {S : CoeffSpace d → ℝ} (hS : Integrable S P) (al be : ℝ) :
    ∫ a, (al + be * S a) ∂P = al + be * ∫ a, S a ∂P := by
  rw [integral_add (integrable_const al) (hS.const_mul be), integral_const,
    integral_const_mul, probReal_univ, smul_eq_mul, one_mul]

end

end Entry
end HighContrast
end HCPolySupport
