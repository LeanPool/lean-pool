/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.Contrast
public import LeanPool.HighContrastHomogenization.Annealed.Positivity
public import LeanPool.HighContrastHomogenization.Provider.Entry.IdentityCells
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# High-contrast homogenization: Provider.Quenched.AnnealedLimitBlock

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed limit block of the Euclidean cubes

The endgame display `e.algebraic.block.decay`
compares the Euclidean annealed blocks `𝐀̄(□_m)` of `e.Theta.m`
with a single deterministic limit block.  This file constructs that limit and
proves the half of the comparison that the coarse ellipticity assumption
`e.coarse.ellipticity` already carries.

The annealed mean order of `p.fixed.geometry.parent.child.recurrence`, read on the identity
grid, makes the doubled quadratic form of `𝐀̄(□_n)` nonincreasing along the
nonnegative generations; positivity of the annealed block bounds it below.  Each
form therefore converges to its infimum, and the polarization identity of the
doubled block turns the convergence of the three forms attached to a pair of
doubled coordinates into convergence of the corresponding entry.  The entrywise
limits assemble into a symmetric doubled block whose form is exactly the
infimum of the forms, so it lies Loewner-below every `𝐀̄(□_m)` with `m ≥ 0`.

The last section records the scalar dilation algebra of the doubled block that
the two-sided comparison uses.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory
open _root_.Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## The forms of the Euclidean annealed blocks -/

/-- The doubled quadratic form of the Euclidean annealed block, indexed by the
nonnegative generations. -/
@[expose]
def annealedForm (P : Measure (CoeffSpace d)) (X : BlockVec d) (n : ℕ) : ℝ :=
  blockVecDot X (blockMatVecMul (annealedBlock P (centeredCube d (n : ℤ))) X)

/-- The entry of a Euclidean annealed block, recovered from the three forms of
the polarization identity of the doubled block. -/
theorem blockMatEntry_annealedBlock_eq_annealedForm (P : Measure (CoeffSpace d))
    (n : ℕ) (α β : BlockCoord d) :
    blockMatEntry (annealedBlock P (centeredCube d (n : ℤ))) α β =
      (annealedForm P (blockBasis α + blockBasis β) n -
          annealedForm P (blockBasis α) n - annealedForm P (blockBasis β) n) / 2 := by
  have hsym := isSymmetricBlockMat_annealedBlock P (centeredCube d (n : ℤ)) α β
  have hpair := blockBasis_sum_pairing (annealedBlock P (centeredCube d (n : ℤ))) α β
  have hαα := blockBasis_pairing (annealedBlock P (centeredCube d (n : ℤ))) α α
  have hββ := blockBasis_pairing (annealedBlock P (centeredCube d (n : ℤ))) β β
  simp only [annealedForm]
  rw [hpair, hαα, hββ]
  linarith only [hsym]

/-! ## The limit block -/

/-- The entries of the annealed limit block: the polarization combination of the
infima of the three forms attached to a pair of doubled coordinates. -/
@[expose]
def annealedLimitEntry (P : Measure (CoeffSpace d)) (α β : BlockCoord d) : ℝ :=
  ((⨅ n, annealedForm P (blockBasis α + blockBasis β) n) -
      (⨅ n, annealedForm P (blockBasis α) n) -
      (⨅ n, annealedForm P (blockBasis β) n)) / 2

/-- The annealed limit block `𝐀̄`: the doubled block assembled from the
entrywise limits of the Euclidean annealed blocks. -/
@[expose]
def annealedLimitBlock (P : Measure (CoeffSpace d)) : BlockMat d :=
  ofFullBlockMat (Matrix.of (annealedLimitEntry P))

@[simp] theorem blockMatEntry_annealedLimitBlock (P : Measure (CoeffSpace d))
    (α β : BlockCoord d) :
    blockMatEntry (annealedLimitBlock P) α β = annealedLimitEntry P α β := by
  simp only [annealedLimitBlock, blockMatEntry_ofFullBlockMat, Matrix.of_apply]

theorem annealedLimitEntry_comm (P : Measure (CoeffSpace d)) (α β : BlockCoord d) :
    annealedLimitEntry P α β = annealedLimitEntry P β α := by
  simp only [annealedLimitEntry, add_comm (blockBasis α) (blockBasis β)]
  ring

/-- The annealed limit block is a symmetric doubled block. -/
theorem isSymmetricBlockMat_annealedLimitBlock (P : Measure (CoeffSpace d)) :
    IsSymmetricBlockMat (annealedLimitBlock P) := by
  intro α β
  simp only [blockMatEntry_annealedLimitBlock]
  exact annealedLimitEntry_comm P α β

/-! ## Monotonicity and convergence under the coarse ellipticity assumption -/

section Dagger

variable [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
  {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}

/-- **The forms of the Euclidean annealed blocks are nonincreasing.**  This is
the annealed mean order of `p.fixed.geometry.parent.child.recurrence` at the identity grid,
which holds from generation zero up. -/
theorem annealedForm_antitone (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (X : BlockVec d) :
    Antitone (annealedForm P X) := by
  intro m n hmn
  have hle :=
    Entry.annealedBlock_centeredCube_le_of_nonneg hstat hdag (j := (m : ℤ)) (p := (n : ℤ))
      (Int.natCast_nonneg m) (by exact_mod_cast hmn) X
  simp only [annealedForm]
  linarith only [hle]

/-- The forms of the Euclidean annealed blocks are nonnegative. -/
theorem annealedForm_nonneg
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (X : BlockVec d) (n : ℕ) :
    0 ≤ annealedForm P X n := by
  rcases eq_or_ne X 0 with hX | hX
  · subst hX
    simp only [annealedForm]
    rw [blockVecDot_blockMatVecMul_eq_sum]
    have hz : ∀ α : BlockCoord d, toFullBlockVec (0 : BlockVec d) α = 0 := by
      intro α; cases α <;> rfl
    simp only [hz, zero_mul, Finset.sum_const_zero]
    exact le_rfl
  · exact (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag (n : ℤ) X hX).le

theorem bddBelow_range_annealedForm
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (X : BlockVec d) :
    BddBelow (Set.range (annealedForm P X)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  exact annealedForm_nonneg hdag X n

/-- Each form of the Euclidean annealed blocks converges to its infimum. -/
theorem tendsto_annealedForm_ciInf (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (X : BlockVec d) :
    Tendsto (annealedForm P X) atTop (𝓝 (⨅ n, annealedForm P X n)) :=
  tendsto_atTop_ciInf (annealedForm_antitone hstat hdag X) (bddBelow_range_annealedForm hdag X)

/-- **The entries of the Euclidean annealed blocks converge to the entries of the
annealed limit block.** -/
theorem tendsto_blockMatEntry_annealedBlock (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (α β : BlockCoord d) :
    Tendsto
      (fun n : ℕ => blockMatEntry (annealedBlock P (centeredCube d (n : ℤ))) α β)
      atTop (𝓝 (blockMatEntry (annealedLimitBlock P) α β)) := by
  have h1 := tendsto_annealedForm_ciInf hstat hdag (blockBasis α + blockBasis β)
  have h2 := tendsto_annealedForm_ciInf hstat hdag (blockBasis α)
  have h3 := tendsto_annealedForm_ciInf hstat hdag (blockBasis β)
  have hcomb := ((h1.sub h2).sub h3).div_const 2
  rw [blockMatEntry_annealedLimitBlock]
  refine Tendsto.congr (fun n => ?_) hcomb
  exact (blockMatEntry_annealedBlock_eq_annealedForm P n α β).symm

/-- The form of the annealed limit block is the limit of the forms of the
Euclidean annealed blocks. -/
theorem tendsto_annealedForm_annealedLimitBlock (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (X : BlockVec d) :
    Tendsto (annealedForm P X) atTop
      (𝓝 (blockVecDot X (blockMatVecMul (annealedLimitBlock P) X))) := by
  have hsum : ∀ n : ℕ,
      (∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec X α *
          (blockMatEntry (annealedBlock P (centeredCube d (n : ℤ))) α β *
            toFullBlockVec X β)) = annealedForm P X n :=
    fun n => (blockVecDot_blockMatVecMul_eq_sum _ X).symm
  refine Tendsto.congr hsum ?_
  rw [blockVecDot_blockMatVecMul_eq_sum]
  refine tendsto_finsetSum _ fun α _ => tendsto_finsetSum _ fun β _ => ?_
  exact ((tendsto_blockMatEntry_annealedBlock hstat hdag α β).mul_const
    (toFullBlockVec X β)).const_mul (toFullBlockVec X α)

/-- **The form of the annealed limit block is the infimum of the forms of the
Euclidean annealed blocks.** -/
theorem blockVecDot_annealedLimitBlock_eq_ciInf
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (annealedLimitBlock P) X) =
      ⨅ n, annealedForm P X n :=
  tendsto_nhds_unique (tendsto_annealedForm_annealedLimitBlock hstat hdag X)
    (tendsto_annealedForm_ciInf hstat hdag X)

/-- **The annealed limit block lies Loewner-below every Euclidean annealed block
of a nonnegative generation.** -/
theorem blockMatLoewnerLE_annealedLimitBlock (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {m : ℤ} (hm : 0 ≤ m) :
    BlockMatLoewnerLE (annealedLimitBlock P) (annealedBlock P (centeredCube d m)) := by
  intro X
  have hlim := blockVecDot_annealedLimitBlock_eq_ciInf hstat hdag X
  have hmn : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
  have hle : (⨅ n, annealedForm P X n) ≤ annealedForm P X m.toNat :=
    ciInf_le (bddBelow_range_annealedForm hdag X) m.toNat
  have heq : annealedForm P X m.toNat =
      blockVecDot X (blockMatVecMul (annealedBlock P (centeredCube d m)) X) := by
    simp only [annealedForm, hmn]
  rw [heq] at hle
  rw [hlim]
  linarith only [hle]

/-- **A doubled block below every Euclidean annealed block is below the limit.**
The limit is the greatest lower bound of the family in the Loewner order. -/
theorem blockMatLoewnerLE_annealedLimitBlock_of_forall
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {A : BlockMat d}
    (hA : ∀ n : ℕ, BlockMatLoewnerLE A (annealedBlock P (centeredCube d (n : ℤ)))) :
    BlockMatLoewnerLE A (annealedLimitBlock P) := by
  intro X
  have hle : ∀ n : ℕ,
      blockVecDot X (blockMatVecMul A X) ≤ annealedForm P X n := by
    intro n
    have h := hA n X
    simp only [annealedForm]
    linarith only [h]
  rw [blockVecDot_annealedLimitBlock_eq_ciInf hstat hdag X]
  have := le_ciInf hle
  linarith only [this]

end Dagger

/-! ## The scalar dilation algebra of the doubled block -/

/-- The doubled quadratic form of a scalar dilation. -/
theorem blockVecDot_blockMatVecMul_blockScale (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  rw [blockVecDot_blockMatVecMul_eq_sum, blockVecDot_blockMatVecMul_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [blockMatEntry_blockScale]
  ring

/-- Scalar dilation by a nonnegative factor preserves the Loewner order. -/
theorem blockMatLoewnerLE_blockScale_of_le {c : ℝ} (hc : 0 ≤ c) {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (blockScale c A) (blockScale c B) := by
  intro X
  rw [blockVecDot_blockMatVecMul_blockScale, blockVecDot_blockMatVecMul_blockScale]
  have hQ : blockVecDot X (blockMatVecMul A X) ≤ blockVecDot X (blockMatVecMul B X) := by
    linarith only [h X]
  have := mul_le_mul_of_nonneg_left hQ hc
  linarith only [this]

/-- Enlarging the scalar enlarges the dilation of a positive definite doubled
block. -/
theorem blockMatLoewnerLE_blockScale_of_scalar_le {c c' : ℝ} (hcc : c ≤ c')
    {A : BlockMat d} (hA : Book.Ch02.BlockPosDef A) :
    BlockMatLoewnerLE (blockScale c A) (blockScale c' A) := by
  intro X
  rw [blockVecDot_blockMatVecMul_blockScale, blockVecDot_blockMatVecMul_blockScale]
  have hQ : 0 ≤ blockVecDot X (blockMatVecMul A X) := by
    rcases eq_or_ne X 0 with hX | hX
    · subst hX
      rw [blockVecDot_blockMatVecMul_eq_sum]
      have hz : ∀ α : BlockCoord d, toFullBlockVec (0 : BlockVec d) α = 0 := by
        intro α; cases α <;> rfl
      simp only [hz, zero_mul, Finset.sum_const_zero]
      exact le_rfl
    · exact (hA X hX).le
  have := mul_le_mul_of_nonneg_right hcc hQ
  linarith only [this]

end

end Quenched
end HighContrast
end HCPolySupport
