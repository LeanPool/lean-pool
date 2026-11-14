/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block

/-!
# Polarization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Polarization on doubled vectors

Finite-dimensional algebra converting the diagonal of an arbitrary bilinear
form on `BlockVec d` into its unique symmetric representing `BlockMat d`.
-/

namespace Algsuperdiff.Section24.CoarseMatrixDerivative.Internal

open HCPolySupport
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Coordinates of a block vector in the two-component basis. -/
def blockVecComp (P : BlockVec d) : BlockCoord d → ℝ
  | Sum.inl i => P.1 i
  | Sum.inr i => P.2 i

theorem blockVec_eq_sum_blockBasis (P : BlockVec d) :
    P = ∑ α : BlockCoord d, blockVecComp P α • blockBasis α := by
  rw [Fintype.sum_sum_type]
  ext
  · simp only [Prod.fst_sum, blockBasis, blockVecComp, Prod.smul_fst, smul_zero,
      Finset.sum_const_zero, add_zero, Prod.fst_add]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  · simp only [Prod.snd_sum, blockBasis, blockVecComp, Prod.smul_snd, smul_zero,
      Finset.sum_const_zero, zero_add, Prod.snd_add]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp

/-- A polarized matrix entry reconstructed from a quadratic form. -/
def blockQuadFormEntry (B : BlockVec d → ℝ) (α β : BlockCoord d) : ℝ :=
  if α = β then B (blockBasis α)
  else (B (blockBasis α + blockBasis β) - B (blockBasis α) - B (blockBasis β)) / 2

/-- The block matrix reconstructed by polarizing a quadratic form. -/
def blockMatOfQuadForm (B : BlockVec d → ℝ) : BlockMat d :=
  { upperLeft := fun i j => blockQuadFormEntry B (Sum.inl i) (Sum.inl j)
    upperRight := fun i j => blockQuadFormEntry B (Sum.inl i) (Sum.inr j)
    lowerLeft := fun i j => blockQuadFormEntry B (Sum.inr i) (Sum.inl j)
    lowerRight := fun i j => blockQuadFormEntry B (Sum.inr i) (Sum.inr j) }

@[simp] theorem blockMatEntry_blockMatOfQuadForm (B : BlockVec d → ℝ)
    (α β : BlockCoord d) :
    blockMatEntry (blockMatOfQuadForm B) α β = blockQuadFormEntry B α β := by
  cases α <;> cases β <;> rfl

theorem blockQuadFormEntry_symm (B : BlockVec d → ℝ) (α β : BlockCoord d) :
    blockQuadFormEntry B α β = blockQuadFormEntry B β α := by
  unfold blockQuadFormEntry
  by_cases h : α = β
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), add_comm (blockBasis α) (blockBasis β)]
    ring

theorem isSymmetricBlockMat_blockMatOfQuadForm (B : BlockVec d → ℝ) :
    IsSymmetricBlockMat (blockMatOfQuadForm B) := by
  intro α β
  rw [blockMatEntry_blockMatOfQuadForm, blockMatEntry_blockMatOfQuadForm]
  exact blockQuadFormEntry_symm B α β

section Bilinear

variable (φ : BlockVec d → BlockVec d → ℝ)
  (hadd_l : ∀ X Y Z : BlockVec d, φ (X + Y) Z = φ X Z + φ Y Z)
  (hsmul_l : ∀ (c : ℝ) (X Y : BlockVec d), φ (c • X) Y = c * φ X Y)
  (hadd_r : ∀ X Y Z : BlockVec d, φ X (Y + Z) = φ X Y + φ X Z)
  (hsmul_r : ∀ (c : ℝ) (X Y : BlockVec d), φ X (c • Y) = c * φ X Y)

include hadd_l hsmul_l in
theorem sum_left {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (g : ι → BlockVec d) (Y : BlockVec d) :
    φ (∑ i ∈ s, f i • g i) Y = ∑ i ∈ s, f i * φ (g i) Y := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [show φ (0 : BlockVec d) Y = 0 by
        have hz := hsmul_l 0 Y Y
        simpa using hz]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, hadd_l, hsmul_l, ih, Finset.sum_insert ha]

include hadd_r hsmul_r in
theorem sum_right {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (g : ι → BlockVec d) (X : BlockVec d) :
    φ X (∑ i ∈ s, f i • g i) = ∑ i ∈ s, f i * φ X (g i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [show φ X (0 : BlockVec d) = 0 by
        have hz := hsmul_r 0 X X
        simpa using hz]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, hadd_r, hsmul_r, ih, Finset.sum_insert ha]

include hadd_l hsmul_l hadd_r hsmul_r in
theorem bilin_apply_eq_sum (P Q : BlockVec d) :
    φ P Q = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      blockVecComp P α * blockVecComp Q β * φ (blockBasis α) (blockBasis β) := by
  conv_lhs => rw [blockVec_eq_sum_blockBasis P, blockVec_eq_sum_blockBasis Q]
  rw [sum_left φ hadd_l hsmul_l]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [sum_right φ hadd_r hsmul_r]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  ring

end Bilinear

theorem blockMatEntry_blockMatOfQuadForm_bilin
    (φ : BlockVec d → BlockVec d → ℝ)
    (hadd_l : ∀ X Y Z : BlockVec d, φ (X + Y) Z = φ X Z + φ Y Z)
    (hadd_r : ∀ X Y Z : BlockVec d, φ X (Y + Z) = φ X Y + φ X Z)
    (α β : BlockCoord d) :
    blockMatEntry (blockMatOfQuadForm (fun X => φ X X)) α β =
      (φ (blockBasis α) (blockBasis β) + φ (blockBasis β) (blockBasis α)) / 2 := by
  rw [blockMatEntry_blockMatOfQuadForm]
  unfold blockQuadFormEntry
  by_cases h : α = β
  · subst h
    rw [ite_eq_left rfl]
    ring
  · rw [ite_eq_right h]
    change
      (φ (blockBasis α + blockBasis β) (blockBasis α + blockBasis β)
        - φ (blockBasis α) (blockBasis α) - φ (blockBasis β) (blockBasis β)) / 2 =
          (φ (blockBasis α) (blockBasis β) + φ (blockBasis β) (blockBasis α)) / 2
    have hexp : φ (blockBasis α + blockBasis β) (blockBasis α + blockBasis β) =
        φ (blockBasis α) (blockBasis α) + φ (blockBasis α) (blockBasis β) +
          φ (blockBasis β) (blockBasis α) + φ (blockBasis β) (blockBasis β) := by
      rw [hadd_l, hadd_r, hadd_r]
      ring
    rw [hexp]
    ring

theorem blockVecDot_blockMatVecMul_blockMatOfQuadForm_of_bilin
    (φ : BlockVec d → BlockVec d → ℝ)
    (hadd_l : ∀ X Y Z : BlockVec d, φ (X + Y) Z = φ X Z + φ Y Z)
    (hsmul_l : ∀ (c : ℝ) (X Y : BlockVec d), φ (c • X) Y = c * φ X Y)
    (hadd_r : ∀ X Y Z : BlockVec d, φ X (Y + Z) = φ X Y + φ X Z)
    (hsmul_r : ∀ (c : ℝ) (X Y : BlockVec d), φ X (c • Y) = c * φ X Y)
    (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (blockMatOfQuadForm (fun X => φ X X)) P) = φ P P := by
  set N := blockMatOfQuadForm (fun X => φ X X) with hN
  have hψadd_l : ∀ X Y Z : BlockVec d,
      blockVecDot (X + Y) (blockMatVecMul N Z) =
        blockVecDot X (blockMatVecMul N Z) + blockVecDot Y (blockMatVecMul N Z) := by
    intro X Y Z
    rw [blockVecDot_add_left]
  have hψsmul_l : ∀ (c : ℝ) (X Y : BlockVec d),
      blockVecDot (c • X) (blockMatVecMul N Y) =
        c * blockVecDot X (blockMatVecMul N Y) := by
    intro c X Y
    rw [blockVecDot_smul_left]
  have hψadd_r : ∀ X Y Z : BlockVec d,
      blockVecDot X (blockMatVecMul N (Y + Z)) =
        blockVecDot X (blockMatVecMul N Y) + blockVecDot X (blockMatVecMul N Z) := by
    intro X Y Z
    rw [blockMatVecMul_add, blockVecDot_add_right]
  have hψsmul_r : ∀ (c : ℝ) (X Y : BlockVec d),
      blockVecDot X (blockMatVecMul N (c • Y)) =
        c * blockVecDot X (blockMatVecMul N Y) := by
    intro c X Y
    rw [blockMatVecMul_smul, blockVecDot_smul_right]
  rw [bilin_apply_eq_sum (fun X Y => blockVecDot X (blockMatVecMul N Y))
        hψadd_l hψsmul_l hψadd_r hψsmul_r P P,
      bilin_apply_eq_sum φ hadd_l hsmul_l hadd_r hsmul_r P P]
  have hentry : ∀ α β : BlockCoord d,
      blockVecDot (blockBasis α) (blockMatVecMul N (blockBasis β)) =
        (φ (blockBasis α) (blockBasis β) + φ (blockBasis β) (blockBasis α)) / 2 := by
    intro α β
    rw [blockBasis_pairing, hN,
      blockMatEntry_blockMatOfQuadForm_bilin φ hadd_l hadd_r α β]
  simp_rw [hentry]
  set c := blockVecComp P with hc
  have hswap :
      (∑ α : BlockCoord d, ∑ β : BlockCoord d,
        c α * c β * φ (blockBasis β) (blockBasis α)) =
        ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          c α * c β * φ (blockBasis α) (blockBasis β) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
    ring
  calc
    (∑ α : BlockCoord d, ∑ β : BlockCoord d,
        c α * c β * ((φ (blockBasis α) (blockBasis β) +
          φ (blockBasis β) (blockBasis α)) / 2)) =
      (1 / 2) * (∑ α : BlockCoord d, ∑ β : BlockCoord d,
        c α * c β * φ (blockBasis α) (blockBasis β)) +
      (1 / 2) * (∑ α : BlockCoord d, ∑ β : BlockCoord d,
        c α * c β * φ (blockBasis β) (blockBasis α)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun β _ => ?_)
          ring
    _ = (1 / 2) * (∑ α : BlockCoord d, ∑ β : BlockCoord d,
          c α * c β * φ (blockBasis α) (blockBasis β)) +
        (1 / 2) * (∑ α : BlockCoord d, ∑ β : BlockCoord d,
          c α * c β * φ (blockBasis α) (blockBasis β)) := by rw [hswap]
    _ = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          c α * c β * φ (blockBasis α) (blockBasis β) := by ring

end

end Algsuperdiff.Section24.CoarseMatrixDerivative.Internal
