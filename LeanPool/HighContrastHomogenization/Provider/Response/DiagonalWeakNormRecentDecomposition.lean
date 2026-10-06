/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentBound

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentDecomposition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Decomposition of a recent scale

The centered parent state is split through the child optimizer.  The first
piece is the coarse-block comparison term; the second is the averaged
optimizer-difference term controlled by its exact energy.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem blockCellAverage_sub_of_memVectorL2
    {U : Domain d} {F G : Vec d → BlockVec d}
    (hF₁ : MemVectorL2 (U : Set (Vec d)) fun x => (F x).1)
    (hF₂ : MemVectorL2 (U : Set (Vec d)) fun x => (F x).2)
    (hG₁ : MemVectorL2 (U : Set (Vec d)) fun x => (G x).1)
    (hG₂ : MemVectorL2 (U : Set (Vec d)) fun x => (G x).2) :
    blockCellAverage (U : Set (Vec d)) (fun x => F x - G x) =
      blockCellAverage (U : Set (Vec d)) F -
        blockCellAverage (U : Set (Vec d)) G := by
  refine Prod.ext ?_ ?_
  · funext i
    change Book.Ch02.average U (fun x => (F x).1 i - (G x).1 i) =
      Book.Ch02.average U (fun x => (F x).1 i) -
        Book.Ch02.average U (fun x => (G x).1 i)
    unfold Book.Ch02.average
    rw [integral_sub (integrableOn_component hF₁ i)
      (integrableOn_component hG₁ i)]
    ring
  · funext i
    change Book.Ch02.average U (fun x => (F x).2 i - (G x).2 i) =
      Book.Ch02.average U (fun x => (F x).2 i) -
        Book.Ch02.average U (fun x => (G x).2 i)
    unfold Book.Ch02.average
    rw [integral_sub (integrableOn_component hF₂ i)
      (integrableOn_component hG₂ i)]
    ring

/-- Averaging the recent child/parent state difference is the difference of
their cell averages. -/
theorem blockCellAverage_recent_difference [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) :
    blockCellAverage (adaptedCellAt q k w) (fun x =>
        diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x) =
      blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakChildState hq k w a p r) -
        blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakState hq t a p r) := by
  let b := a.coeffOn (adaptedDomainAt hq k w)
  let v := diagonalWeakChildOptimizer hq k w a p r
  have hvgrad : MemVectorL2 (adaptedCellAt q k w) v.toH1.grad :=
    v.toH1.grad_memVectorL2
  have hbEll : IsAEEllipticFieldOn b.lam b.Lam (adaptedCellAt q k w)
      b.toCoeffField :=
    ⟨(adaptedDomainAt hq k w).measurableSet, b.aeStronglyMeasurable, b.aeElliptic⟩
  have hvflux : MemVectorL2 (adaptedCellAt q k w)
      (fun x => matVecMul (b.toCoeffField x) (v.toH1.grad x)) :=
    hbEll.memVectorL2_matVecMul hvgrad
  obtain ⟨hpgrad, hpflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  have hsub : adaptedCellAt q k w ⊆ adaptedCell q t :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw
  have hpgrad' := memVectorL2_mono hsub hpgrad
  have hpflux' := memVectorL2_mono hsub hpflux
  exact blockCellAverage_sub_of_memVectorL2
    (U := adaptedDomainAt hq k w)
    (F := diagonalWeakChildState hq k w a p r)
    (G := diagonalWeakState hq t a p r)
    (by simpa only [diagonalWeakChildState, v] using! hvgrad)
    (by simpa only [diagonalWeakChildState, b, v] using! hvflux)
    hpgrad' hpflux'

private theorem blockAvsumL2_neg {iota : Type*}
    (Z : Finset iota) (F : iota → BlockVec d) :
    blockAvsumL2 Z (fun z => -(F z)) = blockAvsumL2 Z F := by
  rw [blockAvsumL2_eq, blockAvsumL2_eq]
  congr 1
  unfold avsum
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rcases F z with ⟨x, y⟩
  simp [blockVecDot, vecDot]

/-- The centered parent contribution at one recent scale is the sum of the
cell-defect and averaged-defect bounds. -/
theorem diagonalWeak_recent_scale_decomposition_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S m : Mat d} (hsymm : matTranspose S = S) (hsq : S * S = m)
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho delta : ℝ} (hrho : 0 < rho)
    (hdelta1 : delta ≤ 1) {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakState hq t a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r))) ≤
      diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
          diagonalWeakCellDefect q k t E a +
        4 * diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
          (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) *
          Real.sqrt (blockSize (diagonalWeakAverageDefect q k t E a)
            (blockIdentity d)) := by
  let Z := alignedIndex q k t
  let R := blockDiag S S⁻¹
  let G : (Fin d → ℤ) → BlockVec d := fun w =>
    blockMatVecMul R
      (blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakChildState hq k w a p r) -
        blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r))
  let H : (Fin d → ℤ) → BlockVec d := fun w =>
    -(blockMatVecMul R
      (blockCellAverage (adaptedCellAt q k w) (fun x =>
        diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x)))
  have hsplit : ∀ w ∈ Z, blockMatVecMul R
      (blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakState hq t a p r) -
        blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r)) = G w + H w := by
    intro w hw
    dsimp only [G, H, R]
    rw [blockCellAverage_recent_difference hq hkt hw a p r]
    have hneg : -(blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakChildState hq k w a p r) -
          blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t a p r))) =
      blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t a p r) -
          blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakChildState hq k w a p r)) := by
      calc
        -(blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakChildState hq k w a p r) -
              blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakState hq t a p r))) =
          blockMatVecMul (blockDiag S S⁻¹)
            (-(blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakChildState hq k w a p r) -
              blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakState hq t a p r))) := by
            simpa only [neg_one_smul] using
              (blockMatVecMul_smul (blockDiag S S⁻¹) (-1)
                (blockCellAverage (adaptedCellAt q k w)
                    (diagonalWeakChildState hq k w a p r) -
                  blockCellAverage (adaptedCellAt q k w)
                    (diagonalWeakState hq t a p r))).symm
        _ = _ := by
          congr 1
          abel
    rw [hneg, ← blockMatVecMul_add]
    congr 1
    abel
  have hsplitL2 : blockAvsumL2 Z (fun w => blockMatVecMul R
      (blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakState hq t a p r) -
        blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r))) =
      blockAvsumL2 Z (fun w => G w + H w) := by
    rw [blockAvsumL2_eq, blockAvsumL2_eq]
    congr 1
    unfold avsum
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    exact congrArg₂ blockVecDot (hsplit w hw) (hsplit w hw)
  have htri := blockAvsumL2_add_le Z G H
  rw [← hsplitL2] at htri
  have hG := diagonalWeak_recent_cell_bound hq k t hsymm hsq hm hE hEpd a p r
  have hHraw := diagonalWeak_recent_average_good_le hq hkt hsymm hsq hm
    hE hEpd hrho hdelta1 p r hfinite hgood
  have hH : blockAvsumL2 Z H ≤
      4 * diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
        (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) *
        Real.sqrt (blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d)) := by
    rw [show H = fun w => -(blockMatVecMul R
        (blockCellAverage (adaptedCellAt q k w) (fun x =>
          diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x))) from rfl,
      blockAvsumL2_neg]
    exact hHraw
  exact htri.trans (add_le_add hG hH)

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The recent-scale coefficient at a released split level. -/
@[expose]
def recentConstantAtLevel (delta : ℝ) : ℝ :=
  Real.sqrt 2 * (1 + Real.sqrt delta)

theorem one_le_recentConstantAtLevel (delta : ℝ) :
    1 ≤ recentConstantAtLevel delta := by
  have hroot2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsd : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  rw [recentConstantAtLevel]
  calc
    1 = 1 * 1 := by ring
    _ ≤ Real.sqrt 2 * 1 := mul_le_mul_of_nonneg_right hroot2 zero_le_one
    _ ≤ Real.sqrt 2 * (1 + Real.sqrt delta) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsd)
        (le_trans zero_le_one hroot2)

theorem zero_le_recentConstantAtLevel (delta : ℝ) :
    0 ≤ recentConstantAtLevel delta :=
  le_trans zero_le_one (one_le_recentConstantAtLevel delta)

/-- The centered parent contribution at one recent scale, at a released split
level. -/
theorem diagonalWeak_recent_scale_decomposition_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S m : Mat d} (hsymm : matTranspose S = S) (hsq : S * S = m)
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho delta : ℝ} (hrho : 0 < rho)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakState hq t a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r))) ≤
      diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
          diagonalWeakCellDefect q k t E a +
        recentConstantAtLevel delta *
          diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
          (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) *
          Real.sqrt (blockSize (diagonalWeakAverageDefect q k t E a)
            (blockIdentity d)) := by
  let Z := alignedIndex q k t
  let R := blockDiag S S⁻¹
  let G : (Fin d → ℤ) → BlockVec d := fun w =>
    blockMatVecMul R
      (blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakChildState hq k w a p r) -
        blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r))
  let H : (Fin d → ℤ) → BlockVec d := fun w =>
    -(blockMatVecMul R
      (blockCellAverage (adaptedCellAt q k w) (fun x =>
        diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x)))
  have hsplit : ∀ w ∈ Z, blockMatVecMul R
      (blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakState hq t a p r) -
        blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r)) = G w + H w := by
    intro w hw
    dsimp only [G, H, R]
    rw [blockCellAverage_recent_difference hq hkt hw a p r]
    have hneg : -(blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakChildState hq k w a p r) -
          blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t a p r))) =
      blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t a p r) -
          blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakChildState hq k w a p r)) := by
      calc
        -(blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakChildState hq k w a p r) -
              blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakState hq t a p r))) =
          blockMatVecMul (blockDiag S S⁻¹)
            (-(blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakChildState hq k w a p r) -
              blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakState hq t a p r))) := by
            simpa only [neg_one_smul] using
              (blockMatVecMul_smul (blockDiag S S⁻¹) (-1)
                (blockCellAverage (adaptedCellAt q k w)
                    (diagonalWeakChildState hq k w a p r) -
                  blockCellAverage (adaptedCellAt q k w)
                    (diagonalWeakState hq t a p r))).symm
        _ = _ := by
          congr 1
          abel
    rw [hneg, ← blockMatVecMul_add]
    congr 1
    abel
  have hsplitL2 : blockAvsumL2 Z (fun w => blockMatVecMul R
      (blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakState hq t a p r) -
        blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r))) =
      blockAvsumL2 Z (fun w => G w + H w) := by
    rw [blockAvsumL2_eq, blockAvsumL2_eq]
    congr 1
    unfold avsum
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    exact congrArg₂ blockVecDot (hsplit w hw) (hsplit w hw)
  have htri := blockAvsumL2_add_le Z G H
  rw [← hsplitL2] at htri
  have hG := diagonalWeak_recent_cell_bound hq k t hsymm hsq hm hE hEpd a p r
  have hHraw := diagonalWeak_recent_average_good_at_level_le hq hkt hsymm hsq
    hm hE hEpd hrho p r hfinite hgood
  have hH : blockAvsumL2 Z H ≤
      recentConstantAtLevel delta *
        diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
        (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) *
        Real.sqrt (blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d)) := by
    rw [show H = fun w => -(blockMatVecMul R
        (blockCellAverage (adaptedCellAt q k w) (fun x =>
          diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x))) from rfl,
      blockAvsumL2_neg]
    rw [recentConstantAtLevel]
    exact hHraw
  exact htri.trans (add_le_add hG hH)

end

end Response
end HighContrast
end HCPolySupport
