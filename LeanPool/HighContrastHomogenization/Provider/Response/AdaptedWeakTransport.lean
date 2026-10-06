/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormAPI
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormCellAverage
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# High-contrast homogenization: Provider.Response.AdaptedWeakTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The concrete weak seminorm under an adapted-cell normalization

An invertible grid identifies every aligned adapted subdivision with the
standard subdivision of the reference cube.  Normalized cell averages have no
Jacobian factor under this identification.  The two slots of a doubled field
transform contravariantly, and their Euclidean square is controlled by the
larger of the two Frobenius norms.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Vector-valued square integrability is preserved by an invertible affine
pullback. -/
theorem memVectorL2_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) :
    MemVectorL2 (matImage L⁻¹ U) (fun y ↦ F (matVecMul L y)) := by
  let T : Vec d → Vec d := matVecMul L
  have hmap := map_restrict_volume_affinePullback hL hU
  have hFmap : MemLp F 2
      (Measure.map T (volume.restrict (matImage L⁻¹ U))) := by
    rw [hmap]
    exact hF.smul_measure ENNReal.ofReal_ne_top
  exact hFmap.comp_of_map (continuous_matVecMul L).aemeasurable

/-- The labels of an aligned subdivision do not depend on its invertible
positive-definite grid. -/
theorem alignedIndex_one_eq {q : Mat d} (hq : q.PosDef) {j t : ℤ}
    (hjt : j ≤ t) :
    alignedIndex (1 : Mat d) j t = alignedIndex q j t := by
  classical
  ext w
  constructor
  · intro hw
    have hw' := (mem_alignedIndex_iff Matrix.PosDef.one hjt).mp hw
    have hi := (Recurrence.adaptedCellCenter_mem_adaptedCell_iff
      Matrix.PosDef.one hjt w).mp hw'
    exact (mem_alignedIndex_iff hq hjt).mpr
      ((Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq hjt w).mpr hi)
  · intro hw
    have hw' := (mem_alignedIndex_iff hq hjt).mp hw
    have hi := (Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq hjt w).mp hw'
    exact (mem_alignedIndex_iff Matrix.PosDef.one hjt).mpr
      ((Recurrence.adaptedCellCenter_mem_adaptedCell_iff
        Matrix.PosDef.one hjt w).mpr hi)

/-- The inverse grid sends an aligned adapted cell to the corresponding cell
of the identity grid. -/
theorem matImage_inv_adaptedCellAt_eq {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ) :
    matImage q⁻¹ (adaptedCellAt q k w) =
      adaptedCellAt (1 : Mat d) k w := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  calc
    matImage q⁻¹ (adaptedCellAt q k w) =
        matImage q⁻¹ (matImage q (standardCell d k w)) := by
      rw [Recurrence.adaptedCellAt_eq_image]
      rfl
    _ = matImage (q⁻¹ * q) (standardCell d k w) :=
      matImage_matImage q⁻¹ q _
    _ = matImage 1 (standardCell d k w) := by
      rw [Matrix.nonsing_inv_mul q hdet]
    _ = matVecMul 1 '' standardCell d k w := rfl
    _ = adaptedCellAt (1 : Mat d) k w :=
      (Recurrence.adaptedCellAt_eq_image (1 : Mat d) k w).symm

/-- The grid sends an identity-grid aligned cell to the corresponding adapted
cell. -/
theorem matImage_adaptedCellAt_one_eq {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ) :
    matImage q (adaptedCellAt (1 : Mat d) k w) =
      adaptedCellAt q k w := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  rw [← matImage_inv_adaptedCellAt_eq hq k w]
  exact matImage_matImage_inv hdet _

/-- A doubled cell average transforms slotwise under the dual affine actions.
The square-integrability hypotheses are inherited from response solutions in
the intended application. -/
theorem blockCellAverage_affinePullback {q : Mat d} (hq : q.PosDef)
    (A B : Mat d) (k : ℤ) (w : Fin d → ℤ)
    (F : Vec d → BlockVec d)
    (hF₁ : MemVectorL2 (adaptedCellAt q k w) (fun x ↦ (F x).1))
    (hF₂ : MemVectorL2 (adaptedCellAt q k w) (fun x ↦ (F x).2)) :
    blockCellAverage (adaptedCellAt (1 : Mat d) k w)
        (fun y ↦ ((matVecMul A (F (matVecMul q y)).1,
          matVecMul B (F (matVecMul q y)).2) : BlockVec d)) =
      ((matVecMul A (blockCellAverage (adaptedCellAt q k w) F).1,
        matVecMul B (blockCellAverage (adaptedCellAt q k w) F).2) : BlockVec d) := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hU : MeasurableSet (adaptedCellAt q k w) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w).isOpen.measurableSet
  have hV : MeasurableSet (adaptedCellAt (1 : Mat d) k w) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt Matrix.PosDef.one k w).isOpen.measurableSet
  have hpull₁ := memVectorL2_affinePullback hdet hU hF₁
  have hpull₂ := memVectorL2_affinePullback hdet hU hF₂
  rw [matImage_inv_adaptedCellAt_eq hq k w] at hpull₁ hpull₂
  have havg₁ :
      volumeAverageVec (adaptedCellAt q k w) (fun x ↦ (F x).1) =
        volumeAverageVec (adaptedCellAt (1 : Mat d) k w)
          (fun y ↦ (F (matVecMul q y)).1) := by
    funext i
    simpa [volumeAverageVec, matImage_adaptedCellAt_one_eq hq k w] using
      (volumeAverage_matImage hdet hV (fun x ↦ (F x).1 i))
  have havg₂ :
      volumeAverageVec (adaptedCellAt q k w) (fun x ↦ (F x).2) =
        volumeAverageVec (adaptedCellAt (1 : Mat d) k w)
          (fun y ↦ (F (matVecMul q y)).2) := by
    funext i
    simpa [volumeAverageVec, matImage_adaptedCellAt_one_eq hq k w] using
      (volumeAverage_matImage hdet hV (fun x ↦ (F x).2 i))
  refine Prod.ext ?_ ?_
  · simp only [blockCellAverage_fst]
    change Book.Ch02.averageVec
        (adaptedDomainAt Matrix.PosDef.one k w)
          (fun y ↦ matVecMul A (F (matVecMul q y)).1) =
      matVecMul A (volumeAverageVec (adaptedCellAt q k w) fun x ↦ (F x).1)
    rw [averageVec_matVecMul (U := adaptedDomainAt Matrix.PosDef.one k w) A hpull₁]
    change matVecMul A
        (volumeAverageVec (adaptedCellAt (1 : Mat d) k w)
          fun y ↦ (F (matVecMul q y)).1) = _
    rw [← havg₁]
  · simp only [blockCellAverage_snd]
    change Book.Ch02.averageVec
        (adaptedDomainAt Matrix.PosDef.one k w)
          (fun y ↦ matVecMul B (F (matVecMul q y)).2) =
      matVecMul B (volumeAverageVec (adaptedCellAt q k w) fun x ↦ (F x).2)
    rw [averageVec_matVecMul (U := adaptedDomainAt Matrix.PosDef.one k w) B hpull₂]
    change matVecMul B
        (volumeAverageVec (adaptedCellAt (1 : Mat d) k w)
          fun y ↦ (F (matVecMul q y)).2) = _
    rw [← havg₂]

/-- The squared length of the two-slot affine image is controlled by the
larger Frobenius square of the two matrices. -/
theorem blockVecDot_affineSlots_le (A B : Mat d) (v : BlockVec d) :
    blockVecDot ((matVecMul A v.1, matVecMul B v.2) : BlockVec d)
        ((matVecMul A v.1, matVecMul B v.2) : BlockVec d) ≤
      max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B) *
        blockVecDot v v := by
  have hA := vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq A v.1
  have hB := vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq B v.2
  have hAmax : matrixFrobeniusNormSq A * vecNormSq v.1 ≤
      max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B) * vecNormSq v.1 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (vecNormSq_nonneg _)
  have hBmax : matrixFrobeniusNormSq B * vecNormSq v.2 ≤
      max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B) * vecNormSq v.2 :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (vecNormSq_nonneg _)
  change vecNormSq (matVecMul A v.1) + vecNormSq (matVecMul B v.2) ≤
    max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B) *
      (vecNormSq v.1 + vecNormSq v.2)
  calc
    vecNormSq (matVecMul A v.1) + vecNormSq (matVecMul B v.2) ≤
        matrixFrobeniusNormSq A * vecNormSq v.1 +
          matrixFrobeniusNormSq B * vecNormSq v.2 := add_le_add hA hB
    _ ≤ max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B) * vecNormSq v.1 +
        max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B) * vecNormSq v.2 :=
      add_le_add hAmax hBmax
    _ = max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B) *
        (vecNormSq v.1 + vecNormSq v.2) := by ring

/-- The normalized finite-family `L²` norm obeys the same two-slot matrix
bound. -/
theorem blockAvsumL2_affineSlots_le {I : Type*} (Z : Finset I)
    (A B : Mat d) (u : I → BlockVec d) :
    blockAvsumL2 Z
        (fun z ↦ ((matVecMul A (u z).1, matVecMul B (u z).2) : BlockVec d)) ≤
      Real.sqrt (max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B)) *
        blockAvsumL2 Z u := by
  let C : ℝ := max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B)
  have hC : 0 ≤ C := le_trans (matrixFrobeniusNormSq_nonneg A) (le_max_left _ _)
  have havg :
      avsum Z (fun z ↦ blockVecDot
          ((matVecMul A (u z).1, matVecMul B (u z).2) : BlockVec d)
          ((matVecMul A (u z).1, matVecMul B (u z).2) : BlockVec d)) ≤
        avsum Z (fun z ↦ C * blockVecDot (u z) (u z)) :=
    avsum_le_avsum fun z _ ↦ blockVecDot_affineSlots_le A B (u z)
  rw [blockAvsumL2_eq, blockAvsumL2_eq]
  calc
    Real.sqrt (avsum Z (fun z ↦ blockVecDot
        ((matVecMul A (u z).1, matVecMul B (u z).2) : BlockVec d)
        ((matVecMul A (u z).1, matVecMul B (u z).2) : BlockVec d))) ≤
      Real.sqrt (avsum Z (fun z ↦ C * blockVecDot (u z) (u z))) :=
        Real.sqrt_le_sqrt havg
    _ = Real.sqrt (C * avsum Z (fun z ↦ blockVecDot (u z) (u z))) := by
      rw [avsum_const_mul]
    _ = Real.sqrt C * Real.sqrt (avsum Z (fun z ↦ blockVecDot (u z) (u z))) := by
      rw [Real.sqrt_mul hC]

/-- Each scale of the reference-cube seminorm is bounded by the corresponding
adapted-cell scale and the explicit two-slot distortion. -/
theorem adaptedWeakScaleTerm_affinePullback_le {q : Mat d} (hq : q.PosDef)
    (A B : Mat d) (t : ℤ) (s : ℝ) (F : Vec d → BlockVec d)
    (hF₁ : MemVectorL2 (adaptedCell q t) (fun x ↦ (F x).1))
    (hF₂ : MemVectorL2 (adaptedCell q t) (fun x ↦ (F x).2))
    (j : ℕ) :
    adaptedWeakScaleTerm (1 : Mat d) t s
        (fun y ↦ ((matVecMul A (F (matVecMul q y)).1,
          matVecMul B (F (matVecMul q y)).2) : BlockVec d)) j ≤
      Real.sqrt (max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B)) *
        adaptedWeakScaleTerm q t s F j := by
  let k : ℤ := t - (j : ℤ)
  have hkt : k ≤ t := by dsimp [k]; omega
  rw [adaptedWeakScaleTerm_eq, adaptedWeakScaleTerm_eq,
    alignedIndex_one_eq hq hkt]
  have hinner := blockAvsumL2_affineSlots_le
    (alignedIndex q k t) A B
      (fun z ↦ blockCellAverage (adaptedCellAt q k z) F)
  have hpow : 0 ≤ (3 : ℝ) ^ (s * ((t : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  -- Only labels in the aligned family occur in the normalized sum.
  have havgOn : ∀ z ∈ alignedIndex q k t,
      blockCellAverage (adaptedCellAt (1 : Mat d) k z)
          (fun y ↦ ((matVecMul A (F (matVecMul q y)).1,
            matVecMul B (F (matVecMul q y)).2) : BlockVec d)) =
        ((matVecMul A (blockCellAverage (adaptedCellAt q k z) F).1,
          matVecMul B (blockCellAverage (adaptedCellAt q k z) F).2) : BlockVec d) := by
    intro z hz
    have hsub := adaptedCellAt_subset_of_mem_alignedIndex hq hkt hz
    exact blockCellAverage_affinePullback hq A B k z F
      (memVectorL2_mono hsub hF₁) (memVectorL2_mono hsub hF₂)
  have heq : blockAvsumL2 (alignedIndex q k t)
      (fun z ↦ blockCellAverage (adaptedCellAt (1 : Mat d) k z)
        (fun y ↦ ((matVecMul A (F (matVecMul q y)).1,
          matVecMul B (F (matVecMul q y)).2) : BlockVec d))) =
      blockAvsumL2 (alignedIndex q k t)
        (fun z ↦ ((matVecMul A (blockCellAverage (adaptedCellAt q k z) F).1,
          matVecMul B (blockCellAverage (adaptedCellAt q k z) F).2) : BlockVec d)) := by
    unfold blockAvsumL2 avsum
    congr 2
    apply Finset.sum_congr rfl
    intro z hz
    exact congrArg (fun v : BlockVec d ↦ blockVecDot v v) (havgOn z hz)
  rw [heq]
  calc
    (3 : ℝ) ^ (s * ((t : ℝ) - (j : ℝ))) *
        blockAvsumL2 (alignedIndex q k t)
          (fun z ↦ ((matVecMul A (blockCellAverage (adaptedCellAt q k z) F).1,
            matVecMul B (blockCellAverage (adaptedCellAt q k z) F).2) : BlockVec d)) ≤
      (3 : ℝ) ^ (s * ((t : ℝ) - (j : ℝ))) *
        (Real.sqrt (max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B)) *
          blockAvsumL2 (alignedIndex q k t)
            (fun z ↦ blockCellAverage (adaptedCellAt q k z) F)) :=
      mul_le_mul_of_nonneg_left hinner hpow
    _ = Real.sqrt (max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B)) *
        ((3 : ℝ) ^ (s * ((t : ℝ) - (j : ℝ))) *
          blockAvsumL2 (alignedIndex q k t)
            (fun z ↦ blockCellAverage (adaptedCellAt q k z) F)) := by ring

/-- The reference-cube concrete weak seminorm is controlled by the adapted
seminorm with the explicit two-slot Frobenius distortion. -/
theorem adaptedWeakSeminorm_affinePullback_le {q : Mat d} (hq : q.PosDef)
    (A B : Mat d) (t : ℤ) (s : ℝ) (F : Vec d → BlockVec d)
    (hF₁ : MemVectorL2 (adaptedCell q t) (fun x ↦ (F x).1))
    (hF₂ : MemVectorL2 (adaptedCell q t) (fun x ↦ (F x).2)) :
    adaptedWeakSeminorm (1 : Mat d) t s
        (fun y ↦ ((matVecMul A (F (matVecMul q y)).1,
          matVecMul B (F (matVecMul q y)).2) : BlockVec d)) ≤
      ENNReal.ofReal
          (Real.sqrt (max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B))) *
        adaptedWeakSeminorm q t s F := by
  have hC : 0 ≤ Real.sqrt
      (max (matrixFrobeniusNormSq A) (matrixFrobeniusNormSq B)) :=
    Real.sqrt_nonneg _
  rw [adaptedWeakSeminorm_eq, adaptedWeakSeminorm_eq,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  rw [← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal
    (adaptedWeakScaleTerm_affinePullback_le hq A B t s F hF₁ hF₂ j)

end

end HCPolySupport.HighContrast.Response
