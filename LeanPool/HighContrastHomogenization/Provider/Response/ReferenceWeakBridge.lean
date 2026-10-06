/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormAPI
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Basic
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Existence
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.Bounds
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeColoring
public import LeanPool.HighContrastHomogenization.Support.Multiscale.Projection

/-!
# High-contrast homogenization: Provider.Response.ReferenceWeakBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The concrete weak seminorm on the reference cube

For the identity grid, the aligned cells at depth `j` are exactly the triadic
descendants of the origin cube at that depth.  This identifies each slot of
the concrete doubled-field seminorm with the finite Chapter-5 negative Besov
seminorm.  The statement keeps the normalized factor `3^{-st}` visible; the
inverse factor used by the div--curl estimate is consequently not hidden in a
constant.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem translate_originCube_injective (d : ℕ) (k : ℤ) :
    Function.Injective
      (fun w : Fin d → ℤ ↦ translateCube w (originCube d k)) := by
  intro w z hwz
  funext i
  have hi := congrArg (fun Q : TriadicCube d ↦ Q.index i) hwz
  simpa [translateCube, originCube] using hi

/-- At the identity grid, the aligned labels at depth `j` enumerate exactly
the depth-`j` descendants of the origin cube. -/
theorem image_translateCube_alignedIndex_one_eq_descendantsAtDepth
    (d : ℕ) (t : ℤ) (j : ℕ) :
    (alignedIndex (1 : Mat d) (t - (j : ℤ)) t).image
        (fun w ↦ translateCube w (originCube d (t - (j : ℤ)))) =
      descendantsAtDepth (originCube d t) j := by
  classical
  let k : ℤ := t - (j : ℤ)
  have hkt : k ≤ t := by
    dsimp [k]
    omega
  ext R
  constructor
  · intro hR
    rcases Finset.mem_image.mp hR with ⟨w, hw, rfl⟩
    have hwParent : standardCellCenter k w ∈ centeredCube d t := by
      have hw' := (mem_alignedIndex_iff Matrix.PosDef.one hkt).mp hw
      simpa [k, Recurrence.adaptedCellCenter_eq, adaptedCell, centeredCube,
        matVecMul_one] using hw'
    have hxParent : standardCellCenter k w ∈ cubeSet (originCube d t) :=
      openCubeSet_subset_cubeSet _ hwParent
    obtain ⟨S, ⟨hS, hxS⟩, _⟩ :=
      existsUnique_descendantAtDepth_mem_cubeSet j hxParent
    have hxCell : standardCellCenter k w ∈
        cubeSet (translateCube w (originCube d k)) :=
      openCubeSet_subset_cubeSet _
        (Recurrence.standardCellCenter_mem_standardCell k w)
    have hSscale : S.scale = k := by
      simpa [k] using! scale_eq_sub_of_mem_descendantsAtDepth hS
    have hscale : (translateCube w (originCube d k)).scale = S.scale := by
      change k = S.scale
      exact hSscale.symm
    have heq : translateCube w (originCube d k) = S := by
      by_contra hne
      exact (Set.disjoint_left.mp
        (disjoint_cubeSet_of_scale_eq_of_ne hscale hne)) hxCell hxS
    simpa [k, heq] using hS
  · intro hR
    have hscale : R.scale = k := by
      simpa [k] using! scale_eq_sub_of_mem_descendantsAtDepth hR
    have hrepr : R = translateCube R.index (originCube d k) := by
      rcases R with ⟨rscale, rindex⟩
      simp only at hscale
      simp [translateCube, originCube, hscale]
    have hset : openCubeSet R = standardCell d k R.index := by
      rw [hrepr]
      simp [standardCell, translateCube, originCube]
    have hxR : standardCellCenter k R.index ∈ openCubeSet R := by
      rw [hset]
      exact Recurrence.standardCellCenter_mem_standardCell k R.index
    have hxParent : standardCellCenter k R.index ∈ centeredCube d t :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR hxR
    have hw : R.index ∈ alignedIndex (1 : Mat d) k t := by
      apply (mem_alignedIndex_iff Matrix.PosDef.one hkt).mpr
      simpa [Recurrence.adaptedCellCenter_eq, adaptedCell, centeredCube,
        matVecMul_one] using hxParent
    exact Finset.mem_image.mpr ⟨R.index, hw, by simpa [k] using hrepr.symm⟩

/-- A vector average on a translated reference cell is the corresponding
triadic cube average.  Passing between the open and half-open cube changes
only a null boundary. -/
theorem cubeAverageVec_translateCube_eq_volumeAverageVec_standardCell
    (k : ℤ) (w : Fin d → ℤ) (F : Vec d → Vec d) :
    cubeAverageVec (translateCube w (originCube d k)) F =
      volumeAverageVec (standardCell d k w) F := by
  funext i
  change cubeAverage (translateCube w (originCube d k)) (fun x ↦ F x i) =
    volumeAverage (standardCell d k w) (fun x ↦ F x i)
  rw [← volumeAverage_cubeSet_eq_cubeAverage,
    ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube]
  rfl

private theorem depthAverage_fst_eq_avsum (t : ℤ) (j : ℕ)
    (F : Vec d → BlockVec d) :
    cubeBesovNegativeVectorDepthAverage (originCube d t)
        (fun x ↦ (F x).1) j =
      avsum (alignedIndex (1 : Mat d) (t - (j : ℤ)) t)
        (fun w ↦ vecNormSq
          (blockCellAverage
            (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F).1) := by
  classical
  let Z := alignedIndex (1 : Mat d) (t - (j : ℤ)) t
  let φ := fun w : Fin d → ℤ ↦
    translateCube w (originCube d (t - (j : ℤ)))
  change Book.Ch02.finsetAverageReal (descendantsAtDepth (originCube d t) j)
      (fun R ↦ vecNormSq (cubeAverageVec R (fun x ↦ (F x).1))) =
    Book.Ch02.finsetAverageReal Z
      (fun w ↦ vecNormSq
        (blockCellAverage (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F).1)
  rw [← image_translateCube_alignedIndex_one_eq_descendantsAtDepth d t j]
  apply Book.Ch02.finsetAverageReal_image Z φ
    (translate_originCube_injective d (t - (j : ℤ))).injOn
  intro w hw
  congr 1
  rw [show adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w =
      standardCell d (t - (j : ℤ)) w from by
        simp [Recurrence.adaptedCellAt_eq_image, matVecMul_one]]
  simpa only [blockCellAverage_fst] using
    cubeAverageVec_translateCube_eq_volumeAverageVec_standardCell
      (t - (j : ℤ)) w (fun x ↦ (F x).1)

private theorem depthAverage_snd_eq_avsum (t : ℤ) (j : ℕ)
    (F : Vec d → BlockVec d) :
    cubeBesovNegativeVectorDepthAverage (originCube d t)
        (fun x ↦ (F x).2) j =
      avsum (alignedIndex (1 : Mat d) (t - (j : ℤ)) t)
        (fun w ↦ vecNormSq
          (blockCellAverage
            (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F).2) := by
  classical
  let Z := alignedIndex (1 : Mat d) (t - (j : ℤ)) t
  let φ := fun w : Fin d → ℤ ↦
    translateCube w (originCube d (t - (j : ℤ)))
  change Book.Ch02.finsetAverageReal (descendantsAtDepth (originCube d t) j)
      (fun R ↦ vecNormSq (cubeAverageVec R (fun x ↦ (F x).2))) =
    Book.Ch02.finsetAverageReal Z
      (fun w ↦ vecNormSq
        (blockCellAverage (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F).2)
  rw [← image_translateCube_alignedIndex_one_eq_descendantsAtDepth d t j]
  apply Book.Ch02.finsetAverageReal_image Z φ
    (translate_originCube_injective d (t - (j : ℤ))).injOn
  intro w hw
  congr 1
  rw [show adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w =
      standardCell d (t - (j : ℤ)) w from by
        simp [Recurrence.adaptedCellAt_eq_image, matVecMul_one]]
  simpa only [blockCellAverage_snd] using
    cubeAverageVec_translateCube_eq_volumeAverageVec_standardCell
      (t - (j : ℤ)) w (fun x ↦ (F x).2)

/-- Each Chapter-5 depth average of the first slot is bounded by the matching
identity-grid doubled scale average. -/
theorem sqrt_depthAverage_fst_le_blockAvsumL2 (t : ℤ) (j : ℕ)
    (F : Vec d → BlockVec d) :
    Real.sqrt (cubeBesovNegativeVectorDepthAverage (originCube d t)
        (fun x ↦ (F x).1) j) ≤
      blockAvsumL2 (alignedIndex (1 : Mat d) (t - (j : ℤ)) t)
        (fun w ↦ blockCellAverage
          (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F) := by
  rw [depthAverage_fst_eq_avsum, blockAvsumL2_eq]
  apply Real.sqrt_le_sqrt
  apply avsum_le_avsum
  intro w hw
  exact le_add_of_nonneg_right
    (vecNormSq_nonneg
      (blockCellAverage
        (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F).2)

/-- Each Chapter-5 depth average of the second slot is bounded by the matching
identity-grid doubled scale average. -/
theorem sqrt_depthAverage_snd_le_blockAvsumL2 (t : ℤ) (j : ℕ)
    (F : Vec d → BlockVec d) :
    Real.sqrt (cubeBesovNegativeVectorDepthAverage (originCube d t)
        (fun x ↦ (F x).2) j) ≤
      blockAvsumL2 (alignedIndex (1 : Mat d) (t - (j : ℤ)) t)
        (fun w ↦ blockCellAverage
          (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F) := by
  rw [depthAverage_snd_eq_avsum, blockAvsumL2_eq]
  apply Real.sqrt_le_sqrt
  apply avsum_le_avsum
  intro w hw
  exact le_add_of_nonneg_left
    (vecNormSq_nonneg
      (blockCellAverage
        (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F).1)

private theorem partialSeminorm_slot_le {t : ℤ} {F : Vec d → BlockVec d}
    (slot : BlockVec d → Vec d)
    (hslot : ∀ j : ℕ, Real.sqrt
      (cubeBesovNegativeVectorDepthAverage (originCube d t)
        (fun x ↦ slot (F x)) j) ≤
      blockAvsumL2 (alignedIndex (1 : Mat d) (t - (j : ℤ)) t)
        (fun w ↦ blockCellAverage
          (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F))
    (s : ℝ) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) s N
        (fun x ↦ slot (F x)) ≤
      ∑ j ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex (1 : Mat d) (t - (j : ℤ)) t)
            (fun w ↦ blockCellAverage
              (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F) := by
  unfold cubeBesovNegativeVectorPartialSeminorm
  apply Finset.sum_le_sum
  intro j hj
  unfold cubeBesovNegativeVectorDepthSeminorm
  have hpow : 0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  simpa only [neg_mul] using! mul_le_mul_of_nonneg_left (hslot j) hpow

private theorem ofReal_partialSeminorm_slot_le_normalized
    {t : ℤ} {F : Vec d → BlockVec d}
    (slot : BlockVec d → Vec d)
    (hslot : ∀ j : ℕ, Real.sqrt
      (cubeBesovNegativeVectorDepthAverage (originCube d t)
        (fun x ↦ slot (F x)) j) ≤
      blockAvsumL2 (alignedIndex (1 : Mat d) (t - (j : ℤ)) t)
        (fun w ↦ blockCellAverage
          (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F))
    (s : ℝ) (N : ℕ) :
    ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
        (originCube d t) s N (fun x ↦ slot (F x))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm (1 : Mat d) t s F := by
  let b := fun j : ℕ ↦
    (3 : ℝ) ^ (-(s * (j : ℝ))) *
      blockAvsumL2 (alignedIndex (1 : Mat d) (t - (j : ℤ)) t)
        (fun w ↦ blockCellAverage
          (adaptedCellAt (1 : Mat d) (t - (j : ℤ)) w) F)
  have hb0 : ∀ j, 0 ≤ b j := fun j ↦
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (blockAvsumL2_nonneg _ _)
  have hreal := partialSeminorm_slot_le slot hslot s N
  calc
    ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
        (originCube d t) s N (fun x ↦ slot (F x))) ≤
        ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), b j) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (b j) :=
      ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hb0 j)
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (b j) :=
      ENNReal.sum_le_tsum (Finset.range (N + 1))
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm (1 : Mat d) t s F := by
      simpa [b] using
        (ofReal_rpow_mul_adaptedWeakSeminorm (1 : Mat d) t s F).symm

/-- Every finite Chapter-5 weak seminorm of the first slot is bounded by the
normalized concrete identity-grid seminorm. -/
theorem ofReal_partialSeminorm_fst_le_normalized_adaptedWeakSeminorm
    (t : ℤ) (s : ℝ) (N : ℕ) (F : Vec d → BlockVec d) :
    ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
        (originCube d t) s N (fun x ↦ (F x).1)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm (1 : Mat d) t s F :=
  ofReal_partialSeminorm_slot_le_normalized (t := t) (F := F) Prod.fst
    (fun j ↦ sqrt_depthAverage_fst_le_blockAvsumL2 t j F) s N

/-- Every finite Chapter-5 weak seminorm of the second slot is bounded by the
normalized concrete identity-grid seminorm. -/
theorem ofReal_partialSeminorm_snd_le_normalized_adaptedWeakSeminorm
    (t : ℤ) (s : ℝ) (N : ℕ) (F : Vec d → BlockVec d) :
    ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
        (originCube d t) s N (fun x ↦ (F x).2)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm (1 : Mat d) t s F :=
  ofReal_partialSeminorm_slot_le_normalized (t := t) (F := F) Prod.snd
    (fun j ↦ sqrt_depthAverage_snd_le_blockAvsumL2 t j F) s N

end

end HCPolySupport.HighContrast.Response
