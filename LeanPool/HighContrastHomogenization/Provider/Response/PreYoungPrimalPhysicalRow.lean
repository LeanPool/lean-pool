/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalPhysicalProjectionLimit

/-!
# High-contrast homogenization: Provider.Response.PreYoungPrimalPhysicalRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The physical primal cutoff row

The physical projection limit is rewritten as the literal cutoff-oscillation
row appearing in the decomposition of the primal cutoff mean.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Annealed integration of the physical primal pairing equals the coordinate
cutoff-oscillation row on the terminal parent partition. -/
theorem integral_primal_physical_oscillation_eq_cutoff_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    (∫ a, primalPhysicalOscillation hq s t g hg p r Qcen a ∂P) =
      avsum (alignedIndex q s t) (fun z ↦
        ∑ i, Qcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
          (adaptedPreYoungCutoff q hq t x -
            volumeAverage (adaptedCellAt q s z)
              (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec
              (diagonalWeakState hq t (a.subSkew g hg) p r x)
              (Sum.inl i)) ∂P) := by
  let Z := alignedIndex q s t
  let coord : (Fin d → ℤ) → Fin d → CoeffSpace d → ℝ := fun z i a ↦
    volumeAverage (adaptedCellAt q s z) (fun x ↦
      (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s z)
          (adaptedPreYoungCutoff q hq t)) *
        toFullBlockVec
          (diagonalWeakState hq t (a.subSkew g hg) p r x)
          (Sum.inl i))
  let parent : (Fin d → ℤ) → CoeffSpace d → ℝ := fun z a ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f G
  have hread :=
    (integrable_primal_adaptedFiveTermSplit_readouts
      hq hm0 hst g hg p r hweak).2
  have hcoord : ∀ z ∈ Z, ∀ i, Integrable (coord z i) P := by
    intro z hz i
    simpa only [coord, toFullBlockVec] using hread z hz (Sum.inl i)
  have hparentEq : ∀ z ∈ Z, parent z =
      fun a ↦ ∑ i, Qcen i * coord z i a := by
    intro z hz
    funext a
    simpa only [parent, coord, toFullBlockVec] using
      primal_physical_parent_pairing_eq_coordinate_sum
        hq hst hz g hg a p r Qcen
  have hparent : ∀ z ∈ Z, Integrable (parent z) P := by
    intro z hz
    rw [hparentEq z hz]
    exact integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i hi ↦
      (hcoord z hz i).const_mul (Qcen i)
  change (∫ a, avsum Z (fun z ↦ parent z a) ∂P) = _
  rw [integral_avsum_eq_avsum_integral Z parent hparent]
  unfold avsum
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  change (∫ a, parent z a ∂P) = _
  rw [hparentEq z hz]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
  · intro i hi
    exact (hcoord z hz i).const_mul (Qcen i)

end

end HCPolySupport.HighContrast.Response
