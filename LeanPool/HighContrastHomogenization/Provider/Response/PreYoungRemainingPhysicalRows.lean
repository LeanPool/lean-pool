/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAdjointFluxPhysicalProjectionLimit
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAdjointGradientPhysicalProjectionLimit
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalFluxPhysicalProjectionLimit

/-!
# High-contrast homogenization: Provider.Response.PreYoungRemainingPhysicalRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Literal physical cutoff rows

The three remaining physical projection limits are rewritten as the literal
cutoff-oscillation rows in the primal and adjoint mean decompositions.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Primal flux row -/

/-- Annealed integration of the physical primal flux pairing equals the
coordinate cutoff-oscillation row. -/
theorem integral_primal_flux_physical_oscillation_eq_cutoff_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    (∫ a, primalFluxPhysicalOscillation hq s t g hg p r Pcen a ∂P) =
      avsum (alignedIndex q s t) (fun z ↦
        ∑ i, Pcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
          (adaptedPreYoungCutoff q hq t x -
            volumeAverage (adaptedCellAt q s z)
              (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec
              (diagonalWeakState hq t (a.subSkew g hg) p r x)
              (Sum.inr i)) ∂P) := by
  let Z := alignedIndex q s t
  let coord : (Fin d → ℤ) → Fin d → CoeffSpace d → ℝ := fun z i a ↦
    volumeAverage (adaptedCellAt q s z) (fun x ↦
      (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s z)
          (adaptedPreYoungCutoff q hq t)) *
        toFullBlockVec
          (diagonalWeakState hq t (a.subSkew g hg) p r x)
          (Sum.inr i))
  let parent : (Fin d → ℤ) → CoeffSpace d → ℝ := fun z a ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    cubeBesovPairing R f G
  have hread :=
    (integrable_primal_adaptedFiveTermSplit_readouts
      hq hm0 hst g hg p r hweak).2
  have hcoord : ∀ z ∈ Z, ∀ i, Integrable (coord z i) P := by
    intro z hz i
    simpa only [coord, toFullBlockVec] using hread z hz (Sum.inr i)
  have hparentEq : ∀ z ∈ Z, parent z =
      fun a ↦ ∑ i, Pcen i * coord z i a := by
    intro z hz
    funext a
    simpa only [parent, coord, toFullBlockVec] using
      primal_flux_physical_parent_pairing_eq_coordinate_sum
        hq hst hz g hg a p r Pcen
  have hparent : ∀ z ∈ Z, Integrable (parent z) P := by
    intro z hz
    rw [hparentEq z hz]
    exact integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i hi ↦
      (hcoord z hz i).const_mul (Pcen i)
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
    exact (hcoord z hz i).const_mul (Pcen i)

/-! ## Adjoint gradient row -/

/-- Annealed integration of the physical adjoint gradient pairing equals the
coordinate cutoff-oscillation row. -/
theorem integral_adjoint_gradient_physical_oscillation_eq_cutoff_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (hweak : profileAdjointWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    (∫ a, adjointGradientPhysicalOscillation hq s t g hg p r Qcen a ∂P) =
      avsum (alignedIndex q s t) (fun z ↦
        ∑ i, Qcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
          (adaptedPreYoungCutoff q hq t x -
            volumeAverage (adaptedCellAt q s z)
              (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec
              (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x)
              (Sum.inl i)) ∂P) := by
  let Z := alignedIndex q s t
  let coord : (Fin d → ℤ) → Fin d → CoeffSpace d → ℝ := fun z i a ↦
    volumeAverage (adaptedCellAt q s z) (fun x ↦
      (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s z)
          (adaptedPreYoungCutoff q hq t)) *
        toFullBlockVec
          (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x)
          (Sum.inl i))
  let parent : (Fin d → ℤ) → CoeffSpace d → ℝ := fun z a ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f G
  have hread :=
    (integrable_adjoint_adaptedFiveTermSplit_readouts
      hq hm0 hst g hg p r hweak).2
  have hcoord : ∀ z ∈ Z, ∀ i, Integrable (coord z i) P := by
    intro z hz i
    simpa only [coord, toFullBlockVec] using hread z hz (Sum.inl i)
  have hparentEq : ∀ z ∈ Z, parent z =
      fun a ↦ ∑ i, Qcen i * coord z i a := by
    intro z hz
    funext a
    simpa only [parent, coord, toFullBlockVec] using
      adjoint_gradient_physical_parent_pairing_eq_coordinate_sum
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

/-! ## Adjoint flux row -/

/-- Annealed integration of the physical adjoint flux pairing equals the
coordinate cutoff-oscillation row. -/
theorem integral_adjoint_flux_physical_oscillation_eq_cutoff_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (hweak : profileAdjointWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    (∫ a, adjointFluxPhysicalOscillation hq s t g hg p r Pcen a ∂P) =
      avsum (alignedIndex q s t) (fun z ↦
        ∑ i, Pcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
          (adaptedPreYoungCutoff q hq t x -
            volumeAverage (adaptedCellAt q s z)
              (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec
              (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x)
              (Sum.inr i)) ∂P) := by
  let Z := alignedIndex q s t
  let coord : (Fin d → ℤ) → Fin d → CoeffSpace d → ℝ := fun z i a ↦
    volumeAverage (adaptedCellAt q s z) (fun x ↦
      (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s z)
          (adaptedPreYoungCutoff q hq t)) *
        toFullBlockVec
          (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x)
          (Sum.inr i))
  let parent : (Fin d → ℤ) → CoeffSpace d → ℝ := fun z a ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    cubeBesovPairing R f G
  have hread :=
    (integrable_adjoint_adaptedFiveTermSplit_readouts
      hq hm0 hst g hg p r hweak).2
  have hcoord : ∀ z ∈ Z, ∀ i, Integrable (coord z i) P := by
    intro z hz i
    simpa only [coord, toFullBlockVec] using hread z hz (Sum.inr i)
  have hparentEq : ∀ z ∈ Z, parent z =
      fun a ↦ ∑ i, Pcen i * coord z i a := by
    intro z hz
    funext a
    simpa only [parent, coord, toFullBlockVec] using
      adjoint_flux_physical_parent_pairing_eq_coordinate_sum
        hq hst hz g hg a p r Pcen
  have hparent : ∀ z ∈ Z, Integrable (parent z) P := by
    intro z hz
    rw [hparentEq z hz]
    exact integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i hi ↦
      (hcoord z hz i).const_mul (Pcen i)
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
    exact (hcoord z hz i).const_mul (Pcen i)

end

end HCPolySupport.HighContrast.Response
