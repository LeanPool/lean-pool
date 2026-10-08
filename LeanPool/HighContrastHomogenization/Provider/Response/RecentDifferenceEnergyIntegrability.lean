/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedFiveTermProfile
public import LeanPool.HighContrastHomogenization.Provider.Response.RecentDifferenceEnergyMeasurability

/-!
# High-contrast homogenization: Provider.Response.RecentDifferenceEnergyIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability of recent optimizer-difference energies

A fixed child energy is controlled by the sum of the nonnegative child
responses.  The exact recent-energy identity supplies the factor two after
the half-energy normalization.  Finite adapted means then make the response
sum integrable.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem integrable_responseJ_of_integrableCoarseBlock
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d))) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U (a.coeffOn U) p r) P := by
  let X : BlockVec d := (-p, r)
  have hquad := (integrable_coarseBlock_quadratic hint X).const_mul (1 / 2 : ℝ)
  have hsub := hquad.sub (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X] using! (responseJ_eq_coarseBlock U a p r).symm

private theorem integrable_responseJ_subSkew
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U ((a.subSkew g hg).coeffOn U) p r) P := by
  refine (integrable_responseJ_of_integrableCoarseBlock hint p
    (r - matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  exact (responseJ_subSkew U a g hg p r).symm

private theorem integrable_adjointResponseJ_of_integrableCoarseBlock
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d))) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U (a.transpose.coeffOn U) p r) P := by
  let X : BlockVec d := (-p, r)
  let D := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  have hquad : Integrable (fun a ↦ blockVecDot X
      (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)) P := by
    have hbase := integrable_coarseBlock_quadratic hint D
    refine hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change blockVecDot D (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) D) =
      blockVecDot X (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
    rw [coarseBlock_transpose a U, blockQuadratic_adjointSign_congr]
  have hsub := (hquad.const_mul (1 / 2 : ℝ)).sub
    (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X] using! (responseJ_eq_coarseBlock U a.transpose p r).symm

private theorem integrable_responseJ_adjointSubSkew
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U
      ((a.subSkew g hg).transpose.coeffOn U) p r) P := by
  refine (integrable_adjointResponseJ_of_integrableCoarseBlock hint p
    (r + matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  change responseJ U (a.transpose.coeffOn U) p (r + matVecMul g p) =
    responseJ U ((a.subSkew g hg).transpose.coeffOn U) p r
  rw [CoeffSpace.transpose_subSkew]
  have h := responseJ_subSkew U a.transpose (-g) (isSkewMat_neg hg) p r
  have hload : r - matVecMul (-g) p = r + matVecMul g p := by
    rw [neg_matVecMul, sub_neg_eq_add]
  rw [hload] at h
  exact h.symm

private theorem recent_half_energy_le_two_mul_sum_responseJ
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (a : CoeffSpace d) (p r : Vec d) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q s t) :
    (1 / 2 : ℝ) * average (adaptedDomainAt hq s w) (fun x ↦
        blockVecDot
          (diagonalWeakChildState hq s w a p r x -
            diagonalWeakState hq t a p r x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakChildState hq s w a p r x -
              diagonalWeakState hq t a p r x))) ≤
      2 * ∑ z ∈ alignedIndex q s t,
        responseJ (adaptedDomainAt hq s z)
          (a.coeffOn (adaptedDomainAt hq s z)) p r := by
  let Z := alignedIndex q s t
  let G := fun z : Fin d → ℤ ↦ average (adaptedDomainAt hq s z) (fun x ↦
    blockVecDot
      (diagonalWeakChildState hq s z a p r x -
        diagonalWeakState hq t a p r x)
      (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
        (diagonalWeakChildState hq s z a p r x -
          diagonalWeakState hq t a p r x)))
  let J := fun z : Fin d → ℤ ↦ responseJ (adaptedDomainAt hq s z)
    (a.coeffOn (adaptedDomainAt hq s z)) p r
  let Jt := responseJ (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t)) p r
  have hZ : Z.Nonempty := alignedIndex_nonempty hq hst
  have hcard : ((Z.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hZ).ne'
  have hG0 : ∀ z ∈ Z, 0 ≤ G z := by
    intro z hz
    exact diagonalWeak_recent_difference_energy_nonneg hq hst hz a p r
  have hterm0 : 0 ≤ Jt := responseJ_nonneg _ _ _ _
  have hwSum : G w ≤ ∑ z ∈ Z, G z :=
    Finset.single_le_sum (fun z hz ↦ hG0 z hz) hw
  have hcardG : (Z.card : ℝ) * avsum Z G = ∑ z ∈ Z, G z := by
    rw [avsum_eq]
    field_simp
  have hcardJ : (Z.card : ℝ) * avsum Z J = ∑ z ∈ Z, J z := by
    rw [avsum_eq]
    field_simp
  have hav : avsum Z G = 4 * (avsum Z J - Jt) := by
    exact diagonalWeak_recent_energy_eq_response_deficit hq hst a p r
  calc
    (1 / 2 : ℝ) * G w ≤ (1 / 2 : ℝ) * ((Z.card : ℝ) * avsum Z G) :=
      mul_le_mul_of_nonneg_left (hwSum.trans_eq hcardG.symm) (by norm_num)
    _ = 2 * (Z.card : ℝ) * (avsum Z J - Jt) := by rw [hav]; ring
    _ ≤ 2 * (Z.card : ℝ) * avsum Z J := by
      exact mul_le_mul_of_nonneg_left (sub_le_self _ hterm0)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = 2 * ∑ z ∈ Z, J z := by rw [← hcardJ]; ring

/-- A primal child half-energy is at most twice the sum of the nonnegative
child responses. -/
theorem profilePrimalRecentEnergy_le_two_mul_sum_responseJ
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q s t) (a : CoeffSpace d) :
    (1 / 2 : ℝ) * average (adaptedDomainAt hq s w) (fun x ↦
        blockVecDot
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
            diagonalWeakState hq t (a.subSkew g hg) p r x)
          (blockMatVecMul (blockMatrixOfCoeff
              ((⇑(a.subSkew g hg).1 : CoeffField d) x))
            (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
              diagonalWeakState hq t (a.subSkew g hg) p r x))) ≤
      2 * ∑ z ∈ alignedIndex q s t,
        responseJ (adaptedDomainAt hq s z)
          ((a.subSkew g hg).coeffOn (adaptedDomainAt hq s z)) p r :=
  recent_half_energy_le_two_mul_sum_responseJ hq hst (a.subSkew g hg) p r hw

/-- The literal primal energy is measurable, and finite adapted means imply
its integrability on every aligned child. -/
theorem profilePrimalRecentEnergy_integrable
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let energy := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦ (1 / 2 : ℝ) *
      average (adaptedDomainAt hq s w) (fun x ↦
        blockVecDot
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
            diagonalWeakState hq t (a.subSkew g hg) p r x)
          (blockMatVecMul (blockMatrixOfCoeff
              ((⇑(a.subSkew g hg).1 : CoeffField d) x))
            (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
              diagonalWeakState hq t (a.subSkew g hg) p r x)))
    ∀ w ∈ alignedIndex q s t, Integrable (energy w) P := by
  dsimp only
  intro w hw
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let J := fun z : Fin d → ℤ ↦ fun a : CoeffSpace d ↦
    responseJ (adaptedDomainAt hq s z)
      ((a.subSkew g hg).coeffOn (adaptedDomainAt hq s z)) p r
  have hJint : ∀ z ∈ alignedIndex q s t, Integrable (J z) P := by
    intro z _
    exact integrable_responseJ_subSkew
      (P := P) (U := adaptedDomainAt hq s z)
      (Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hstat hgrid hls hints z)
      g hg p r
  have hmajor : Integrable (fun a ↦
      2 * ∑ z ∈ alignedIndex q s t, J z a) P :=
    (integrable_finsetSum (alignedIndex q s t) hJint).const_mul 2
  refine hmajor.mono'
    (Selection.aestronglyMeasurable_recentDifferenceEnergy_alignedIndex
      hq hst P g hg p r hw)
    (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
    (diagonalWeak_recent_difference_energy_nonneg hq hst hw
      (a.subSkew g hg) p r))]
  exact profilePrimalRecentEnergy_le_two_mul_sum_responseJ hq hst g hg p r hw a

/-- An adjoint child half-energy obeys the same response-sum domination, with
the transpose retained on the coefficient carrier. -/
theorem profileAdjointRecentEnergy_le_two_mul_sum_responseJ
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q s t) (a : CoeffSpace d) :
    (1 / 2 : ℝ) * average (adaptedDomainAt hq s w) (fun x ↦
        blockVecDot
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
            diagonalWeakState hq t (a.subSkew g hg).transpose p r x)
          (blockMatVecMul (blockMatrixOfCoeff
              ((⇑(a.subSkew g hg).transpose.1 : CoeffField d) x))
            (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
              diagonalWeakState hq t (a.subSkew g hg).transpose p r x))) ≤
      2 * ∑ z ∈ alignedIndex q s t,
        responseJ (adaptedDomainAt hq s z)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomainAt hq s z)) p r :=
  recent_half_energy_le_two_mul_sum_responseJ
    hq hst (a.subSkew g hg).transpose p r hw

/-- The independently transformed adjoint responses dominate every adjoint
child half-energy by an integrable finite sum. -/
theorem profileAdjointRecentEnergy_integrable
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let energy := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦ (1 / 2 : ℝ) *
      average (adaptedDomainAt hq s w) (fun x ↦
        blockVecDot
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
            diagonalWeakState hq t (a.subSkew g hg).transpose p r x)
          (blockMatVecMul (blockMatrixOfCoeff
              ((⇑(a.subSkew g hg).transpose.1 : CoeffField d) x))
            (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
              diagonalWeakState hq t (a.subSkew g hg).transpose p r x)))
    ∀ w ∈ alignedIndex q s t, Integrable (energy w) P := by
  dsimp only
  intro w hw
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let J := fun z : Fin d → ℤ ↦ fun a : CoeffSpace d ↦
    responseJ (adaptedDomainAt hq s z)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomainAt hq s z)) p r
  have hJint : ∀ z ∈ alignedIndex q s t, Integrable (J z) P := by
    intro z _
    exact integrable_responseJ_adjointSubSkew
      (P := P) (U := adaptedDomainAt hq s z)
      (Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hstat hgrid hls hints z)
      g hg p r
  have hmajor : Integrable (fun a ↦
      2 * ∑ z ∈ alignedIndex q s t, J z a) P :=
    (integrable_finsetSum (alignedIndex q s t) hJint).const_mul 2
  refine hmajor.mono'
    (Selection.aestronglyMeasurable_adjointRecentDifferenceEnergy_alignedIndex
      hq hst P g hg p r hw)
    (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
    (diagonalWeak_recent_difference_energy_nonneg hq hst hw
      (a.subSkew g hg).transpose p r))]
  exact profileAdjointRecentEnergy_le_two_mul_sum_responseJ hq hst g hg p r hw a

end

end HCPolySupport.HighContrast.Response
