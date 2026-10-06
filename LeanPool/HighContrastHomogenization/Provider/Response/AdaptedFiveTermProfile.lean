/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedFiveTermSplit
public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedDefectIdentification
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentBound

/-!
# High-contrast homogenization: Provider.Response.AdaptedFiveTermProfile

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical response defects for the adapted cutoff rows

The energy defect in a cutoff row is one half of the doubled energy of the
child optimizer minus the parent optimizer.  Its annealed normalized average
is twice the corresponding response defect.  Aligned-cell stationarity
identifies the child expectations directly on the physical domains.
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

private theorem integrable_responseJ_subSkew
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U ((a.subSkew g hg).coeffOn U) p r) P := by
  refine (integrable_responseJ_of_integrableCoarseBlock hint p
    (r - matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  exact (responseJ_subSkew U a g hg p r).symm

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

private theorem responseJ_adjointSubSkew (U : Domain d) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    responseJ U ((a.subSkew g hg).transpose.coeffOn U) p r =
      responseJ U (a.transpose.coeffOn U) p (r + matVecMul g p) := by
  rw [CoeffSpace.transpose_subSkew]
  have h := responseJ_subSkew U a.transpose (-g) (isSkewMat_neg hg) p r
  have hload : r - matVecMul (-g) p = r + matVecMul g p := by
    rw [neg_matVecMul, sub_neg_eq_add]
  rwa [hload] at h

private theorem integral_avsum_eq_avsum_integral {P : Measure (CoeffSpace d)}
    {iota : Type*} (Z : Finset iota) (F : iota → CoeffSpace d → ℝ)
    (hF : ∀ z ∈ Z, Integrable (F z) P) :
    (∫ a, avsum Z (fun z ↦ F z a) ∂P) = avsum Z (fun z ↦ ∫ a, F z a ∂P) := by
  unfold avsum
  rw [integral_const_mul, integral_finsetSum Z hF]

/-! ## The primal row energy -/

/-- The actual primal child--parent half doubled-energy is nonnegative on each
aligned cell, and its normalized annealed average is twice the physical primal
response defect. -/
theorem profilePrimalRecentEnergyDefect [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s) (hintt : HasFiniteAdaptedMean P q t)
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
    let defect := fun (w : Fin d → ℤ) ↦ ∫ a, energy w a ∂P
    (∀ w ∈ alignedIndex q s t, Integrable (energy w) P) →
      (∀ w ∈ alignedIndex q s t, 0 ≤ defect w) ∧
        avsum (alignedIndex q s t) defect =
          2 * profilePrimalResponseDefect P hq g hg s t p r := by
  dsimp only
  intro henergyInt
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let energy := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦ (1 / 2 : ℝ) *
    average (adaptedDomainAt hq s w) (fun x ↦
      blockVecDot
        (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
          diagonalWeakState hq t (a.subSkew g hg) p r x)
        (blockMatVecMul (blockMatrixOfCoeff
            ((⇑(a.subSkew g hg).1 : CoeffField d) x))
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
            diagonalWeakState hq t (a.subSkew g hg) p r x)))
  let Jcell := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦
    responseJ (adaptedDomainAt hq s w)
    ((a.subSkew g hg).coeffOn (adaptedDomainAt hq s w)) p r
  let Jscale := fun k (a : CoeffSpace d) ↦ responseJ (adaptedDomain hq k)
    ((a.subSkew g hg).coeffOn (adaptedDomain hq k)) p r
  have hs : Integrable (Jscale s) P :=
    integrable_responseJ_subSkew (U := adaptedDomain hq s) hints g hg p r
  have ht : Integrable (Jscale t) P :=
    integrable_responseJ_subSkew (U := adaptedDomain hq t) hintt g hg p r
  have hJcellInt : ∀ w ∈ Z, Integrable (Jcell w) P := by
    intro w _
    exact integrable_responseJ_subSkew
      (U := adaptedDomainAt hq s w)
      (Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hstat hgrid hls hints w)
      g hg p r
  have hJcell : ∀ w ∈ Z, (∫ a, Jcell w a ∂P) = ∫ a, Jscale s a ∂P := by
    intro w _
    have hintCell :=
      Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hstat hgrid hls hints w
    have hmean := Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean
      hstat hgrid hls (fun alpha beta ↦ (hints alpha beta).aestronglyMeasurable) w
    calc
      (∫ a, Jcell w a ∂P) = ∫ a, responseJ (adaptedDomainAt hq s w)
          (a.coeffOn (adaptedDomainAt hq s w)) p (r - matVecMul g p) ∂P :=
        integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦
          responseJ_subSkew (adaptedDomainAt hq s w) a g hg p r)
      _ = (1 / 2 : ℝ) * blockVecDot ((-p, r - matVecMul g p) : BlockVec d)
          (blockMatVecMul (annealedBlock P (adaptedCellAt q s w))
            ((-p, r - matVecMul g p) : BlockVec d)) -
          vecDot p (r - matVecMul g p) :=
        annealed_responseJ_eq (adaptedDomainAt hq s w) hintCell p _
      _ = (1 / 2 : ℝ) * blockVecDot ((-p, r - matVecMul g p) : BlockVec d)
          (blockMatVecMul (adaptedMean P q s)
            ((-p, r - matVecMul g p) : BlockVec d)) -
          vecDot p (r - matVecMul g p) := by rw [hmean]
      _ = ∫ a, responseJ (adaptedDomain hq s)
          (a.coeffOn (adaptedDomain hq s)) p (r - matVecMul g p) ∂P := by
        rw [annealed_responseJ_eq (adaptedDomain hq s) hints]
        rfl
      _ = ∫ a, Jscale s a ∂P :=
        integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦
          (responseJ_subSkew (adaptedDomain hq s) a g hg p r).symm)
  have hpoint : ∀ a, avsum Z (fun w ↦ energy w a) =
      2 * (avsum Z (fun w ↦ Jcell w a) - Jscale t a) := by
    intro a
    dsimp only [energy, Jcell, Jscale]
    rw [avsum_const_mul,
      diagonalWeak_recent_energy_eq_response_deficit
        hq hst (a.subSkew g hg) p r]
    ring
  have hJavgInt : Integrable (fun a ↦ avsum Z (fun w ↦ Jcell w a)) P := by
    unfold avsum
    exact (integrable_finsetSum Z hJcellInt).const_mul _
  constructor
  · intro w hw
    exact integral_nonneg_of_ae (_root_.Filter.Eventually.of_forall fun a ↦
      mul_nonneg (by norm_num) (diagonalWeak_recent_difference_energy_nonneg
        hq hst hw (a.subSkew g hg) p r))
  · calc
      avsum Z (fun w ↦ ∫ a, energy w a ∂P) =
          ∫ a, avsum Z (fun w ↦ energy w a) ∂P :=
        (integral_avsum_eq_avsum_integral Z energy henergyInt).symm
      _ = ∫ a, 2 * (avsum Z (fun w ↦ Jcell w a) - Jscale t a) ∂P :=
        integral_congr_ae (_root_.Filter.Eventually.of_forall hpoint)
      _ = 2 * ((∫ a, avsum Z (fun w ↦ Jcell w a) ∂P) -
          ∫ a, Jscale t a ∂P) := by
        rw [integral_const_mul, integral_sub hJavgInt ht]
      _ = 2 * (avsum Z (fun w ↦ ∫ a, Jcell w a ∂P) -
          ∫ a, Jscale t a ∂P) := by
        rw [integral_avsum_eq_avsum_integral Z Jcell hJcellInt]
      _ = 2 * ((∫ a, Jscale s a ∂P) - ∫ a, Jscale t a ∂P) := by
        rw [avsum_eq_of_forall_eq (alignedIndex_nonempty hq hst) hJcell]
      _ = 2 * profilePrimalResponseDefect P hq g hg s t p r := by
        rw [profilePrimalResponseDefect_eq_sub_integral P hq g hg s t p r hs ht]

/-! ## The adjoint row energy -/

/-- The coefficient-transpose row has the independently transported physical
half doubled-energy and the adjoint response defect. -/
theorem profileAdjointRecentEnergyDefect [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s) (hintt : HasFiniteAdaptedMean P q t)
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
    let defect := fun (w : Fin d → ℤ) ↦ ∫ a, energy w a ∂P
    (∀ w ∈ alignedIndex q s t, Integrable (energy w) P) →
      (∀ w ∈ alignedIndex q s t, 0 ≤ defect w) ∧
        avsum (alignedIndex q s t) defect =
          2 * profileAdjointResponseDefect P hq g hg s t p r := by
  dsimp only
  intro henergyInt
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let energy := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦ (1 / 2 : ℝ) *
    average (adaptedDomainAt hq s w) (fun x ↦
      blockVecDot
        (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
          diagonalWeakState hq t (a.subSkew g hg).transpose p r x)
        (blockMatVecMul (blockMatrixOfCoeff
            ((⇑(a.subSkew g hg).transpose.1 : CoeffField d) x))
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
            diagonalWeakState hq t (a.subSkew g hg).transpose p r x)))
  let Jcell := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦
    responseJ (adaptedDomainAt hq s w)
    ((a.subSkew g hg).transpose.coeffOn (adaptedDomainAt hq s w)) p r
  let Jscale := fun k (a : CoeffSpace d) ↦ responseJ (adaptedDomain hq k)
    ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq k)) p r
  have hs : Integrable (Jscale s) P :=
    integrable_responseJ_adjointSubSkew (U := adaptedDomain hq s) hints g hg p r
  have ht : Integrable (Jscale t) P :=
    integrable_responseJ_adjointSubSkew (U := adaptedDomain hq t) hintt g hg p r
  have hJcellInt : ∀ w ∈ Z, Integrable (Jcell w) P := by
    intro w _
    exact integrable_responseJ_adjointSubSkew
      (U := adaptedDomainAt hq s w)
      (Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hstat hgrid hls hints w)
      g hg p r
  have hJcell : ∀ w ∈ Z, (∫ a, Jcell w a ∂P) = ∫ a, Jscale s a ∂P := by
    intro w _
    have hintCell :=
      Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hstat hgrid hls hints w
    have hmean := Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean
      hstat hgrid hls (fun alpha beta ↦ (hints alpha beta).aestronglyMeasurable) w
    calc
      (∫ a, Jcell w a ∂P) = ∫ a, responseJ (adaptedDomainAt hq s w)
          (a.transpose.coeffOn (adaptedDomainAt hq s w))
            p (r + matVecMul g p) ∂P :=
        integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦
          responseJ_adjointSubSkew (adaptedDomainAt hq s w) a g hg p r)
      _ = (1 / 2 : ℝ) * blockVecDot ((-p, r + matVecMul g p) : BlockVec d)
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (annealedBlock P (adaptedCellAt q s w))
                (blockDiag 1 (-1))))
            ((-p, r + matVecMul g p) : BlockVec d)) -
          vecDot p (r + matVecMul g p) :=
        annealed_adjoint_responseJ_eq (adaptedDomainAt hq s w) hintCell p _
      _ = (1 / 2 : ℝ) * blockVecDot ((-p, r + matVecMul g p) : BlockVec d)
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (adaptedMean P q s) (blockDiag 1 (-1))))
            ((-p, r + matVecMul g p) : BlockVec d)) -
          vecDot p (r + matVecMul g p) := by rw [hmean]
      _ = ∫ a, responseJ (adaptedDomain hq s)
          (a.transpose.coeffOn (adaptedDomain hq s))
            p (r + matVecMul g p) ∂P := by
        rw [annealed_adjoint_responseJ_eq (adaptedDomain hq s) hints]
        rfl
      _ = ∫ a, Jscale s a ∂P :=
        integral_congr_ae (_root_.Filter.Eventually.of_forall fun a ↦
          (responseJ_adjointSubSkew (adaptedDomain hq s) a g hg p r).symm)
  have hpoint : ∀ a, avsum Z (fun w ↦ energy w a) =
      2 * (avsum Z (fun w ↦ Jcell w a) - Jscale t a) := by
    intro a
    dsimp only [energy, Jcell, Jscale]
    rw [avsum_const_mul,
      diagonalWeak_recent_energy_eq_response_deficit
        hq hst (a.subSkew g hg).transpose p r]
    ring
  have hJavgInt : Integrable (fun a ↦ avsum Z (fun w ↦ Jcell w a)) P := by
    unfold avsum
    exact (integrable_finsetSum Z hJcellInt).const_mul _
  constructor
  · intro w hw
    exact integral_nonneg_of_ae (_root_.Filter.Eventually.of_forall fun a ↦
      mul_nonneg (by norm_num) (diagonalWeak_recent_difference_energy_nonneg
        hq hst hw (a.subSkew g hg).transpose p r))
  · calc
      avsum Z (fun w ↦ ∫ a, energy w a ∂P) =
          ∫ a, avsum Z (fun w ↦ energy w a) ∂P :=
        (integral_avsum_eq_avsum_integral Z energy henergyInt).symm
      _ = ∫ a, 2 * (avsum Z (fun w ↦ Jcell w a) - Jscale t a) ∂P :=
        integral_congr_ae (_root_.Filter.Eventually.of_forall hpoint)
      _ = 2 * ((∫ a, avsum Z (fun w ↦ Jcell w a) ∂P) -
          ∫ a, Jscale t a ∂P) := by
        rw [integral_const_mul, integral_sub hJavgInt ht]
      _ = 2 * (avsum Z (fun w ↦ ∫ a, Jcell w a ∂P) -
          ∫ a, Jscale t a ∂P) := by
        rw [integral_avsum_eq_avsum_integral Z Jcell hJcellInt]
      _ = 2 * ((∫ a, Jscale s a ∂P) - ∫ a, Jscale t a ∂P) := by
        rw [avsum_eq_of_forall_eq (alignedIndex_nonempty hq hst) hJcell]
      _ = 2 * profileAdjointResponseDefect P hq g hg s t p r := by
        rw [profileAdjointResponseDefect_eq_sub_integral P hq g hg s t p r hs ht]

end

end HCPolySupport.HighContrast.Response
