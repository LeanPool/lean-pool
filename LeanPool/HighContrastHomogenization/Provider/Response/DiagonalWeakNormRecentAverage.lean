/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentEnergy

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentAverage

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The averaged optimizer-difference energy

The variational deficit on each recent child recombines over the exact
partition.  The affine load terms cancel, leaving twice the quadratic form of
the averaged coarse-response defect.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem blockQuadratic_of_avsum {iota : Type*}
    (Z : Finset iota) (A : iota → BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul
        (ofFullBlockMat (((Z.card : ℝ))⁻¹ •
          ∑ w ∈ Z, toFullBlockMat (A w))) X) =
      avsum Z (fun w => blockVecDot X (blockMatVecMul (A w) X)) := by
  rw [blockVecDot_blockMatVecMul_eq_dotProduct,
    toFullBlockMat_ofFullBlockMat, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.sum_mulVec, dotProduct_sum, avsum_eq]
  exact congrArg (((Z.card : ℝ))⁻¹ * ·)
    (Finset.sum_congr rfl fun w _ =>
      blockVecDot_blockMatVecMul_eq_dotProduct (A w) X).symm

/-- The difference energy on one child is four times its response deficit,
with the restricted parent value written as the child average of the parent
integrand. -/
theorem diagonalWeak_child_difference_energy_eq_responseAverage [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) :
    Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
        blockVecDot
          (diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x)
          (blockMatVecMul
            (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x))) =
      4 * (responseJ (adaptedDomainAt hq k w)
            (a.coeffOn (adaptedDomainAt hq k w)) p r -
          volumeAverage (adaptedCellAt q k w)
            (responseIntegrand (adaptedDomain hq t)
              (a.coeffOn (adaptedDomain hq t)) p r
              (diagonalWeakOptimizer hq t a p r))) := by
  obtain ⟨u, hu, henergy⟩ := diagonalWeak_child_difference_energy_eq
    hq hkt hw a p r
  rw [henergy]
  congr 2
  unfold responseValue Book.Ch02.average volumeAverage
  congr 2
  funext x
  unfold responseIntegrand
  rw [hu]
  rfl

/-- Averaging the child identities and recombining the parent integrand gives
four times the averaged response deficit. -/
theorem diagonalWeak_recent_energy_eq_response_deficit [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (a : CoeffSpace d) (p r : Vec d) :
    avsum (alignedIndex q k t) (fun w =>
        Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
          blockVecDot
            (diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x)
            (blockMatVecMul
              (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
              (diagonalWeakChildState hq k w a p r x -
                diagonalWeakState hq t a p r x)))) =
      4 * (avsum (alignedIndex q k t) (fun w =>
            responseJ (adaptedDomainAt hq k w)
              (a.coeffOn (adaptedDomainAt hq k w)) p r) -
          responseJ (adaptedDomain hq t)
            (a.coeffOn (adaptedDomain hq t)) p r) := by
  let Z := alignedIndex q k t
  let G := responseIntegrand (adaptedDomain hq t)
    (a.coeffOn (adaptedDomain hq t)) p r
    (diagonalWeakOptimizer hq t a p r)
  have hcell : ∀ w ∈ Z,
      Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
          blockVecDot
            (diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x)
            (blockMatVecMul
              (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
              (diagonalWeakChildState hq k w a p r x -
                diagonalWeakState hq t a p r x))) =
        4 * (responseJ (adaptedDomainAt hq k w)
              (a.coeffOn (adaptedDomainAt hq k w)) p r -
            volumeAverage (adaptedCellAt q k w) G) := by
    intro w hw
    exact diagonalWeak_child_difference_energy_eq_responseAverage
      hq hkt hw a p r
  have hpartition : avsum Z
      (fun w => volumeAverage (adaptedCellAt q k w) G) =
      responseJ (adaptedDomain hq t)
        (a.coeffOn (adaptedDomain hq t)) p r := by
    rw [avsum_volumeAverage_adaptedCellAt_eq hq hkt
      (responseIntegrand_diagonalWeakOptimizer_integrableOn hq t a p r)]
    exact (responseJ_eq_responseValue_of_isResponseMaximizer
      (diagonalWeakOptimizer_isMaximizer hq t a p r)).symm
  change avsum Z _ = _
  calc
    avsum Z (fun w => Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
        blockVecDot
          (diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x)
          (blockMatVecMul
            (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x)))) =
        avsum Z (fun w => 4 *
          (responseJ (adaptedDomainAt hq k w)
              (a.coeffOn (adaptedDomainAt hq k w)) p r -
            volumeAverage (adaptedCellAt q k w) G)) := by
      rw [avsum_eq, avsum_eq]
      exact congrArg (((Z.card : ℝ))⁻¹ * ·)
        (Finset.sum_congr rfl hcell)
    _ = 4 * (avsum Z (fun w =>
          responseJ (adaptedDomainAt hq k w)
            (a.coeffOn (adaptedDomainAt hq k w)) p r) -
        avsum Z (fun w => volumeAverage (adaptedCellAt q k w) G)) := by
      simp only [avsum_eq, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ = 4 * (avsum Z (fun w =>
          responseJ (adaptedDomainAt hq k w)
            (a.coeffOn (adaptedDomainAt hq k w)) p r) -
        responseJ (adaptedDomain hq t)
          (a.coeffOn (adaptedDomain hq t)) p r) := by rw [hpartition]

/-- The averaged response deficit is one half of the quadratic form of the
averaged coarse-response defect. -/
theorem diagonalWeak_response_deficit_eq_blockQuadratic [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (a : CoeffSpace d) (p r : Vec d) :
    avsum (alignedIndex q k t) (fun w =>
          responseJ (adaptedDomainAt hq k w)
            (a.coeffOn (adaptedDomainAt hq k w)) p r) -
        responseJ (adaptedDomain hq t)
          (a.coeffOn (adaptedDomain hq t)) p r =
      (1 / 2 : ℝ) * blockVecDot ((-p, r) : BlockVec d)
        (blockMatVecMul
          (blockSub
            (ofFullBlockMat
              ((((alignedIndex q k t).card : ℝ))⁻¹ •
                ∑ w ∈ alignedIndex q k t,
                  toFullBlockMat (adaptedResponse q k w a)))
            (coarseBlock (adaptedCell q t) a))
          ((-p, r) : BlockVec d)) := by
  let Z := alignedIndex q k t
  let X : BlockVec d := ((-p, r) : BlockVec d)
  let Abar : BlockMat d := ofFullBlockMat
    ((((Z.card : ℝ))⁻¹ •
      ∑ w ∈ Z, toFullBlockMat (adaptedResponse q k w a)))
  let At : BlockMat d := coarseBlock (adaptedCell q t) a
  have hZ : Z.Nonempty := alignedIndex_nonempty hq hkt
  have hchild : ∀ w ∈ Z,
      responseJ (adaptedDomainAt hq k w)
          (a.coeffOn (adaptedDomainAt hq k w)) p r =
        (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (adaptedResponse q k w a) X) - vecDot p r := by
    intro w _hw
    rw [HCPolySupport.Internal.Ch02.BookCh02.responseJ_eq_block_quadratic,
      ← coarseBlock_eq_coarseBlockMatrix a (adaptedDomainAt hq k w)]
    rfl
  have hparent : responseJ (adaptedDomain hq t)
      (a.coeffOn (adaptedDomain hq t)) p r =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul At X) - vecDot p r := by
    rw [HCPolySupport.Internal.Ch02.BookCh02.responseJ_eq_block_quadratic,
      ← coarseBlock_eq_coarseBlockMatrix a (adaptedDomain hq t)]
    rfl
  have havg : blockVecDot X (blockMatVecMul Abar X) =
      avsum Z (fun w => blockVecDot X
        (blockMatVecMul (adaptedResponse q k w a) X)) :=
    blockQuadratic_of_avsum Z (fun w => adaptedResponse q k w a) X
  have hsub : blockSub Abar At =
      ofFullBlockMat (toFullBlockMat Abar - toFullBlockMat At) := by
    rw [← Recurrence.toFullBlockMat_blockSub]
    exact (ofFullBlockMat_toFullBlockMat (blockSub Abar At)).symm
  change avsum Z _ - _ = _
  rw [show responseJ (adaptedDomain hq t)
      (a.coeffOn (adaptedDomain hq t)) p r =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul At X) - vecDot p r from hparent]
  calc
    avsum Z (fun w => responseJ (adaptedDomainAt hq k w)
          (a.coeffOn (adaptedDomainAt hq k w)) p r) -
        ((1 / 2 : ℝ) * blockVecDot X (blockMatVecMul At X) - vecDot p r) =
      avsum Z (fun w =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (adaptedResponse q k w a) X) - vecDot p r) -
        ((1 / 2 : ℝ) * blockVecDot X (blockMatVecMul At X) - vecDot p r) := by
      congr 1
      rw [avsum_eq, avsum_eq]
      exact congrArg (((Z.card : ℝ))⁻¹ * ·)
        (Finset.sum_congr rfl hchild)
    _ = (1 / 2 : ℝ) *
        (avsum Z (fun w => blockVecDot X
            (blockMatVecMul (adaptedResponse q k w a) X)) -
          blockVecDot X (blockMatVecMul At X)) := by
      rw [show (fun w =>
          (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (adaptedResponse q k w a) X) - vecDot p r) =
            fun w => (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (adaptedResponse q k w a) X) + (-(vecDot p r)) by
          funext w
          ring,
        avsum_add, avsum_const hZ, avsum_const_mul]
      ring
    _ = (1 / 2 : ℝ) *
        (blockVecDot X (blockMatVecMul Abar X) -
          blockVecDot X (blockMatVecMul At X)) := by rw [havg]
    _ = (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (blockSub Abar At) X) := by
      rw [hsub, blockVecDot_blockMatVecMul_ofFullBlockMat_sub]

/-- The exact factor-two identity for the recent optimizer-difference
energy. -/
theorem diagonalWeak_recent_difference_energy_eq [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (a : CoeffSpace d) (p r : Vec d) :
    avsum (alignedIndex q k t) (fun w =>
        Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
          blockVecDot
            (diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x)
            (blockMatVecMul
              (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
              (diagonalWeakChildState hq k w a p r x -
                diagonalWeakState hq t a p r x)))) =
      2 * blockVecDot ((-p, r) : BlockVec d)
        (blockMatVecMul
          (blockSub
            (ofFullBlockMat
              ((((alignedIndex q k t).card : ℝ))⁻¹ •
                ∑ w ∈ alignedIndex q k t,
                  toFullBlockMat (adaptedResponse q k w a)))
            (coarseBlock (adaptedCell q t) a))
          ((-p, r) : BlockVec d)) := by
  rw [diagonalWeak_recent_energy_eq_response_deficit hq hkt a p r,
    diagonalWeak_response_deficit_eq_blockQuadratic hq hkt a p r]
  ring

end

end Response
end HighContrast
end HCPolySupport
