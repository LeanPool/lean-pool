/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentAverage

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentQuadratic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalizing the recent quadratic defect

Congruence by the reference square root identifies the unnormalized averaged
response defect with `D_{k,t}(E)`.  Its positive-semidefinite order bound then
controls the load quadratic form by the spectral size of that normalized
defect.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The response quadratic form is bounded by the squared reference load
times the size of the normalized averaged defect. -/
theorem diagonalWeak_recent_response_quadratic_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) (p r : Vec d) :
    blockVecDot ((-p, r) : BlockVec d)
        (blockMatVecMul
          (blockSub
            (ofFullBlockMat
              ((((alignedIndex q k t).card : ℝ))⁻¹ •
                ∑ w ∈ alignedIndex q k t,
                  toFullBlockMat (adaptedResponse q k w a)))
            (coarseBlock (adaptedCell q t) a))
          ((-p, r) : BlockVec d)) ≤
      diagonalWeakLoadMinus E p r ^ 2 *
        blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d) := by
  let Z := alignedIndex q k t
  let X : BlockVec d := ((-p, r) : BlockVec d)
  let Abar : BlockMat d := ofFullBlockMat
    ((((Z.card : ℝ))⁻¹ •
      ∑ w ∈ Z, toFullBlockMat (adaptedResponse q k w a)))
  let At : BlockMat d := coarseBlock (adaptedCell q t) a
  let H : BlockMat d := blockSub Abar At
  let D : BlockMat d := diagonalWeakAverageDefect q k t E a
  let Ef : FullBlockMat d := toFullBlockMat E
  let S : FullBlockMat d := matSqrt Ef
  let SI : FullBlockMat d := matSqrt Ef⁻¹
  let xf : FullBlockVec d := toFullBlockVec X
  let y : FullBlockVec d := S *ᵥ xf
  have hEf : Ef.PosDef := posDef_toFullBlockMat hE hEpd
  have hD : toFullBlockMat D = SI * toFullBlockMat H * SI := by
    rw [show D = diagonalWeakAverageDefect q k t E a from rfl,
      toFullBlockMat_diagonalWeakAverageDefect_eq_normalized hq hkt,
      Recurrence.toFullBlockMat_normalizedBlock]
  have hSSI : S * SI = 1 := matSqrt_mul_matSqrt_inv hEf
  have hSIS : SI * S = 1 := matSqrt_inv_mul_matSqrt hEf
  have hfactor : S * toFullBlockMat D * S = toFullBlockMat H := by
    rw [hD]
    calc
      S * (SI * toFullBlockMat H * SI) * S =
          (S * SI) * toFullBlockMat H * (SI * S) := by noncomm_ring
      _ = toFullBlockMat H := by rw [hSSI, hSIS, Matrix.one_mul, Matrix.mul_one]
  have hSsymm : Sᵀ = S := by
    rw [← conjTranspose_eq_transpose']
    exact (matSqrt_spec hEf.posSemidef).1.isHermitian
  have hquad : blockVecDot X (blockMatVecMul H X) =
      y ⬝ᵥ toFullBlockMat D *ᵥ y := by
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    change xf ⬝ᵥ toFullBlockMat H *ᵥ xf =
      (S *ᵥ xf) ⬝ᵥ toFullBlockMat D *ᵥ (S *ᵥ xf)
    calc
      xf ⬝ᵥ toFullBlockMat H *ᵥ xf =
          xf ⬝ᵥ (S * toFullBlockMat D * S) *ᵥ xf := by rw [hfactor]
      _ = xf ⬝ᵥ S *ᵥ (toFullBlockMat D *ᵥ (S *ᵥ xf)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (S *ᵥ xf) ⬝ᵥ toFullBlockMat D *ᵥ (S *ᵥ xf) :=
        dotProduct_mulVec_symm hSsymm xf
          (toFullBlockMat D *ᵥ (S *ᵥ xf))
  have hy : y ⬝ᵥ y = xf ⬝ᵥ Ef *ᵥ xf := by
    change (S *ᵥ xf) ⬝ᵥ (S *ᵥ xf) = xf ⬝ᵥ Ef *ᵥ xf
    rw [← dotProduct_mulVec_symm hSsymm xf (S *ᵥ xf), Matrix.mulVec_mulVec]
    exact congrArg (fun M => xf ⬝ᵥ M *ᵥ xf) (matSqrt_spec hEf.posSemidef).2
  have hDsym : IsSymmetricBlockMat D :=
    isSymmetricBlockMat_diagonalWeakAverageDefect hq hkt hE hEpd a
  have hup := (PortableHistory.blockSize_sandwich hDsym isSymmetricBlockMat_blockIdentity
    blockPosDef_blockIdentity).1
  have hboundRaw := (Matrix.le_iff.mp hup).dotProduct_mulVec_nonneg y
  have hbound : y ⬝ᵥ toFullBlockMat D *ᵥ y ≤
      blockSize D (blockIdentity d) * (y ⬝ᵥ y) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, toFullBlockMat_blockIdentity,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul] at hboundRaw
    simp only [star_trivial, smul_eq_mul] at hboundRaw
    linarith only [hboundRaw]
  change blockVecDot X (blockMatVecMul H X) ≤ _
  rw [hquad]
  calc
    y ⬝ᵥ toFullBlockMat D *ᵥ y ≤
        blockSize D (blockIdentity d) * (y ⬝ᵥ y) := hbound
    _ = blockSize D (blockIdentity d) *
        blockVecDot X (blockMatVecMul E X) := by
      rw [hy, blockVecDot_blockMatVecMul_eq_dotProduct]
    _ = diagonalWeakLoadMinus E p r ^ 2 *
        blockSize D (blockIdentity d) := by
      rw [sq_diagonalWeakLoadMinus hE hEpd]
      ring

/-- The recent optimizer-difference energy is bounded by twice the squared
load times the normalized averaged defect. -/
theorem diagonalWeak_recent_difference_energy_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) (p r : Vec d) :
    avsum (alignedIndex q k t) (fun w =>
        Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
          blockVecDot
            (diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x)
            (blockMatVecMul
              (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
              (diagonalWeakChildState hq k w a p r x -
                diagonalWeakState hq t a p r x)))) ≤
      2 * diagonalWeakLoadMinus E p r ^ 2 *
        blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d) := by
  calc
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
            ((-p, r) : BlockVec d)) :=
      diagonalWeak_recent_difference_energy_eq hq hkt a p r
    _ ≤ 2 * (diagonalWeakLoadMinus E p r ^ 2 *
        blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d)) :=
      mul_le_mul_of_nonneg_left
        (diagonalWeak_recent_response_quadratic_le hq hkt hE hEpd a p r)
        (by norm_num)
    _ = 2 * diagonalWeakLoadMinus E p r ^ 2 *
        blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d) := by ring

end

end Response
end HighContrast
end HCPolySupport
