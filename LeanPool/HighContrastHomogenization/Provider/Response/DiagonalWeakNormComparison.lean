/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormCarriers
public import LeanPool.HighContrastHomogenization.Geometry.SchurData
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AveragedEntries
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.PositiveGapClosure

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Matrix comparisons for the diagonal weak norm

The estimates in this file compare the diagonal metric, a positive reference
block, and the coarse response of an aligned cell.  They also record positivity
of the normalized averaged defect from exact aligned subadditivity.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Positivity of the diagonal metric -/

private theorem posDef_toFullBlockMat_diagonalMetric {m0 : Mat d}
    (hm0 : m0.PosDef) :
    (toFullBlockMat (blockDiag m0 m0⁻¹)).PosDef := by
  rw [toFullBlockMat_blockDiag]
  have h := posDef_schurBlock (s := m0) (sStar := m0) (k := 0) hm0 hm0
  simpa [schurBlock, fullBlockShear] using h

/-- The block `M₀ = diag(m₀,m₀⁻¹)` is symmetric. -/
theorem isSymmetricBlockMat_diagonalMetric {m0 : Mat d} (hm0 : m0.PosDef) :
    IsSymmetricBlockMat (blockDiag m0 m0⁻¹) :=
  isSymmetricBlockMat_of_posSemidef
    (posDef_toFullBlockMat_diagonalMetric hm0).posSemidef

/-- The block `M₀ = diag(m₀,m₀⁻¹)` is positive definite. -/
theorem blockPosDef_diagonalMetric {m0 : Mat d} (hm0 : m0.PosDef) :
    BlockPosDef (blockDiag m0 m0⁻¹) :=
  (blockPosDef_iff_posDef (isSymmetricBlockMat_diagonalMetric hm0)).mpr
    (posDef_toFullBlockMat_diagonalMetric hm0)

/-- The structural doubled identity is symmetric. -/
theorem isSymmetricBlockMat_blockIdentity :
    IsSymmetricBlockMat (blockIdentity d) := by
  refine isSymmetricBlockMat_of_posSemidef ?_
  rw [toFullBlockMat_blockIdentity]
  exact Matrix.PosDef.one.posSemidef

/-- The structural doubled identity is positive definite. -/
theorem blockPosDef_blockIdentity : BlockPosDef (blockIdentity d) :=
  (blockPosDef_iff_posDef isSymmetricBlockMat_blockIdentity).mpr <| by
    rw [toFullBlockMat_blockIdentity]
    exact Matrix.PosDef.one

/-! ## Squares of the printed factors -/

/-- The square of `K_{M,E}` is the relative block size it names. -/
theorem sq_diagonalWeakMetricFactor {m0 : Mat d} {E : BlockMat d}
    (hm0 : m0.PosDef) (hE : IsSymmetricBlockMat E) :
    diagonalWeakMetricFactor m0 E ^ 2 =
      blockSize E (blockDiag m0 m0⁻¹) := by
  rw [diagonalWeakMetricFactor_eq, Real.sq_sqrt]
  exact PortableHistory.blockSize_nonneg hE (isSymmetricBlockMat_diagonalMetric hm0)
    (blockPosDef_diagonalMetric hm0)

/-- The square of the primal load factor is the reference quadratic form. -/
theorem sq_diagonalWeakLoadMinus {E : BlockMat d} {p q : Vec d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    diagonalWeakLoadMinus E p q ^ 2 =
      blockVecDot ((-p, q) : BlockVec d)
        (blockMatVecMul E ((-p, q) : BlockVec d)) := by
  rw [diagonalWeakLoadMinus_eq, Real.sq_sqrt]
  rw [blockVecDot_blockMatVecMul_eq_dotProduct]
  exact (posDef_toFullBlockMat hE hEpd).posSemidef.dotProduct_mulVec_nonneg _

/-- The square of the adjoint load factor is the reference quadratic form. -/
theorem sq_diagonalWeakLoadPlus {E : BlockMat d} {p q : Vec d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    diagonalWeakLoadPlus E p q ^ 2 =
      blockVecDot ((p, q) : BlockVec d)
        (blockMatVecMul E ((p, q) : BlockVec d)) := by
  rw [diagonalWeakLoadPlus_eq, Real.sq_sqrt]
  rw [blockVecDot_blockMatVecMul_eq_dotProduct]
  exact (posDef_toFullBlockMat hE hEpd).posSemidef.dotProduct_mulVec_nonneg _

/-! ## Positivity of the recent averaged defect -/

/-- Flattening the averaged defect gives the printed average of the normalized
cell defects. -/
theorem toFullBlockMat_diagonalWeakAverageDefect (q : Mat d) (k t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) :
    toFullBlockMat (diagonalWeakAverageDefect q k t E a) =
      ((alignedIndex q k t).card : ℝ)⁻¹ •
        ∑ w ∈ alignedIndex q k t,
          toFullBlockMat
            (normalizedBlock
              (blockSub (adaptedResponse q k w a)
                (coarseBlock (adaptedCell q t) a)) E) := by
  rw [diagonalWeakAverageDefect_eq, toFullBlockMat_ofFullBlockMat]

/-- Linearity identifies the printed average with the normalized difference
between the aligned response average and the parent response. -/
theorem toFullBlockMat_diagonalWeakAverageDefect_eq_normalized
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (E : BlockMat d) (a : CoeffSpace d) :
    toFullBlockMat (diagonalWeakAverageDefect q k t E a) =
      toFullBlockMat
        (normalizedBlock
          (blockSub
            (ofFullBlockMat
              (((alignedIndex q k t).card : ℝ)⁻¹ •
                ∑ w ∈ alignedIndex q k t,
                  toFullBlockMat (adaptedResponse q k w a)))
            (coarseBlock (adaptedCell q t) a)) E) := by
  rw [toFullBlockMat_diagonalWeakAverageDefect]
  ext α β
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  exact (Recurrence.toFullBlockMat_normalizedBlock_blockSub_average_apply
    (alignedIndex_nonempty hq hkt) (fun w => adaptedResponse q k w a)
    (coarseBlock (adaptedCell q t) a) E α β).symm

/-- Exact aligned subadditivity makes `D_{k,t}(E)` positive semidefinite. -/
theorem posSemidef_diagonalWeakAverageDefect [NeZero d] {q : Mat d}
    (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) :
    (toFullBlockMat (diagonalWeakAverageDefect q k t E a)).PosSemidef := by
  have hsub := Recurrence.toFullBlockMat_coarseBlock_adaptedCell_le_average hq hkt
    (coe_alignedIndex hq hkt) a
  have hdiff :
      ((((alignedIndex q k t).card : ℝ)⁻¹ •
            ∑ w ∈ alignedIndex q k t,
              toFullBlockMat (adaptedResponse q k w a)) -
          toFullBlockMat (coarseBlock (adaptedCell q t) a)).PosSemidef := by
    exact Matrix.le_iff.mp hsub
  rw [toFullBlockMat_diagonalWeakAverageDefect_eq_normalized hq hkt]
  rw [Recurrence.toFullBlockMat_normalizedBlock]
  exact posSemidef_normalize
    (by simpa [Recurrence.toFullBlockMat_blockSub, toFullBlockMat_ofFullBlockMat] using hdiff)
    (posDef_toFullBlockMat hE hEpd)

/-- The averaged defect is structurally symmetric. -/
theorem isSymmetricBlockMat_diagonalWeakAverageDefect [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) :
    IsSymmetricBlockMat (diagonalWeakAverageDefect q k t E a) :=
  isSymmetricBlockMat_of_posSemidef
    (posSemidef_diagonalWeakAverageDefect hq hkt hE hEpd a)

/-- The scalar norm of a positive averaged defect is nonnegative. -/
theorem blockSize_diagonalWeakAverageDefect_nonneg [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) :
    0 ≤ blockSize (diagonalWeakAverageDefect q k t E a)
      (blockIdentity d) :=
  PortableHistory.blockSize_nonneg
    (isSymmetricBlockMat_diagonalWeakAverageDefect hq hkt hE hEpd a)
    isSymmetricBlockMat_blockIdentity blockPosDef_blockIdentity

/-! ## The average comparison inequality -/

private theorem fullBlockMat_mulVec_sq_le (A : FullBlockMat d)
    (x : FullBlockVec d) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ ‖A‖ ^ 2 * (x ⬝ᵥ x) := by
  rw [show (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (Aᴴ * A) *ᵥ x by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
      ← Matrix.dotProduct_mulVec,
      show Aᴴ = Aᵀ by rw [conjTranspose_eq_transpose']]]
  have h := dotProduct_mulVec_le_norm_mul (Aᴴ * A) x
  have hnorm : ‖Aᴴ * A‖ = ‖A‖ * ‖A‖ := by
    change ‖star A * A‖ = _
    exact CStarRing.norm_star_mul_self
  rw [hnorm] at h
  simpa only [pow_two] using h

/-- A centered symmetric block measured against `E` obeys the comparison
quadratic form used in the comparison of the optimizer averages of two cells. -/
theorem centered_metric_quadratic_le {M E D : FullBlockMat d}
    (hM : M.PosDef) (hE : E.PosDef) (x : FullBlockVec d) :
    (D *ᵥ x) ⬝ᵥ M⁻¹ *ᵥ (D *ᵥ x) ≤
      relSize E M * ‖matSqrt E⁻¹ * D * matSqrt E⁻¹‖ ^ 2 *
        (x ⬝ᵥ E *ᵥ x) := by
  set SM : FullBlockMat d := matSqrt M⁻¹ with hSM
  set SE : FullBlockMat d := matSqrt E with hSE
  set SI : FullBlockMat d := matSqrt E⁻¹ with hSI
  set B : FullBlockMat d := SI * D * SI with hB
  set N : FullBlockMat d := SM * SE with hN
  set y : FullBlockVec d := SE *ᵥ x with hy
  set z : FullBlockVec d := B *ᵥ y with hz
  set w : FullBlockVec d := N *ᵥ z with hw
  have hSMsymm : SMᴴ = SM := by
    rw [hSM]
    exact (matSqrt_spec hM.inv.posSemidef).1.isHermitian
  have hSEsymm : SEᴴ = SE := by
    rw [hSE]
    exact (matSqrt_spec hE.posSemidef).1.isHermitian
  have hSMSM : SM * SM = M⁻¹ := by
    rw [hSM]
    exact (matSqrt_spec hM.inv.posSemidef).2
  have hSESE : SE * SE = E := by
    rw [hSE]
    exact (matSqrt_spec hE.posSemidef).2
  have hSIeq : SI = SE⁻¹ := by
    rw [hSI, hSE, matSqrt_inv hE]
  have hSEunit : IsUnit SE := by
    rw [hSE]
    exact isUnit_matSqrt hE
  have hSEdet : IsUnit SE.det := (Matrix.isUnit_iff_isUnit_det _).mp hSEunit
  have hSESI : SE * SI = 1 := by
    rw [hSIeq, Matrix.mul_nonsing_inv _ hSEdet]
  have hSISE : SI * SE = 1 := by
    rw [hSIeq, Matrix.nonsing_inv_mul _ hSEdet]
  have hfactorD : SE * B * SE = D := by
    rw [hB]
    calc
      SE * (SI * D * SI) * SE = (SE * SI) * D * (SI * SE) := by
        noncomm_ring
      _ = D := by rw [hSESI, hSISE, Matrix.one_mul, Matrix.mul_one]
  have hquadM :
      (D *ᵥ x) ⬝ᵥ M⁻¹ *ᵥ (D *ᵥ x) =
        (SM *ᵥ (D *ᵥ x)) ⬝ᵥ (SM *ᵥ (D *ᵥ x)) := by
    rw [← hSMSM, ← Matrix.mulVec_mulVec]
    exact dotProduct_mulVec_symm
      (by rw [← conjTranspose_eq_transpose']; exact hSMsymm) _ _
  have hwform : w = SM *ᵥ (D *ᵥ x) := by
    have hmatrix : N * B * SE = SM * D := by
      rw [hN]
      calc
        SM * SE * B * SE = SM * (SE * B * SE) := by noncomm_ring
        _ = SM * D := by rw [hfactorD]
    calc
      w = N *ᵥ (B *ᵥ (SE *ᵥ x)) := by rw [hw, hz, hy]
      _ = (N * B * SE) *ᵥ x := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (SM * D) *ᵥ x := by rw [hmatrix]
      _ = SM *ᵥ (D *ᵥ x) := by rw [Matrix.mulVec_mulVec]
  have hyquad : y ⬝ᵥ y = x ⬝ᵥ E *ᵥ x := by
    calc
      y ⬝ᵥ y = (SE *ᵥ x) ⬝ᵥ (SE *ᵥ x) := by rw [hy]
      _ = x ⬝ᵥ SE *ᵥ (SE *ᵥ x) :=
        (dotProduct_mulVec_symm
          (by rw [← conjTranspose_eq_transpose']; exact hSEsymm) _ _).symm
      _ = x ⬝ᵥ (SE * SE) *ᵥ x := by rw [Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ E *ᵥ x := by rw [hSESE]
  have hNnorm : ‖N‖ ^ 2 = relSize E M := by
    have hNN : N * Nᴴ = SM * E * SM := by
      rw [hN, Matrix.conjTranspose_mul, hSEsymm, hSMsymm]
      calc
        SM * SE * (SE * SM) = SM * (SE * SE) * SM := by noncomm_ring
        _ = SM * E * SM := by rw [hSESE]
    rw [pow_two, ← CStarRing.norm_self_mul_star,
      Matrix.star_eq_conjTranspose, hNN, relSize_def, hSM]
  have hwle : w ⬝ᵥ w ≤ ‖N‖ ^ 2 * (z ⬝ᵥ z) := by
    rw [hw]
    exact fullBlockMat_mulVec_sq_le N z
  have hzle : z ⬝ᵥ z ≤ ‖B‖ ^ 2 * (y ⬝ᵥ y) := by
    rw [hz]
    exact fullBlockMat_mulVec_sq_le B y
  have hN0 : 0 ≤ ‖N‖ ^ 2 := sq_nonneg _
  have hstep : ‖N‖ ^ 2 * (z ⬝ᵥ z) ≤
      ‖N‖ ^ 2 * (‖B‖ ^ 2 * (y ⬝ᵥ y)) :=
    mul_le_mul_of_nonneg_left hzle hN0
  calc
    (D *ᵥ x) ⬝ᵥ M⁻¹ *ᵥ (D *ᵥ x) = w ⬝ᵥ w := by
      rw [hquadM, hwform]
    _ ≤ ‖N‖ ^ 2 * (z ⬝ᵥ z) := hwle
    _ ≤ ‖N‖ ^ 2 * (‖B‖ ^ 2 * (y ⬝ᵥ y)) := hstep
    _ = relSize E M * ‖matSqrt E⁻¹ * D * matSqrt E⁻¹‖ ^ 2 *
          (x ⬝ᵥ E *ᵥ x) := by
      rw [hNnorm, hB, hyquad]
      ring

/-- The exact aligned-cell comparison is bounded by the metric factor, the
primal load factor, and the normalized response defect. -/
theorem metricNormSq_blockAverage_sub_adapted_le
    {q : Mat d} (hq : q.PosDef) (k t : ℤ) (w : Fin d → ℤ)
    {a : CoeffSpace d} {c : Book.Ch02.CoeffOn (adaptedDomainAt hq k w)}
    {b : Book.Ch02.CoeffOn (adaptedDomain hq t)} {m : Mat d}
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E)
    (hc : Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c =
      adaptedResponse q k w a)
    (hb : Book.Ch02.coarseBlockMatrix (adaptedDomain hq t) b =
      coarseBlock (adaptedCell q t) a)
    {p₀ q₀ : Vec d} {v : Book.Ch02.Solution (adaptedDomainAt hq k w) c}
    {u : Book.Ch02.Solution (adaptedDomain hq t) b}
    (hv : Book.Ch02.IsResponseMaximizer (adaptedDomainAt hq k w) c p₀ q₀ v)
    (hu : Book.Ch02.IsResponseMaximizer (adaptedDomain hq t) b p₀ q₀ u) :
    blockVecDot
        (((Book.Ch02.averageGradient (adaptedDomainAt hq k w) c v,
            Book.Ch02.averageFlux (adaptedDomainAt hq k w) c v) : BlockVec d) -
          ((Book.Ch02.averageGradient (adaptedDomain hq t) b u,
            Book.Ch02.averageFlux (adaptedDomain hq t) b u) : BlockVec d))
        (blockMatVecMul (blockDiag m m⁻¹)
          (((Book.Ch02.averageGradient (adaptedDomainAt hq k w) c v,
              Book.Ch02.averageFlux (adaptedDomainAt hq k w) c v) : BlockVec d) -
            ((Book.Ch02.averageGradient (adaptedDomain hq t) b u,
              Book.Ch02.averageFlux (adaptedDomain hq t) b u) : BlockVec d))) ≤
      diagonalWeakMetricFactor m E ^ 2 *
        diagonalWeakLoadMinus E p₀ q₀ ^ 2 *
          blockSize
            (blockSub (adaptedResponse q k w a)
              (coarseBlock (adaptedCell q t) a)) E ^ 2 := by
  let M : BlockMat d := blockDiag m m⁻¹
  let D : BlockMat d := blockSub (adaptedResponse q k w a)
    (coarseBlock (adaptedCell q t) a)
  let x : BlockVec d := ((-p₀, q₀) : BlockVec d)
  have hMsymm : IsSymmetricBlockMat M := by
    rw [show M = blockDiag m m⁻¹ from rfl]
    exact isSymmetricBlockMat_diagonalMetric hm
  have hMpd : BlockPosDef M := by
    rw [show M = blockDiag m m⁻¹ from rfl]
    exact blockPosDef_diagonalMetric hm
  have hMfull : (toFullBlockMat M).PosDef :=
    posDef_toFullBlockMat hMsymm hMpd
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hE hEpd
  have hDsymm : IsSymmetricBlockMat D := by
    exact isSymmetricBlockMat_blockSub
      (isSymmetricBlockMat_coarseBlock _ a)
      (isSymmetricBlockMat_coarseBlock _ a)
  have hreflect :
      toFullBlockMat (blockReflect M) = (toFullBlockMat M)⁻¹ := by
    rw [← toFullBlockMat_blockMatInv]
    exact congrArg toFullBlockMat
      (blockMatInv_metric_eq_blockReflect (isUnit_det_of_posDef hm)).symm
  have hcomparison := centered_metric_quadratic_le hMfull hEfull
    (toFullBlockVec x) (D := toFullBlockMat D)
  have hexact := metricNormSq_blockAverage_sub_adapted hq k t w m hc hb hv hu
  rw [show M = blockDiag m m⁻¹ from rfl] at hreflect
  rw [hexact, show blockSub (adaptedResponse q k w a)
      (coarseBlock (adaptedCell q t) a) = D from rfl,
    show ((-p₀, q₀) : BlockVec d) = x from rfl,
    blockVecDot_blockMatVecMul_eq_dotProduct,
    toFullBlockVec_blockMatVecMul, hreflect]
  calc
    toFullBlockMat D *ᵥ toFullBlockVec x ⬝ᵥ
        (toFullBlockMat M)⁻¹ *ᵥ (toFullBlockMat D *ᵥ toFullBlockVec x) ≤
        relSize (toFullBlockMat E) (toFullBlockMat M) *
          ‖matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat D *
              matSqrt (toFullBlockMat E)⁻¹‖ ^ 2 *
            (toFullBlockVec x ⬝ᵥ
              toFullBlockMat E *ᵥ toFullBlockVec x) := hcomparison
    _ = diagonalWeakMetricFactor m E ^ 2 *
          diagonalWeakLoadMinus E p₀ q₀ ^ 2 * blockSize D E ^ 2 := by
      rw [sq_diagonalWeakMetricFactor hm hE,
        sq_diagonalWeakLoadMinus hE hEpd,
        blockVecDot_blockMatVecMul_eq_dotProduct,
        show toFullBlockVec x = toFullBlockVec ((-p₀, q₀) : BlockVec d) from rfl,
        ← blockSize_eq_relSize hE hMsymm hMpd hEfull.posSemidef,
        PortableHistory.blockSize_eq_norm hDsymm hE hEpd,
        Recurrence.toFullBlockMat_normalizedBlock]
      ring

end

end Response
end HighContrast
end HCPolySupport
