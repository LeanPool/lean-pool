/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedAnalyticGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedHarmonicReplacement
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.BlockExcessHomogenizationError
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.AEEq
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Finite
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.Energy
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutions
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.Response
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.RHSCorrections
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincare.QTwo

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationHarmonicComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
/-!
# Common-scale rounded harmonic comparison
The physical rounded response row is first identified exactly with the
canonical response row of the rounded coefficient and rounded constant
matrix.  The finite `q = 2` recurrence then feeds the already selected
common-scale dual comparison without changing the printed order or scale
normalization.
-/
namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator
noncomputable section
@[expose]
public def inverseAffinePrimalLoad {d : ℕ}
    (q : Mat d) (X : BlockVec d) : BlockVec d :=
  (matVecMul (matTranspose q)⁻¹ X.1, matVecMul q X.2)
@[expose]
public def inverseAffineDualLoad {d : ℕ}
    (q : Mat d) (X : BlockVec d) : BlockVec d :=
  (matVecMul q X.1, matVecMul (matTranspose q)⁻¹ X.2)
private theorem affineReferencePrimalLoad_inverseAffinePrimalLoad
    {d : ℕ} {q : Mat d} (hq : q.PosDef) (X : BlockVec d) :
    affineReferencePrimalLoad q (inverseAffinePrimalLoad q X) = X := by
  rcases X with ⟨x, y⟩
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hqT : matTranspose q = q := by
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using!
      hq.isHermitian
  rw [Prod.mk.injEq]
  constructor
  · simp only [affineReferencePrimalLoad, inverseAffinePrimalLoad, hqT,
      matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
  · simp only [affineReferencePrimalLoad, inverseAffinePrimalLoad, hqT,
      matVecMul_mul, Matrix.nonsing_inv_mul q hqdet, matVecMul_one]
private theorem affineReferenceDualLoad_inverseAffineDualLoad
    {d : ℕ} {q : Mat d} (hq : q.PosDef) (X : BlockVec d) :
    affineReferenceDualLoad q (inverseAffineDualLoad q X) = X := by
  rcases X with ⟨x, y⟩
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hqT : matTranspose q = q := by
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using!
      hq.isHermitian
  rw [Prod.mk.injEq]
  constructor
  · simp only [affineReferenceDualLoad, inverseAffineDualLoad, hqT,
      matVecMul_mul, Matrix.nonsing_inv_mul q hqdet, matVecMul_one]
  · simp only [affineReferenceDualLoad, inverseAffineDualLoad, hqT,
      matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
private theorem blockVecDot_affineReferenceLoads_direct
    {d : ℕ} {q : Mat d} (hq : q.PosDef) (P Q : BlockVec d) :
    blockVecDot (affineReferencePrimalLoad q P)
        (affineReferenceDualLoad q Q) = blockVecDot P Q := by
  rcases P with ⟨p, r⟩
  rcases Q with ⟨rStar, pStar⟩
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hleft :
      vecDot (matVecMul (matTranspose q) p) (matVecMul q⁻¹ rStar) =
        vecDot p rStar := by
    calc
      vecDot (matVecMul (matTranspose q) p) (matVecMul q⁻¹ rStar) =
          vecDot (matVecMul q⁻¹ rStar) (matVecMul (matTranspose q) p) :=
        vecDot_comm _ _
      _ = vecDot (matVecMul q (matVecMul q⁻¹ rStar)) p :=
        vecDot_matVecMul_transpose _ _ q
      _ = vecDot rStar p := by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
      _ = vecDot p rStar := vecDot_comm _ _
  have hright :
      vecDot (matVecMul q⁻¹ r) (matVecMul (matTranspose q) pStar) =
        vecDot r pStar := by
    calc
      vecDot (matVecMul q⁻¹ r) (matVecMul (matTranspose q) pStar) =
          vecDot (matVecMul q (matVecMul q⁻¹ r)) pStar :=
        vecDot_matVecMul_transpose _ _ q
      _ = vecDot r pStar := by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
  simp only [affineReferencePrimalLoad, affineReferenceDualLoad, blockVecDot,
    hleft, hright]
private theorem referenceMatrix_eq_grid_conj_normalizedRoot_sq
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    geom.referenceMatrix abar hS =
      (geom.grid (symmPart abar))⁻¹ *
        (Selection.normalizedRoot (symmPart abar) *
          Selection.normalizedRoot (symmPart abar)) *
      (geom.grid (symmPart abar))⁻¹ := by
  unfold RoundedGenerationAnalyticGeometry.referenceMatrix roundedReferenceMatrixAtGeneration
    RoundedGenerationAnalyticGeometry.grid
  rw [show matTranspose (roundedGrid geom.generation (symmPart abar))⁻¹ =
      (roundedGrid geom.generation (symmPart abar))⁻¹ by
    rw [matTranspose, Matrix.transpose_nonsing_inv]
    rw [show Matrix.transpose
          (roundedGrid geom.generation (symmPart abar)) =
        roundedGrid geom.generation (symmPart abar) by
      simpa only [matTranspose, RoundedGenerationAnalyticGeometry.grid] using
        geom.grid_transpose hS]]
  change
    (geom.grid (symmPart abar))⁻¹ *
        (specBound (symmPart abar)⁻¹ • symmPart abar) *
        (geom.grid (symmPart abar))⁻¹ = _
  rw [normalizedRoot_mul_self hS]
  rfl
private theorem inverse_baseRounded_conj_normalizedRoot_sq
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    (geom.referenceMatrix abar hS)⁻¹ =
      geom.grid (symmPart abar) *
        ((Selection.normalizedRoot (symmPart abar))⁻¹ *
          (Selection.normalizedRoot (symmPart abar))⁻¹) *
        geom.grid (symmPart abar) := by
  let q := geom.grid (symmPart abar)
  let L := Selection.normalizedRoot (symmPart abar)
  have hqdet : IsUnit q.det := by
    simpa only [q] using geom.grid_det_isUnit hS
  rw [referenceMatrix_eq_grid_conj_normalizedRoot_sq abar hS]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  change q⁻¹⁻¹ * ((L⁻¹ * L⁻¹) * q⁻¹⁻¹) =
    q * (L⁻¹ * L⁻¹) * q
  rw [Matrix.nonsing_inv_nonsing_inv q hqdet]
  noncomm_ring
private theorem skewPart_eq_zero_of_isSymm_direct
    {d : ℕ} {A : Mat d} (hA : A.IsSymm) :
    skewPart A = 0 := by
  ext i j
  have hij : A j i = A i j := (Matrix.IsSymm.ext_iff.mp hA) i j
  change (A i j - A j i) / 2 = 0
  rw [hij]
  ring
private theorem blockMatVecMul_constantBlockMatrix_of_isSymm
    {d : ℕ} {A : Mat d} (hA : A.IsSymm) (P : BlockVec d) :
    blockMatVecMul (Book.Ch02.constantBlockMatrix A) P =
      (matVecMul A P.1, matVecMul A⁻¹ P.2) := by
  rcases P with ⟨p, r⟩
  have hsymm : symmPart A = A := symmPart_eq_of_isSymm hA
  have hskew : skewPart A = 0 := skewPart_eq_zero_of_isSymm_direct hA
  apply Prod.ext
  · simp [Book.Ch02.constantBlockMatrix, blockMatVecMul, hsymm, hskew,
      matTranspose]
    ext i
    simp [matVecMul]
  · simp [Book.Ch02.constantBlockMatrix, blockMatVecMul, hsymm, hskew,
      matTranspose]
    ext i
    simp [matVecMul]
private theorem roundedAffineLoad_common_iff_constantBlock
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (P Q : BlockVec d) :
    affineReferencePrimalLoad (Selection.normalizedRoot (symmPart abar)) P =
        affineReferenceDualLoad (Selection.normalizedRoot (symmPart abar)) Q ↔
      affineReferenceDualLoad (geom.grid (symmPart abar)) Q =
        blockMatVecMul
          (Book.Ch02.constantBlockMatrix (geom.referenceMatrix abar hS))
          (affineReferencePrimalLoad (geom.grid (symmPart abar)) P) := by
  let L := Selection.normalizedRoot (symmPart abar)
  let q := geom.grid (symmPart abar)
  let A := geom.referenceMatrix abar hS
  rcases P with ⟨p, r⟩
  rcases Q with ⟨rStar, pStar⟩
  have hL : L.PosDef := by
    simpa only [L] using normalizedRoot_posDef_of_posDef hS
  have hq : q.PosDef := by
    simpa only [q] using geom.grid_posDef hS
  have hA : A.PosDef := by
    simpa only [A] using! geom.reference_posDef abar hS
  have hLT : matTranspose L = L := by
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using!
      hL.isHermitian
  have hqT : matTranspose q = q := by
    simpa only [q] using geom.grid_transpose hS
  have hLdet : IsUnit L.det := isUnit_det_of_posDef hL
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hAeq : A = q⁻¹ * (L * L) * q⁻¹ := by
    simpa only [A, q, L] using
      referenceMatrix_eq_grid_conj_normalizedRoot_sq abar hS
  have hAinv : A⁻¹ = q * (L⁻¹ * L⁻¹) * q := by
    simpa only [A, q, L] using
      inverse_baseRounded_conj_normalizedRoot_sq abar hS
  have hAq : A * q = q⁻¹ * (L * L) := by
    rw [hAeq, Matrix.mul_assoc, Matrix.nonsing_inv_mul q hqdet,
      Matrix.mul_one]
  have hAinvqinv : A⁻¹ * q⁻¹ = q * (L⁻¹ * L⁻¹) := by
    rw [hAinv, Matrix.mul_assoc, Matrix.mul_nonsing_inv q hqdet,
      Matrix.mul_one]
  have hLinvSq : L⁻¹ * (L * L) = L := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLdet, Matrix.one_mul]
  have hLSqInv : L * (L⁻¹ * L⁻¹) = L⁻¹ := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv L hLdet, Matrix.one_mul]
  change
    (matVecMul (matTranspose L) p, matVecMul L⁻¹ r) =
        (matVecMul L⁻¹ rStar, matVecMul (matTranspose L) pStar) ↔
      (matVecMul q⁻¹ rStar, matVecMul (matTranspose q) pStar) =
        blockMatVecMul (Book.Ch02.constantBlockMatrix A)
          (matVecMul (matTranspose q) p, matVecMul q⁻¹ r)
  rw [blockMatVecMul_constantBlockMatrix_of_isSymm
    (isSymm_of_isHermitian hA.isHermitian)]
  simp only [hLT, hqT, Prod.mk.injEq]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    have hrStar : rStar = matVecMul (L * L) p := by
      symm
      calc
        matVecMul (L * L) p = matVecMul L (matVecMul L p) := by
          rw [matVecMul_mul]
        _ = matVecMul L (matVecMul L⁻¹ rStar) := by rw [hfirst]
        _ = rStar := by
          rw [matVecMul_mul, Matrix.mul_nonsing_inv L hLdet, matVecMul_one]
    have hpStar : pStar = matVecMul (L⁻¹ * L⁻¹) r := by
      symm
      calc
        matVecMul (L⁻¹ * L⁻¹) r =
            matVecMul L⁻¹ (matVecMul L⁻¹ r) := by
          rw [matVecMul_mul]
        _ = matVecMul L⁻¹ (matVecMul L pStar) := by rw [hsecond]
        _ = pStar := by
          rw [matVecMul_mul, Matrix.nonsing_inv_mul L hLdet, matVecMul_one]
    constructor
    · calc
        matVecMul q⁻¹ rStar =
            matVecMul q⁻¹ (matVecMul (L * L) p) := by rw [hrStar]
        _ = matVecMul (q⁻¹ * (L * L)) p := by rw [matVecMul_mul]
        _ = matVecMul (A * q) p := by rw [hAq]
        _ = matVecMul A (matVecMul q p) := by rw [matVecMul_mul]
    · calc
        matVecMul q pStar =
            matVecMul q (matVecMul (L⁻¹ * L⁻¹) r) := by rw [hpStar]
        _ = matVecMul (q * (L⁻¹ * L⁻¹)) r := by rw [matVecMul_mul]
        _ = matVecMul (A⁻¹ * q⁻¹) r := by rw [hAinvqinv]
        _ = matVecMul A⁻¹ (matVecMul q⁻¹ r) := by rw [matVecMul_mul]
  · rintro ⟨hfirst, hsecond⟩
    have hrStar : rStar = matVecMul (L * L) p := by
      apply Matrix.mulVec_injective_of_isUnit
        ((Matrix.isUnit_nonsing_inv_iff).2 hq.isUnit)
      calc
        matVecMul q⁻¹ rStar = matVecMul A (matVecMul q p) := hfirst
        _ = matVecMul (A * q) p := by rw [matVecMul_mul]
        _ = matVecMul (q⁻¹ * (L * L)) p := by rw [hAq]
        _ = matVecMul q⁻¹ (matVecMul (L * L) p) := by rw [matVecMul_mul]
    have hpStar : pStar = matVecMul (L⁻¹ * L⁻¹) r := by
      apply Matrix.mulVec_injective_of_isUnit hq.isUnit
      calc
        matVecMul q pStar = matVecMul A⁻¹ (matVecMul q⁻¹ r) := hsecond
        _ = matVecMul (A⁻¹ * q⁻¹) r := by rw [matVecMul_mul]
        _ = matVecMul (q * (L⁻¹ * L⁻¹)) r := by rw [hAinvqinv]
        _ = matVecMul q (matVecMul (L⁻¹ * L⁻¹) r) := by
          rw [matVecMul_mul]
    constructor
    · calc
        matVecMul L p = matVecMul (L⁻¹ * (L * L)) p := by rw [hLinvSq]
        _ = matVecMul L⁻¹ (matVecMul (L * L) p) := by rw [matVecMul_mul]
        _ = matVecMul L⁻¹ rStar := by rw [hrStar]
    · calc
        matVecMul L⁻¹ r = matVecMul (L * (L⁻¹ * L⁻¹)) r := by rw [hLSqInv]
        _ = matVecMul L (matVecMul (L⁻¹ * L⁻¹) r) := by
          rw [matVecMul_mul]
        _ = matVecMul L pStar := by rw [hpStar]
@[expose]
public def inverseCenteredPrimalLoad {d : ℕ} [NeZero d]
    (abar : Mat d) (P : BlockVec d) : BlockVec d :=
  let alpha := Real.sqrt (specBound (symmPart abar)⁻¹)
  let p := alpha • P.1
  (p, alpha⁻¹ • P.2 + matVecMul (skewPart abar) p)
@[expose]
public def inverseCenteredDualLoad {d : ℕ} [NeZero d]
    (abar : Mat d) (Q : BlockVec d) : BlockVec d :=
  let alpha := Real.sqrt (specBound (symmPart abar)⁻¹)
  let pStar := alpha • Q.2
  (alpha⁻¹ • Q.1 + matVecMul (skewPart abar) pStar, pStar)
private theorem centeredPrimalLoad_inverseCenteredPrimalLoad
    {d : ℕ} [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (P : BlockVec d) :
    scalarNormalizedPrimalLoad
        (Real.sqrt (specBound (symmPart abar)⁻¹))
        (skewCenteredPrimalLoad (skewPart abar)
          (inverseCenteredPrimalLoad abar P)) = P := by
  rcases P with ⟨p, r⟩
  let alpha := Real.sqrt (specBound (symmPart abar)⁻¹)
  have halpha : 0 < alpha := by
    exact Real.sqrt_pos.mpr (by
      simpa only [alpha] using normalizedRootScale_pos hS)
  rw [Prod.mk.injEq]
  constructor
  · simp only [scalarNormalizedPrimalLoad, skewCenteredPrimalLoad,
      inverseCenteredPrimalLoad, alpha, smul_smul,
      inv_mul_cancel₀ halpha.ne', one_smul]
  · simp only [scalarNormalizedPrimalLoad, skewCenteredPrimalLoad,
      inverseCenteredPrimalLoad, alpha, add_sub_cancel_right, smul_smul,
      mul_inv_cancel₀ halpha.ne', one_smul]
private theorem centeredDualLoad_inverseCenteredDualLoad
    {d : ℕ} [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (Q : BlockVec d) :
    scalarNormalizedDualLoad
        (Real.sqrt (specBound (symmPart abar)⁻¹))
        (skewCenteredDualLoad (skewPart abar)
          (inverseCenteredDualLoad abar Q)) = Q := by
  rcases Q with ⟨rStar, pStar⟩
  let alpha := Real.sqrt (specBound (symmPart abar)⁻¹)
  have halpha : 0 < alpha := by
    exact Real.sqrt_pos.mpr (by
      simpa only [alpha] using normalizedRootScale_pos hS)
  rw [Prod.mk.injEq]
  constructor
  · simp only [scalarNormalizedDualLoad, skewCenteredDualLoad,
      inverseCenteredDualLoad, alpha, add_sub_cancel_right, smul_smul,
      mul_inv_cancel₀ halpha.ne', one_smul]
  · simp only [scalarNormalizedDualLoad, skewCenteredDualLoad,
      inverseCenteredDualLoad, alpha, smul_smul,
      inv_mul_cancel₀ halpha.ne', one_smul]
private theorem normalizedReferencePrimalLoad_inverseCenteredPrimalLoad
    {d : ℕ} [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (P : BlockVec d) :
    normalizedReferencePrimalLoad abar (inverseCenteredPrimalLoad abar P) =
      affineReferencePrimalLoad (Selection.normalizedRoot (symmPart abar)) P := by
  change affineReferencePrimalLoad (Selection.normalizedRoot (symmPart abar))
    (scalarNormalizedPrimalLoad
      (Real.sqrt (specBound (symmPart abar)⁻¹))
      (skewCenteredPrimalLoad (skewPart abar)
        (inverseCenteredPrimalLoad abar P))) = _
  rw [centeredPrimalLoad_inverseCenteredPrimalLoad hS P]
private theorem normalizedReferenceDualLoad_inverseCenteredDualLoad
    {d : ℕ} [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (Q : BlockVec d) :
    normalizedReferenceDualLoad abar (inverseCenteredDualLoad abar Q) =
      affineReferenceDualLoad (Selection.normalizedRoot (symmPart abar)) Q := by
  change affineReferenceDualLoad (Selection.normalizedRoot (symmPart abar))
    (scalarNormalizedDualLoad
      (Real.sqrt (specBound (symmPart abar)⁻¹))
      (skewCenteredDualLoad (skewPart abar)
        (inverseCenteredDualLoad abar Q))) = _
  rw [centeredDualLoad_inverseCenteredDualLoad hS Q]
private theorem doubledResponseJ_normalizedCenteredCoeff_inverseLoads
    {d : ℕ} [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (U : Book.Ch02.Domain d)
    (P Q : BlockVec d) :
    Book.Ch02.doubledResponseJ U
        ((normalizedCenteredCoeff a abar hS).coeffOn U) P Q =
      Book.Ch02.doubledResponseJ U (a.coeffOn U)
        (inverseCenteredPrimalLoad abar P)
        (inverseCenteredDualLoad abar Q) := by
  let c := specBound (symmPart abar)⁻¹
  have hc : 0 < c := by
    simpa only [c] using normalizedRootScale_pos hS
  have hscale := doubledResponseJ_positiveScale c hc
    (a.subSkew (skewPart abar) (matTranspose_skewPart abar)) U
    (skewCenteredPrimalLoad (skewPart abar)
      (inverseCenteredPrimalLoad abar P))
    (skewCenteredDualLoad (skewPart abar)
      (inverseCenteredDualLoad abar Q))
  have hskew := doubledResponseJ_subSkew (U := U) a (skewPart abar)
    (matTranspose_skewPart abar)
    (inverseCenteredPrimalLoad abar P)
    (inverseCenteredDualLoad abar Q)
  rw [centeredPrimalLoad_inverseCenteredPrimalLoad hS P,
    centeredDualLoad_inverseCenteredDualLoad hS Q] at hscale
  simpa only [normalizedCenteredCoeff, c] using hscale.trans hskew
private theorem canonicalNormalizedResponseLoads
    {d : ℕ} [NeZero d] {A : Mat d} {lam Lam : ℝ}
    (hA : IsEllipticMatrix lam Lam A) (e : FullBlockVec d)
    (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    let P : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt A) e)
    let Q : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt A) e)
    Q = blockMatVecMul (Book.Ch02.constantBlockMatrix A) P ∧
      blockVecDot P (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) = 1 := by
  let M := Book.Ch02.constantFullBlockMatrix A
  let S := Book.Ch02.constantFullBlockMatrixSqrt A
  let P : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt A) e)
  let Q : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt A) e)
  have hMpos : M.PosDef := by
    simpa only [M] using
      Book.Ch02.constantFullBlockMatrix_posDef_of_isEllipticMatrix hA
  have hSunit : IsUnit S := by
    dsimp [S, M, Book.Ch02.constantFullBlockMatrixSqrt]
    simpa using
      (CFC.isUnit_sqrt_iff M (ha := hMpos.posSemidef.nonneg)).2 hMpos.isUnit
  have hSdet : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det (A := S)).mp hSunit
  have hPfull : toFullBlockVec P = Matrix.mulVec S⁻¹ e := by
    simp only [P, toFullBlockVec_ofFullBlockVec,
      Book.Ch02.constantFullBlockMatrixInvSqrt, S]
  have hSP : Matrix.mulVec S (toFullBlockVec P) = e := by
    rw [hPfull, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hSdet]
    exact Matrix.one_mulVec e
  have hquad : blockVecDot P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) = 1 := by
    have hnorm :=
      Book.Ch02.fullBlockVecNormSq_constantFullBlockMatrixSqrt_mul_toFullBlockVec_eq
        hA P
    rw [hSP, he] at hnorm
    exact hnorm.symm
  have hsq : S * S = M := by
    have hsqrt := CFC.sq_sqrt M (ha := hMpos.posSemidef.nonneg)
    simpa only [S, M, Book.Ch02.constantFullBlockMatrixSqrt, pow_two] using hsqrt
  have hMSinv : M * S⁻¹ = S := by
    rw [← hsq, Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet,
      Matrix.mul_one]
  have hdual : Q =
      blockMatVecMul (Book.Ch02.constantBlockMatrix A) P := by
    rw [← ofFullBlockVec_toFullBlockVec
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P)]
    dsimp only [Q]
    congr 1
    rw [toFullBlockVec_blockMatVecMul, hPfull]
    change Matrix.mulVec S e = Matrix.mulVec M (Matrix.mulVec S⁻¹ e)
    rw [Matrix.mulVec_mulVec, hMSinv]
  exact ⟨hdual, hquad⟩
@[expose]
public def baseRoundedPhysicalResponseValueSet {d : ℕ} [NeZero d]
    {geom : RoundedGenerationAnalyticGeometry d}
    (a : CoeffSpace d) (abar : Mat d) (k : ℤ) (w : Fin d → ℤ) : Set ℝ :=
  {r : ℝ | ∃ e : FullBlockVec d, ∃ P Q : BlockVec d,
    Book.Ch02.fullBlockVecNormSq e = 1 ∧
      normalizedReferencePrimalLoad abar P = ofFullBlockVec e ∧
      normalizedReferenceDualLoad abar Q = ofFullBlockVec e ∧
      r = Transport.coeffSpaceDoubledResponse
        (adaptedCellAt (geom.grid (symmPart abar)) k w) a P Q}
private theorem normalizedBlockResponseValueSet_eq_baseRoundedPhysical
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (b : Book.Ch03.CoeffFamily d)
    (hb : ∀ R : TriadicCube d,
      (b.coeffOn R).toCoeffField =
        affineCoefficient (geom.grid (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (geom.grid_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (geom.grid_posDef hS) 0)).toCoeffField)
    (k : ℤ) (w : Fin d → ℤ) :
    Book.Ch02.normalizedBlockResponseValueSet
        (translateCube w (originCube d k)) b
        (geom.referenceMatrix abar hS) =
      baseRoundedPhysicalResponseValueSet (geom := geom) a abar k w := by
  classical
  let L := Selection.normalizedRoot (symmPart abar)
  let q := geom.grid (symmPart abar)
  let A := geom.referenceMatrix abar hS
  let R := translateCube w (originCube d k)
  let U := Response.adaptedDomainAt (geom.grid_posDef hS) k w
  have hL : L.PosDef := by
    simpa only [L] using normalizedRoot_posDef_of_posDef hS
  have hq : q.PosDef := by
    simpa only [q] using geom.grid_posDef hS
  have hAell : IsEllipticMatrix (99 / 100 : ℝ) (101 / 100 : ℝ) A := by
    simpa only [A] using! geom.reference_elliptic abar hS
  ext z
  constructor
  · rintro ⟨e, he, rfl⟩
    let P₀ : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt A) e)
    let Q₀ : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt A) e)
    obtain ⟨hQ₀Raw, hquadRaw⟩ := canonicalNormalizedResponseLoads hAell e he
    have hQ₀ : Q₀ =
        blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀ := by
      simpa only [P₀, Q₀] using hQ₀Raw
    have hquad : blockVecDot P₀
        (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀) = 1 := by
      simpa only [P₀] using hquadRaw
    let P := inverseAffinePrimalLoad q P₀
    let Q := inverseAffineDualLoad q Q₀
    have hP₀ : affineReferencePrimalLoad q P = P₀ := by
      simpa only [P] using affineReferencePrimalLoad_inverseAffinePrimalLoad hq P₀
    have hQ₀' : affineReferenceDualLoad q Q = Q₀ := by
      simpa only [Q] using affineReferenceDualLoad_inverseAffineDualLoad hq Q₀
    have hcommon : affineReferencePrimalLoad L P =
        affineReferenceDualLoad L Q := by
      apply (roundedAffineLoad_common_iff_constantBlock abar hS P Q).2
      rw [hP₀, hQ₀', hQ₀]
    let X : BlockVec d := affineReferencePrimalLoad L P
    let ePhysical : FullBlockVec d := toFullBlockVec X
    let PPhysical := inverseCenteredPrimalLoad abar P
    let QPhysical := inverseCenteredDualLoad abar Q
    have hXcommon : X = affineReferenceDualLoad L Q := by
      simpa only [X] using hcommon
    have hXX : blockVecDot X X = 1 := by
      calc
        blockVecDot X X =
            blockVecDot X (affineReferenceDualLoad L Q) := by rw [hXcommon]
        _ = blockVecDot P Q := by
          simpa only [X] using blockVecDot_affineReferenceLoads_direct hL P Q
        _ = blockVecDot
            (affineReferencePrimalLoad q P)
            (affineReferenceDualLoad q Q) :=
          (blockVecDot_affineReferenceLoads_direct hq P Q).symm
        _ = blockVecDot P₀ Q₀ := by rw [hP₀, hQ₀']
        _ = 1 := by rw [hQ₀]; exact hquad
    have hePhysical : Book.Ch02.fullBlockVecNormSq ePhysical = 1 := by
      simpa only [ePhysical, X, Book.Ch02.fullBlockVecNormSq,
        blockVecDot, vecDot, toFullBlockVec, Fintype.sum_sum_type,
        pow_two] using hXX
    have hPPhysical : normalizedReferencePrimalLoad abar PPhysical =
        ofFullBlockVec ePhysical := by
      calc
        normalizedReferencePrimalLoad abar PPhysical =
            affineReferencePrimalLoad L P := by
          simpa only [PPhysical, L] using
            normalizedReferencePrimalLoad_inverseCenteredPrimalLoad hS P
        _ = X := rfl
        _ = ofFullBlockVec ePhysical := by
          simp only [ePhysical, ofFullBlockVec_toFullBlockVec]
    have hQPhysical : normalizedReferenceDualLoad abar QPhysical =
        ofFullBlockVec ePhysical := by
      calc
        normalizedReferenceDualLoad abar QPhysical =
            affineReferenceDualLoad L Q := by
          simpa only [QPhysical, L] using
            normalizedReferenceDualLoad_inverseCenteredDualLoad hS Q
        _ = X := hcommon.symm
        _ = ofFullBlockVec ePhysical := by
          simp only [ePhysical, ofFullBlockVec_toFullBlockVec]
    have hcov := doubledResponseJ_affineResponseCell hq 0 k w
      (normalizedCenteredCoeff a abar hS) b hb P Q
    rw [hP₀, hQ₀'] at hcov
    have hresponse :
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
            (b.coeffOn R) P₀ Q₀ =
          Transport.coeffSpaceDoubledResponse
            (adaptedCellAt q k w) a PPhysical QPhysical := by
      calc
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
            (b.coeffOn R) P₀ Q₀ =
          Book.Ch02.doubledResponseJ U
            ((normalizedCenteredCoeff a abar hS).coeffOn U) P Q := by
              simpa only [R, U, q] using hcov
        _ = Book.Ch02.doubledResponseJ U (a.coeffOn U)
            PPhysical QPhysical := by
          simpa only [PPhysical, QPhysical] using
            doubledResponseJ_normalizedCenteredCoeff_inverseLoads
              a abar hS U P Q
        _ = Transport.coeffSpaceDoubledResponse
            (adaptedCellAt q k w) a PPhysical QPhysical := by
          simpa only [U, q] using!
            (Transport.coeffSpaceDoubledResponse_eq_doubledResponseJ
              U a PPhysical QPhysical).symm
    refine ⟨ePhysical, PPhysical, QPhysical, hePhysical,
      hPPhysical, hQPhysical, ?_⟩
    simpa only [A, R, P₀, Q₀, q] using hresponse
  · rintro ⟨e, PPhysical, QPhysical, he,
      hPPhysical, hQPhysical, rfl⟩
    let alpha := Real.sqrt (specBound (symmPart abar)⁻¹)
    let P := scalarNormalizedPrimalLoad alpha
      (skewCenteredPrimalLoad (skewPart abar) PPhysical)
    let Q := scalarNormalizedDualLoad alpha
      (skewCenteredDualLoad (skewPart abar) QPhysical)
    let P₀ := affineReferencePrimalLoad q P
    let Q₀ := affineReferenceDualLoad q Q
    have hcommon : affineReferencePrimalLoad L P =
        affineReferenceDualLoad L Q := by
      change normalizedReferencePrimalLoad abar PPhysical =
        normalizedReferenceDualLoad abar QPhysical
      rw [hPPhysical, hQPhysical]
    have hQ₀ : Q₀ =
        blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀ := by
      simpa only [P₀, Q₀, A, q, L] using
        (roundedAffineLoad_common_iff_constantBlock abar hS P Q).1 hcommon
    have hquad : blockVecDot P₀
        (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀) = 1 := by
      rw [← hQ₀]
      calc
        blockVecDot P₀ Q₀ = blockVecDot P Q := by
          simpa only [P₀, Q₀] using
            blockVecDot_affineReferenceLoads_direct hq P Q
        _ = blockVecDot (affineReferencePrimalLoad L P)
            (affineReferenceDualLoad L Q) :=
          (blockVecDot_affineReferenceLoads_direct hL P Q).symm
        _ = blockVecDot (ofFullBlockVec e) (ofFullBlockVec e) := by
          change blockVecDot
              (normalizedReferencePrimalLoad abar PPhysical)
              (normalizedReferenceDualLoad abar QPhysical) = _
          rw [hPPhysical, hQPhysical]
        _ = Book.Ch02.fullBlockVecNormSq e :=
          blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq e
        _ = 1 := he
    have hmem :=
      Book.Ch02.normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
        R b hAell P₀ hquad
    rw [← hQ₀] at hmem
    have hcov := doubledResponseJ_affineResponseCell hq 0 k w
      (normalizedCenteredCoeff a abar hS) b hb P Q
    have hc : 0 < specBound (symmPart abar)⁻¹ := normalizedRootScale_pos hS
    have hscale := doubledResponseJ_positiveScale
      (specBound (symmPart abar)⁻¹) hc
      (a.subSkew (skewPart abar) (matTranspose_skewPart abar)) U
      (skewCenteredPrimalLoad (skewPart abar) PPhysical)
      (skewCenteredDualLoad (skewPart abar) QPhysical)
    have hskew := doubledResponseJ_subSkew (U := U) a (skewPart abar)
      (matTranspose_skewPart abar) PPhysical QPhysical
    have hcentered :
        Book.Ch02.doubledResponseJ U
            ((normalizedCenteredCoeff a abar hS).coeffOn U) P Q =
          Book.Ch02.doubledResponseJ U (a.coeffOn U) PPhysical QPhysical := by
      simpa only [P, Q, alpha, normalizedCenteredCoeff] using hscale.trans hskew
    have hresponse :
        Transport.coeffSpaceDoubledResponse
            (adaptedCellAt q k w) a PPhysical QPhysical =
          Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
            (b.coeffOn R) P₀ Q₀ := by
      calc
        Transport.coeffSpaceDoubledResponse
            (adaptedCellAt q k w) a PPhysical QPhysical =
          Book.Ch02.doubledResponseJ U (a.coeffOn U)
            PPhysical QPhysical := by
          simpa only [U, q] using!
            Transport.coeffSpaceDoubledResponse_eq_doubledResponseJ
              U a PPhysical QPhysical
        _ = Book.Ch02.doubledResponseJ U
            ((normalizedCenteredCoeff a abar hS).coeffOn U) P Q :=
          hcentered.symm
        _ = Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
            (b.coeffOn R) P₀ Q₀ := by
          simpa only [P₀, Q₀, R, U, q] using hcov.symm
    simpa only [A, R, q] using hresponse.symm ▸ hmem
private theorem normalizedBlockResponseMax_eq_baseRoundedPhysical
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (b : Book.Ch03.CoeffFamily d)
    (hb : ∀ R : TriadicCube d,
      (b.coeffOn R).toCoeffField =
        affineCoefficient (geom.grid (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (geom.grid_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (geom.grid_posDef hS) 0)).toCoeffField)
    (k : ℤ) (w : Fin d → ℤ) :
    Book.Ch02.normalizedBlockResponseMax
        (translateCube w (originCube d k)) b
        (geom.referenceMatrix abar hS) =
      geom.responseMax a abar hS k w := by
  unfold Book.Ch02.normalizedBlockResponseMax
    RoundedGenerationAnalyticGeometry.responseMax
    roundedNormalizedDoubledResponseMaxAtGeneration
  rw [normalizedBlockResponseValueSet_eq_baseRoundedPhysical
    a abar hS b hb k w]
  rfl
private theorem
    normalizedBlockResponseMax_roundedCenteredCoeffFamily_eq_baseRoundedPhysical
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef)
    (aRounded : Book.Ch03.CoeffFamily d)
    (hRounded : ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d))
    (k : ℤ) (w : Fin d → ℤ) :
    Book.Ch02.normalizedBlockResponseMax
        (translateCube w (originCube d k)) aRounded
        (geom.referenceMatrix abar hS) =
      geom.responseMax a abar hS k w := by
  let q : Mat d := geom.grid (symmPart abar)
  have hq : q.PosDef := by
    simpa only [q] using geom.grid_posDef hS
  obtain ⟨b, hb⟩ := exists_adaptedReferenceCoeffFamily hq 0
    (normalizedCenteredCoeff a abar hS)
  have hab : Book.Ch02.TriadicCoeffFamily.AEEq aRounded b := by
    intro Q
    unfold Book.Ch02.CoeffOn.AEEq
    rw [hRounded Q, hb Q]
    have hpull := affinePullbackCoeffSpace_ae q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (normalizedCenteredCoeff a abar hS)
    simpa only [volumeMeasureOn, RoundedGenerationAnalyticGeometry.centeredCoeffSpace,
      roundedCenteredCoeffSpaceAtGeneration, q,
      CoeffSpace.coeffOn_toCoeffField] using! ae_restrict_of_ae hpull
  calc
    Book.Ch02.normalizedBlockResponseMax
        (translateCube w (originCube d k)) aRounded
        (geom.referenceMatrix abar hS) =
      Book.Ch02.normalizedBlockResponseMax
        (translateCube w (originCube d k)) b
        (geom.referenceMatrix abar hS) :=
      Book.Ch02.normalizedBlockResponseMax_eq_ofAEEq hab _ _
    _ = geom.responseMax a abar hS k w :=
      normalizedBlockResponseMax_eq_baseRoundedPhysical a abar hS b
        (by simpa only [q] using hb) k w
private theorem
    maxDescendantNormalizedBlockResponseAtScale_roundedCenteredCoeffFamily_eq
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef)
    (aRounded : Book.Ch03.CoeffFamily d)
    (hRounded : ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d))
    (m : ℤ) (n : ℕ) :
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        (originCube d m) (m - (n : ℤ)) aRounded
        (geom.referenceMatrix abar hS) =
      Book.Ch02.finsetSupReal
        (Response.alignedIndex (geom.grid (symmPart abar))
          (m - (n : ℤ)) m)
        (fun w ↦ geom.responseMax
          a abar hS (m - (n : ℤ)) w) := by
  rw [maxDescendantNormalizedBlockResponseAtScale_originCube_eq_alignedIndex]
  rw [Response.alignedIndex_one_eq (geom.grid_posDef hS) (by omega)]
  apply Book.Ch02.finsetSupReal_congr
  intro w _hw
  exact
    normalizedBlockResponseMax_roundedCenteredCoeffFamily_eq_baseRoundedPhysical
      a abar hS aRounded hRounded (m - (n : ℤ)) w
private theorem cubeBesovNegativeVectorSeminormTwo_le_responseError
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch03.CoeffFamily d) (a0 : Mat d) (s : ℝ) (hs : 0 < s)
    (defect : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : IntegrableOn energy (cubeSet Q) volume)
    (hresp : CubeAverageFluxResponseControl Q
      (Book.Ch03.publicCoeffField Q a) a0 defect energy) :
    cubeBesovNegativeVectorSeminormTwo Q s defect ≤
      Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.sqrt ((4 : ℝ) * matNorm a0) *
          Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 *
            Real.sqrt (cubeAverage Q energy) := by
  let coeff : ℕ → ℝ := fun n ↦
    Book.Ch02.geometricWeight s 2 n *
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        Q (Q.scale - (n : ℤ)) a a0
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hdisc_nonneg : 0 ≤ Book.Ch02.geometricDiscount s 2 :=
    (Book.Ch02.book_geometricDiscount_pos hs2).le
  have hconst_nonneg : 0 ≤ (4 : ℝ) * matNorm a0 :=
    mul_nonneg (by norm_num) (matNorm_nonneg a0)
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hhom_nonneg : 0 ≤
      Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    apply Real.rpow_nonneg
    refine tsum_nonneg ?_
    intro n
    refine mul_nonneg ?_ ?_
    · simpa only [Book.Ch02.geometricWeight_eq_old] using
        geometricWeight_nonneg n (by nlinarith only [hs.le])
    · exact Real.rpow_nonneg
        (Book.Ch02.scaleResponseAtScale_infinity_nonneg Q
          (sub_le_self _ (Nat.cast_nonneg n)) a a0) _
  have hsum : Summable coeff := by
    simpa only [coeff] using
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 hs
  have hcoeff_nonneg : ∀ n : ℕ, 0 ≤ coeff n := by
    intro n
    dsimp only [coeff]
    exact mul_nonneg
      (by simpa only [Book.Ch02.geometricWeight_eq_old] using
        geometricWeight_nonneg n (by nlinarith only [hs.le]))
      (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        (sub_le_self _ (Nat.cast_nonneg n)) a a0)
  let B : ℝ :=
    Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
      Real.sqrt ((4 : ℝ) * matNorm a0) *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 *
          Real.sqrt (cubeAverage Q energy)
  have hB_nonneg : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hdisc_nonneg _)
          (Real.sqrt_nonneg _)) hhom_nonneg)
      (Real.sqrt_nonneg _)
  change cubeBesovNegativeVectorSeminormTwo Q s defect ≤ B
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s defect ?_
  intro N
  have hdepth : ∀ j ∈ Finset.range (N + 1),
      cubeBesovNegativeVectorDepthAverage Q defect j ≤
        ((4 : ℝ) * matNorm a0 *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            Q (Q.scale - (j : ℤ)) a a0) * cubeAverage Q energy := by
    intro j _hj
    have havg := cubeBesovNegativeVectorDepthAverage_le_fluxResponseEnergy
      (Book.Ch03.publicCoeffField Q a) a0 defect energy
        henergy_nonneg henergy_int hresp j
    rw [Book.Ch03.maxDescendantNormalizedBlockResponseAtScale_publicCoeffField_eq_ch02
      a Q (sub_le_self _ (by exact_mod_cast Nat.zero_le j)) a0] at havg
    exact havg
  have hpartial_sq :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N defect) ^ 2 ≤
        (Book.Ch02.geometricDiscount s 2)⁻¹ *
          ((4 : ℝ) * matNorm a0) *
            Finset.sum (Finset.range (N + 1)) coeff * cubeAverage Q energy := by
    calc
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N defect) ^ 2 ≤
          ∑ j ∈ Finset.range (N + 1),
            (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              (((4 : ℝ) * matNorm a0 *
                Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
                  Q (Q.scale - (j : ℤ)) a a0) * cubeAverage Q energy) :=
        sq_cubeBesovNegativeVectorPartialSeminormTwo_le_of_depthAverage_le
          Q s N defect hdepth
      _ = (Book.Ch02.geometricDiscount s 2)⁻¹ *
          ((4 : ℝ) * matNorm a0) *
            Finset.sum (Finset.range (N + 1)) coeff * cubeAverage Q energy := by
        calc
          ∑ j ∈ Finset.range (N + 1),
              (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                (((4 : ℝ) * matNorm a0 *
                  Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
                    Q (Q.scale - (j : ℤ)) a a0) * cubeAverage Q energy) =
            ∑ j ∈ Finset.range (N + 1),
              (Book.Ch02.geometricDiscount s 2)⁻¹ *
                ((4 : ℝ) * matNorm a0) * coeff j * cubeAverage Q energy := by
            apply Finset.sum_congr rfl
            intro j _hj
            have hweight :
                (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
                  (Book.Ch02.geometricDiscount s 2)⁻¹ *
                    Book.Ch02.geometricWeight s 2 j := by
              calc
                (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
                    Real.rpow (3 : ℝ) ((-s * (j : ℝ)) * 2) := by
                  simpa [Real.rpow_natCast] using
                    (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                      (-s * (j : ℝ)) (2 : ℝ)).symm
                _ = Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) := by ring_nf
                _ = (Book.Ch02.geometricDiscount s 2)⁻¹ *
                    Book.Ch02.geometricWeight s 2 j :=
                  by simpa only [Book.Ch02.geometricDiscount_eq_old,
                      Book.Ch02.geometricWeight_eq_old] using
                    rpow_neg_two_mul_s_nat_eq_inv_geometricDiscount_mul_geometricWeight_two
                      hs j
            rw [hweight]
            dsimp only [coeff]
            ring
          _ = (Book.Ch02.geometricDiscount s 2)⁻¹ *
              ((4 : ℝ) * matNorm a0) *
                Finset.sum (Finset.range (N + 1)) coeff * cubeAverage Q energy := by
            rw [Finset.mul_sum, Finset.sum_mul]
  have hfinite : Finset.sum (Finset.range (N + 1)) coeff ≤ ∑' n, coeff n :=
    hsum.sum_le_tsum _ (fun n _hn ↦ hcoeff_nonneg n)
  have hpartial_sq' :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N defect) ^ 2 ≤
        (Book.Ch02.geometricDiscount s 2)⁻¹ *
          ((4 : ℝ) * matNorm a0) *
            (∑' n, coeff n) * cubeAverage Q energy := by
    exact hpartial_sq.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfinite
        (mul_nonneg (inv_nonneg.mpr hdisc_nonneg) hconst_nonneg))
      henergy_avg_nonneg)
  have hhom_sq :
      (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0) ^ 2 =
        ∑' n, coeff n := by
    simpa only [coeff] using
      Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0
  have hB_sq : B ^ 2 =
      (Book.Ch02.geometricDiscount s 2)⁻¹ *
        ((4 : ℝ) * matNorm a0) *
          (∑' n, coeff n) * cubeAverage Q energy := by
    dsimp only [B]
    calc
      (Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
          Real.sqrt ((4 : ℝ) * matNorm a0) *
            Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 *
              Real.sqrt (cubeAverage Q energy)) ^ 2 =
        (Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ)) ^ 2 *
          (Real.sqrt ((4 : ℝ) * matNorm a0)) ^ 2 *
            (Book.Ch02.HomogenizationErrorOnCube Q s .infinity
              (.finite 2) a a0) ^ 2 *
                (Real.sqrt (cubeAverage Q energy)) ^ 2 := by ring
      _ = (Book.Ch02.geometricDiscount s 2)⁻¹ *
          ((4 : ℝ) * matNorm a0) *
            (∑' n, coeff n) * cubeAverage Q energy := by
        rw [sq_rpow_neg_half_eq_inv_of_nonneg hdisc_nonneg,
          Real.sq_sqrt hconst_nonneg, Real.sq_sqrt henergy_avg_nonneg,
          hhom_sq]
  rw [← hB_sq] at hpartial_sq'
  have habs := sq_le_sq.mp hpartial_sq'
  simpa only [abs_of_nonneg
      (cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N defect),
    abs_of_nonneg hB_nonneg] using habs
private theorem
    homogenizationErrorOnCube_roundedCenteredCoeffFamily_eq_baseRoundedSpatialWeakError
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef)
    (aRounded : Book.Ch03.CoeffFamily d)
    (hRounded : ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d))
    (s : ℝ) (m : ℤ) :
    Book.Ch02.HomogenizationErrorOnCube (originCube d m) s .infinity
        (.finite 2) aRounded (geom.referenceMatrix abar hS) =
      geom.spatialWeakError a abar hS s m := by
  unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
    Book.Ch02.HomogenizationErrorFinite
    RoundedGenerationAnalyticGeometry.spatialWeakError
    roundedGenerationSpatialWeakError
  rw [Real.sqrt_eq_rpow]
  change
    Real.rpow (∑' n : ℕ,
      Book.Ch02.geometricWeight s 2 n *
        Real.rpow
          (Book.Ch02.scaleResponseAtScale (originCube d m)
            (m - (n : ℤ)) .infinity aRounded
            (geom.referenceMatrix abar hS)) 2) (1 / 2 : ℝ) = _
  congr 1
  apply tsum_congr
  intro n
  rw [Book.Ch02.scaleResponseAtScale_infinity_rpow_two_eq
    (originCube d m) (by
      change m - (n : ℤ) ≤ m
      omega) aRounded (geom.referenceMatrix abar hS)]
  rw [maxDescendantNormalizedBlockResponseAtScale_roundedCenteredCoeffFamily_eq
    a abar hS aRounded hRounded m n]
  rfl
/-- The standard Chapter 2 homogenization error of the exact rounded
coefficient family is the physical rounded weak-error row.  This public
bridge exposes the identity already used internally by the rounded harmonic
comparison, without changing either response family. -/
theorem homogenizationErrorOnCube_eq_roundedGenerationSpatialWeakError
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef)
    (aRounded : Book.Ch03.CoeffFamily d)
    (hRounded : ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d))
    (s : ℝ) (m : ℤ) :
    Book.Ch02.HomogenizationErrorOnCube (originCube d m) s .infinity
        (.finite 2) aRounded (geom.referenceMatrix abar hS) =
      geom.spatialWeakError a abar hS s m :=
  homogenizationErrorOnCube_roundedCenteredCoeffFamily_eq_baseRoundedSpatialWeakError
    a abar hS aRounded hRounded s m
private theorem
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_roundedReference_mul
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (Q : TriadicCube d) (s : ℝ)
    (hs : 0 < s) (w : Vec d → Vec d)
    (hw : MemVectorL2 (cubeSet Q)
      (fun x ↦ matVecMul (geom.referenceMatrix abar hS) (w x))) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s w ≤
      (d : ℝ) * (100 / 99 : ℝ) *
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
          (fun x ↦ matVecMul (geom.referenceMatrix abar hS) (w x)) := by
  let A : Mat d := geom.referenceMatrix abar hS
  let G : Vec d → Vec d := fun x ↦ matVecMul A (w x)
  let D : ℝ := ∑ j : Fin d,
    cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
      (fun x ↦ G x j)
  have hAell : IsEllipticMatrix (99 / 100 : ℝ) (101 / 100 : ℝ) A := by
    simpa only [A] using! geom.reference_elliptic abar hS
  have hAsymm : A.IsSymm :=
    isSymm_of_isHermitian (geom.reference_posDef abar hS).isHermitian
  have hAdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hAell
  have hwPoint : ∀ x, w x = matVecMul A⁻¹ (G x) := by
    intro x
    dsimp only [G]
    rw [matVecMul_mul, Matrix.nonsing_inv_mul A hAdet, matVecMul_one]
  have hG : MemVectorL2 (cubeSet Q) G := by
    simpa only [G, A] using hw
  have hcomponent : ∀ (i : Fin d) (g : Vec d → ℝ),
      CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g →
        |cubeBesovPairing Q (fun x ↦ w x i) g| ≤ (100 / 99 : ℝ) * D := by
    intro i g hg
    have hgTwo : MeasureTheory.MemLp g (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
      have hmem := hg.memLp
      rw [show cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) by
        simpa [cubeBesovConjExponent] using
          (ENNReal.HolderConjugate.conjExponent_eq
            (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))] at hmem
      exact hmem
    have hGTwo : ∀ j : Fin d,
        MeasureTheory.MemLp (fun x ↦ G x j) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
      intro j
      exact
        Book.Ch01.Legacy.component_memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1
          Q hG j
    have htermInt : ∀ j : Fin d,
        MeasureTheory.Integrable
          (fun x ↦ A⁻¹ i j * (G x j * g x))
          (normalizedCubeMeasure Q) := by
      intro j
      exact ((hGTwo j).integrable_mul hgTwo).const_mul (A⁻¹ i j)
    have hpair :
        cubeBesovPairing Q (fun x ↦ w x i) g =
          ∑ j : Fin d, A⁻¹ i j *
            cubeBesovPairing Q (fun x ↦ G x j) g := by
      unfold cubeBesovPairing
      simp_rw [cubeAverage_eq_integral_normalizedCubeMeasure]
      have hfun :
          (fun x ↦ w x i * g x) =
            fun x ↦ ∑ j : Fin d, A⁻¹ i j * (G x j * g x) := by
        funext x
        rw [hwPoint x, matVecMul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      rw [hfun, MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _hj
        rw [MeasureTheory.integral_const_mul]
      · intro j _hj
        exact htermInt j
    rw [hpair]
    calc
      |∑ j : Fin d, A⁻¹ i j *
          cubeBesovPairing Q (fun x ↦ G x j) g| ≤
          ∑ j : Fin d,
            |A⁻¹ i j * cubeBesovPairing Q (fun x ↦ G x j) g| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin d, |A⁻¹ i j| *
          |cubeBesovPairing Q (fun x ↦ G x j) g| := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [abs_mul]
      _ ≤ ∑ j : Fin d, (100 / 99 : ℝ) *
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x ↦ G x j) := by
        apply Finset.sum_le_sum
        intro j _hj
        have hentryRaw := abs_apply_symmPartInv_le_of_isEllipticMatrix hAell i j
        have hentry : |A⁻¹ i j| ≤ (100 / 99 : ℝ) := by
          rw [symmPart_eq_of_isSymm hAsymm] at hentryRaw
          norm_num at hentryRaw ⊢
          exact hentryRaw
        have hpairNorm :=
          abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp
            Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x ↦ G x j) g hs
            (hGTwo j) (by norm_num) (by norm_num) (by
              rw [show cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) by
                simpa [cubeBesovConjExponent] using
                  (ENNReal.HolderConjugate.conjExponent_eq
                    (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))]
              norm_num) (by norm_num) hg
        exact mul_le_mul hentry hpairNorm
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 100 / 99)
      _ = (100 / 99 : ℝ) * D := by
        rw [Finset.mul_sum]
  calc
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s w ≤
        cubeBesovScaleWeight s Q *
          ((Fintype.card (Fin d) : ℝ) * ((100 / 99 : ℝ) * D)) :=
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_card_mul
        Q s w hcomponent
    _ = (d : ℝ) * (100 / 99 : ℝ) *
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s G := by
      simp only [cubeScaleNormalizedDualNegativeBesovVectorNormTwo, D,
        Fintype.card_fin]
      ring
    _ = (d : ℝ) * (100 / 99 : ℝ) *
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
          (fun x ↦ matVecMul (geom.referenceMatrix abar hS) (w x)) := by
      rfl
private theorem matNorm_referenceMatrix_le_entry_budget
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    matNorm (geom.referenceMatrix abar hS) ≤
      ∑ _i : Fin d, ∑ _j : Fin d, (101 / 100 : ℝ) := by
  calc
    matNorm (geom.referenceMatrix abar hS) ≤
        ∑ i : Fin d, ∑ j : Fin d,
          |geom.referenceMatrix abar hS i j| :=
      Book.Ch02.matNorm_le_sum_abs_entries _
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (101 / 100 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact abs_apply_le_of_isEllipticMatrix
        (geom.reference_elliptic abar hS) i j
private theorem cubeLpNorm_originCube_pred_le_card_mul_printOrder
    {d : ℕ} (m : ℤ) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m))) :
    cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f ≤
      ((3 ^ d : ℕ) : ℝ) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f := by
  have hraw :=
    CubeCalderonZygmund.eLpNorm_centralDescendant_le_descendantCount_mul
      (originCube d m) 1 FiniteLpExponent.two f
  rw [centralDescendant_originCube_eq_originCube_sub] at hraw
  have htop :
      ENNReal.ofReal ((3 ^ d : ℕ) : ℝ) *
          MeasureTheory.eLpNorm f 2
            (normalizedCubeMeasure (originCube d m)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hraw' :
      MeasureTheory.eLpNorm f 2
          (normalizedCubeMeasure (originCube d (m - 1))) ≤
        ENNReal.ofReal ((3 ^ d : ℕ) : ℝ) *
          MeasureTheory.eLpNorm f 2
            (normalizedCubeMeasure (originCube d m)) := by
    simpa using hraw
  have hreal := ENNReal.toReal_mono htop hraw'
  simpa [cubeLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    Nat.cast_nonneg] using hreal
private theorem cubeLpNorm_eq_of_ae_eq_on_parent_cube
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} {f g : Vec d → ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hfg : f =ᵐ[volumeMeasureOn (cubeSet Q)] g) :
    cubeLpNorm R (2 : ℝ≥0∞) f = cubeLpNorm R (2 : ℝ≥0∞) g := by
  have hvol : f =ᵐ[MeasureTheory.volume.restrict (cubeSet R)] g := by
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (cubeSet_subset_of_mem_descendantsAtDepth hR)
      (by simpa only [volumeMeasureOn] using! hfg)
  have hnorm : f =ᵐ[normalizedCubeMeasure R] g := by
    simpa only [normalizedCubeMeasure, cubeMeasure] using!
      MeasureTheory.Measure.ae_smul_measure hvol
        (ENNReal.ofReal ((cubeVolume R)⁻¹))
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae hnorm]
private theorem
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d} (s : ℝ)
    (hFG : F =ᵐ[volumeMeasureOn (cubeSet Q)] G) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F =
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s G := by
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  exact Book.Ch03.cubeBesovDualFullNorm_eq_of_ae_eq_on_cubeSet
    s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (hFG.fun_comp fun z ↦ z i)
private theorem zeroTraceDifference_childDistance_le_dualGradient
    {d : ℕ} [NeZero d] (m : ℤ) (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (u v : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (w : H10Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hw : w.toH1Function.toFun =ᵐ[volumeMeasureOn
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x ↦ u.toFun x - v.toFun x) :
    cubeBesovScaleWeight 1 (originCube d m) *
      cubeLpNorm (originCube d (m - 1)) 2 (fun x ↦ u.toFun x - v.toFun x) ≤
      (((3 ^ d : ℕ) : ℝ) *
        ((((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) +
          2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          Real.sqrt ((1 - Real.rpow 3 (-2 * ((1 / 2 : ℝ) - s)))⁻¹)) *
        besovExponentLossGap (2 * s) s) *
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo (originCube d m) s
        (fun x ↦ u.grad x - v.grad x) := by
  let Q := originCube d m
  let wdiff : Vec d → Vec d := fun x ↦ u.grad x - v.grad x
  let Kg : ℝ := besovExponentLossGap (2 * s) s
  let Kp : ℝ :=
    ((((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) +
        2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      Real.sqrt ((1 - Real.rpow 3 (-2 * ((1 / 2 : ℝ) - s)))⁻¹))
  let Kc : ℝ := ((3 ^ d : ℕ) : ℝ)
  let wCube := Book.Ch03.publicH10ToCubeSet w
  have hwCube : w.toH1Function.toFun =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x ↦ u.toFun x - v.toFun x := by
    simpa [Q, volumeMeasureOn, Book.Ch02.cubeDomain_coe,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hw
  have hgradCube : wCube.toH1Function.grad =ᵐ[volumeMeasureOn (cubeSet Q)] wdiff := by
    have hgrad := Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (Book.Ch02.cubeDomain Q).isOpen
      (u := w.toH1Function) (v := u - v) (by
        simpa only [H1Function.sub_toFun] using hw)
    rw [H1Function.sub_grad] at hgrad
    simp only [wCube, wdiff, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      Book.Ch03.publicH10ToCubeSet_toH1Function_grad]
    exact hgrad
  have hdualGrad : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
      wCube.toH1Function.grad =
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff :=
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet
      s hgradCube
  have hgap : 0 ≤ Kg := by
    exact besovExponentLossGap_nonneg hs (by nlinarith only [hs])
  have hneg := (concreteNegativeFromDualExponentLoss_geometric d).2 Q
    wCube.toH1Function.grad (s := 2 * s) (t := s) hs
    (by nlinarith only [hs]) (by nlinarith only [hs_lt])
    wCube.toH1Function.grad_memVectorL2
  have hKp : 0 ≤ Kp := by
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d)
          (Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d))
          (Real.rpow_nonneg (by norm_num) _)) (Nat.cast_nonneg d))
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)))
      (Real.sqrt_nonneg _)
  have hpoincare :=
    Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
      Q wCube hs hs_lt
  have hparent : cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ w.toH1Function.toFun x) ≤
      Kp * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff := by
    calc
      _ ≤ Kp * cubeBesovNegativeVectorSeminormTwo Q (2 * s)
          wCube.toH1Function.grad := by
            simpa only [Kp, wCube,
              Book.Ch03.publicH10ToCubeSet_toH1Function_toFun] using hpoincare
      _ ≤ Kp * (1 * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
          wCube.toH1Function.grad) := mul_le_mul_of_nonneg_left hneg hKp
      _ = Kp * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff := by
        rw [hdualGrad]
        ring
  have hchild : cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
      (fun x ↦ u.toFun x - v.toFun x) ≤
      Kc * cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ w.toH1Function.toFun x) := by
    have hdesc : originCube d (m - 1) ∈ descendantsAtDepth Q 1 := by
      simpa only [Q, centralDescendant_originCube_eq_originCube_sub] using!
        CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth Q 1
    rw [← cubeLpNorm_eq_of_ae_eq_on_parent_cube hdesc hwCube]
    simpa only [Kc, Q] using cubeLpNorm_originCube_pred_le_card_mul_printOrder m
      (fun x ↦ w.toH1Function.toFun x)
      (by simpa only [wCube,
          Book.Ch03.publicH10ToCubeSet_toH1Function_toFun,
          H10Function.toOpenCubeSet_toH1Function_toFun] using
        wCube.toOpenCubeSet.toH1Function.memL2_normalizedCubeMeasure)
  have hl20 : cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
        (fun x ↦ u.toFun x - v.toFun x) ≤ Kc * Kp * Kg *
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff := by
    calc
      _ ≤ cubeBesovScaleWeight (1 : ℝ) Q *
          (Kc * cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ w.toH1Function.toFun x)) :=
        mul_le_mul_of_nonneg_left hchild (cubeBesovScaleWeight_nonneg 1 Q)
      _ = Kc * (cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ w.toH1Function.toFun x)) := by ring
      _ ≤ Kc * (Kp * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q s wdiff) := mul_le_mul_of_nonneg_left hparent (by positivity)
      _ = Kc * Kp * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q s wdiff := by ring
  exact hl20

private theorem responseSeminorm_le_matrixBudget
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (hs : 0 < s) (F : Vec d → Vec d)
    (matrix : Mat d) (budget error energy : ℝ)
    (hmatrix : matNorm matrix ≤ budget) (herror : 0 ≤ error) (henergy : 0 ≤ energy)
    (hresponse : cubeBesovNegativeVectorSeminormTwo Q s F ≤
      Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.sqrt (4 * matNorm matrix) * error * energy) :
    cubeBesovNegativeVectorSeminormTwo Q s F ≤
      (Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.sqrt (4 * budget)) * error * energy := by
  have hsqrt : Real.sqrt (4 * matNorm matrix) ≤ Real.sqrt (4 * budget) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmatrix (by norm_num))
  have hdiscount : 0 ≤ Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) :=
    Real.rpow_nonneg
      (Book.Ch02.book_geometricDiscount_pos (by positivity : 0 < s * 2)).le _
  exact hresponse.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt hdiscount) herror) henergy)

private theorem comparisonFlux_ae_eq_referenceGradient_add_defect
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (aRounded : Book.Ch03.CoeffFamily d)
    (a0 : Book.Ch03.ConstantCoeffMatrix d)
    (u v : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    Book.Ch03.homogenizationComparisonFluxField Q aRounded a0 u v
      =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x ↦ matVecMul a0.matrix (u.grad x - v.grad x) +
        fluxDefect (Book.Ch03.publicCoeffField Q aRounded) a0.matrix u.grad x := by
  have hbase :=
    Book.Ch03.homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
      (Q := Q) (a := aRounded) (a0 := a0) u v
  filter_upwards [hbase] with x hx
  rw [hx]
  ext i
  simp [fluxComparison, fluxDefect, matVecMul, sub_eq_add_neg, mul_add,
    Finset.sum_add_distrib]
  ring

/-- The printed finite response recurrence, specialized to the rounded
harmonic replacement and closed by the genuine-dual comparison. -/
theorem exists_roundedGenerationHarmonicComparisonSpecializationConstant
    (d : ℕ) [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (s Cdual : ℝ) (hs : 0 < s)
    (hs_lt : s < (1 : ℝ) / 2) (hCdual : 0 ≤ Cdual) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffSpace d) (abar : Mat d)
        (hS : (symmPart abar).PosDef)
        (aRounded : Book.Ch03.CoeffFamily d),
        (∀ R : TriadicCube d,
          (aRounded.coeffOn R).toCoeffField =
            (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d)) →
        ∀ (m : ℤ)
          (u : H1Function
            (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
          (hu : IsWeakSolutionOn
            (aRounded.coeffOn (originCube d m)).toCoeffField
            (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad),
          (∀ {w F : Vec d → Vec d},
            MemVectorL2 (cubeSet (originCube d m)) F →
            IsPotentialZeroTraceOn (cubeSet (originCube d m)) w →
            IsSolenoidalOn (cubeSet (originCube d m)) (fun x ↦
              matVecMul (geom.referenceMatrix abar hS) (w x) + F x) →
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                (originCube d m) s (fun x ↦
                  matVecMul (geom.referenceMatrix abar hS) (w x)) ≤
              Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                (originCube d m) s F ∧
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                (originCube d m) s (fun x ↦
                  matVecMul (geom.referenceMatrix abar hS) (w x) + F x) ≤
              Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                (originCube d m) s F) →
          let W := geom.harmonicReplacementDatum abar hS aRounded m u hu
          let E := geom.spatialWeakError a abar hS s m
          let A := Book.Ch03.h1EnergyNormOnCube
            (originCube d m) aRounded u
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d m) s (fun x ↦ u.grad x - W.v.grad x) ≤
            C * E * A ∧
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d m) s
              (Book.Ch03.homogenizationComparisonFluxField
                (originCube d m) aRounded
                (geom.referenceConstantCoeffMatrix abar hS) u W.v) ≤
            C * E * A ∧
          cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
              cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
                (fun x ↦ u.toFun x - W.v.toFun x) ≤ C * E * A := by
  let M : ℝ := ∑ _i : Fin d, ∑ _j : Fin d, (101 / 100 : ℝ)
  let Kr : ℝ := Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
    Real.sqrt ((4 : ℝ) * M)
  let Kd : ℝ := (d : ℝ) * Real.rpow 3 ((d : ℝ) + s)
  let Ki : ℝ := (d : ℝ) * (100 / 99 : ℝ)
  let Kg : ℝ := besovExponentLossGap (2 * s) s
  let Kp : ℝ :=
    ((((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) +
        2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      Real.sqrt ((1 - Real.rpow 3 (-2 * ((1 / 2 : ℝ) - s)))⁻¹))
  let Kc : ℝ := ((3 ^ d : ℕ) : ℝ)
  let B : ℝ := Kd * Kr
  let Cg : ℝ := Ki * Cdual * B
  let Cf : ℝ := Cdual * B
  let Cl : ℝ := Kc * Kp * Kg * Cg
  let C : ℝ := max 0 (max Cg (max Cf Cl))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a abar hS aRounded hRounded m u hu hdual
  let Q := originCube d m
  let a0 := geom.referenceConstantCoeffMatrix abar hS
  let A0 := geom.referenceMatrix abar hS
  let W := geom.harmonicReplacementDatum abar hS aRounded m u hu
  let E := geom.spatialWeakError a abar hS s m
  let A := Book.Ch03.h1EnergyNormOnCube Q aRounded u
  let F := fluxDefect (Book.Ch03.publicCoeffField Q aRounded) A0 u.grad
  let wdiff : Vec d → Vec d := fun x ↦ u.grad x - W.v.grad x
  have hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q aRounded
  have huWeak :=
    Book.Ch03.isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
      (isForcedEquation_zero_of_isWeakSolutionOn u hu)
  let uh : AHarmonicFunction (Book.Ch03.publicCoeffField Q aRounded)
      (cubeSet Q) :=
    { toH1 := Book.Ch03.publicH1ToCubeSet u
      isHarmonic := ⟨(Book.Ch03.publicH1ToCubeSet u).isPotentialOn, by
        simpa [Book.Ch03.publicH1ToCubeSet_grad] using
          huWeak.residual_solenoidal hEll MeasureTheory.MemLp.zero⟩ }
  let energy := scalarVariationEnergyIntegrand
    (Book.Ch03.publicCoeffField Q aRounded) uh
  let := isFiniteMeasureVolumeMeasureOnCubeSet Q
  have henergy0 : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    exact scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      (cubeSet Q) _ hEll uh
  have henergyInt : IntegrableOn energy (cubeSet Q) volume := by
    exact ResponseLinearIntegrabilityData.energy
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) uh
  have hresp : CubeAverageFluxResponseControl Q
      (Book.Ch03.publicCoeffField Q aRounded) A0 F energy := by
    simpa [F, energy, uh, fluxDefect, Book.Ch03.publicH1ToCubeSet_grad] using!
      cubeAverageFluxResponseControl_of_aHarmonicFunction Q
        (Book.Ch03.publicCoeffField Q aRounded) A0 hEll
        (geom.reference_elliptic abar hS)
        (isSymm_of_isHermitian
          (geom.reference_posDef abar hS).isHermitian) uh
  have hrec := cubeBesovNegativeVectorSeminormTwo_le_responseError
    Q aRounded A0 s hs F energy henergy0 henergyInt hresp
  have henergyFun : energy = coefficientEnergyDensity
      (Book.Ch03.publicCoeffField Q aRounded) u.grad := by
    funext x
    change vecDot ((Book.Ch03.publicH1ToCubeSet u).grad x)
        (matVecMul (symmPart (Book.Ch03.publicCoeffField Q aRounded x))
          ((Book.Ch03.publicH1ToCubeSet u).grad x)) = _
    rw [Book.Ch03.publicH1ToCubeSet_grad]
    rfl
  have henergyEq : Real.sqrt (cubeAverage Q energy) = A := by
    dsimp only [A]
    rw [Book.Ch03.h1EnergyNormOnCube_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField]
    rw [henergyFun]
  rw [homogenizationErrorOnCube_roundedCenteredCoeffFamily_eq_baseRoundedSpatialWeakError
    a abar hS aRounded hRounded s m, henergyEq] at hrec
  have hconcrete : cubeBesovNegativeVectorSeminormTwo Q s F ≤ Kr * E * A :=
    responseSeminorm_le_matrixBudget Q s hs F A0 M E A
      (by simpa only [A0, M] using matNorm_referenceMatrix_le_entry_budget abar hS)
      (geom.spatialWeakError_nonneg a abar hS s m)
      (by dsimp [A, Book.Ch03.h1EnergyNormOnCube]; exact Real.sqrt_nonneg _)
      (by simpa only [A0, E] using hrec)
  have hFmem : MemVectorL2 (cubeSet Q) F := by
    simpa only [Q, F, A0, a0, geom.referenceConstantCoeffMatrix_matrix] using
      Book.Ch03.publicH1_fluxDefect_memVectorL2_descendant_cubeSet
        (Q := Q) (R := Q) (a := aRounded) (a0 := a0) (j := 0) u (by simp)
  have hKd : 0 ≤ Kd := by
    exact mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (by norm_num) _)
  have hFdual : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F ≤
      B * E * A := by
    have hraw :=
      Book.Ch03.normalizedDualNegativeBesovNormTwo_le_constant_mul_negativeBesovSeminormTwo
        Q s F hs hFmem
    rw [Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo,
      Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight] at hraw
    calc
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F ≤
          Kd * cubeBesovNegativeVectorSeminormTwo Q s F := by
            simpa only [Kd] using! hraw
      _ ≤ Kd * (Kr * E * A) := mul_le_mul_of_nonneg_left hconcrete hKd
      _ = B * E * A := by dsimp only [B]; ring
  have hWu : W.u = u := by
    simpa only [W] using geom.harmonicReplacementDatum_u abar hS aRounded m u hu
  have hpair := W.isHomogenizationComparisonPairOn_publicCoeffField_cubeSet
  rw [hWu] at hpair
  have hpot : IsPotentialZeroTraceOn (cubeSet Q) wdiff := by
    simpa only [wdiff, W, Book.Ch03.publicH1ToCubeSet_grad] using hpair.2
  have hsol : IsSolenoidalOn (cubeSet Q)
      (fun x ↦ matVecMul A0 (wdiff x) + F x) := by
    simpa only [wdiff, F, A0, W, geom.referenceConstantCoeffMatrix_matrix,
      Book.Ch03.publicH1ToCubeSet_grad] using! hpair.comparisonPair_solenoidal
  obtain ⟨hAw, hflux⟩ := hdual hFmem hpot hsol
  have hwmem : MemVectorL2 (cubeSet Q) wdiff := by
    rcases hpot with ⟨w0, hw0⟩
    rw [← hw0]
    exact w0.toH1Function.grad_memVectorL2
  have hAwmem : MemVectorL2 (cubeSet Q) (fun x ↦ matVecMul A0 (wdiff x)) := by
    exact memVectorL2_matVecMul_of_isEllipticFieldOn
      (isEllipticFieldOn_constantCoeffField (measurableSet_cubeSet Q)
        (geom.reference_elliptic abar hS)) hwmem
  have hgrad0 : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff ≤
      Cg * E * A := by
    calc
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff ≤
          Ki * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
            (fun x ↦ matVecMul A0 (wdiff x)) := by
              simpa only [Ki, A0] using
                cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_roundedReference_mul
                  abar hS Q s hs wdiff hAwmem
      _ ≤ Ki * (Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F) :=
        mul_le_mul_of_nonneg_left hAw (by positivity)
      _ ≤ Ki * (Cdual * (B * E * A)) := by gcongr
      _ = Cg * E * A := by dsimp only [Cg]; ring
  have hfluxAE : Book.Ch03.homogenizationComparisonFluxField Q aRounded a0 u W.v
      =ᵐ[volumeMeasureOn (cubeSet Q)]
        fun x ↦ matVecMul A0 (wdiff x) + F x :=
    comparisonFlux_ae_eq_referenceGradient_add_defect Q aRounded a0 u W.v
  have hflux0 : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
      (Book.Ch03.homogenizationComparisonFluxField Q aRounded a0 u W.v) ≤
      Cf * E * A := by
    rw [cubeScaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet
      s hfluxAE]
    calc
      _ ≤ Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F := hflux
      _ ≤ Cdual * (B * E * A) := mul_le_mul_of_nonneg_left hFdual hCdual
      _ = Cf * E * A := by dsimp only [Cf]; ring
  obtain ⟨w, hw⟩ := W.zeroTraceDifference
  rw [hWu] at hw
  have hzeroTrace := zeroTraceDifference_childDistance_le_dualGradient
    m s hs hs_lt u W.v w hw
  have hgap : 0 ≤ Kg := besovExponentLossGap_nonneg hs (by nlinarith only [hs])
  have hKp : 0 ≤ Kp := by
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d)
          (Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d))
          (Real.rpow_nonneg (by norm_num) _)) (Nat.cast_nonneg d))
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)))
      (Real.sqrt_nonneg _)
  have hl20 : cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
        (fun x ↦ u.toFun x - W.v.toFun x) ≤ Cl * E * A := by
    calc
      _ ≤ Kc * Kp * Kg *
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff := hzeroTrace
      _ ≤ Kc * Kp * Kg * (Cg * E * A) := by gcongr
      _ = Cl * E * A := by dsimp only [Cl]; ring
  have hEA : 0 ≤ E * A := mul_nonneg
    (geom.spatialWeakError_nonneg a abar hS s m)
    (by dsimp [A, Book.Ch03.h1EnergyNormOnCube]; exact Real.sqrt_nonneg _)
  have hCgC : Cg ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCfC : Cf ≤ C :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hClC : Cl ≤ C :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · exact hgrad0.trans (by
      rw [mul_assoc Cg, mul_assoc C]
      exact mul_le_mul_of_nonneg_right hCgC hEA)
  · exact hflux0.trans (by
      rw [mul_assoc Cf, mul_assoc C]
      exact mul_le_mul_of_nonneg_right hCfC hEA)
  · exact hl20.trans (by
      rw [mul_assoc Cl, mul_assoc C]
      exact mul_le_mul_of_nonneg_right hClC hEA)
end
end HighContrast
end HCPolySupport
