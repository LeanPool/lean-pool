/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileDefectCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormComparison

/-!
# High-contrast homogenization: Provider.Response.ProfileDefectIdentities

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Identities and positivity for the response defects

Constant-skew covariance moves each recentered response to its corrected load.
The annealed quadratic identities then identify the two defects with the
corresponding recentered mean increments.  Mean order gives their signs.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The structural shear sends `(x,y)` to `(x,gx+y)`. -/
theorem profileDefect_blockG_mulVec (g : Mat d) (X : BlockVec d) :
    blockMatVecMul (blockG g) X = (X.1, matVecMul g X.1 + X.2) := by
  apply Prod.ext
  · change matVecMul 1 X.1 + matVecMul 0 X.2 = X.1
    rw [matVecMul_one, zero_matVecMul, add_zero]
  · change matVecMul g X.1 + matVecMul 1 X.2 = _
    rw [matVecMul_one]

/-- A quadratic form of the recentered mean is the original quadratic form at
the sheared load. -/
theorem profileRecenteredMean_quadratic (P : Measure (CoeffSpace d))
    (q g : Mat d) (k : ℤ) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (profileRecenteredMean P q g k) X) =
      blockVecDot (blockMatVecMul (blockG g) X)
        (blockMatVecMul (adaptedMean P q k)
          (blockMatVecMul (blockG g) X)) := by
  rw [blockVecDot_blockMatVecMul_eq_dotProduct,
    blockVecDot_blockMatVecMul_eq_dotProduct]
  simp only [profileRecenteredMean, toFullBlockMat_blockMatMul,
    toFullBlockMat_blockMatTranspose_conj,
    toFullBlockVec_blockMatVecMul]
  rw [← Matrix.mul_assoc]
  exact Initialization.quad_conj (toFullBlockMat (blockG g))
    (toFullBlockMat (adaptedMean P q k)) (toFullBlockVec X)

/-- A quadratic form of the recentered adjoint mean is the original quadratic
form at the signed, sheared load. -/
theorem profileRecenteredAdjointMean_quadratic
    (P : Measure (CoeffSpace d)) (q g : Mat d) (k : ℤ)
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (profileRecenteredAdjointMean P q g k) X) =
      blockVecDot
        (blockMatVecMul (blockG g)
          (blockMatVecMul (blockDiag 1 (-1)) X))
        (blockMatVecMul (adaptedMean P q k)
          (blockMatVecMul (blockG g)
            (blockMatVecMul (blockDiag 1 (-1)) X))) := by
  rw [profileRecenteredAdjointMean,
    blockQuadratic_adjointSign_congr,
    profileRecenteredMean_quadratic]

/-- Recentered mean order is inherited from the original mean order. -/
theorem profileRecenteredMean_le {P : Measure (CoeffSpace d)}
    {q g : Mat d} {s t : ℤ}
    (hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s)) :
    BlockMatLoewnerLE (profileRecenteredMean P q g t)
      (profileRecenteredMean P q g s) := by
  intro X
  rw [profileRecenteredMean_quadratic,
    profileRecenteredMean_quadratic]
  exact hmean _

/-- Recentered adjoint mean order is inherited from the original mean order. -/
theorem profileRecenteredAdjointMean_le {P : Measure (CoeffSpace d)}
    {q g : Mat d} {s t : ℤ}
    (hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s)) :
    BlockMatLoewnerLE (profileRecenteredAdjointMean P q g t)
      (profileRecenteredAdjointMean P q g s) := by
  intro X
  rw [profileRecenteredAdjointMean_quadratic,
    profileRecenteredAdjointMean_quadratic]
  exact hmean _

private theorem integrable_responseJ
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (p r : Vec d) :
    Integrable (fun a ↦ responseJ U (a.coeffOn U) p r) P := by
  let X : BlockVec d := (-p, r)
  have hquad := (integrable_coarseBlock_quadratic hint X).const_mul (1 / 2 : ℝ)
  have hsub := hquad.sub (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X] using! (responseJ_eq_coarseBlock U a p r).symm

private theorem integrable_adjoint_responseJ
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (p r : Vec d) :
    Integrable (fun a ↦ responseJ U (a.transpose.coeffOn U) p r) P := by
  let X : BlockVec d := (-p, r)
  let D := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  have hquad : Integrable (fun a ↦ blockVecDot X
      (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)) P := by
    have hbase := integrable_coarseBlock_quadratic hint D
    refine hbase.congr (Filter.Eventually.of_forall fun a ↦ ?_)
    change blockVecDot D
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) D) =
      blockVecDot X
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
    rw [coarseBlock_transpose a U, blockQuadratic_adjointSign_congr]
  have hsub := (hquad.const_mul (1 / 2 : ℝ)).sub
    (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X] using! (responseJ_eq_coarseBlock U a.transpose p r).symm

/-- Constant-skew covariance and integrability turn the primal expectation of
a difference into the difference of the two corrected-load expectations. -/
theorem profilePrimalResponseDefect_eq_corrected_integrals
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    profilePrimalResponseDefect P hq g hg s t p r =
      (∫ a, responseJ (adaptedDomain hq s)
        (a.coeffOn (adaptedDomain hq s)) p (r - matVecMul g p) ∂P) -
      ∫ a, responseJ (adaptedDomain hq t)
        (a.coeffOn (adaptedDomain hq t)) p (r - matVecMul g p) ∂P := by
  have hsint := integrable_responseJ (P := P)
    (U := adaptedDomain hq s) hints p (r - matVecMul g p)
  have htint := integrable_responseJ (P := P)
    (U := adaptedDomain hq t) hintt p (r - matVecMul g p)
  rw [profilePrimalResponseDefect_eq]
  calc
    (∫ a, responseJ (adaptedDomain hq s)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq s)) p r -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P) =
        ∫ a, responseJ (adaptedDomain hq s)
            (a.coeffOn (adaptedDomain hq s)) p (r - matVecMul g p) -
          responseJ (adaptedDomain hq t)
            (a.coeffOn (adaptedDomain hq t)) p (r - matVecMul g p) ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
      change responseJ (adaptedDomain hq s)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq s)) p r -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r = _
      rw [responseJ_subSkew (adaptedDomain hq s) a g hg p r,
        responseJ_subSkew (adaptedDomain hq t) a g hg p r]
    _ = _ := integral_sub hsint htint

/-- The primal defect is exactly one half of the recentered mean-increment
quadratic form. -/
theorem profilePrimalResponseDefect_identity
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    profilePrimalResponseDefect P hq g hg s t p r =
      (1 / 2 : ℝ) * blockVecDot ((-p, r) : BlockVec d)
        (blockMatVecMul
          (blockSub (profileRecenteredMean P q g s)
            (profileRecenteredMean P q g t))
          ((-p, r) : BlockVec d)) := by
  let r₀ : Vec d := r - matVecMul g p
  let X₀ : BlockVec d := (-p, r₀)
  have hload : blockMatVecMul (blockG g) ((-p, r) : BlockVec d) = X₀ := by
    rw [profileDefect_blockG_mulVec]
    apply Prod.ext
    · rfl
    · dsimp only [X₀, r₀]
      rw [matVecMul_neg]
      abel
  rw [profilePrimalResponseDefect_eq_corrected_integrals hq hg hints hintt]
  calc
    (∫ a, responseJ (adaptedDomain hq s)
          (a.coeffOn (adaptedDomain hq s)) p r₀ ∂P) -
        ∫ a, responseJ (adaptedDomain hq t)
          (a.coeffOn (adaptedDomain hq t)) p r₀ ∂P =
        ((1 / 2 : ℝ) * blockVecDot X₀
            (blockMatVecMul (adaptedMean P q s) X₀) - vecDot p r₀) -
          ((1 / 2 : ℝ) * blockVecDot X₀
            (blockMatVecMul (adaptedMean P q t) X₀) - vecDot p r₀) := by
      rw [annealed_responseJ_eq (adaptedDomain hq s) hints,
        annealed_responseJ_eq (adaptedDomain hq t) hintt]
      rfl
    _ = (1 / 2 : ℝ) * blockVecDot ((-p, r) : BlockVec d)
          (blockMatVecMul
            (blockSub (profileRecenteredMean P q g s)
              (profileRecenteredMean P q g t))
            ((-p, r) : BlockVec d)) := by
      rw [blockMatVecMul_blockSub, blockVecDot_sub_right,
        profileRecenteredMean_quadratic,
        profileRecenteredMean_quadratic, hload]
      ring

/-- Constant-skew covariance and integrability turn the adjoint expectation
of a difference into the difference of its two corrected-load expectations. -/
theorem profileAdjointResponseDefect_eq_corrected_integrals
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    profileAdjointResponseDefect P hq g hg s t p r =
      (∫ a, responseJ (adaptedDomain hq s)
        (a.transpose.coeffOn (adaptedDomain hq s)) p
          (r + matVecMul g p) ∂P) -
      ∫ a, responseJ (adaptedDomain hq t)
        (a.transpose.coeffOn (adaptedDomain hq t)) p
          (r + matVecMul g p) ∂P := by
  have hsint := integrable_adjoint_responseJ (P := P)
    (U := adaptedDomain hq s) hints p (r + matVecMul g p)
  have htint := integrable_adjoint_responseJ (P := P)
    (U := adaptedDomain hq t) hintt p (r + matVecMul g p)
  rw [profileAdjointResponseDefect_eq]
  calc
    (∫ a, responseJ (adaptedDomain hq s)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq s)) p r -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r ∂P) =
        ∫ a, responseJ (adaptedDomain hq s)
            (a.transpose.coeffOn (adaptedDomain hq s)) p
              (r + matVecMul g p) -
          responseJ (adaptedDomain hq t)
            (a.transpose.coeffOn (adaptedDomain hq t)) p
              (r + matVecMul g p) ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
      change responseJ (adaptedDomain hq s)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq s)) p r -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r = _
      rw [CoeffSpace.transpose_subSkew]
      rw [responseJ_subSkew (adaptedDomain hq s) a.transpose
          (-g) (isSkewMat_neg hg) p r,
        responseJ_subSkew (adaptedDomain hq t) a.transpose
          (-g) (isSkewMat_neg hg) p r]
      simp only [neg_matVecMul, sub_neg_eq_add]
    _ = _ := integral_sub hsint htint

/-- The coefficient-transpose defect is exactly one half of the adjoint
recentered mean-increment quadratic form. -/
theorem profileAdjointResponseDefect_identity
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    profileAdjointResponseDefect P hq g hg s t p r =
      (1 / 2 : ℝ) * blockVecDot ((-p, r) : BlockVec d)
        (blockMatVecMul
          (blockSub (profileRecenteredAdjointMean P q g s)
            (profileRecenteredAdjointMean P q g t))
          ((-p, r) : BlockVec d)) := by
  let r₀ : Vec d := r + matVecMul g p
  let X₀ : BlockVec d := (-p, r₀)
  have hload :
      blockMatVecMul (blockG g)
          (blockMatVecMul (blockDiag 1 (-1)) ((-p, r) : BlockVec d)) =
        blockMatVecMul (blockDiag 1 (-1)) X₀ := by
    rw [adjointSign_mulVec, adjointSign_mulVec,
      profileDefect_blockG_mulVec]
    apply Prod.ext
    · rfl
    · dsimp only [X₀, r₀]
      funext i
      simp [matVecMul]
  rw [profileAdjointResponseDefect_eq_corrected_integrals hq hg hints hintt]
  calc
    (∫ a, responseJ (adaptedDomain hq s)
            (a.transpose.coeffOn (adaptedDomain hq s)) p r₀ ∂P) -
          ∫ a, responseJ (adaptedDomain hq t)
            (a.transpose.coeffOn (adaptedDomain hq t)) p r₀ ∂P =
        ((1 / 2 : ℝ) * blockVecDot X₀
            (blockMatVecMul
              (blockMatMul (blockDiag 1 (-1))
                (blockMatMul (adaptedMean P q s) (blockDiag 1 (-1)))) X₀) -
              vecDot p r₀) -
          ((1 / 2 : ℝ) * blockVecDot X₀
            (blockMatVecMul
              (blockMatMul (blockDiag 1 (-1))
                (blockMatMul (adaptedMean P q t) (blockDiag 1 (-1)))) X₀) -
              vecDot p r₀) := by
      rw [annealed_adjoint_responseJ_eq (adaptedDomain hq s) hints,
        annealed_adjoint_responseJ_eq (adaptedDomain hq t) hintt]
      rfl
    _ = (1 / 2 : ℝ) * blockVecDot ((-p, r) : BlockVec d)
          (blockMatVecMul
            (blockSub (profileRecenteredAdjointMean P q g s)
              (profileRecenteredAdjointMean P q g t))
            ((-p, r) : BlockVec d)) := by
      rw [blockQuadratic_adjointSign_congr,
        blockQuadratic_adjointSign_congr,
        blockMatVecMul_blockSub, blockVecDot_sub_right,
        profileRecenteredAdjointMean_quadratic,
        profileRecenteredAdjointMean_quadratic, hload]
      ring

/-- The primal response defect is nonnegative on an ordered scale pair. -/
theorem profilePrimalResponseDefect_nonneg
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t)
    (hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s)) (p r : Vec d) :
    0 ≤ profilePrimalResponseDefect P hq g hg s t p r := by
  rw [profilePrimalResponseDefect_identity hq hg hints hintt]
  have h := profileRecenteredMean_le (g := g) hmean
    ((-p, r) : BlockVec d)
  rw [blockMatVecMul_blockSub, blockVecDot_sub_right]
  linarith only [h]

/-- The coefficient-transpose response defect is nonnegative on an ordered
scale pair. -/
theorem profileAdjointResponseDefect_nonneg
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t)
    (hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s)) (p r : Vec d) :
    0 ≤ profileAdjointResponseDefect P hq g hg s t p r := by
  rw [profileAdjointResponseDefect_identity hq hg hints hintt]
  have h := profileRecenteredAdjointMean_le (g := g) hmean
    ((-p, r) : BlockVec d)
  rw [blockMatVecMul_blockSub, blockVecDot_sub_right]
  linarith only [h]

end

end HCPolySupport.HighContrast.Response
