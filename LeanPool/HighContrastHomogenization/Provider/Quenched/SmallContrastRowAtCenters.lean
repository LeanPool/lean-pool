/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenterSchur
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenterMagnitude
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringSmallness
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRowAtCenters

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The hatted quadratic load at the calibrated profile centers

The row caps majorize the earlier rows by the hatted reference quadratic
load at the profile centers.  Here that load is second order in the hatted
contrast defect: the centers are the closed Schur pairs of the terminal
mean, the reference is comparable to the terminal mean through the carried
deterministic comparability, and the mean's own hatted quadratic load at
the closed pairs is controlled by the center magnitudes and the smallness
pack.  The final constant is `κ_ref · 36·(1 + d)·ε²` in both orientations.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem quad_inl (H : BlockMat d) (u : Vec d) :
    blockVecDot ((u, 0) : BlockVec d)
        (blockMatVecMul H ((u, 0) : BlockVec d)) =
      vecDot u (matVecMul H.upperLeft u) := by
  change vecDot u (matVecMul H.upperLeft u + matVecMul H.upperRight 0) +
      vecDot 0 (matVecMul H.lowerLeft u + matVecMul H.lowerRight 0) = _
  rw [matVecMul_zero, matVecMul_zero, add_zero, add_zero,
    vecDot_zero_left, add_zero]

/-- The recentered terminal mean in structural Schur form. -/
private theorem hatMean_eq_schur
    {P : Measure (CoeffSpace d)}
    {q : Mat d} (t : ℤ) {S SStar K : Mat d}
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K) :
    Response.skewBlockCongr (Response.responseSkew K) (adaptedMean P q t) =
      ofFullBlockMat (schurBlock S SStar (Response.responseSymmetric K)) := by
  have hE2 : toFullBlockMat
      (Response.skewBlockCongr (Response.responseSkew K) (adaptedMean P q t)) =
      schurBlock S SStar (Response.responseSymmetric K) := by
    have h := toFullBlockMat_skewBlockCongr_of_schurBlock
      (Response.responseSkew K) hform
    rwa [Response.sub_responseSkew K] at h
  apply toFullBlockMat_injective
  simpa using hE2

/-- The gradient-slot quadratic form of the recentered hatted mean. -/
private theorem hatMean_quad_inl
    {P : Measure (CoeffSpace d)}
    {q : Mat d} (t : ℤ) {S SStar K : Mat d}
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K)
    (u : Vec d) :
    blockVecDot ((u, 0) : BlockVec d)
        (blockMatVecMul
          (Response.profileHattedBlock (Response.responseSkew K) (adaptedMean P q t))
          ((u, 0) : BlockVec d)) =
      u ⬝ᵥ (S + Response.responseSymmetric K * SStar⁻¹ *
        Response.responseSymmetric K) *ᵥ u := by
  rw [Response.profileHattedBlock, hatMean_eq_schur t hform,
    Response.ofFullBlockMat_schurBlock, quad_inl]
  change vecDot u (matVecMul (S + (Response.responseSymmetric K)ᴴ * SStar⁻¹ *
    Response.responseSymmetric K) u) = _
  rw [Response.responseSymmetric_isHermitian]
  rfl

/-- The flux-slot quadratic form of the recentered hatted mean. -/
private theorem hatMean_quad_inr
    {P : Measure (CoeffSpace d)}
    {q : Mat d} (t : ℤ) {S SStar K : Mat d}
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K)
    (v : Vec d) :
    blockVecDot (((0 : Vec d), v) : BlockVec d)
        (blockMatVecMul
          (Response.profileHattedBlock (Response.responseSkew K) (adaptedMean P q t))
          (((0 : Vec d), v) : BlockVec d)) =
      v ⬝ᵥ SStar⁻¹ *ᵥ v := by
  rw [Response.profileHattedBlock, hatMean_eq_schur t hform,
    Response.ofFullBlockMat_schurBlock, blockVecDot_inr]
  rfl

/-- The mean's hatted quadratic load at a closed center pair, by the two
center magnitudes and the smallness pack. -/
private theorem hatMean_load_le {S SStar : Mat d} (κ : Mat d)
    (hStar : SStar.PosDef)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (hgapM : S - SStar ≤ eps • SStar)
    (hskewM : κ * SStar⁻¹ * κ ≤ (eps ^ 2 / 4) • SStar)
    {u v : Vec d}
    (hu : u ⬝ᵥ SStar *ᵥ u ≤ 5 * (1 + (d : ℝ)) * eps ^ 2)
    (hv : v ⬝ᵥ SStar⁻¹ *ᵥ v ≤ 24 * (1 + (d : ℝ)) * eps ^ 2) :
    u ⬝ᵥ (S + κ * SStar⁻¹ * κ) *ᵥ u + v ⬝ᵥ SStar⁻¹ *ᵥ v ≤
      36 * (1 + (d : ℝ)) * eps ^ 2 := by
  have hX0 : 0 ≤ u ⬝ᵥ SStar *ᵥ u := by
    have h := hStar.posSemidef.dotProduct_mulVec_nonneg u
    simpa using h
  have hgap : u ⬝ᵥ S *ᵥ u - u ⬝ᵥ SStar *ᵥ u ≤
      eps * (u ⬝ᵥ SStar *ᵥ u) := by
    have h := Initialization.dotProduct_mulVec_le_of_le hgapM u
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul] at h
    exact h
  have hskew : u ⬝ᵥ (κ * SStar⁻¹ * κ) *ᵥ u ≤
      eps ^ 2 / 4 * (u ⬝ᵥ SStar *ᵥ u) := by
    have h := Initialization.dotProduct_mulVec_le_of_le hskewM u
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    exact h
  have hsplit : u ⬝ᵥ (S + κ * SStar⁻¹ * κ) *ᵥ u =
      u ⬝ᵥ S *ᵥ u + u ⬝ᵥ (κ * SStar⁻¹ * κ) *ᵥ u := by
    rw [Matrix.add_mulVec, dotProduct_add]
  have hepsX : eps * (u ⬝ᵥ SStar *ᵥ u) ≤ u ⬝ᵥ SStar *ᵥ u := by
    have h := mul_le_mul_of_nonneg_right heps1 hX0
    rwa [one_mul] at h
  have heps2 : eps ^ 2 ≤ 1 := by nlinarith only [hpos.le, heps1]
  have heps2X : eps ^ 2 / 4 * (u ⬝ᵥ SStar *ᵥ u) ≤
      1 / 4 * (u ⬝ᵥ SStar *ᵥ u) := by
    have h4 : eps ^ 2 / 4 ≤ 1 / 4 := by linarith only [heps2]
    exact mul_le_mul_of_nonneg_right h4 hX0
  rw [hsplit]
  linarith only [hgap, hskew, hepsX, heps2X, hu, hv, hX0]

/-- **The hatted reference quadratic load at the primal center** is at most
`κ_ref · 36·(1+d)·ε²`. -/
theorem profileQuadraticLoad_hatted_primal_center_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t)
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S SStar - 1) ≤ eps)
    {E : BlockMat d} {kap : ℝ} (hkap0 : 0 ≤ kap)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X (blockMatVecMul (adaptedMean P q t) X))
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    Response.profileQuadraticLoad
        (Response.profileHattedBlock (Response.responseSkew K) E)
        (Response.profilePrimalCenter P hq t
          (fun a ↦ a.subSkew (Response.responseSkew K)
            (Response.is_skew_mat_response_skew K))
          (Response.centeredResponseLoadP S SStar K e)
          (Response.centeredResponseLoadQ S SStar K e)).1
        (Response.profilePrimalCenter P hq t
          (fun a ↦ a.subSkew (Response.responseSkew K)
            (Response.is_skew_mat_response_skew K))
          (Response.centeredResponseLoadP S SStar K e)
          (Response.centeredResponseLoadQ S SStar K e)).2 ≤
      kap * (36 * (1 + (d : ℝ)) * eps ^ 2) := by
  classical
  have hint' : HasIntegrableCoarseBlock P
      ((Response.adaptedDomain hq t : Domain d) : Set (Vec d)) := by
    simpa only [Response.adaptedDomain_carrier] using! hint
  have hE' : toFullBlockMat
      (annealedBlock P ((Response.adaptedDomain hq t : Domain d) : Set (Vec d))) =
      schurBlock S SStar K := by
    simpa only [adaptedMean, Response.adaptedDomain_carrier] using hform
  obtain ⟨horder, hgapM, hskewM, htrGap, htrSkew⟩ :=
    centering_smallness_supply (Response.adaptedDomain hq t) hint' hS hStar hE'
      hpos htr
  have hks : (Response.responseSymmetric K)ᴴ = Response.responseSymmetric K :=
    Response.responseSymmetric_isHermitian K
  have hmag := centering_center_quads_le hS hStar hks hpos.le heps1 horder
    hgapM hskewM htrGap htrSkew e he
  have hloadP : Response.centeredResponseLoadP S SStar K e =
      matSqrt (matGeomMean (S + Response.responseSymmetric K * SStar⁻¹ *
        Response.responseSymmetric K) SStar)⁻¹ *ᵥ e := by
    rw [Response.centeredResponseLoadP, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  have hloadQ : Response.centeredResponseLoadQ S SStar K e =
      matSqrt (matGeomMean (S + Response.responseSymmetric K * SStar⁻¹ *
        Response.responseSymmetric K) SStar) *ᵥ e := by
    rw [Response.centeredResponseLoadQ, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  have hstep : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul
        (Response.profileHattedBlock (Response.responseSkew K) E) X) ≤
      kap * blockVecDot X (blockMatVecMul
        (Response.profileHattedBlock (Response.responseSkew K)
          (adaptedMean P q t)) X) := by
    intro X
    rw [Response.profileHattedBlock, Response.profileHattedBlock,
      Response.blockQuadratic_skewBlockCongr, Response.blockQuadratic_skewBlockCongr]
    exact hcomp _
  have hmain : ∀ u v : Vec d,
      u ⬝ᵥ SStar *ᵥ u ≤ 5 * (1 + (d : ℝ)) * eps ^ 2 →
      v ⬝ᵥ SStar⁻¹ *ᵥ v ≤ 24 * (1 + (d : ℝ)) * eps ^ 2 →
      blockVecDot ((u, 0) : BlockVec d)
          (blockMatVecMul
            (Response.profileHattedBlock (Response.responseSkew K) E)
            ((u, 0) : BlockVec d)) +
        blockVecDot (((0 : Vec d), v) : BlockVec d)
          (blockMatVecMul
            (Response.profileHattedBlock (Response.responseSkew K) E)
            (((0 : Vec d), v) : BlockVec d)) ≤
        kap * (36 * (1 + (d : ℝ)) * eps ^ 2) := by
    intro u v hu hv
    have hA := hstep ((u, 0) : BlockVec d)
    have hB := hstep (((0 : Vec d), v) : BlockVec d)
    rw [hatMean_quad_inl t hform] at hA
    rw [hatMean_quad_inr t hform] at hB
    refine le_trans (add_le_add hA hB) ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (hatMean_load_le (Response.responseSymmetric K) hStar hpos heps1
        hgapM hskewM hu hv) hkap0
  rw [hloadP, hloadQ]
  have hcen := profilePrimalCenter_calibrated_eq hq t hint hform
    (matSqrt (matGeomMean (S + Response.responseSymmetric K * SStar⁻¹ *
      Response.responseSymmetric K) SStar)⁻¹ *ᵥ e)
    (matSqrt (matGeomMean (S + Response.responseSymmetric K * SStar⁻¹ *
      Response.responseSymmetric K) SStar) *ᵥ e)
  rw [Response.profileQuadraticLoad]
  refine hmain _ _ ?_ ?_
  · rw [hcen]
    exact hmag.1
  · rw [hcen]
    exact hmag.2

/-- **The hatted reference quadratic load at the adjoint center** is at most
`κ_ref · 36·(1+d)·ε²`. -/
theorem profileQuadraticLoad_hatted_adjoint_center_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t)
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S SStar - 1) ≤ eps)
    {E : BlockMat d} {kap : ℝ} (hkap0 : 0 ≤ kap)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X (blockMatVecMul (adaptedMean P q t) X))
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    Response.profileQuadraticLoad
        (Response.profileHattedAdjointBlock (Response.responseSkew K) E)
        (Response.profileAdjointCenter P hq t
          (fun a ↦ a.subSkew (Response.responseSkew K)
            (Response.is_skew_mat_response_skew K))
          (Response.centeredResponseLoadP S SStar K e)
          (Response.centeredResponseLoadQ S SStar K e)).1
        (Response.profileAdjointCenter P hq t
          (fun a ↦ a.subSkew (Response.responseSkew K)
            (Response.is_skew_mat_response_skew K))
          (Response.centeredResponseLoadP S SStar K e)
          (Response.centeredResponseLoadQ S SStar K e)).2 ≤
      kap * (36 * (1 + (d : ℝ)) * eps ^ 2) := by
  classical
  have hint' : HasIntegrableCoarseBlock P
      ((Response.adaptedDomain hq t : Domain d) : Set (Vec d)) := by
    simpa only [Response.adaptedDomain_carrier] using! hint
  have hE' : toFullBlockMat
      (annealedBlock P ((Response.adaptedDomain hq t : Domain d) : Set (Vec d))) =
      schurBlock S SStar K := by
    simpa only [adaptedMean, Response.adaptedDomain_carrier] using hform
  obtain ⟨horder, hgapM, hskewM, htrGap, htrSkew⟩ :=
    centering_smallness_supply (Response.adaptedDomain hq t) hint' hS hStar hE'
      hpos htr
  have hks : (Response.responseSymmetric K)ᴴ = Response.responseSymmetric K :=
    Response.responseSymmetric_isHermitian K
  -- the adjoint center magnitudes, at the negated symmetric coordinate
  have hknegherm : (-(Response.responseSymmetric K))ᴴ =
      -(Response.responseSymmetric K) := by
    rw [Matrix.conjTranspose_neg, hks]
  have hnegconj : -(Response.responseSymmetric K) * SStar⁻¹ *
      -(Response.responseSymmetric K) =
      Response.responseSymmetric K * SStar⁻¹ * Response.responseSymmetric K := by
    rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  have hskewMneg : -(Response.responseSymmetric K) * SStar⁻¹ *
      -(Response.responseSymmetric K) ≤ (eps ^ 2 / 4) • SStar := by
    rw [hnegconj]
    exact hskewM
  have htrSkewneg : Matrix.trace (-(Response.responseSymmetric K) * SStar⁻¹ *
      -(Response.responseSymmetric K) * SStar⁻¹) ≤ (d : ℝ) * eps ^ 2 / 4 := by
    rw [hnegconj]
    exact htrSkew
  have hmagA := centering_center_quads_le hS hStar hknegherm hpos.le heps1
    horder hgapM hskewMneg htrGap htrSkewneg e he
  rw [hnegconj, Matrix.neg_mulVec, ← sub_eq_add_neg, Matrix.neg_mul,
    sub_neg_eq_add] at hmagA
  have hloadP : Response.centeredResponseLoadP S SStar K e =
      matSqrt (matGeomMean (S + Response.responseSymmetric K * SStar⁻¹ *
        Response.responseSymmetric K) SStar)⁻¹ *ᵥ e := by
    rw [Response.centeredResponseLoadP, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  have hloadQ : Response.centeredResponseLoadQ S SStar K e =
      matSqrt (matGeomMean (S + Response.responseSymmetric K * SStar⁻¹ *
        Response.responseSymmetric K) SStar) *ᵥ e := by
    rw [Response.centeredResponseLoadQ, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  have hDu : ∀ u : Vec d,
      blockMatVecMul (blockDiag 1 (-1)) ((u, 0) : BlockVec d) =
      ((u, (0 : Vec d)) : BlockVec d) := by
    intro u
    rw [Response.adjointSign_mulVec]
    apply Prod.ext
    · rfl
    · exact neg_zero
  have hDv : ∀ v : Vec d,
      blockMatVecMul (blockDiag 1 (-1)) (((0 : Vec d), v) : BlockVec d) =
      (((0 : Vec d), -v) : BlockVec d) := by
    intro v
    rw [Response.adjointSign_mulVec]
  have hstepA : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul
        (Response.profileHattedAdjointBlock (Response.responseSkew K) E) X) ≤
      kap * blockVecDot X (blockMatVecMul
        (Response.profileHattedAdjointBlock (Response.responseSkew K)
          (adaptedMean P q t)) X) := by
    intro X
    rw [Response.profileHattedAdjointBlock, Response.profileHattedAdjointBlock,
      Response.profileAdjointBlock, Response.profileAdjointBlock,
      Response.blockQuadratic_adjointSign_congr,
      Response.blockQuadratic_adjointSign_congr,
      Response.profileHattedBlock, Response.profileHattedBlock,
      Response.blockQuadratic_skewBlockCongr, Response.blockQuadratic_skewBlockCongr]
    exact hcomp _
  have hAq : ∀ u : Vec d,
      blockVecDot ((u, 0) : BlockVec d)
        (blockMatVecMul
          (Response.profileHattedAdjointBlock (Response.responseSkew K)
            (adaptedMean P q t)) ((u, 0) : BlockVec d)) =
      u ⬝ᵥ (S + Response.responseSymmetric K * SStar⁻¹ *
        Response.responseSymmetric K) *ᵥ u := by
    intro u
    rw [Response.profileHattedAdjointBlock, Response.profileAdjointBlock,
      Response.blockQuadratic_adjointSign_congr, hDu,
      hatMean_quad_inl t hform]
  have hBq : ∀ v : Vec d,
      blockVecDot (((0 : Vec d), v) : BlockVec d)
        (blockMatVecMul
          (Response.profileHattedAdjointBlock (Response.responseSkew K)
            (adaptedMean P q t)) (((0 : Vec d), v) : BlockVec d)) =
      v ⬝ᵥ SStar⁻¹ *ᵥ v := by
    intro v
    rw [Response.profileHattedAdjointBlock, Response.profileAdjointBlock,
      Response.blockQuadratic_adjointSign_congr, hDv,
      hatMean_quad_inr t hform, Matrix.mulVec_neg, dotProduct_neg,
      neg_dotProduct, neg_neg]
  have hmain : ∀ u v : Vec d,
      u ⬝ᵥ SStar *ᵥ u ≤ 5 * (1 + (d : ℝ)) * eps ^ 2 →
      v ⬝ᵥ SStar⁻¹ *ᵥ v ≤ 24 * (1 + (d : ℝ)) * eps ^ 2 →
      blockVecDot ((u, 0) : BlockVec d)
          (blockMatVecMul
            (Response.profileHattedAdjointBlock (Response.responseSkew K) E)
            ((u, 0) : BlockVec d)) +
        blockVecDot (((0 : Vec d), v) : BlockVec d)
          (blockMatVecMul
            (Response.profileHattedAdjointBlock (Response.responseSkew K) E)
            (((0 : Vec d), v) : BlockVec d)) ≤
        kap * (36 * (1 + (d : ℝ)) * eps ^ 2) := by
    intro u v hu hv
    have hA := hstepA ((u, 0) : BlockVec d)
    have hB := hstepA (((0 : Vec d), v) : BlockVec d)
    rw [hAq] at hA
    rw [hBq] at hB
    refine le_trans (add_le_add hA hB) ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (hatMean_load_le (Response.responseSymmetric K) hStar hpos heps1
        hgapM hskewM hu hv) hkap0
  rw [hloadP, hloadQ]
  have hcen := profileAdjointCenter_calibrated_eq hq t hint hform
    (matSqrt (matGeomMean (S + Response.responseSymmetric K * SStar⁻¹ *
      Response.responseSymmetric K) SStar)⁻¹ *ᵥ e)
    (matSqrt (matGeomMean (S + Response.responseSymmetric K * SStar⁻¹ *
      Response.responseSymmetric K) SStar) *ᵥ e)
  rw [Response.profileQuadraticLoad]
  refine hmain _ _ ?_ ?_
  · rw [hcen]
    exact hmagA.1
  · rw [hcen]
    exact hmagA.2

end

end HCPolySupport.HighContrast.Quenched
