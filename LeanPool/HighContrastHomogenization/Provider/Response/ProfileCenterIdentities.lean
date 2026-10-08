/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewAdjoint
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewBlock
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileCenterPointwise

/-!
# High-contrast homogenization: Provider.Response.ProfileCenterIdentities

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact centers after constant-skew recentering

The primal and coefficient-transpose optimizer centers are computed from their
own loads.  Constant-skew covariance identifies their annealed blocks with the
corresponding shear congruences.  The final two results flatten the identities
in the signs used by the load-calibration argument.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

private theorem toFullBlockVec_injective :
    Function.Injective (toFullBlockVec (d := d)) := by
  intro X Y hXY
  rw [← ofFullBlockVec_toFullBlockVec X,
    ← ofFullBlockVec_toFullBlockVec Y, hXY]

private theorem toFullBlockVec_add (X Y : BlockVec d) :
    toFullBlockVec (X + Y) = toFullBlockVec X + toFullBlockVec Y := by
  funext α
  cases α <;> rfl

private theorem toFullBlockVec_sub (X Y : BlockVec d) :
    toFullBlockVec (X - Y) = toFullBlockVec X - toFullBlockVec Y := by
  funext α
  cases α <;> rfl

private theorem blockG_mulVec (g : Mat d) (X : BlockVec d) :
    blockMatVecMul (blockG g) X =
      (X.1, matVecMul g X.1 + X.2) := by
  apply Prod.ext
  · change matVecMul 1 X.1 + matVecMul 0 X.2 = X.1
    rw [matVecMul_one, zero_matVecMul, add_zero]
  · change matVecMul g X.1 + matVecMul 1 X.2 = _
    rw [matVecMul_one]

private theorem blockG_neg_reflected_center (g : Mat d)
    (hg : IsSkewMat g) (A : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (blockG (-g))
        (blockMatVecMul (blockR d)
            (blockMatVecMul A (blockMatVecMul (blockG g) X)) +
          blockMatVecMul (blockG g) X) =
      blockMatVecMul (blockR d)
          (blockMatVecMul (skewBlockCongr g A) X) + X := by
  apply toFullBlockVec_injective
  simp only [toFullBlockVec_blockMatVecMul, toFullBlockVec_add,
    toFullBlockMat_blockG, toFullBlockMat_blockR,
    toFullBlockMat_skewBlockCongr]
  have hgstar : gᴴ = -g := by
    rwa [conjTranspose_eq_transpose']
  have hGR : fullBlockShear (-g) * fullBlockRefl d =
      fullBlockRefl d * (fullBlockShear g)ᴴ := by
    rw [fullBlockShear, fullBlockRefl, conjTranspose_fullBlockShear,
      hgstar, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hGG : fullBlockShear (-g) * fullBlockShear g = 1 := by
    rw [fullBlockShear_mul, neg_add_cancel, fullBlockShear_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hGR]
  have hsecond : fullBlockShear (-g) *ᵥ
      (fullBlockShear g *ᵥ toFullBlockVec X) = toFullBlockVec X := by
    rw [Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  rw [hsecond]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem skewBlockCongr_neg_adjointSign (g : Mat d)
    (A : BlockMat d) :
    skewBlockCongr (-g)
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul A (blockDiag 1 (-1)))) =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (skewBlockCongr g A) (blockDiag 1 (-1))) := by
  apply toFullBlockMat_injective
  simp only [toFullBlockMat_skewBlockCongr,
    toFullBlockMat_blockMatMul, toFullBlockMat_blockDiag]
  let D : FullBlockMat d := Matrix.fromBlocks 1 0 0 (-1)
  have hDstar : Dᴴ = D := by
    dsimp only [D]
    rw [Matrix.fromBlocks_conjTranspose]
    simp
  have hDD : D * D = 1 := by
    dsimp only [D]
    rw [Matrix.fromBlocks_multiply]
    simp
  have hG : fullBlockShear (-g) = D * fullBlockShear g * D := by
    dsimp only [D]
    rw [fullBlockShear, fullBlockShear, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp
  change (fullBlockShear (-g))ᴴ *
      (D * (toFullBlockMat A * D)) * fullBlockShear (-g) =
    D * (((fullBlockShear g)ᴴ * toFullBlockMat A *
      fullBlockShear g) * D)
  rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hDstar]
  calc
    (D * ((fullBlockShear g)ᴴ * D)) *
          (D * (toFullBlockMat A * D)) *
        (D * fullBlockShear g * D) =
        D * (fullBlockShear g)ᴴ * (D * D) *
          toFullBlockMat A * (D * D) * fullBlockShear g * D := by
      noncomm_ring
    _ = D * (fullBlockShear g)ᴴ * toFullBlockMat A *
        fullBlockShear g * D := by
      rw [hDD]
      simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = D * (((fullBlockShear g)ᴴ * toFullBlockMat A *
        fullBlockShear g) * D) := by
      noncomm_ring

private theorem paperAdjointSign_mulVec (X : BlockVec d) :
    blockMatVecMul (blockDiag (-1) 1) X = (-X.1, X.2) := by
  apply Prod.ext
  · change matVecMul (-1) X.1 + matVecMul 0 X.2 = -X.1
    rw [zero_matVecMul, add_zero, neg_matVecMul, matVecMul_one]
  · change matVecMul 0 X.1 + matVecMul 1 X.2 = X.2
    rw [zero_matVecMul, zero_add, matVecMul_one]

private theorem paperAdjointSign_center (A : BlockMat d)
    (p r : Vec d) :
    blockMatVecMul (blockDiag (-1) 1)
        (blockMatVecMul (blockR d)
            (blockMatVecMul
              (blockMatMul (blockDiag 1 (-1))
                (blockMatMul A (blockDiag 1 (-1))))
              ((-p, r) : BlockVec d)) +
          ((-p, r) : BlockVec d)) =
      ((p, r) : BlockVec d) -
        blockMatVecMul (blockR d)
          (blockMatVecMul A ((p, r) : BlockVec d)) := by
  let X : BlockVec d := (p, r)
  let Z : BlockVec d := blockMatVecMul A X
  have hsign :
      blockMatVecMul (blockDiag 1 (-1))
          ((-p, r) : BlockVec d) = -X := by
    rw [adjointSign_mulVec]
    rfl
  have hneg : blockMatVecMul A (-X) = -Z := by
    simpa only [Z, neg_one_smul] using blockMatVecMul_smul A (-1) X
  rw [blockMatVecMul_adjointSign_congr, hsign, hneg,
    adjointSign_mulVec, blockMatVecMul_blockR, blockMatVecMul_add,
    paperAdjointSign_mulVec, paperAdjointSign_mulVec,
    blockMatVecMul_blockR]
  apply Prod.ext <;> funext i
  · simp only [X, Z, Prod.fst_add, Prod.fst_sub, Prod.fst_neg,
      Prod.snd_neg, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, neg_neg]
    abel
  · simp only [X, Z, Prod.snd_add, Prod.snd_sub, Prod.fst_neg,
      Prod.snd_neg, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, neg_neg]
    abel

/-! ## The two independently annealed centers -/

/-- The primal hatted center is `(I + R Êₜ)(-p⁻,q⁻)`. -/
theorem profilePrimalCenter_subSkew_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) (h0 : Mat d)
    (hh0 : IsSkewMat h0) (pMinus qMinus : Vec d) :
    profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 hh0)
        pMinus qMinus =
      blockMatVecMul (blockR d)
          (blockMatVecMul (skewBlockCongr h0 (adaptedMean P q t))
            ((-pMinus, qMinus) : BlockVec d)) +
        ((-pMinus, qMinus) : BlockVec d) := by
  let U := adaptedDomain hq t
  let q0 : Vec d := qMinus - matVecMul h0 pMinus
  let X : BlockVec d := (-pMinus, qMinus)
  let X0 : BlockVec d := (-pMinus, q0)
  let C0 : BlockVec d :=
    (annealedOptimizerGradient P U pMinus q0,
      annealedOptimizerFlux P U pMinus q0)
  have hcenter :
      profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 hh0)
          pMinus qMinus =
        ((fun i ↦ ∫ a, averageGradient U
            ((a.subSkew h0 hh0).coeffOn U)
            (centeredResponseOptimizer U (a.subSkew h0 hh0)
              pMinus qMinus) i ∂P),
          fun i ↦ ∫ a, averageFlux U
            ((a.subSkew h0 hh0).coeffOn U)
            (centeredResponseOptimizer U (a.subSkew h0 hh0)
              pMinus qMinus) i ∂P) := by
    apply Prod.ext
    · funext i
      apply integral_congr_ae
      filter_upwards [] with a
      rw [blockCellAverage_diagonalWeakState]
      rfl
    · funext i
      apply integral_congr_ae
      filter_upwards [] with a
      rw [blockCellAverage_diagonalWeakState]
      rfl
  have hX0 : blockMatVecMul (blockG h0) X = X0 := by
    rw [blockG_mulVec]
    apply Prod.ext
    · rfl
    · dsimp only [X, X0, q0]
      rw [matVecMul_neg]
      abel
  have hC0 : C0 =
      blockMatVecMul (blockR d)
          (blockMatVecMul (adaptedMean P q t) X0) + X0 := by
    simpa only [U, C0, X0, adaptedMean, adaptedDomain_carrier] using
      annealed_optimizer_average_eq U hint pMinus q0
  have htransport :
      ((annealedOptimizerGradient P U pMinus q0,
          annealedOptimizerFlux P U pMinus q0 -
            matVecMul h0
              (annealedOptimizerGradient P U pMinus q0)) : BlockVec d) =
        blockMatVecMul (blockG (-h0)) C0 := by
    rw [blockG_mulVec]
    apply Prod.ext
    · rfl
    · dsimp only [C0]
      rw [neg_matVecMul]
      abel
  rw [hcenter,
    annealedOptimizerGradient_subSkew (P := P) U h0 hh0,
    annealedOptimizerFlux_subSkew U hint h0 hh0, htransport, hC0,
    ← hX0]
  exact blockG_neg_reflected_center h0 hh0 (adaptedMean P q t) X

/-- The independently computed adjoint hatted center uses the signed
congruence of the hatted mean and its own load. -/
theorem profileAdjointCenter_subSkew_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) (h0 : Mat d)
    (hh0 : IsSkewMat h0) (pPlus qPlus : Vec d) :
    profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0)
        pPlus qPlus =
      blockMatVecMul (blockR d)
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul
                (skewBlockCongr h0 (adaptedMean P q t))
                (blockDiag 1 (-1))))
            ((-pPlus, qPlus) : BlockVec d)) +
        ((-pPlus, qPlus) : BlockVec d) := by
  let U := adaptedDomain hq t
  let q0 : Vec d := qPlus + matVecMul h0 pPlus
  let X : BlockVec d := (-pPlus, qPlus)
  let X0 : BlockVec d := (-pPlus, q0)
  let Ead : BlockMat d :=
    blockMatMul (blockDiag 1 (-1))
      (blockMatMul (adaptedMean P q t) (blockDiag 1 (-1)))
  let C0 : BlockVec d :=
    (annealedAdjointOptimizerGradient P U pPlus q0,
      annealedAdjointOptimizerFlux P U pPlus q0)
  have hcenter :
      profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0)
          pPlus qPlus =
        ((fun i ↦ ∫ a, averageGradient U
            ((a.subSkew h0 hh0).transpose.coeffOn U)
            (centeredAdjointOptimizer U (a.subSkew h0 hh0)
              pPlus qPlus) i ∂P),
          fun i ↦ ∫ a, averageFlux U
            ((a.subSkew h0 hh0).transpose.coeffOn U)
            (centeredAdjointOptimizer U (a.subSkew h0 hh0)
              pPlus qPlus) i ∂P) := by
    apply Prod.ext
    · funext i
      apply integral_congr_ae
      filter_upwards [] with a
      change (blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t (a.subSkew h0 hh0).transpose
            pPlus qPlus)).1 i = _
      rw [blockCellAverage_diagonalWeakState]
      rfl
    · funext i
      apply integral_congr_ae
      filter_upwards [] with a
      change (blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t (a.subSkew h0 hh0).transpose
            pPlus qPlus)).2 i = _
      rw [blockCellAverage_diagonalWeakState]
      rfl
  have hX0 : blockMatVecMul (blockG (-h0)) X = X0 := by
    rw [blockG_mulVec]
    apply Prod.ext
    · rfl
    · dsimp only [X, X0, q0]
      funext i
      simp [matVecMul]
      abel
  have hC0 : C0 =
      blockMatVecMul (blockR d) (blockMatVecMul Ead X0) + X0 := by
    simpa only [U, C0, Ead, X0, adaptedMean,
      adaptedDomain_carrier] using
      annealed_adjoint_optimizer_average_eq U hint pPlus q0
  have htransport :
      ((annealedAdjointOptimizerGradient P U pPlus q0,
          annealedAdjointOptimizerFlux P U pPlus q0 +
            matVecMul h0
              (annealedAdjointOptimizerGradient P U pPlus q0)) : BlockVec d) =
        blockMatVecMul (blockG h0) C0 := by
    rw [blockG_mulVec]
    apply Prod.ext
    · rfl
    · dsimp only [C0]
      abel
  rw [hcenter,
    annealedAdjointOptimizerGradient_subSkew (P := P) U h0 hh0,
    annealedAdjointOptimizerFlux_subSkew U hint h0 hh0, htransport,
    hC0, ← hX0]
  have halgebra := blockG_neg_reflected_center (-h0)
    (isSkewMat_neg hh0) Ead X
  simp only [neg_neg, Ead] at halgebra
  rw [skewBlockCongr_neg_adjointSign] at halgebra
  exact halgebra

/-! ## Load-calibration forms -/

/-- Flattened primal identity in the exact `x⁻ + R Êₜx⁻` form. -/
theorem toFullBlockVec_profilePrimalCenter_subSkew_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) (h0 : Mat d)
    (hh0 : IsSkewMat h0) (pMinus qMinus : Vec d) :
    toFullBlockVec
        (profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 hh0)
          pMinus qMinus) =
      toFullBlockVec ((-pMinus, qMinus) : BlockVec d) +
        fullBlockRefl d *ᵥ
          (toFullBlockMat (skewBlockCongr h0 (adaptedMean P q t)) *ᵥ
            toFullBlockVec ((-pMinus, qMinus) : BlockVec d)) := by
  rw [profilePrimalCenter_subSkew_eq hq t hint h0 hh0]
  simp only [toFullBlockVec_add, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_blockR]
  rw [add_comm]

/-- The paper-signed adjoint center is exactly `x⁺ - R Êₜx⁺`. -/
theorem profileAdjointCenter_subSkew_paperSign_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) (h0 : Mat d)
    (hh0 : IsSkewMat h0) (pPlus qPlus : Vec d) :
    blockMatVecMul (blockDiag (-1) 1)
        (profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0)
          pPlus qPlus) =
      ((pPlus, qPlus) : BlockVec d) -
        blockMatVecMul (blockR d)
          (blockMatVecMul (skewBlockCongr h0 (adaptedMean P q t))
            ((pPlus, qPlus) : BlockVec d)) := by
  rw [profileAdjointCenter_subSkew_eq hq t hint h0 hh0]
  exact paperAdjointSign_center
    (skewBlockCongr h0 (adaptedMean P q t)) pPlus qPlus

/-- Flattened adjoint identity in the exact `x⁺ - R Êₜx⁺` form. -/
theorem toFullBlockVec_profileAdjointCenter_subSkew_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) (h0 : Mat d)
    (hh0 : IsSkewMat h0) (pPlus qPlus : Vec d) :
    toFullBlockVec
        (blockMatVecMul (blockDiag (-1) 1)
          (profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0)
            pPlus qPlus)) =
      toFullBlockVec ((pPlus, qPlus) : BlockVec d) -
        fullBlockRefl d *ᵥ
          (toFullBlockMat (skewBlockCongr h0 (adaptedMean P q t)) *ᵥ
            toFullBlockVec ((pPlus, qPlus) : BlockVec d)) := by
  rw [profileAdjointCenter_subSkew_paperSign_eq hq t hint h0 hh0]
  simp only [toFullBlockVec_sub, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_blockR]

end

end HCPolySupport.HighContrast.Response
