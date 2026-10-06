/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecentredCoeffIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers

/-!
# High-contrast homogenization: Entry.Response.Core.LoadQuadraticSchur

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur bounds for the load quadratic forms

This file proves the load-quadratic conjuncts of the response energy-and-defect estimate
`e.response.energy.and.defect`: it completes the load quadratic forms `respEJ^∓` and `respTau^∓`
and proves they are nonnegative, then compares the recentred energies `respEhatMinus`/`respEhatPlus`
and the response mean across scales. The supporting algebra serves the response transfer
`p.response.transfer`: it proves the Schur identity for the block quadratic form under a block
swap, the Riccati exchange identity between the primal and swapped-conjugate quadratic forms, the
nonnegativity of the canonical imbalance, and the identity and bound for the sum of the load
quadratics `respLsq^∓` used to compare scales.
-/

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockScale matSqrt
  matSqrt_spec posDef_lowerRight schurSigma schurSigmaStar schurSkew
  toFullBlockMat_eq_blockMatEntry)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! #### The conjuncts -/

/-- First conjunct, unconditional (`e.response.energy.and.defect`). -/
theorem respEJMinus_nonneg [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F)) :
    0 ≤ respEJMinus P jStar F t e :=
  integral_nonneg fun a => respJ_respCoeffMinus_nonneg (respGrid jStar F) hq t F hg a _ _

/-- Second conjunct, unconditional. -/
theorem respEJPlus_nonneg [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F)) :
    0 ≤ respEJPlus P jStar F t e :=
  integral_nonneg fun a => respJ_respCoeffPlus_nonneg (respGrid jStar F) hq t F hg a _ _

/-- Third conjunct, from the raw output alone. -/
theorem respEJMinus_eq_final [NeZero d] (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (he : vecDot e e = 1) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respEJMinus P jStar F t e = (1 / 2 : ℝ) * respLsqMinus P jStar F t e - 1 :=
  respEJMinus_eq P jStar F t e he hM hg
    (fun a => respJ_eq_respCoeffMinus (respGrid jStar F) hq t F hg a _ _)
    (integrable_respCoeffMinus P jStar F t hq hg hint)
    (annealedBlockOf_respCoeffMinus P jStar F t hq hg hint)

/-- Fourth conjunct, from the raw output alone. -/
theorem respEJPlus_eq_final [NeZero d] (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (he : vecDot e e = 1) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respEJPlus P jStar F t e = (1 / 2 : ℝ) * respLsqPlus P jStar F t e - 1 :=
  respEJPlus_eq P jStar F t e he hM hg
    (fun a => respJ_eq_respCoeffPlus (respGrid jStar F) hq t F hg a _ _)
    (integrable_respCoeffPlus P jStar F t hq hg hint)
    (annealedBlockOf_respCoeffPlus P jStar F t hq hg hint)

/-- Seventh conjunct, from the raw output alone. -/
theorem zero_le_respTauMinus_final [NeZero d] (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (s t : ℤ) (e : Vec d)
    (he : vecDot e e = 1) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hord : BlockMatLoewnerLE (respMean P jStar F t) (respMean P jStar F s))
    (hintT : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hintS : HasIntegrableCoarseBlock P (respCell jStar F s)) :
    0 ≤ respTauMinus P jStar F s t e :=
  zero_le_respTauMinus P jStar F s t e (respEhatMinus_mono P jStar F s t hord)
    (respTauMinus_eq P jStar F s t e
      (fun a => respJ_eq_respCoeffMinus (respGrid jStar F) hq s F hg a _ _)
      (integrable_respCoeffMinus P jStar F s hq hg hintS)
      (annealedBlockOf_respCoeffMinus P jStar F s hq hg hintS)
      (respEJMinus_eq_final P jStar F t e he hq hg hM hintT)
      (vecDot_respP_respqMinus_eq_one P jStar F t e he hM hg))

/-- Eighth conjunct, from the raw output alone. -/
theorem zero_le_respTauPlus_final [NeZero d] (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (s t : ℤ) (e : Vec d)
    (he : vecDot e e = 1) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hord : BlockMatLoewnerLE (respMean P jStar F t) (respMean P jStar F s))
    (hintT : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hintS : HasIntegrableCoarseBlock P (respCell jStar F s)) :
    0 ≤ respTauPlus P jStar F s t e :=
  zero_le_respTauPlus P jStar F s t e (respEhatPlus_mono P jStar F s t hord)
    (respTauPlus_eq P jStar F s t e
      (fun a => respJ_eq_respCoeffPlus (respGrid jStar F) hq s F hg a _ _)
      (integrable_respCoeffPlus P jStar F s hq hg hintS)
      (annealedBlockOf_respCoeffPlus P jStar F s hq hg hintS)
      (respEJPlus_eq_final P jStar F t e he hq hg hM hintT)
      (vecDot_respP_respqPlus_eq_one P jStar F t e he hM hg))

/-! ## Part A: the Schur expansion of the block quadratic form -/

private theorem matVecMul_add_mat (A B : Mat d) (x : Vec d) :
    matVecMul (A + B) x = matVecMul A x + matVecMul B x := by
  funext i
  simp [matVecMul, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem matVecMul_neg_mat (A : Mat d) (x : Vec d) :
    matVecMul (-A) x = -matVecMul A x := by
  funext i
  simp [matVecMul, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

private theorem matVecMul_zero_vec (A : Mat d) : matVecMul A (0 : Vec d) = 0 := by
  funext i; simp [matVecMul]

private theorem schur_lowerLeft {A : BlockMat d} (hLR : IsUnit A.lowerRight.det) :
    A.lowerLeft = -(A.lowerRight * schurSkew A) := by
  rw [schurSkew, mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLR, Matrix.one_mul,
    neg_neg]

private theorem schur_upperLeft (A : BlockMat d) :
    A.upperLeft = schurSigma A + matTranspose (schurSkew A) * A.lowerRight * schurSkew A := by
  rw [schurSigma]
  abel

private theorem sym_upperRight {A : BlockMat d} (hs : IsSymmetricBlockMat A) :
    A.upperRight = matTranspose A.lowerLeft := by
  ext i j
  exact hs (Sum.inl i) (Sum.inr j)

private theorem sym_lowerRight {A : BlockMat d} (hs : IsSymmetricBlockMat A) :
    matTranspose A.lowerRight = A.lowerRight := by
  ext i j
  exact hs (Sum.inr j) (Sum.inr i)

private theorem vecDot_sym {S : Mat d} (hS : matTranspose S = S) (u v : Vec d) :
    vecDot u (matVecMul S v) = vecDot v (matVecMul S u) := by
  conv_lhs => rw [← hS]
  rw [vecDot_matVecMul_transpose, vecDot_comm]

/-- The Schur expansion `(z,w)·A(z,w) = z·σz + (kz-w)·σ_*⁻¹(kz-w)`. -/
private theorem blockQuad_schur {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hLR : IsUnit A.lowerRight.det) (z w : Vec d) :
    blockVecDot (z, w) (blockMatVecMul A (z, w))
      = vecDot z (matVecMul (schurSigma A) z)
        + vecDot (matVecMul (schurSkew A) z - w)
            (matVecMul A.lowerRight (matVecMul (schurSkew A) z - w)) := by
  have hST : matTranspose A.lowerRight = A.lowerRight := sym_lowerRight hs
  have hLL : A.lowerLeft = -(A.lowerRight * schurSkew A) := schur_lowerLeft hLR
  have hUR : A.upperRight = -(matTranspose (schurSkew A) * A.lowerRight) := by
    rw [sym_upperRight hs, hLL]
    ext i j
    simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply, Matrix.mul_apply,
      Matrix.transpose_apply]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : A.lowerRight j l = A.lowerRight l j := by
      have := hST
      have h2 := congrFun (congrFun this l) j
      simpa [matTranspose, Matrix.transpose_apply] using h2
    rw [this]
    ring
  have hUL : A.upperLeft
      = schurSigma A + matTranspose (schurSkew A) * A.lowerRight * schurSkew A :=
    schur_upperLeft A
  set k := schurSkew A with hkdef
  set S := A.lowerRight with hSdef
  set σ := schurSigma A with hσdef
  have hsym := vecDot_sym hST
  -- three normalisations
  have e1 : vecDot z (matVecMul (matTranspose k * S * k) z)
      = vecDot (matVecMul k z) (matVecMul S (matVecMul k z)) := by
    rw [Matrix.mul_assoc, ← matVecMul_mul, ← matVecMul_mul, vecDot_matVecMul_transpose]
  have e2 : vecDot z (matVecMul (matTranspose k * S) w)
      = vecDot (matVecMul k z) (matVecMul S w) := by
    rw [← matVecMul_mul, vecDot_matVecMul_transpose]
  have e3 : vecDot w (matVecMul (S * k) z) = vecDot w (matVecMul S (matVecMul k z)) := by
    rw [matVecMul_mul]
  -- expand the left side
  have hleft : blockVecDot (z, w) (blockMatVecMul A (z, w))
      = vecDot z (matVecMul σ z) + vecDot (matVecMul k z) (matVecMul S (matVecMul k z))
        - vecDot (matVecMul k z) (matVecMul S w)
        - vecDot w (matVecMul S (matVecMul k z)) + vecDot w (matVecMul S w) := by
    show vecDot z (matVecMul A.upperLeft z + matVecMul A.upperRight w)
        + vecDot w (matVecMul A.lowerLeft z + matVecMul S w) = _
    rw [vecDot_add_right, vecDot_add_right, hUL, hUR, hLL, matVecMul_add_mat,
      matVecMul_neg_mat, matVecMul_neg_mat, vecDot_add_right, vecDot_neg_right,
      vecDot_neg_right, e1, e2, e3]
    ring
  -- expand the right side
  have hright : vecDot (matVecMul k z - w) (matVecMul S (matVecMul k z - w))
      = vecDot (matVecMul k z) (matVecMul S (matVecMul k z))
        - vecDot (matVecMul k z) (matVecMul S w)
        - vecDot w (matVecMul S (matVecMul k z)) + vecDot w (matVecMul S w) := by
    have hsub : ∀ u v : Vec d, matVecMul S (u - v) = matVecMul S u - matVecMul S v := by
      intro u v
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
    have hA : vecDot (matVecMul k z - w) (matVecMul S (matVecMul k z - w))
        = vecDot (matVecMul k z) (matVecMul S (matVecMul k z - w))
          - vecDot w (matVecMul S (matVecMul k z - w)) := by
      rw [sub_eq_add_neg (matVecMul k z) w, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]
    have hB : ∀ y : Vec d, vecDot y (matVecMul S (matVecMul k z - w))
        = vecDot y (matVecMul S (matVecMul k z)) - vecDot y (matVecMul S w) := by
      intro y
      rw [hsub, sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, sub_eq_add_neg]
    rw [hA, hB, hB]
    ring
  rw [hleft, hright]
  ring

/-! ## Part B: `b_t ≤ 𝔡(A) · σ_*` -/

private theorem blockVecDot_blockScale (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X)
      = c * blockVecDot X (blockMatVecMul A X) := by
  have hs : ∀ (M : Mat d) (x : Vec d), matVecMul (c • M) x = c • matVecMul M x := by
    intro M x; funext i
    simp [matVecMul, Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  show vecDot X.1 (matVecMul (c • A.upperLeft) X.1 + matVecMul (c • A.upperRight) X.2)
      + vecDot X.2 (matVecMul (c • A.lowerLeft) X.1 + matVecMul (c • A.lowerRight) X.2)
    = c * (vecDot X.1 (matVecMul A.upperLeft X.1 + matVecMul A.upperRight X.2)
      + vecDot X.2 (matVecMul A.lowerLeft X.1 + matVecMul A.lowerRight X.2))
  rw [hs, hs, hs, hs, ← smul_add, ← smul_add, vecDot_smul_right, vecDot_smul_right]
  ring

/-- The swap-conjugate quadratic form at the special load `(z, -kᵀz)` is `z·σ_* z`. -/
private theorem swapConj_quad {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hfull : (toFullBlockMat A).PosDef) (hLR : IsUnit A.lowerRight.det) (z : Vec d) :
    blockVecDot (z, -matVecMul (matTranspose (schurSkew A)) z)
        (blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
            toFullBlockMat (blockSwap d)))
          (z, -matVecMul (matTranspose (schurSkew A)) z))
      = vecDot z (matVecMul (schurSigmaStar A) z) := by
  classical
  set k := schurSkew A with hkdef
  set S := A.lowerRight with hSdef
  set X : BlockVec d := (z, -matVecMul (matTranspose k) z) with hXdef
  set u : BlockVec d := (0, matVecMul S⁻¹ z) with hudef
  have hST : matTranspose S = S := sym_lowerRight hs
  have hLL : A.lowerLeft = -(S * k) := schur_lowerLeft hLR
  have hUR : A.upperRight = -(matTranspose k * S) := by
    rw [sym_upperRight hs, hLL]
    ext i j
    simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply, Matrix.mul_apply,
      Matrix.transpose_apply]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hsl : S j l = S l j := by
      have h2 := congrFun (congrFun hST l) j
      simpa [matTranspose, Matrix.transpose_apply] using h2
    rw [hsl]; ring
  have hSSinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hLR
  have hAu : blockMatVecMul A u = (X.2, X.1) := by
    refine Prod.ext ?_ ?_
    · show matVecMul A.upperLeft 0 + matVecMul A.upperRight (matVecMul S⁻¹ z)
        = -matVecMul (matTranspose k) z
      rw [matVecMul_zero_vec, zero_add, hUR, matVecMul_neg_mat, matVecMul_mul,
        Matrix.mul_assoc, hSSinv, Matrix.mul_one]
    · show matVecMul A.lowerLeft 0 + matVecMul S (matVecMul S⁻¹ z) = z
      rw [matVecMul_zero_vec, zero_add, matVecMul_mul, hSSinv]
      funext i; simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  have hRsym : (toFullBlockMat (blockSwap d))ᵀ = toFullBlockMat (blockSwap d) := by
    ext α β
    have := Analysis.isSymmetricBlockMat_blockSwap d β α
    simpa [toFullBlockMat_eq_blockMatEntry] using this
  have hAinv : (toFullBlockMat A)⁻¹ * toFullBlockMat A = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hfull.isUnit)
  have hY : toFullBlockVec (blockMatVecMul (blockSwap d) X)
      = (toFullBlockMat (blockSwap d)) *ᵥ toFullBlockVec X := by
    rw [toFullBlockVec_blockMatVecMul]
  have key : blockVecDot X (blockMatVecMul
      (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
        toFullBlockMat (blockSwap d))) X) = blockVecDot (X.2, X.1) u := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_ofFullBlockMat]
    have hstep : (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
        toFullBlockMat (blockSwap d)) *ᵥ toFullBlockVec X
        = toFullBlockMat (blockSwap d) *ᵥ ((toFullBlockMat A)⁻¹ *ᵥ
            (toFullBlockMat (blockSwap d) *ᵥ toFullBlockVec X)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hRmove : ∀ v w : FullBlockVec d,
        v ⬝ᵥ (toFullBlockMat (blockSwap d) *ᵥ w)
          = (toFullBlockMat (blockSwap d) *ᵥ v) ⬝ᵥ w := by
      intro v w
      have hvm : v ᵥ* toFullBlockMat (blockSwap d) = toFullBlockMat (blockSwap d) *ᵥ v := by
        rw [← hRsym, Matrix.vecMul_transpose, hRsym]
      rw [Matrix.dotProduct_mulVec, hvm]
    rw [hstep, hRmove]
    have hswapX : toFullBlockMat (blockSwap d) *ᵥ toFullBlockVec X
        = toFullBlockVec ((X.2, X.1) : BlockVec d) := by
      rw [← toFullBlockVec_blockMatVecMul, blockMatVecMul_blockSwap]
    rw [hswapX]
    have hAu' : toFullBlockMat A *ᵥ toFullBlockVec u = toFullBlockVec ((X.2, X.1) : BlockVec d) := by
      rw [← toFullBlockVec_blockMatVecMul, hAu]
    rw [← hAu', Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec, hAu',
      dotProduct_toFullBlockVec]
  rw [key]
  show vecDot X.2 0 + vecDot X.1 (matVecMul S⁻¹ z) = _
  have hz : vecDot X.2 (0 : Vec d) = 0 := by simp [vecDot]
  rw [hz, zero_add, hXdef]
  show vecDot z (matVecMul S⁻¹ z) = vecDot z (matVecMul (schurSigmaStar A) z)
  rfl

/-! ### Part B, conclusion: `b_t ≤ 𝔡(A)·σ_*` -/

private theorem matTranspose_respSym_eq_self (A : BlockMat d) :
    matTranspose (respSym A) = respSym A := by
  ext i j
  simp only [respSym, matTranspose, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul]
  ring

private theorem schurSkew_add_transpose (A : BlockMat d) :
    schurSkew A + matTranspose (schurSkew A) = (2 : ℝ) • respSym A := by
  ext i j
  simp only [respSym, matTranspose, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul]
  ring

private theorem schurSkew_sub_respSkew (A : BlockMat d) :
    schurSkew A - respSkew A = respSym A := by
  ext i j
  simp only [respSkew, respSym, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    matTranspose, Matrix.transpose_apply, smul_eq_mul]
  ring

private theorem vecDot_conj (M S : Mat d) (hM : matTranspose M = M) (z : Vec d) :
    vecDot z (matVecMul (M * S * M) z) = vecDot (matVecMul M z) (matVecMul S (matVecMul M z)) := by
  conv_lhs => rw [show M * S * M = matTranspose M * S * M by rw [hM]]
  rw [Matrix.mul_assoc, ← matVecMul_mul, ← matVecMul_mul, vecDot_matVecMul_transpose]

private theorem zero_le_quad {S : Mat d} (hS : S.PosDef) (y : Vec d) :
    0 ≤ vecDot y (matVecMul S y) := by
  have h := hS.posSemidef.dotProduct_mulVec_nonneg y
  simpa [star_trivial, vecDot, matVecMul] using! h

private theorem respBlockB_quad (A : BlockMat d) (z : Vec d) :
    vecDot z (matVecMul (respBlockB A) z)
      = vecDot z (matVecMul (schurSigma A) z)
        + vecDot (matVecMul (respSym A) z)
            (matVecMul A.lowerRight (matVecMul (respSym A) z)) := by
  rw [respBlockB, matVecMul_add_mat, vecDot_add_right,
    vecDot_conj _ _ (matTranspose_respSym_eq_self A)]

/-- **(b).**  `b_t = σ + r σ_*⁻¹ r ≤ 𝔡(A)·σ_*` pointwise, from
`loewner_swapConj_of_canonicalImbalance_le` tested at the load `(z, -kᵀz)`. -/
private theorem respBlockB_le_imbalance [NeZero d] (hd : 2 ≤ d) {A : BlockMat d}
    (hs : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A) (z : Vec d) :
    vecDot z (matVecMul (respBlockB A) z)
      ≤ canonicalImbalance A * vecDot z (matVecMul (schurSigmaStar A) z) := by
  have hfull : (toFullBlockMat A).PosDef := posDef_toFullBlockMat hs hp
  have hLRpd : A.lowerRight.PosDef := posDef_lowerRight hs hp
  have hLR : IsUnit A.lowerRight.det := (Matrix.isUnit_iff_isUnit_det _).mp hLRpd.isUnit
  have hLoew := loewner_swapConj_of_canonicalImbalance_le hd A hs hp (le_refl _)
  have hX := hLoew (z, -matVecMul (matTranspose (schurSkew A)) z)
  rw [blockQuad_schur hs hLR, blockVecDot_blockScale,
    swapConj_quad hs hfull hLR] at hX
  have hy : matVecMul (schurSkew A) z - -matVecMul (matTranspose (schurSkew A)) z
      = (2 : ℝ) • matVecMul (respSym A) z := by
    rw [sub_neg_eq_add, ← matVecMul_add_mat, schurSkew_add_transpose]
    funext i
    simp [matVecMul, Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  rw [hy] at hX
  have hscal : vecDot ((2 : ℝ) • matVecMul (respSym A) z)
      (matVecMul A.lowerRight ((2 : ℝ) • matVecMul (respSym A) z))
      = 4 * vecDot (matVecMul (respSym A) z) (matVecMul A.lowerRight
          (matVecMul (respSym A) z)) := by
    rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    ring
  rw [hscal] at hX
  have hQ : 0 ≤ vecDot (matVecMul (respSym A) z)
      (matVecMul A.lowerRight (matVecMul (respSym A) z)) := zero_le_quad hLRpd _
  rw [respBlockB_quad]
  linarith only [hX, hQ]

/-! ### Part A2: the printed identity `(L^-)^2 + (L^+)^2 = 4 p·b_t p` -/

/-- The two recentred loads, summed: the parallelogram law kills the cross terms. -/
private theorem quad_pair {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) (p q : Vec d) :
    blockVecDot (-p, q - matVecMul (respSkew A) p)
        (blockMatVecMul A (-p, q - matVecMul (respSkew A) p))
      + blockVecDot (-p, -(q + matVecMul (respSkew A) p))
        (blockMatVecMul A (-p, -(q + matVecMul (respSkew A) p)))
      = 2 * vecDot p (matVecMul (respBlockB A) p)
        + 2 * vecDot q (matVecMul A.lowerRight q) := by
  have hLRpd : A.lowerRight.PosDef := posDef_lowerRight hs hp
  have hLR : IsUnit A.lowerRight.det := (Matrix.isUnit_iff_isUnit_det _).mp hLRpd.isUnit
  have hST : matTranspose A.lowerRight = A.lowerRight := sym_lowerRight hs
  have hkr : matVecMul (schurSkew A) p - matVecMul (respSkew A) p
      = matVecMul (respSym A) p := by
    have hlin : matVecMul (schurSkew A - respSkew A) p
        = matVecMul (schurSkew A) p - matVecMul (respSkew A) p := by
      rw [sub_eq_add_neg, matVecMul_add_mat, matVecMul_neg_mat, ← sub_eq_add_neg]
    rw [← hlin, schurSkew_sub_respSkew]
  have hneg : ∀ y : Vec d, vecDot (-y) (matVecMul A.lowerRight (-y))
      = vecDot y (matVecMul A.lowerRight y) := by
    intro y
    rw [matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]
  have hnegS : vecDot (-p) (matVecMul (schurSigma A) (-p))
      = vecDot p (matVecMul (schurSigma A) p) := by
    rw [matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]
  have h1 : matVecMul (schurSkew A) (-p) - (q - matVecMul (respSkew A) p)
      = -(q + matVecMul (respSym A) p) := by
    rw [matVecMul_neg, ← hkr]
    abel
  have h2 : matVecMul (schurSkew A) (-p) - -(q + matVecMul (respSkew A) p)
      = q - matVecMul (respSym A) p := by
    rw [matVecMul_neg, ← hkr]
    abel
  rw [blockQuad_schur hs hLR, blockQuad_schur hs hLR, h1, h2, hnegS, hneg]
  have hpar : forall y : Vec d, vecDot (q + y) (matVecMul A.lowerRight (q + y))
      + vecDot (q - y) (matVecMul A.lowerRight (q - y))
      = 2 * vecDot q (matVecMul A.lowerRight q)
        + 2 * vecDot y (matVecMul A.lowerRight y) := by
    intro y
    have hcross := vecDot_sym hST q y
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
      vecDot_add_right, vecDot_neg_left, vecDot_neg_right]
    linarith only [hcross]
  linarith only [hpar (matVecMul (respSym A) p), respBlockB_quad A p]

/-- The Riccati exchange `q·σ_*⁻¹q = p·b_t p` for the calibrated loads
`p = m_t^{-1/2}e`, `q = m_t^{1/2}e`. -/
private theorem riccati_exchange {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) (e : Vec d) :
    vecDot (respQ A e) (matVecMul A.lowerRight (respQ A e))
      = vecDot (respP A e) (matVecMul (respBlockB A) (respP A e)) := by
  have hLRpd : A.lowerRight.PosDef := posDef_lowerRight hs hp
  have hLR : IsUnit A.lowerRight.det := (Matrix.isUnit_iff_isUnit_det _).mp hLRpd.isUnit
  have hbpd : (respBlockB A).PosDef := response_by_centered_energies_respBlockB_posDef hs hp
  have hsspd : (schurSigmaStar A).PosDef := Matrix.posDef_inv_iff.2 hLRpd
  have hmpd : (respM A).PosDef := GeometricMean.geoMeanPosDef hbpd hsspd
  have hriccati : respM A * (respBlockB A)⁻¹ * respM A = schurSigmaStar A :=
    GeometricMean.geoMean_riccati hbpd hsspd
  have hinv : (schurSigmaStar A)⁻¹ = A.lowerRight := Matrix.nonsing_inv_nonsing_inv _ hLR
  have hSeq : A.lowerRight = (respM A)⁻¹ * respBlockB A * (respM A)⁻¹ := by
    rw [← hinv, ← hriccati, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hbpd.isUnit),
      Matrix.mul_assoc]
  have hsqrtpd : (matSqrt (respM A)).PosDef := HCPolySupport.HighContrast.posDef_matSqrt hmpd
  have hminvT : matTranspose (respM A)⁻¹ = (respM A)⁻¹ := by
    have h := hmpd.inv.isHermitian.eq
    rw [HCPolySupport.HighContrast.conjTranspose_eq_transpose'] at h
    exact h
  have hminvsqrt : (respM A)⁻¹ * matSqrt (respM A) = (matSqrt (respM A))⁻¹ := by
    have hmm : matSqrt (respM A) * matSqrt (respM A) = respM A :=
      (matSqrt_spec hmpd.posSemidef).2
    have hu : IsUnit (matSqrt (respM A)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hsqrtpd.isUnit
    have hinvmm : (respM A)⁻¹ = (matSqrt (respM A))⁻¹ * (matSqrt (respM A))⁻¹ := by
      rw [← Matrix.mul_inv_rev, hmm]
    rw [hinvmm, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hpq : respP A e = matVecMul (matSqrt (respM A))⁻¹ e := by
    show matVecMul (matSqrt ((respM A)⁻¹)) e = matVecMul (matSqrt (respM A))⁻¹ e
    rw [HCPolySupport.HighContrast.matSqrt_inv hmpd]
  have hqq : respQ A e = matVecMul (matSqrt (respM A)) e := rfl
  have hA1 : matVecMul (respM A)⁻¹ (matVecMul (matSqrt (respM A)) e) = respP A e := by
    rw [matVecMul_mul, hminvsqrt, ← hpq]
  have hA2 : matVecMul ((respM A)⁻¹ * respBlockB A * (respM A)⁻¹)
        (matVecMul (matSqrt (respM A)) e)
      = matVecMul (respM A)⁻¹ (matVecMul (respBlockB A) (respP A e)) := by
    rw [← matVecMul_mul ((respM A)⁻¹ * respBlockB A) (respM A)⁻¹,
      ← matVecMul_mul (respM A)⁻¹ (respBlockB A), hA1]
  have hsymmove : forall x y : Vec d, vecDot x (matVecMul (respM A)⁻¹ y)
      = vecDot (matVecMul (respM A)⁻¹ x) y := by
    intro x y
    conv_lhs => rw [← hminvT]
    rw [vecDot_matVecMul_transpose]
  rw [hSeq, hqq, hA2, hsymmove, hA1]

/-- **(a).**  `p.response.transfer`. -/
private theorem lsq_sum_eq (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d)
    (hs : IsSymmetricBlockMat (respMean P jStar F t))
    (hp : Book.Ch02.BlockPosDef (respMean P jStar F t)) :
    respLsqMinus P jStar F t e + respLsqPlus P jStar F t e
      = 4 * vecDot (respP (respMean P jStar F t) e)
          (matVecMul (respBlockB (respMean P jStar F t))
            (respP (respMean P jStar F t) e)) := by
  rw [respLsqMinus_eq, respLsqPlus_eq, quad_pair hs hp,
    riccati_exchange hs hp]
  ring

/-! ### Part C: from `b_t ≤ 𝔡 σ_*` to the energy bound -/

private theorem quadG_le_of_mat_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (h : A ≤ B) (x : ι → ℝ) : x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x := by
  have ht := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at ht
  linarith only [ht]

private theorem matG_le_of_quad {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x : ι → ℝ, x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x) : A ≤ B := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_)
  intro x
  have hx := h x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  linarith only [hx]

private theorem quadG_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (c • M) *ᵥ x = c * (x ⬝ᵥ M *ᵥ x) := by
  simp [Matrix.smul_mulVec, dotProduct_smul]

/-- `Z ≤ c·Z⁻¹` forces `Z ≤ √c·I` for positive definite `Z`. -/
private theorem le_sqrt_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) {c : ℝ} (hc : 0 ≤ c) (h : Z ≤ c • Z⁻¹) :
    Z ≤ Real.sqrt c • (1 : Matrix ι ι ℝ) := by
  have hsqT : (matSqrt Z)ᴴ = matSqrt Z := HCPolySupport.HighContrast.conjTranspose_matSqrt hZ.posSemidef
  have hZZ : matSqrt Z * matSqrt Z = Z := (matSqrt_spec hZ.posSemidef).2
  have hsqpd : (matSqrt Z).PosDef := HCPolySupport.HighContrast.posDef_matSqrt hZ
  have hu : IsUnit (matSqrt Z).det := (Matrix.isUnit_iff_isUnit_det _).mp hsqpd.isUnit
  have hcong := HCPolySupport.HighContrast.conj_le_conj' hsqT h
  have hL : matSqrt Z * Z * matSqrt Z = Z * Z := by
    calc matSqrt Z * Z * matSqrt Z
        = matSqrt Z * (matSqrt Z * matSqrt Z) * matSqrt Z := by rw [hZZ]
      _ = (matSqrt Z * matSqrt Z) * (matSqrt Z * matSqrt Z) := by noncomm_ring
      _ = Z * Z := by rw [hZZ]
  have hZinv : Z⁻¹ = (matSqrt Z)⁻¹ * (matSqrt Z)⁻¹ := by
    rw [← Matrix.mul_inv_rev, hZZ]
  have hR : matSqrt Z * (c • Z⁻¹) * matSqrt Z = c • (1 : Matrix ι ι ℝ) := by
    calc matSqrt Z * (c • Z⁻¹) * matSqrt Z
        = c • (matSqrt Z * Z⁻¹ * matSqrt Z) := by simp
      _ = c • (matSqrt Z * ((matSqrt Z)⁻¹ * (matSqrt Z)⁻¹) * matSqrt Z) := by rw [← hZinv]
      _ = c • (1 : Matrix ι ι ℝ) := by
          congr 1
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
            Matrix.nonsing_inv_mul _ hu]
  rw [hL, hR] at hcong
  have hZZpsd : (Z * Z).PosSemidef := by
    have hh := Matrix.posSemidef_conjTranspose_mul_self Z
    rwa [hZ.isHermitian.eq] at hh
  have hnorm : ‖Z * Z‖ ≤ c := GeometricMean.norm_le_of_le_smul_one hZZpsd hc hcong
  have hsq : ‖Z‖ ^ 2 ≤ c := by
    rwa [GeometricMean.norm_mul_self_of_symm hZ.isHermitian.eq] at hnorm
  have hnn : ‖Z‖ ≤ Real.sqrt c := by
    have h1 : Real.sqrt (‖Z‖ ^ 2) ≤ Real.sqrt c := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg Z)] at h1
  exact GeometricMean.le_smul_one_of_norm_le hZ.posSemidef hnn

private theorem canonicalImbalance_nonneg (A : BlockMat d) :
    0 ≤ canonicalImbalance A := norm_nonneg _

/-- The calibrated quadratic form is bounded by the square root of the canonical imbalance. -/
private theorem respP_quad_le [NeZero d] (hd : 2 ≤ d) {A : BlockMat d}
    (hs : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A)
    (e : Vec d) (he : vecDot e e = 1) :
    vecDot (respP A e) (matVecMul (respBlockB A) (respP A e))
      ≤ Real.sqrt (canonicalImbalance A) := by
  have hLRpd : A.lowerRight.PosDef := posDef_lowerRight hs hp
  have hbpd : (respBlockB A).PosDef := response_by_centered_energies_respBlockB_posDef hs hp
  have hsspd : (schurSigmaStar A).PosDef := Matrix.posDef_inv_iff.2 hLRpd
  have hmpd : (respM A).PosDef := GeometricMean.geoMeanPosDef hbpd hsspd
  have hriccati : respM A * (respBlockB A)⁻¹ * respM A = schurSigmaStar A :=
    GeometricMean.geoMean_riccati hbpd hsspd
  have hpq : respP A e = matVecMul (matSqrt (respM A))⁻¹ e := by
    show matVecMul (matSqrt ((respM A)⁻¹)) e = matVecMul (matSqrt (respM A))⁻¹ e
    rw [HCPolySupport.HighContrast.matSqrt_inv hmpd]
  set R := matSqrt (respM A) with hRdef
  have hsqpd : R.PosDef := HCPolySupport.HighContrast.posDef_matSqrt hmpd
  have hsqinvpd : (R⁻¹).PosDef := hsqpd.inv
  have hsqinvT : matTranspose R⁻¹ = R⁻¹ := by
    have h := hsqinvpd.isHermitian.eq
    rw [HCPolySupport.HighContrast.conjTranspose_eq_transpose'] at h
    exact h
  have hu : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp hsqpd.isUnit
  have hmm : R * R = respM A := (matSqrt_spec hmpd.posSemidef).2
  have hcancelL : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ hu
  have hcancelR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  set Z : Mat d := R⁻¹ * respBlockB A * R⁻¹ with hZdef
  have hZpd : Z.PosDef := GeometricMean.posDef_conj_of_posDef hbpd hsqinvpd
  have hZinv : Z⁻¹ = R * (respBlockB A)⁻¹ * R := by
    rw [hZdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc]
  have hconjss : R⁻¹ * schurSigmaStar A * R⁻¹ = Z⁻¹ := by
    rw [← hriccati, hZinv, ← hmm]
    calc R⁻¹ * (R * R * (respBlockB A)⁻¹ * (R * R)) * R⁻¹
        = (R⁻¹ * R) * (R * (respBlockB A)⁻¹ * R) * (R * R⁻¹) := by noncomm_ring
      _ = R * (respBlockB A)⁻¹ * R := by
          rw [hcancelL, hcancelR, Matrix.one_mul, Matrix.mul_one]
  have hZle : Z ≤ canonicalImbalance A • Z⁻¹ := by
    refine matG_le_of_quad hZpd.isHermitian ?_ ?_
    · have hh : (Z⁻¹)ᵀ = Z⁻¹ := by
        have h0 : (Z⁻¹)ᴴ = Z⁻¹ := hZpd.inv.isHermitian
        rwa [HCPolySupport.HighContrast.conjTranspose_eq_transpose'] at h0
      simp [Matrix.IsHermitian, hh]
    · intro x
      have hq : vecDot x (matVecMul Z x) ≤
          canonicalImbalance A * vecDot x (matVecMul Z⁻¹ x) := by
        rw [hZdef, vecDot_conj _ _ hsqinvT, ← hconjss, vecDot_conj _ _ hsqinvT]
        exact respBlockB_le_imbalance hd hs hp _
      have hr : x ⬝ᵥ (canonicalImbalance A • Z⁻¹) *ᵥ x
          = canonicalImbalance A * (x ⬝ᵥ Z⁻¹ *ᵥ x) := quadG_smul _ _ _
      rw [hr]
      exact hq
  have hfin := le_sqrt_smul_one hZpd (canonicalImbalance_nonneg A) hZle
  have hquad := quadG_le_of_mat_le hfin e
  have hrhs : e ⬝ᵥ (Real.sqrt (canonicalImbalance A) • (1 : Mat d)) *ᵥ e
      = Real.sqrt (canonicalImbalance A) * (e ⬝ᵥ e) := by
    rw [quadG_smul, Matrix.one_mulVec]
  rw [hrhs] at hquad
  have hee : (e ⬝ᵥ e) = 1 := he
  rw [hee, mul_one] at hquad
  have hgoal : vecDot (respP A e) (matVecMul (respBlockB A) (respP A e))
      = vecDot e (matVecMul Z e) := by
    rw [hpq, hZdef, vecDot_conj _ _ hsqinvT]
  rw [hgoal]
  exact hquad

/-! ### Part C, conclusion -/

private theorem lsq_sum_le [NeZero d] (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (he : vecDot e e = 1)
    (hs : IsSymmetricBlockMat (respMean P jStar F t))
    (hp : Book.Ch02.BlockPosDef (respMean P jStar F t)) :
    respLsqMinus P jStar F t e + respLsqPlus P jStar F t e
      ≤ 4 * Real.sqrt (respKappa P jStar F t) := by
  rw [lsq_sum_eq P jStar F t e hs hp]
  have h := respP_quad_le hd hs hp e he
  show 4 * vecDot (respP (respMean P jStar F t) e)
      (matVecMul (respBlockB (respMean P jStar F t)) (respP (respMean P jStar F t) e))
    ≤ 4 * Real.sqrt (canonicalImbalance (respMean P jStar F t))
  linarith only [h]

theorem ehatMinus_scale_cmp (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s t : ℤ) (X : BlockVec d) (c : ℝ)
    (hcmp : ∀ Y : BlockVec d, blockVecDot Y (blockMatVecMul (respMean P jStar F s) Y)
      ≤ c * blockVecDot Y (blockMatVecMul (respMean P jStar F t) Y)) :
    blockVecDot X (blockMatVecMul (respEhatMinus P jStar F s) X)
      ≤ c * blockVecDot X (blockMatVecMul (respEhatMinus P jStar F t) X) := by
  rw [respEhatMinus, respEhatMinus, blockVecDot_blockCongr, blockVecDot_blockCongr]
  exact hcmp _

theorem ehatPlus_scale_cmp (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s t : ℤ) (X : BlockVec d) (c : ℝ)
    (hcmp : ∀ Y : BlockVec d, blockVecDot Y (blockMatVecMul (respMean P jStar F s) Y)
      ≤ c * blockVecDot Y (blockMatVecMul (respMean P jStar F t) Y)) :
    blockVecDot X (blockMatVecMul (respEhatPlus P jStar F s) X)
      ≤ c * blockVecDot X (blockMatVecMul (respEhatPlus P jStar F t) X) := by
  rw [respEhatPlus, respEhatPlus, blockAdjoint, blockAdjoint, respEhatMinus, respEhatMinus,
    blockVecDot_blockCongr, blockVecDot_blockCongr, blockVecDot_blockCongr,
    blockVecDot_blockCongr]
  exact hcmp _

/-- The scale comparison `E_s ≤ r E_t` in quadratic-form shape. -/
theorem respMean_scale_cmp (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s t : ℤ) (c : ℝ)
    (hfull : toFullBlockMat (respMean P jStar F s) ≤ c • toFullBlockMat (respMean P jStar F t))
    (Y : BlockVec d) :
    blockVecDot Y (blockMatVecMul (respMean P jStar F s) Y)
      ≤ c * blockVecDot Y (blockMatVecMul (respMean P jStar F t) Y) := by
  have h := quadG_le_of_mat_le hfull (toFullBlockVec Y)
  rw [quadG_smul] at h
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul]
  exact h

/-! ### Conjuncts 5, 6 (the energy bound) and 9, 10 (the defect bound) -/

theorem respEJ_le [NeZero d] (hd : 2 ≤ d) (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (s t : ℤ) (e : Vec d)
    (he : vecDot e e = 1) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hsymm : IsSymmetricBlockMat (respMean P jStar F t))
    (hposd : Book.Ch02.BlockPosDef (respMean P jStar F t))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hkts : respKappa P jStar F t ≤ respKappa P jStar F s) :
    respEJMinus P jStar F t e ≤ 2 * Real.sqrt (respKappa P jStar F s) ∧
      respEJPlus P jStar F t e ≤ 2 * Real.sqrt (respKappa P jStar F s) := by
  have hM : (respM (respMean P jStar F t)).PosDef := response_by_centered_energies_respM_posDef hsymm hposd
  have h1 := respEJMinus_nonneg P jStar F t e hq hg
  have h2 := respEJPlus_nonneg P jStar F t e hq hg
  have h3 := respEJMinus_eq_final P jStar F t e he hq hg hM hint
  have h4 := respEJPlus_eq_final P jStar F t e he hq hg hM hint
  have hsum := lsq_sum_le hd P jStar F t e he hsymm hposd
  have hsqle : Real.sqrt (respKappa P jStar F t) ≤ Real.sqrt (respKappa P jStar F s) :=
    Real.sqrt_le_sqrt hkts
  constructor <;> linarith only [h1, h2, h3, h4, hsum, hsqle]

end HCPolySupport.HighContrast.Multiscale
end
