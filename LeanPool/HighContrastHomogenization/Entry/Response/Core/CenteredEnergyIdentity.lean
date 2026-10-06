/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.GeoMeanBlocks
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.BlockAdjointCalculus
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryExponent

/-!
# High-contrast homogenization: Entry.Response.Core.CenteredEnergyIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centred-response energy comparison

This file proves the centred-response energy identity `e.response.by.centered.energies`. The key
input is the printed matrix comparison `e.matrix.block.comparison`,
`F ≤ (1 + 6(θ - 1)) F♯`, established at the skew correction `h = h_t` for which `k - h = r_t` is
symmetric and the printed transpose step is the identity; the file also proves the Loewner,
quadratic-form and positive-semidefiniteness facts the comparison needs along the way. It then
packages the hypothesis bundles — `RespCalibrated`, `RespCutoffBound`, `RespEnergyDefect`,
`RespLoadBound`, `RespLoadMean`, `RespSourceSmall` and `RespWeakBound` — that carry each stage of
the decomposition of `adapted_response_core` into the next, and proves the centred-energy estimate
itself from them.
-/

section
/-!
## The block comparison and the trace step

Two inputs of `e.response.by.centered.energies`:

* `response_by_centered_energies_block_comparison`, the printed matrix comparison
  `e.matrix.block.comparison` (near `e.matrix.block.comparison`) `F <= (1+6(theta-1)) F^sharp`,
  proved at the skew correction `h = h_t`, for which `k - h = r_t` is symmetric and the printed
  transpose step is an identity;
* `response_by_centered_energies_loewner_of_trace`, the passage from the trace estimate of
  `p.response.transfer` to the Loewner estimate `b_t <= (1+c) S_*`, through
  `lambda_max <= tr` on the positive semidefinite normalized defect.
-/

open HCPolySupport.HighContrast (matLoewnerLE_smul_iff_conj matSqrt matSqrt_lowerRight_spec
  matSqrt_spec posDef_lowerRight posSemidef_lowerRight schurSigma schurSigmaStar schurSkew)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}
/-- The explicit Schur inverse of a symmetric positive block. -/
theorem response_by_centered_energies_full_inv {A : BlockMat d}
    (hs : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A) :
    (toFullBlockMat A)⁻¹ =
      Matrix.fromBlocks (schurSigma A)⁻¹ ((schurSigma A)⁻¹ * (schurSkew A)ᴴ)
        (schurSkew A * (schurSigma A)⁻¹)
        (schurSkew A * (schurSigma A)⁻¹ * (schurSkew A)ᴴ + A.lowerRight⁻¹) := by
  have hS := Analysis.posDef_schurSigma hs hp
  have hL := posDef_lowerRight hs hp
  have hSi : schurSigma A * (schurSigma A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)
  have hLi : A.lowerRight * A.lowerRight⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hL.isUnit)
  obtain ⟨hk, hk'⟩ := schur_cancel hs hp
  have hU : A.upperRight = -((schurSkew A)ᴴ * A.lowerRight) := by rw [hk', neg_neg]
  have hC : A.lowerLeft = -(A.lowerRight * schurSkew A) := by rw [hk, neg_neg]
  have hA11 : A.upperLeft = schurSigma A + (schurSkew A)ᴴ * A.lowerRight * schurSkew A := by
    unfold schurSigma
    simp only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    abel
  apply Matrix.inv_eq_right_inv
  rw [toFullBlockMat_eq_fromBlocks, hU, hC, hA11, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1
  · rw [Matrix.add_mul, Matrix.neg_mul, hSi]
    rw [Matrix.mul_assoc ((schurSkew A)ᴴ * A.lowerRight) (schurSkew A) (schurSigma A)⁻¹,
      Matrix.mul_assoc ((schurSkew A)ᴴ) A.lowerRight (schurSkew A * (schurSigma A)⁻¹),
      ← Matrix.mul_assoc A.lowerRight (schurSkew A) (schurSigma A)⁻¹]
    abel
  · rw [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_add]
    rw [← Matrix.mul_assoc (schurSigma A) (schurSigma A)⁻¹ ((schurSkew A)ᴴ), hSi, Matrix.one_mul]
    rw [Matrix.mul_assoc ((schurSkew A)ᴴ * A.lowerRight) (schurSkew A)
        ((schurSigma A)⁻¹ * (schurSkew A)ᴴ),
      ← Matrix.mul_assoc (schurSkew A) (schurSigma A)⁻¹ ((schurSkew A)ᴴ)]
    rw [Matrix.mul_assoc ((schurSkew A)ᴴ) A.lowerRight
        (schurSkew A * (schurSigma A)⁻¹ * (schurSkew A)ᴴ)]
    rw [Matrix.mul_assoc ((schurSkew A)ᴴ) A.lowerRight A.lowerRight⁻¹, hLi, Matrix.mul_one]
    abel
  · rw [Matrix.neg_mul, Matrix.mul_assoc A.lowerRight (schurSkew A) (schurSigma A)⁻¹]
    abel
  · rw [Matrix.neg_mul, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    rw [hLi]
    abel

/-- The Schur form of the block quadratic form. -/
theorem response_by_centered_energies_qform {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) (x y : Vec d) :
    blockVecDot (x, y) (blockMatVecMul A (x, y)) =
      vecDot x (matVecMul (schurSigma A) x) +
        vecDot (y - matVecMul (schurSkew A) x)
          (matVecMul A.lowerRight (y - matVecMul (schurSkew A) x)) := by
  have hE := response_by_centered_energies_aux_energy A hs hp (-x) y
  unfold blockResponseEnergy at hE
  rw [neg_neg] at hE
  simp only [matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg,
    sub_eq_add_neg, matVecMul_add] at hE ⊢
  linarith only [hE]

/-- The blocks of the reflected inverse `A^# = R A⁻¹ R`. -/
theorem response_by_centered_energies_sharp_blocks {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) :
    ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
        toFullBlockMat (blockSwap d)) =
      (⟨schurSkew A * (schurSigma A)⁻¹ * (schurSkew A)ᴴ + A.lowerRight⁻¹,
        schurSkew A * (schurSigma A)⁻¹, (schurSigma A)⁻¹ * (schurSkew A)ᴴ,
        (schurSigma A)⁻¹⟩ : BlockMat d) := by
  have hR : toFullBlockMat (blockSwap d) = Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
    rw [toFullBlockMat_eq_fromBlocks]; rfl
  rw [response_by_centered_energies_full_inv hs hp, hR, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
  rfl

/-- The Schur form of the quadratic form of `A^# = R A⁻¹ R`. -/
theorem response_by_centered_energies_qform_sharp {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) (x y : Vec d) :
    blockVecDot (x, y) (blockMatVecMul (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d))) (x, y)) =
      vecDot x (matVecMul A.lowerRight⁻¹ x) +
        vecDot (y + matVecMul (matTranspose (schurSkew A)) x)
          (matVecMul (schurSigma A)⁻¹ (y + matVecMul (matTranspose (schurSkew A)) x)) := by
  have hH : (schurSkew A)ᴴ = matTranspose (schurSkew A) := by
    simp [matTranspose]
  have hflip : ∀ v : Vec d, vecDot x (matVecMul (schurSkew A) v) =
      vecDot (matVecMul (matTranspose (schurSkew A)) x) v := by
    intro v
    have h := vecDot_matVecMul_transpose x v (matTranspose (schurSkew A))
    rwa [show matTranspose (matTranspose (schurSkew A)) = schurSkew A from by
      simp [matTranspose]] at h
  rw [response_by_centered_energies_sharp_blocks hs hp, hH]
  simp only [blockVecDot, blockMatVecMul, add_matVecMul, ← matVecMul_mul, matVecMul_add,
    vecDot_add_left, vecDot_add_right]
  simp only [hflip]
  ring

/-- Scalar core of the printed block comparison `e.matrix.block.comparison`. -/
theorem response_by_centered_energies_cross {θ a b n tw tLx β : ℝ}
    (hH : b + 25 * n ≤ a + (25 * tw + 10 * β + tLx))
    (hF1 : a ≤ θ * b) (hF2 : tLx ≤ 4 * (θ * b) - 4 * b) (hF3 : tw ≤ θ * n) :
    a + (tw - 2 * β + tLx) ≤ (1 + 6 * (θ - 1)) * (b + n) := by
  linarith only [hH, hF1, hF2, hF3]

/-- **`e.matrix.block.comparison`** (near `e.matrix.block.comparison`) at the skew
correction `h = h_t`, for which `k - h = r_t` is symmetric. -/
theorem response_by_centered_energies_block_comparison {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A)
    (ho : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d))) A)
    {θ : ℝ} (hθ : 1 ≤ θ)
    (hle : MatLoewnerLE (respBlockB A) (θ • schurSigmaStar A)) :
    canonicalImbalance A ≤ 1 + 6 * (θ - 1) := by
  have hθ0 : (0 : ℝ) < θ := by linarith only [hθ]
  have hT : A.lowerRight.PosDef := posDef_lowerRight hs hp
  have hS : (schurSigma A).PosDef := Analysis.posDef_schurSigma hs hp
  have hLsymm : A.lowerRight.IsSymm := by
    ext i j; exact hs (Sum.inr j) (Sum.inr i)
  have hTform : ∀ u v : Vec d, vecDot u (matVecMul A.lowerRight v) =
      vecDot v (matVecMul A.lowerRight u) := by
    intro u v
    conv_lhs => rw [← hLsymm.eq]
    change vecDot u (matVecMul (matTranspose A.lowerRight) v) = _
    rw [vecDot_matVecMul_transpose, vecDot_comm]
  have hTnn : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul A.lowerRight v) := fun v =>
    hT.posSemidef.dotProduct_mulVec_nonneg v
  have hrsym : matTranspose (respSym A) = respSym A := by
    unfold respSym matTranspose
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose]
    congr 1
    abel
  have hrflip : ∀ x v : Vec d, vecDot x (matVecMul (respSym A) v) =
      vecDot (matVecMul (respSym A) x) v := by
    intro x v
    have h := vecDot_matVecMul_transpose x v (respSym A)
    rw [hrsym] at h
    exact h
  have hbils : ∀ u v : Vec d, vecDot (u - v) (matVecMul A.lowerRight (u - v)) =
      vecDot u (matVecMul A.lowerRight u) - 2 * vecDot u (matVecMul A.lowerRight v) +
        vecDot v (matVecMul A.lowerRight v) := by
    intro u v
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
      vecDot_add_right, vecDot_neg_left, vecDot_neg_right]
    rw [hTform v u]
    ring
  -- the contrast hypothesis, pointwise
  have hle_pt : ∀ x : Vec d, vecDot x (matVecMul (schurSigma A) x) +
      vecDot (matVecMul (respSym A) x)
        (matVecMul A.lowerRight (matVecMul (respSym A) x)) ≤
      θ * vecDot x (matVecMul A.lowerRight⁻¹ x) := by
    intro x
    have h := hle x
    unfold respBlockB schurSigmaStar at h
    simp only [add_matVecMul, ← matVecMul_mul, smul_matVecMul, vecDot_add_right,
      vecDot_smul_right] at h
    rw [hrflip] at h
    linarith only [h]
  -- the reference order, pointwise
  have hba : ∀ x : Vec d, vecDot x (matVecMul A.lowerRight⁻¹ x) ≤
      vecDot x (matVecMul (schurSigma A) x) := by
    intro x
    have hmat : schurSigmaStar A ≤ schurSigma A := response_by_centered_energies_aux_sigmaStar_le_sigma hs hp ho
    have h := (BlockGeometricMean.matLE_iff hT.inv.isHermitian hS.isHermitian).1 hmat x
    linarith only [h]
  have hF1 : ∀ x : Vec d, vecDot x (matVecMul (schurSigma A) x) ≤
      θ * vecDot x (matVecMul A.lowerRight⁻¹ x) := by
    intro x
    have h1 := hle_pt x
    have h2 := hTnn (matVecMul (respSym A) x)
    linarith only [h1, h2]
  have hF2r : ∀ x : Vec d, vecDot (matVecMul (respSym A) x)
      (matVecMul A.lowerRight (matVecMul (respSym A) x)) ≤
      (θ - 1) * vecDot x (matVecMul A.lowerRight⁻¹ x) := by
    intro x
    have h1 := hle_pt x
    have h2 := hba x
    linarith only [h1, h2]
  -- the dual bound `T ≤ θ σ⁻¹`
  have hσle : schurSigma A ≤ θ • A.lowerRight⁻¹ := by
    refine (BlockGeometricMean.matLE_iff hS.isHermitian ?_).2 ?_
    · change (θ • A.lowerRight⁻¹)ᴴ = _
      rw [Matrix.conjTranspose_smul, star_trivial, hT.inv.isHermitian.eq]
    · intro x
      have h := hF1 x
      simp only [smul_matVecMul, vecDot_smul_right]
      linarith only [h]
  have hF3 : ∀ w : Vec d, vecDot w (matVecMul A.lowerRight w) ≤
      θ * vecDot w (matVecMul (schurSigma A)⁻¹ w) := by
    have hinv := inv_le_inv_of_le hS (hT.inv.smul hθ0) hσle
    rw [inv_smul_real hT.inv hθ0.ne', Matrix.nonsing_inv_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hT.isUnit)] at hinv
    have hsc := smul_le_smul_of_nonneg_left hinv hθ0.le
    rw [smul_smul, mul_inv_cancel₀ hθ0.ne', one_smul] at hsc
    intro w
    have h := (BlockGeometricMean.matLE_iff hT.isHermitian ?_).1 hsc w
    · simp only [smul_matVecMul, vecDot_smul_right] at h
      linarith only [h]
    · change (θ • (schurSigma A)⁻¹)ᴴ = _
      rw [Matrix.conjTranspose_smul, star_trivial, hS.inv.isHermitian.eq]
  -- the printed test vector
  have hsum2 : matTranspose (schurSkew A) + schurSkew A = respSym A + respSym A := by
    unfold respSym
    module
  have hH : ∀ x w : Vec d,
      vecDot x (matVecMul A.lowerRight⁻¹ x) + vecDot w (matVecMul (schurSigma A)⁻¹ w) ≤
      vecDot x (matVecMul (schurSigma A) x) +
        vecDot (w - (matVecMul (respSym A) x + matVecMul (respSym A) x))
          (matVecMul A.lowerRight
            (w - (matVecMul (respSym A) x + matVecMul (respSym A) x))) := by
    intro x w
    have h := ho (x, w - matVecMul (matTranspose (schurSkew A)) x)
    rw [response_by_centered_energies_qform_sharp hs hp, response_by_centered_energies_qform hs hp] at h
    rw [sub_add_cancel] at h
    rw [show w - matVecMul (matTranspose (schurSkew A)) x - matVecMul (schurSkew A) x =
        w - (matVecMul (respSym A) x + matVecMul (respSym A) x) by
      rw [sub_sub, ← add_matVecMul, ← add_matVecMul, hsum2]] at h
    linarith only [h]
  -- assemble
  have hmain : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul A X) ≤
      (1 + 6 * (θ - 1)) * blockVecDot X (blockMatVecMul (ofFullBlockMat
        (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
          toFullBlockMat (blockSwap d))) X) := by
    rintro ⟨x, y⟩
    rw [response_by_centered_energies_qform hs hp, response_by_centered_energies_qform_sharp hs hp]
    set w : Vec d := y + matVecMul (matTranspose (schurSkew A)) x with hw
    set rr : Vec d := matVecMul (respSym A) x + matVecMul (respSym A) x with hrr
    have hrr2 : rr = matVecMul (matTranspose (schurSkew A)) x + matVecMul (schurSkew A) x := by
      rw [hrr, ← add_matVecMul, ← add_matVecMul, hsum2]
    have hy : y - matVecMul (schurSkew A) x = w - rr := by
      rw [hw, hrr2]; abel
    rw [hy]
    -- instantiate the printed test vector at `-5 w`
    have hneg := hH x ((-5 : ℝ) • w)
    have hn5 : vecDot ((-5 : ℝ) • w) (matVecMul (schurSigma A)⁻¹ ((-5 : ℝ) • w)) =
        25 * vecDot w (matVecMul (schurSigma A)⁻¹ w) := by
      rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]; ring
    have hexp : vecDot ((-5 : ℝ) • w - rr) (matVecMul A.lowerRight ((-5 : ℝ) • w - rr)) =
        25 * vecDot w (matVecMul A.lowerRight w) +
          10 * vecDot w (matVecMul A.lowerRight rr) +
          vecDot rr (matVecMul A.lowerRight rr) := by
      rw [hbils]
      rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right, vecDot_smul_left]
      ring
    rw [hn5, hexp] at hneg
    have hpos := hH x w
    have hLsq : vecDot rr (matVecMul A.lowerRight rr) =
        4 * vecDot (matVecMul (respSym A) x)
          (matVecMul A.lowerRight (matVecMul (respSym A) x)) := by
      rw [hrr]
      simp only [matVecMul_add, vecDot_add_left, vecDot_add_right]
      rw [hTform (matVecMul (respSym A) x) (matVecMul (respSym A) x)]
      ring
    rw [hbils]
    refine response_by_centered_energies_cross (θ := θ) ?_ (hF1 x) ?_ (hF3 w)
    · linarith only [hneg]
    · rw [hLsq]
      have := hF2r x
      linarith only [this]
  -- back to the full matrix order
  have hsharp : (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
      toFullBlockMat (blockSwap d)).PosDef := by
    have h := Analysis.swapConj_posDef (posDef_toFullBlockMat hs hp)
    rwa [toFullBlockMat_ofFullBlockMat] at h
  refine imbalance_le_of_le (posDef_toFullBlockMat hs hp) (by linarith only [hθ]) ?_
  apply Matrix.le_iff.mpr
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.sub ?_ ((Analysis.toFullBlockMat_isHermitian_iff A).2 hs)
    change ((1 + 6 * (θ - 1)) • (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
      toFullBlockMat (blockSwap d)))ᴴ = _
    rw [Matrix.conjTranspose_smul, star_trivial, hsharp.isHermitian.eq]
  · intro v
    have hx := hmain (ofFullBlockVec v)
    simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_ofFullBlockVec, toFullBlockMat_ofFullBlockMat] at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul]
    linarith only [hx]

/-- A positive semidefinite matrix is dominated by its trace. -/
theorem response_by_centered_energies_psd_le_trace {P : Mat d} (hP : P.PosSemidef) (x : Vec d) :
    vecDot x (matVecMul P x) ≤ Matrix.trace P * vecDot x x := by
  obtain ⟨hBpsd, hBB⟩ := matSqrt_spec hP
  have hBt : matTranspose (matSqrt P) = matSqrt P := by
    have h := hBpsd.isHermitian.eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hBji : ∀ i j, matSqrt P j i = matSqrt P i j := by
    intro i j
    exact congrFun (congrFun hBt i) j
  have hstep : vecDot x (matVecMul P x) =
      vecDot (matVecMul (matSqrt P) x) (matVecMul (matSqrt P) x) := by
    conv_lhs => rw [← hBB]
    rw [← matVecMul_mul]
    have h := vecDot_matVecMul_transpose x (matVecMul (matSqrt P) x) (matSqrt P)
    rw [hBt] at h
    exact h
  have htr : Matrix.trace P = ∑ i : Fin d, ∑ j : Fin d, matSqrt P i j ^ 2 := by
    conv_lhs => rw [← hBB]
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hBji i j]; ring
  have hxx : vecDot x x = ∑ j : Fin d, x j ^ 2 := by
    unfold vecDot
    exact Finset.sum_congr rfl fun j _ => (sq (x j)).symm
  rw [hstep, htr, hxx]
  have hcs : ∀ i : Fin d,
      matVecMul (matSqrt P) x i * matVecMul (matSqrt P) x i ≤
        (∑ j : Fin d, matSqrt P i j ^ 2) * ∑ j : Fin d, x j ^ 2 := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => matSqrt P i j) (fun j => x j)
    calc matVecMul (matSqrt P) x i * matVecMul (matSqrt P) x i
        = (∑ j : Fin d, matSqrt P i j * x j) ^ 2 := by
          unfold matVecMul; ring
      _ ≤ _ := h
  calc vecDot (matVecMul (matSqrt P) x) (matVecMul (matSqrt P) x)
      = ∑ i : Fin d, matVecMul (matSqrt P) x i * matVecMul (matSqrt P) x i := rfl
    _ ≤ ∑ _i : Fin d, (∑ j : Fin d, matSqrt P _i j ^ 2) * ∑ j : Fin d, x j ^ 2 :=
        Finset.sum_le_sum fun i _ => hcs i
    _ = (∑ i : Fin d, ∑ j : Fin d, matSqrt P i j ^ 2) * ∑ j : Fin d, x j ^ 2 := by
        rw [← Finset.sum_mul]

/-- `r_t` is symmetric. -/
theorem response_by_centered_energies_respSym_herm (A : BlockMat d) : (respSym A)ᴴ = respSym A := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  have : matTranspose (respSym A) = respSym A := by
    unfold respSym matTranspose
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose]
    congr 1
    abel
  exact this

/-- `r_t S_*^{-1} r_t` is positive semidefinite. -/
theorem response_by_centered_energies_rTr_posSemidef {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) :
    (respSym A * A.lowerRight * respSym A).PosSemidef := by
  have h := (posDef_lowerRight hs hp).posSemidef.conjTranspose_mul_mul_same (respSym A)
  rwa [response_by_centered_energies_respSym_herm] at h

/-- `b_t` is positive definite. -/
theorem response_by_centered_energies_respBlockB_posDef {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) : (respBlockB A).PosDef :=
  (Analysis.posDef_schurSigma hs hp).add_posSemidef
    (response_by_centered_energies_rTr_posSemidef hs hp)

/-- `m_t` is positive definite. -/
theorem response_by_centered_energies_respM_posDef {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) : (respM A).PosDef :=
  GeometricMean.geoMeanPosDef (response_by_centered_energies_respBlockB_posDef hs hp)
    (Matrix.posDef_inv_iff.2 (posDef_lowerRight hs hp))

/-- `tr(R b_t R) = tr(S S_*^{-1}) + tr(r_t S_*^{-1} r_t S_*^{-1})`, `R = S_*^{-1/2}`. -/
theorem response_by_centered_energies_trace_conj {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) :
    Matrix.trace (matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight) =
      Matrix.trace (schurSigma A * A.lowerRight) +
        Matrix.trace (respSym A * A.lowerRight * respSym A * A.lowerRight) := by
  have hRR : matSqrt A.lowerRight * matSqrt A.lowerRight = A.lowerRight :=
    (matSqrt_spec (posSemidef_lowerRight hs hp)).2
  calc Matrix.trace (matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight)
      = Matrix.trace (matSqrt A.lowerRight * (respBlockB A * matSqrt A.lowerRight)) := by
        congr 1; noncomm_ring
    _ = Matrix.trace (respBlockB A * matSqrt A.lowerRight * matSqrt A.lowerRight) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace (respBlockB A * (matSqrt A.lowerRight * matSqrt A.lowerRight)) := by
        congr 1; noncomm_ring
    _ = Matrix.trace (respBlockB A * A.lowerRight) := by rw [hRR]
    _ = _ := by
        unfold respBlockB
        rw [Matrix.add_mul, Matrix.trace_add]

/-- `tr(r_t S_*^{-1} r_t S_*^{-1}) ≥ 0`. -/
theorem response_by_centered_energies_trace_rTrT_nonneg {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) :
    0 ≤ Matrix.trace (respSym A * A.lowerRight * respSym A * A.lowerRight) := by
  have hRR : matSqrt A.lowerRight * matSqrt A.lowerRight = A.lowerRight :=
    (matSqrt_spec (posSemidef_lowerRight hs hp)).2
  have hRh : (matSqrt A.lowerRight)ᴴ = matSqrt A.lowerRight :=
    (matSqrt_spec (posSemidef_lowerRight hs hp)).1.isHermitian.eq
  set N : Mat d := matSqrt A.lowerRight * respSym A * matSqrt A.lowerRight with hN
  have hNh : Nᴴ = N := by
    rw [hN]
    simp only [Matrix.conjTranspose_mul, hRh, response_by_centered_energies_respSym_herm]
    noncomm_ring
  have h := (Matrix.posSemidef_conjTranspose_mul_self N).trace_nonneg
  rw [hNh] at h
  have hid : Matrix.trace (N * N) =
      Matrix.trace (respSym A * A.lowerRight * respSym A * A.lowerRight) := by
    calc Matrix.trace (N * N)
        = Matrix.trace (matSqrt A.lowerRight *
            (respSym A * matSqrt A.lowerRight *
              (matSqrt A.lowerRight * respSym A * matSqrt A.lowerRight))) := by
          rw [hN]; congr 1; noncomm_ring
      _ = Matrix.trace (respSym A * matSqrt A.lowerRight *
            (matSqrt A.lowerRight * respSym A * matSqrt A.lowerRight) *
              matSqrt A.lowerRight) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (respSym A * (matSqrt A.lowerRight * matSqrt A.lowerRight) *
            respSym A * (matSqrt A.lowerRight * matSqrt A.lowerRight)) := by
          congr 1; noncomm_ring
      _ = _ := by rw [hRR]
  linarith only [h, hid]

/-- From a trace bound on the normalized `b_t` to the Loewner bound `b_t ≤ (1+c) S_*`. -/
theorem response_by_centered_energies_loewner_of_trace {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A)
    (ho : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d))) A)
    {c : ℝ}
    (hc : Matrix.trace (matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight) -
      (d : ℝ) ≤ c) :
    MatLoewnerLE (respBlockB A) ((1 + c) • schurSigmaStar A) := by
  obtain ⟨hRt, hRdet, hRR⟩ := matSqrt_lowerRight_spec hs hp
  rw [matLoewnerLE_smul_iff_conj hRt hRR hRdet]
  have hRh : (matSqrt A.lowerRight)ᴴ = matSqrt A.lowerRight := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hRt
  -- the normalized defect is positive semidefinite
  have hBge : schurSigmaStar A ≤ respBlockB A := by
    refine (response_by_centered_energies_aux_sigmaStar_le_sigma hs hp ho).trans ?_
    have h := response_by_centered_energies_rTr_posSemidef hs hp
    rw [Matrix.le_iff]
    unfold respBlockB
    simpa using h
  have hpsd : (matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight -
      (1 : Mat d)).PosSemidef := by
    have h := (Matrix.le_iff.mp hBge).conjTranspose_mul_mul_same (matSqrt A.lowerRight)
    rw [hRh] at h
    have heq : matSqrt A.lowerRight * (respBlockB A - schurSigmaStar A) *
        matSqrt A.lowerRight =
        matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight - (1 : Mat d) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hRR]
    rwa [heq] at h
  have htr : Matrix.trace (matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight -
      (1 : Mat d)) =
      Matrix.trace (matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight) - (d : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
  intro x
  have hx := response_by_centered_energies_psd_le_trace hpsd x
  rw [htr] at hx
  have hxx : 0 ≤ vecDot x x := by
    unfold vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsplit : vecDot x (matVecMul (matSqrt A.lowerRight * respBlockB A *
      matSqrt A.lowerRight - (1 : Mat d)) x) =
      vecDot x (matVecMul (matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight) x) -
        vecDot x x := by
    rw [sub_matVecMul, matVecMul_one]
    simp only [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
  have hrhs : vecDot x (matVecMul ((1 + c) • (1 : Mat d)) x) = (1 + c) * vecDot x x := by
    rw [smul_matVecMul, matVecMul_one, vecDot_smul_right]
  rw [hrhs]
  rw [hsplit] at hx
  have hTX : (Matrix.trace (matSqrt A.lowerRight * respBlockB A * matSqrt A.lowerRight) -
      (d : ℝ) - c) * vecDot x x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) hxx
  linarith only [hx, hTX]
end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Decomposition of `adapted_response_core`, part 1: the predicate bundles and the
centred-energy estimate

The predicate bundles that carry the output of one step of the decomposition of
`adapted_response_core` into the hypotheses of the next, together with the centred-energy
estimate.
-/

open HCPolySupport.HighContrast (CoeffSpace aspectRatio blockScale matSqrt schurSigma)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## Bundles -/

/-- The calibrated-block sandwich `e.response.calibrated.blocks`
(`e.response.calibrated.blocks`):
`C^{-1} M_0 <= Ehat_t^± <= C kappa_t^{1/2} M_0` and `Ehat_s^± <= C kappa_s^{1/2} M_0`. -/
@[expose]
def RespCalibrated (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) : Prop :=
  BlockMatLoewnerLE (blockScale C⁻¹ (respM0 F)) (respEhatMinus P jStar F t) ∧
    BlockMatLoewnerLE (blockScale C⁻¹ (respM0 F)) (respEhatPlus P jStar F t) ∧
    BlockMatLoewnerLE (respEhatMinus P jStar F t)
      (blockScale (C * Real.sqrt (respKappa P jStar F t)) (respM0 F)) ∧
    BlockMatLoewnerLE (respEhatPlus P jStar F t)
      (blockScale (C * Real.sqrt (respKappa P jStar F t)) (respM0 F)) ∧
    BlockMatLoewnerLE (respEhatMinus P jStar F s)
      (blockScale (C * Real.sqrt (respKappa P jStar F s)) (respM0 F)) ∧
    BlockMatLoewnerLE (respEhatPlus P jStar F s)
      (blockScale (C * Real.sqrt (respKappa P jStar F s)) (respM0 F))

/-- The energy and defect bounds `e.response.energy.and.defect`
(`e.response.energy.and.defect`). -/
@[expose]
def RespEnergyDefect (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) : Prop :=
  0 ≤ respEJMinus P jStar F t e ∧ 0 ≤ respEJPlus P jStar F t e ∧
    respEJMinus P jStar F t e = (1 / 2 : ℝ) * respLsqMinus P jStar F t e - 1 ∧
    respEJPlus P jStar F t e = (1 / 2 : ℝ) * respLsqPlus P jStar F t e - 1 ∧
    respEJMinus P jStar F t e ≤ C * Real.sqrt (respKappa P jStar F s) ∧
    respEJPlus P jStar F t e ≤ C * Real.sqrt (respKappa P jStar F s) ∧
    0 ≤ respTauMinus P jStar F s t e ∧ 0 ≤ respTauPlus P jStar F s t e ∧
    respTauMinus P jStar F s t e ≤
      C * (respRatio P jStar F s t - 1) * Real.sqrt (respKappa P jStar F s) ∧
    respTauPlus P jStar F s t e ≤
      C * (respRatio P jStar F s t - 1) * Real.sqrt (respKappa P jStar F s)

/-- The load and mean bounds `e.response.load.and.mean`:
`|M_0^{1/2}x^±|^2 <= C kappa_s^{1/2}` and `|M_0^{1/2}Y^±|^2 <= C kappa_s`. -/
@[expose]
def RespLoadMean (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) : Prop :=
  blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (respxMinus P jStar F t e))
      (blockMatVecMul (blockSqrt (respM0 F)) (respxMinus P jStar F t e)) ≤
    C * Real.sqrt (respKappa P jStar F s) ∧
  blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (respxPlus P jStar F t e))
      (blockMatVecMul (blockSqrt (respM0 F)) (respxPlus P jStar F t e)) ≤
    C * Real.sqrt (respKappa P jStar F s) ∧
  blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (respYMinus P jStar F t e))
      (blockMatVecMul (blockSqrt (respM0 F)) (respYMinus P jStar F t e)) ≤
    C * respKappa P jStar F s ∧
  blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (respYPlus P jStar F t e))
      (blockMatVecMul (blockSqrt (respM0 F)) (respYPlus P jStar F t e)) ≤
    C * respKappa P jStar F s

/-- The source-smallness pair `e.response.source.smallness`
(`e.response.source.smallness`), with `Pi = aspectRatio E` and
`e(m)^2 = ‖m‖ ‖m⁻¹‖` for `m = explicitCanonicalMetric F`. -/
@[expose]
def RespSourceSmall (d : ℕ) (γ C η : ℝ) (E F : BlockMat d) (jStar : ℕ) (s t : ℤ) : Prop :=
  C * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
        (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤ η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) ∧
    C * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
        (3 : ℝ) ^ (-((3 : ℝ) / 2 * ((s : ℝ) - (jStar : ℝ)))) ≤ 1

/-- The generation-`n` summand of the source load `L_s` (`p.response.transfer`): the
printed weight `3^{-3n/2}` times the flat average over the generation-`(s-n)` cells of
`(|b_{s-n,z}^{1/2} P| + |(S_{*,s-n,z})^{-1/2} Q|)^2`.  `respSourceLoad` is the sum of this family
over `n`. -/
@[expose]
noncomputable def respSourceLoadSummand (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s : ℤ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
    ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
              Y.2))) ^ 2)

/-- The source load is the sum of its generation summands. -/
theorem respSourceLoad_eq_tsum_summand (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    respSourceLoad P jStar F s b Y = ∑' n : ℕ, respSourceLoadSummand P jStar F s b Y n := rfl

/-- The source-load bound `L_s^± <= C kappa_s^{3/2}` (`p.response.transfer`).
-- READING: `kappa_s^{3/2}` is written `(sqrt kappa_s)^3`.

The two summability conjuncts are not decoration.  `respSourceLoad` is a `tsum`, whose value on a
non-summable family is `0`, and the two inequalities above then hold vacuously; the estimate of
`e.response.cutoff.estimate` divides by `L_s^±` in the sense that it pairs against it, and is false
at the junk value.  The printed proof of the bound establishes convergence on the way ("the series
converges because `gamma < 3/2`"), so the summability belongs here, where `L_s^±` is produced. -/
@[expose]
def RespLoadBound (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) : Prop :=
  0 ≤ respLsMinus P jStar F s t e ∧ 0 ≤ respLsPlus P jStar F s t e ∧
    respLsMinus P jStar F s t e ≤ C * Real.sqrt (respKappa P jStar F s) ^ 3 ∧
    respLsPlus P jStar F s t e ≤ C * Real.sqrt (respKappa P jStar F s) ^ 3 ∧
    Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F) (respYMinus P jStar F t e)) ∧
    Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F) (respYPlus P jStar F t e))

/-- The weak-norm estimate `e.response.weak.estimate`:
`(W^±)^{1/2} <= C (3^{-alpha H} + C_H eta^{1/(2Q)}) kappa_s^{1/2}`. -/
@[expose]
def RespWeakBound (C : ℝ) (CH : ℕ → ℝ) (d : ℕ) (γ : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (η : ℝ) (s t : ℤ) (e : Vec d) : Prop :=
  0 ≤ respWMinus P jStar F t e ∧ 0 ≤ respWPlus P jStar F t e ∧
    Real.sqrt (respWMinus P jStar F t e) ≤
      C * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
        CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) * Real.sqrt (respKappa P jStar F s) ∧
    Real.sqrt (respWPlus P jStar F t e) ≤
      C * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
        CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) * Real.sqrt (respKappa P jStar F s)

/-- The cutoff estimate `e.response.cutoff.estimate`. -/
@[expose]
def RespCutoffBound (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ)
    (s t : ℤ) (e : Vec d) : Prop :=
  |respCenteredJMinus P jStar F t e| ≤
      C * (respTauMinus P jStar F s t e +
        Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
        Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
        (3 : ℝ) ^ (-(H : ℝ)) * (respEJMinus P jStar F t e +
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) +
        respWMinus P jStar F t e) ∧
    |respCenteredJPlus P jStar F t e| ≤
      C * (respTauPlus P jStar F s t e +
        Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
        Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
        (3 : ℝ) ^ (-(H : ℝ)) * (respEJPlus P jStar F t e +
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) +
        respWPlus P jStar F t e)

/-! ## The centred-energy estimate -/

/-- The centred-energy estimate `e.response.by.centered.energies`:
`kappa_t - 1 <= 12 d sup_{|e|=1}(|Jtilde^-(e)| + |Jtilde^+(e)|)`, stated with an explicit
bound `M` instead of a supremum.

Route: the trace identity of `p.response.transfer`
(`response_by_centered_energies_aux_centered_sum` and
`response_by_centered_energies_aux_basis_trace`), both trace terms nonnegative
(`p.response.transfer`,
`response_by_centered_energies_trace_rTrT_nonneg`), the passage from the trace estimate to the
Loewner estimate `b_t <= (1 + d M) S_*` (`response_by_centered_energies_loewner_of_trace`), and
then `e.matrix.block.comparison` (`e.matrix.block.comparison`) with `h = h_t`.

-- READING: the docstring of `Analysis.schurSigma_le_corrected`
together with `coupled_schur_le` as the in-tree form of `e.matrix.block.comparison`.  That is
not what those two prove: `coupled_schur_le` goes from an imbalance bound to a corrected-Schur
bound, i.e. the converse implication, and the only `6` in this direction is the
aspect-ratio six of `Analysis.refBlock_le_six_aspectRatio_smul_swapConj`.  The printed
`F <= (1+6(theta-1)) F^sharp` is therefore proved here from scratch, at `h = h_t`, as
`response_by_centered_energies_block_comparison`.

The printed `12 d` is `2 * 6 * d`: this proof gives `kappa_t - 1 <= 6 d M`, and `M >= 0`
supplies the remaining factor two. -/
theorem response_by_centered_energies (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (M : ℝ)
    (_hM : ∀ e : Vec d, vecDot e e = 1 →
      |respCenteredJMinus P jStar F t e| + |respCenteredJPlus P jStar F t e| ≤ M) :
    respKappa P jStar F t - 1 ≤ 12 * (d : ℝ) * M := by
  have := _raw.prob
  let : NeZero d := ⟨by omega⟩
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef _raw.symm _raw.pos
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
      (explicitCanonicalMetric F) hm t
  have hsT : IsSymmetricBlockMat (respMean P jStar F t) :=
    isSymmetricBlockMat_annealedBlock P _
  have hbT : Book.Ch02.BlockPosDef (respMean P jStar F t) :=
    blockPosDef_of_toFullBlockMat_posDef _ hEt
  have hoT : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat (respMean P jStar F t))⁻¹ * toFullBlockMat (blockSwap d)))
      (respMean P jStar F t) :=
    Analysis.adaptedMean_swapConj_le _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
      (explicitCanonicalMetric F) hm t
  have hM0 : 0 ≤ M := by
    have i0 : Fin d := ⟨0, by omega⟩
    have he : vecDot (Pi.single i0 (1 : ℝ)) (Pi.single i0 (1 : ℝ)) = 1 := by
      simp [vecDot, Pi.single_apply]
    have h := _hM _ he
    linarith only [h, abs_nonneg (respCenteredJMinus P jStar F t (Pi.single i0 (1 : ℝ))),
      abs_nonneg (respCenteredJPlus P jStar F t (Pi.single i0 (1 : ℝ)))]
  have hmpos : (respM (respMean P jStar F t)).PosDef := response_by_centered_energies_respM_posDef hsT hbT
  have hsum := response_by_centered_energies_aux_response_sum (respMean P jStar F t) hsT hbT
    (respCenteredJMinus P jStar F t) (respCenteredJPlus P jStar F t) (fun _ => rfl) M _hM
  have ht1 : ∑ i : Fin d, vecDot (respP (respMean P jStar F t) (Pi.single i 1))
      (matVecMul (schurSigma (respMean P jStar F t) * (respMean P jStar F t).lowerRight - 1)
        (respQ (respMean P jStar F t) (Pi.single i 1))) =
      Matrix.trace (schurSigma (respMean P jStar F t) *
        (respMean P jStar F t).lowerRight - 1) :=
    response_by_centered_energies_aux_basis_trace
      (m := respM (respMean P jStar F t)) hmpos _
  have ht2 : ∑ i : Fin d, vecDot (respP (respMean P jStar F t) (Pi.single i 1))
      (matVecMul (respSym (respMean P jStar F t) * (respMean P jStar F t).lowerRight *
        respSym (respMean P jStar F t) * (respMean P jStar F t).lowerRight)
        (respQ (respMean P jStar F t) (Pi.single i 1))) =
      Matrix.trace (respSym (respMean P jStar F t) * (respMean P jStar F t).lowerRight *
        respSym (respMean P jStar F t) * (respMean P jStar F t).lowerRight) :=
    response_by_centered_energies_aux_basis_trace
      (m := respM (respMean P jStar F t)) hmpos _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ht1, ht2] at hsum
  have htr1 : Matrix.trace (schurSigma (respMean P jStar F t) *
      (respMean P jStar F t).lowerRight - 1) =
      Matrix.trace (schurSigma (respMean P jStar F t) *
        (respMean P jStar F t).lowerRight) - (d : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
  have hnn := response_by_centered_energies_trace_rTrT_nonneg hsT hbT
  have hconj := response_by_centered_energies_trace_conj hsT hbT
  have hc : Matrix.trace (matSqrt (respMean P jStar F t).lowerRight *
      respBlockB (respMean P jStar F t) *
      matSqrt (respMean P jStar F t).lowerRight) - (d : ℝ) ≤ (d : ℝ) * M := by
    rw [hconj]
    rw [htr1] at hsum
    linarith only [hsum, hnn]
  have hL := response_by_centered_energies_loewner_of_trace hsT hbT hoT hc
  have hθ : (1 : ℝ) ≤ 1 + (d : ℝ) * M := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hM0
    linarith only [this]
  have hcmp := response_by_centered_energies_block_comparison hsT hbT hoT hθ hL
  have hκ : respKappa P jStar F t ≤ 1 + 6 * ((1 + (d : ℝ) * M) - 1) := hcmp
  have hdM : 0 ≤ (d : ℝ) * M := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hM0
  linarith only [hκ, hdM]

end HCPolySupport.HighContrast.Multiscale
end
