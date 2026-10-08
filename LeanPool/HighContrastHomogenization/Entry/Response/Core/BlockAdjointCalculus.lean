/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects

/-!
# High-contrast homogenization: Entry.Response.Core.BlockAdjointCalculus

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur calculus for the centred block response

This file develops the block algebra behind the centred-response identity
`e.response.by.centered.energies`, for a single symmetric positive doubled block. It proves the
Schur formulas expressing the block energy, the block mean and the centred response of a doubled
block in terms of its constituent pieces, together with the calculus of the block adjoint
`K ↦ -K` — its positivity, symmetry and skewness behaviour under conjugation — and the
cancellation of the basis trace the identity relies on. Every statement concerns a single
symmetric positive doubled block in isolation; none of it refers to a raw coefficient sample.
-/

section
/-!
## The block algebra of the centred responses

The Schur formulas for the block energy, the block means and the centred response, the
block-adjoint calculus (`K -> -K`), and the basis-trace cancellation, all used by the
centred-response identity `e.response.by.centered.energies`
(`p.response.transfer`).  Nothing here mentions `RawOutput`; every statement is
about a single symmetric positive doubled block.
-/

open HCPolySupport.HighContrast (blockVecDot_inr matSqrt posDef_lowerRight schurSigma
  schurSigmaStar schurSkew)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- `blockAdjoint A` negates the off-diagonal blocks of `A` and keeps its diagonal blocks. -/
theorem response_by_centered_energies_aux_adjoint (A : BlockMat d) :
    blockAdjoint A = ⟨A.upperLeft, -A.upperRight, -A.lowerLeft, A.lowerRight⟩ := by
  rw [← ofFullBlockMat_toFullBlockMat (blockAdjoint A),
    ← ofFullBlockMat_toFullBlockMat
      (⟨A.upperLeft, -A.upperRight, -A.lowerLeft, A.lowerRight⟩ : BlockMat d)]
  congr 1
  ext (i | i) (j | j) <;>
    simp [blockAdjoint, blockCongr, blockD, toFullBlockMat, ofFullBlockMat,
      Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- The skew Schur coefficient flips sign under the block adjoint. -/
theorem response_by_centered_energies_aux_adjoint_skew (A : BlockMat d) :
    schurSkew (blockAdjoint A) = -schurSkew A := by
  rw [response_by_centered_energies_aux_adjoint]
  unfold schurSkew
  simp only [Matrix.mul_neg, neg_neg]

/-- The Schur complement `schurSigma` is invariant under the block adjoint. -/
theorem response_by_centered_energies_aux_adjoint_sigma (A : BlockMat d) :
    schurSigma (blockAdjoint A) = schurSigma A := by
  unfold schurSigma
  rw [response_by_centered_energies_aux_adjoint_skew]
  rw [response_by_centered_energies_aux_adjoint]
  simp only [matTranspose, Matrix.transpose_neg, neg_mul, mul_neg, neg_neg]

/-- The block adjoint preserves symmetry. -/
theorem response_by_centered_energies_aux_adjoint_symm {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) : IsSymmetricBlockMat (blockAdjoint A) := by
  rw [response_by_centered_energies_aux_adjoint]
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j => simpa [blockMatEntry] using hA (Sum.inl i) (Sum.inl j)
      | inr j => simpa [blockMatEntry] using hA (Sum.inl i) (Sum.inr j)
  | inr i =>
      cases β with
      | inl j => simpa [blockMatEntry] using hA (Sum.inr i) (Sum.inl j)
      | inr j => simpa [blockMatEntry] using hA (Sum.inr i) (Sum.inr j)

/-- The block adjoint preserves positive definiteness. -/
theorem response_by_centered_energies_aux_adjoint_pos {A : BlockMat d}
    (hp : Book.Ch02.BlockPosDef A) : Book.Ch02.BlockPosDef (blockAdjoint A) := by
  rw [response_by_centered_energies_aux_adjoint]
  intro X hX
  have hX' : (X.1, -X.2) ≠ (0 : BlockVec d) := by
    intro h
    apply hX
    have h1 : X.1 = 0 := congrArg Prod.fst h
    have h2 : X.2 = 0 := by
      have h2' : -X.2 = 0 := congrArg Prod.snd h
      simpa using congrArg Neg.neg h2'
    exact Prod.ext h1 h2
  have h := hp (X.1, -X.2) hX'
  convert h using 1
  all_goals
    simp [blockVecDot, blockMatVecMul, matVecMul_neg, neg_matVecMul,
      vecDot_neg_left]
  all_goals simp [vecDot_add_right, vecDot_neg_right]
  all_goals ring

/-- The block response mean `blockResponseMean A (-p, q')`, expanded through the Schur
cancellation identities `schur_cancel` into the skew and Schur-complement pieces of `A`. -/
theorem response_by_centered_energies_aux_mean (A : BlockMat d)
    (hA : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A) (p q' : Vec d) :
    blockResponseMean A (-p, q') =
      (-p + matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p),
        q' - matVecMul (matTranspose (schurSkew A))
              (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p)) -
          matVecMul (schurSigma A) p) := by
  obtain ⟨hk, hk'⟩ := schur_cancel hA hp
  have hU : A.upperRight = -(matTranspose (schurSkew A) * A.lowerRight) := by
    have hk'' : matTranspose (schurSkew A) * A.lowerRight = -A.upperRight := by
      simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hk'
    rw [← neg_neg A.upperRight, ← hk'']
  have hC : A.lowerLeft = -(A.lowerRight * schurSkew A) := by rw [hk, neg_neg]
  have hA11 : A.upperLeft = schurSigma A +
      matTranspose (schurSkew A) * A.lowerRight * schurSkew A := by
    unfold schurSigma
    abel
  have hzero (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
    funext i
    simp [matVecMul]
  have hone (x : Vec d) : matVecMul (1 : Mat d) x = x := by
    funext i
    simp [matVecMul, Matrix.one_apply]
  rw [show blockResponseMean A (-p, q') =
      (-p + matVecMul A.lowerLeft (-p) + matVecMul A.lowerRight q',
       q' + matVecMul A.upperLeft (-p) + matVecMul A.upperRight q') by
        ext i <;>
          simp [blockResponseMean, blockSwap, Book.Ch02.blockR, blockMatVecMul,
            hzero, hone, Pi.add_apply] <;> ring]
  rw [hU, hC, hA11]
  ext i <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, matVecMul_add, matVecMul_neg,
      matVecMul_mul, neg_matVecMul, Matrix.mul_assoc]
  · ring
  · simp only [add_matVecMul]
    simp only [Pi.add_apply]
    ring

/-- The block response energy `blockResponseEnergy A p q'`, expanded through the Schur
cancellation identities into the skew and Schur-complement pieces of `A`. -/
theorem response_by_centered_energies_aux_energy (A : BlockMat d)
    (hA : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A) (p q' : Vec d) :
    blockResponseEnergy A p q' =
      (1 / 2 : ℝ) * vecDot p (matVecMul (schurSigma A) p) +
        (1 / 2 : ℝ) * vecDot (q' + matVecMul (schurSkew A) p)
          (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p)) - vecDot p q' := by
  obtain ⟨hk, hk'⟩ := schur_cancel hA hp
  have hU : A.upperRight = -(matTranspose (schurSkew A) * A.lowerRight) := by
    have hk'' : matTranspose (schurSkew A) * A.lowerRight = -A.upperRight := by
      simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hk'
    rw [← neg_neg A.upperRight, ← hk'']
  have hC : A.lowerLeft = -(A.lowerRight * schurSkew A) := by rw [hk, neg_neg]
  have hLsymm : A.lowerRight.IsSymm := by
    ext i j
    exact hA (Sum.inr j) (Sum.inr i)
  have hA11 : A.upperLeft = schurSigma A +
      matTranspose (schurSkew A) * A.lowerRight * schurSkew A := by
    unfold schurSigma
    abel
  unfold blockResponseEnergy blockVecDot blockMatVecMul
  rw [hU, hC, hA11]
  simp only [matVecMul_neg, neg_matVecMul, add_matVecMul,
    vecDot_add_left, vecDot_add_right, vecDot_neg_left,
    vecDot_neg_right, Matrix.mul_assoc]
  have hL : ∀ x y : Vec d, vecDot x (matVecMul A.lowerRight y) =
      vecDot y (matVecMul A.lowerRight x) := by
    intro x y
    conv_lhs => rw [← hLsymm.eq]
    change vecDot x (matVecMul (matTranspose A.lowerRight) y) = _
    rw [vecDot_matVecMul_transpose, vecDot_comm]
  have hKK : vecDot p (matVecMul
      (matTranspose (schurSkew A) * (A.lowerRight * schurSkew A)) p) =
      vecDot (matVecMul (schurSkew A) p)
        (matVecMul A.lowerRight (matVecMul (schurSkew A) p)) := by
    rw [← matVecMul_mul, vecDot_matVecMul_transpose, ← matVecMul_mul]
  have hKq : vecDot p
      (matVecMul (matTranspose (schurSkew A) * A.lowerRight) q') =
      vecDot (matVecMul (schurSkew A) p) (matVecMul A.lowerRight q') := by
    rw [← matVecMul_mul, vecDot_matVecMul_transpose]
  have hqK : vecDot q' (matVecMul (A.lowerRight * schurSkew A) p) =
      vecDot (matVecMul (schurSkew A) p) (matVecMul A.lowerRight q') := by
    rw [← matVecMul_mul, hL]
  rw [hKK, hKq, hqK]
  simp only [matVecMul_add, vecDot_add_right]
  rw [hL q' (matVecMul (schurSkew A) p)]
  ring

/-- The centred response `blockCenteredResponse A p q'`, expanded via
`response_by_centered_energies_aux_energy` and `response_by_centered_energies_aux_mean`. -/
theorem response_by_centered_energies_aux_centered (A : BlockMat d)
    (hA : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A) (p q' : Vec d) :
    blockCenteredResponse A p q' = (1 / 2 : ℝ) *
      (vecDot (matVecMul (schurSkew A)
          (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p)))
        (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p)) +
       vecDot (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p))
        (matVecMul (schurSigma A) p) - vecDot p q') := by
  rw [blockCenteredResponse, response_by_centered_energies_aux_energy A hA hp,
    response_by_centered_energies_aux_mean A hA hp]
  simp only [sub_eq_add_neg, vecDot_add_left, vecDot_add_right,
    vecDot_neg_left, vecDot_neg_right]
  have hK : vecDot
      (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p))
      (matVecMul (matTranspose (schurSkew A))
        (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p))) =
      vecDot (matVecMul (schurSkew A)
        (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p)))
        (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p)) := by
    rw [vecDot_matVecMul_transpose]
  have hq : vecDot q' (matVecMul A.lowerRight
      (q' + matVecMul (schurSkew A) p)) =
      vecDot (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p)) q' :=
    vecDot_comm _ _
  have hKp : vecDot p (matVecMul (matTranspose (schurSkew A))
      (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p))) =
      vecDot (matVecMul (schurSkew A) p)
        (matVecMul A.lowerRight (q' + matVecMul (schurSkew A) p)) := by
    rw [vecDot_matVecMul_transpose]
  rw [hK, hq, hKp]
  ring

/-- The sum of the centred responses at `(p, q - h_t p)` and at the adjoint `(p, q + h_t p)`,
expanded into the Schur-complement and `respSym` cross terms: the key algebraic identity behind
the centred-response identity. -/
theorem response_by_centered_energies_aux_centered_sum (A : BlockMat d)
    (hA : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A) (p q : Vec d) :
    blockCenteredResponse A p
        (q - matVecMul (respSkew A) p) +
      blockCenteredResponse (blockAdjoint A) p
        (q + matVecMul (respSkew A) p) =
      vecDot p (matVecMul (schurSigma A * A.lowerRight - 1) q) +
        2 * vecDot p
          (matVecMul (respSym A * A.lowerRight * respSym A * A.lowerRight) q) := by
  rw [response_by_centered_energies_aux_centered A hA hp,
    response_by_centered_energies_aux_centered (blockAdjoint A)
      (response_by_centered_energies_aux_adjoint_symm hA)
      (response_by_centered_energies_aux_adjoint_pos hp)]
  rw [response_by_centered_energies_aux_adjoint_skew,
    response_by_centered_energies_aux_adjoint_sigma,
    response_by_centered_energies_aux_adjoint]
  have hKr : schurSkew A - respSkew A = respSym A := by
    unfold respSkew respSym
    module
  have hrT : matTranspose (respSym A) = respSym A := by
    unfold respSym matTranspose
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose]
    congr 1
    abel
  have hLT : matTranspose A.lowerRight = A.lowerRight := by
    ext i j
    exact hA (Sum.inr j) (Sum.inr i)
  have hUT : matTranspose A.upperLeft = A.upperLeft := by
    ext i j
    exact hA (Sum.inl j) (Sum.inl i)
  have hST : matTranspose (schurSigma A) = schurSigma A := by
    unfold schurSigma matTranspose at hUT hLT ⊢
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hLT, hUT]
    rw [Matrix.mul_assoc]
  have hminus : q - matVecMul (respSkew A) p + matVecMul (schurSkew A) p =
      q + matVecMul (respSym A) p := by
    calc
      _ = q + (matVecMul (schurSkew A) p - matVecMul (respSkew A) p) := by module
      _ = q + matVecMul (schurSkew A - respSkew A) p := by rw [sub_matVecMul]
      _ = _ := by rw [hKr]
  have hplus : q + matVecMul (respSkew A) p + matVecMul (-schurSkew A) p =
      q - matVecMul (respSym A) p := by
    rw [neg_matVecMul]
    calc
      _ = q - (matVecMul (schurSkew A) p - matVecMul (respSkew A) p) := by module
      _ = q - matVecMul (schurSkew A - respSkew A) p := by rw [sub_matVecMul]
      _ = _ := by rw [hKr]
  rw [hminus, hplus]
  simp only [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
  simp only [matVecMul_add, matVecMul_neg, neg_matVecMul, add_matVecMul,
    vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right]
  have hSterm : vecDot (matVecMul A.lowerRight q) (matVecMul (schurSigma A) p) =
      vecDot p (matVecMul (schurSigma A * A.lowerRight) q) := by
    rw [← matVecMul_mul]
    calc
      _ = vecDot (matVecMul (schurSigma A) p) (matVecMul A.lowerRight q) :=
        vecDot_comm _ _
      _ = vecDot p (matVecMul (matTranspose (schurSigma A))
          (matVecMul A.lowerRight q)) :=
        (vecDot_matVecMul_transpose _ _ _).symm
      _ = _ := by rw [hST]
  have hcross :
      vecDot (matVecMul (schurSkew A) (matVecMul A.lowerRight q))
          (matVecMul A.lowerRight (matVecMul (respSym A) p)) +
        vecDot (matVecMul (schurSkew A)
            (matVecMul A.lowerRight (matVecMul (respSym A) p)))
          (matVecMul A.lowerRight q) =
        2 * vecDot p
          (matVecMul (respSym A * A.lowerRight * respSym A * A.lowerRight) q) := by
    let u := matVecMul A.lowerRight q
    let v := matVecMul A.lowerRight (matVecMul (respSym A) p)
    change vecDot (matVecMul (schurSkew A) u) v +
      vecDot (matVecMul (schurSkew A) v) u = _
    have hKsym : matTranspose (schurSkew A) + schurSkew A =
        (2 : ℝ) • respSym A := by
      unfold respSym
      ext i j
      simp [matTranspose, Matrix.transpose_apply]
      ring
    have hsum : vecDot (matVecMul (schurSkew A) u) v +
        vecDot (matVecMul (schurSkew A) v) u =
        2 * vecDot u (matVecMul (respSym A) v) := by
      rw [← vecDot_matVecMul_transpose, vecDot_comm (matVecMul (schurSkew A) v) u,
        ← vecDot_add_right, ← add_matVecMul, hKsym, smul_matVecMul,
        vecDot_smul_right]
    rw [hsum]
    congr 1
    rw [← matVecMul_mul, ← matVecMul_mul, ← matVecMul_mul]
    change vecDot u (matVecMul (respSym A) v) =
      vecDot p (matVecMul (respSym A)
        (matVecMul A.lowerRight (matVecMul (respSym A) u)))
    calc
      vecDot u (matVecMul (respSym A) v) =
          vecDot (matVecMul (respSym A) u) v := by
            conv_lhs => rw [← hrT]
            exact vecDot_matVecMul_transpose _ _ _
      _ = vecDot v (matVecMul (respSym A) u) := vecDot_comm _ _
      _ = vecDot (matVecMul (respSym A) p)
          (matVecMul A.lowerRight (matVecMul (respSym A) u)) := by
            dsimp [v]
            have ht := vecDot_matVecMul_transpose (matVecMul (respSym A) p)
              (matVecMul (respSym A) u) A.lowerRight
            rw [hLT] at ht
            exact ht.symm
      _ = _ := by
            have ht := vecDot_matVecMul_transpose p
              (matVecMul A.lowerRight (matVecMul (respSym A) u)) (respSym A)
            rw [hrT] at ht
            exact ht.symm
  have hone : matVecMul (1 : Mat d) q = q := by
    funext i
    simp [matVecMul, Matrix.one_apply]
  rw [hSterm, hone]
  linarith only [hcross]

/-- The dual Schur complement `schurSigmaStar A` is Loewner-below the primal one
`schurSigma A`, given the swap-conjugate Loewner hypothesis `ho`. -/
theorem response_by_centered_energies_aux_sigmaStar_le_sigma {A : BlockMat d}
    (hs : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A)
    (ho : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d))) A) :
    schurSigmaStar A ≤ schurSigma A := by
  have hflux : MatLoewnerLE ((schurSigma A)⁻¹) A.lowerRight := by
    intro x
    have h := ho (0, x)
    simp only [blockVecDot_inr] at h
    rw [Analysis.swapConj_lowerRight hs hp] at h
    exact h
  have hS := Analysis.posDef_schurSigma hs hp
  have hL := posDef_lowerRight hs hp
  have hflux' : (schurSigma A)⁻¹ ≤ A.lowerRight := by
    apply Matrix.le_iff.mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hL.isHermitian.sub hS.inv.isHermitian) ?_
    intro x
    have hx := hflux x
    have hx' : vecDot x (matVecMul (schurSigma A)⁻¹ x) ≤
        vecDot x (matVecMul A.lowerRight x) := by
      linarith only [hx]
    have hx'' : x ⬝ᵥ (schurSigma A)⁻¹ *ᵥ x ≤ x ⬝ᵥ A.lowerRight *ᵥ x := by
      simpa only [dotProduct, Matrix.mulVec, vecDot, matVecMul, star_trivial] using hx'
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    exact sub_nonneg.mpr hx''
  have hi := inv_le_inv_of_le hS.inv hL
    hflux'
  simpa only [Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit), schurSigmaStar] using hi

/-- A uniform bound `|Jminus e| + |Jplus e| ≤ M` at every unit basis vector sums, over the `d`
standard basis vectors, to at most `d * M`. -/
theorem response_by_centered_energies_aux_sum_bound
    (Jminus Jplus : Vec d → ℝ) (M : ℝ)
    (hM : ∀ e : Vec d, vecDot e e = 1 → |Jminus e| + |Jplus e| ≤ M) :
    ∑ i : Fin d, (Jminus (Pi.single i 1) + Jplus (Pi.single i 1)) ≤ (d : ℝ) * M := by
  calc
    _ ≤ ∑ _i : Fin d, M := by
      apply Finset.sum_le_sum
      intro i _hi
      refine (add_le_add (le_abs_self _) (le_abs_self _)).trans (hM _ ?_)
      simp [vecDot, Pi.single_apply]
    _ = _ := by simp

/-- The basis sum of the Schur-complement and `respSym` cross terms is bounded by `d * M`,
combining `response_by_centered_energies_aux_centered_sum` with the uniform response bound
`hM`. -/
theorem response_by_centered_energies_aux_response_sum (A : BlockMat d)
    (hA : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A)
    (Jminus Jplus : Vec d → ℝ)
    (hJ : ∀ e : Vec d,
      Jminus e + Jplus e =
        blockCenteredResponse A (respP A e)
            (respQ A e - matVecMul (respSkew A) (respP A e)) +
          blockCenteredResponse (blockAdjoint A) (respP A e)
            (respQ A e + matVecMul (respSkew A) (respP A e)))
    (M : ℝ) (hM : ∀ e : Vec d, vecDot e e = 1 → |Jminus e| + |Jplus e| ≤ M) :
    ∑ i : Fin d,
      (vecDot (respP A (Pi.single i 1))
          (matVecMul (schurSigma A * A.lowerRight - 1)
            (respQ A (Pi.single i 1))) +
        2 * vecDot (respP A (Pi.single i 1))
          (matVecMul (respSym A * A.lowerRight * respSym A * A.lowerRight)
            (respQ A (Pi.single i 1)))) ≤ (d : ℝ) * M := by
  calc
    _ = ∑ i : Fin d, (Jminus (Pi.single i 1) + Jplus (Pi.single i 1)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hJ]
      exact (response_by_centered_energies_aux_centered_sum A hA hp _ _).symm
    _ ≤ _ := response_by_centered_energies_aux_sum_bound Jminus Jplus M hM

/-- The basis sum `∑ᵢ (m^{-1/2} eᵢ). C (m^{1/2} eᵢ)` equals `trace C`, for `m` positive
definite, by cyclicity of the trace and cancellation of the two square roots. -/
theorem response_by_centered_energies_aux_basis_trace {m : Mat d} (hm : m.PosDef)
    (C : Mat d) :
    ∑ i : Fin d, vecDot (matVecMul (matSqrt m⁻¹) (Pi.single i 1))
      (matVecMul C (matVecMul (matSqrt m) (Pi.single i 1))) = Matrix.trace C := by
  have hPt : matTranspose (matSqrt m⁻¹) = matSqrt m⁻¹ := by
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (HCPolySupport.HighContrast.posDef_matSqrt hm.inv).isHermitian.eq
  calc
    _ = ∑ i : Fin d, (matSqrt m⁻¹ * C * matSqrt m) i i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← vecDot_matVecMul_transpose, hPt]
      rw [matVecMul_mul (matSqrt m⁻¹) C,
        matVecMul_mul (matSqrt m⁻¹ * C) (matSqrt m)]
      rw [vecDot_single_left, matVecMul_single]
    _ = Matrix.trace (matSqrt m⁻¹ * C * matSqrt m) := rfl
    _ = Matrix.trace (matSqrt m * matSqrt m⁻¹ * C) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace C := by
      rw [(GeometricMean.sqrtCancel hm).1, Matrix.one_mul]

/-! ## The metric dichotomy of the selected grid

`respGrid jStar F` is `𝒬(m(F))`, the rounded grid of the canonical metric of `F`.  The metric
is positive semidefinite for every `F` -- no hypothesis -- because the junk values of
`matSqrt` and of `Matrix.inv` are positive semidefinite
(`Geometry.explicitCanonicalMetric_posSemidef`).  So exactly one of two things happens: the metric
is
positive definite, which is the branch on which the pullback estimates apply, or it is
singular, and then the selected grid is the zero matrix, which is the branch on which the
adapted cell is Lebesgue-null.  This is Step 0' of the response cutoff kernel; it is why that
kernel needs no positivity hypothesis on `F`. -/

end

end HCPolySupport.HighContrast.Multiscale
end
