/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import Mathlib.Analysis.Matrix.Order

/-!
# High-contrast homogenization: Setup.SpectralBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scalar Loewner bound and the positive semidefinite square root

The reference text writes `|M|` for the spectral norm of a symmetric positive
semidefinite matrix and `m^{1/2}` for the positive square root.  This file proves
that the encodings `specBound` and `matSqrt` are those objects: `specBound M` is
the least `t ≥ 0` with `M ≤ t I`, and `matSqrt M` is *the* positive semidefinite
square root, independently of the choice made in its definition.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem matVecMul_one' (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem matVecMul_smul_one' (t : ℝ) (x : Vec d) :
    matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq, mul_comm]

private theorem vecDot_smul_self' (t : ℝ) (x : Vec d) :
    vecDot x (t • x) = t * vecNormSq x := by
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem vecDot_matVecMul_smul' (t : ℝ) (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (t • A) x) = t * vecDot x (matVecMul A x) := by
  simp only [vecDot, matVecMul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem specBoundSet_isClosed (M : Mat d) :
    IsClosed {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))} := by
  have hset : {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))} =
      {t : ℝ | 0 ≤ t} ∩
        ⋂ x : Vec d,
          {t : ℝ | (1 / 2 : ℝ) * vecDot x (matVecMul M x) ≤
            (1 / 2 : ℝ) * (t * vecNormSq x)} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, MatLoewnerLE,
      matVecMul_smul_one']
    constructor
    · rintro ⟨h0, h⟩
      exact ⟨h0, fun x => by rw [← vecDot_smul_self']; exact h x⟩
    · rintro ⟨h0, h⟩
      exact ⟨h0, fun x => by rw [vecDot_smul_self']; exact h x⟩
  rw [hset]
  refine isClosed_Ici.inter (isClosed_iInter fun x => ?_)
  exact isClosed_le continuous_const (by fun_prop)

/-- `specBound` is nonnegative, junk branch included. -/
theorem specBound_nonneg (M : Mat d) : 0 ≤ specBound M :=
  Real.sInf_nonneg fun _ hx => hx.1

/-- `specBound M` is a lower bound for the admissible scalar Loewner bounds. -/
theorem specBound_le {M : Mat d} {t : ℝ} (h0 : 0 ≤ t)
    (h : MatLoewnerLE M (t • (1 : Mat d))) : specBound M ≤ t :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨h0, h⟩

/-- The scalar Loewner order between multiples of the identity. -/
theorem matLoewnerLE_smul_one_of_le {s t : ℝ} (hst : s ≤ t) :
    MatLoewnerLE (s • (1 : Mat d)) (t • (1 : Mat d)) := by
  intro x
  rw [matVecMul_smul_one', matVecMul_smul_one', vecDot_smul_self', vecDot_smul_self']
  have hx := vecNormSq_nonneg x
  have hmul : s * vecNormSq x ≤ t * vecNormSq x :=
    mul_le_mul_of_nonneg_right hst hx
  linarith only [hmul]

/-- Every matrix admits a scalar Loewner bound, so the infimum defining
`specBound` is taken over a nonempty set. -/
theorem exists_matLoewnerLE_smul_one (M : Mat d) :
    ∃ t : ℝ, 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d)) := by
  refine ⟨∑ i : Fin d, ∑ j : Fin d, |M i j|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  · intro x
    rw [matVecMul_smul_one', vecDot_smul_self']
    have hbound : vecDot x (matVecMul M x) ≤
        (∑ i : Fin d, ∑ j : Fin d, |M i j|) * vecNormSq x := by
      have hexp : vecDot x (matVecMul M x) =
          ∑ i : Fin d, ∑ j : Fin d, x i * (M i j * x j) := by
        simp only [vecDot, matVecMul, Finset.mul_sum]
      rw [hexp, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      have hij : |x i| * |x j| ≤ vecNormSq x := by
        have h1 : x i ^ 2 ≤ vecNormSq x := sq_apply_le_vecNormSq x i
        have h2 : x j ^ 2 ≤ vecNormSq x := sq_apply_le_vecNormSq x j
        nlinarith only [h1, h2, sq_abs (x i), sq_abs (x j),
          sq_nonneg (|x i| - |x j|)]
      calc x i * (M i j * x j) ≤ |x i * (M i j * x j)| := le_abs_self _
        _ = |M i j| * (|x i| * |x j|) := by rw [abs_mul, abs_mul]; ring
        _ ≤ |M i j| * vecNormSq x :=
            mul_le_mul_of_nonneg_left hij (abs_nonneg _)
    linarith only [hbound]

/-- `specBound M` is itself an admissible scalar Loewner bound. -/
theorem matLoewnerLE_specBound_smul_one (M : Mat d) :
    MatLoewnerLE M (specBound M • (1 : Mat d)) :=
  ((specBoundSet_isClosed M).csInf_mem (exists_matLoewnerLE_smul_one M)
    ⟨0, fun _ hx => hx.1⟩).2

/-- **`specBound` characterization.**  `specBound M` is the least nonnegative `t`
with `M ≤ t I`; on symmetric positive semidefinite data this is the norm `|M|` of
the reference text. -/
theorem specBound_le_iff {M : Mat d} {t : ℝ} (ht : 0 ≤ t) :
    specBound M ≤ t ↔ MatLoewnerLE M (t • (1 : Mat d)) :=
  ⟨fun h => (matLoewnerLE_specBound_smul_one M).trans (matLoewnerLE_smul_one_of_le h),
    fun h => specBound_le ht h⟩

/-! ## The positive semidefinite square root -/

/-- The positive semidefinite square root exists on positive semidefinite
data. -/
theorem exists_posSemidef_mul_self {n : Type*} [Fintype n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = M := by
  classical
  have h : (0 : Matrix n n ℝ) ≤ CFC.sqrt M := CFC.sqrt_nonneg M
  exact ⟨CFC.sqrt M, Matrix.nonneg_iff_posSemidef.mp h, CFC.sqrt_mul_sqrt_self M⟩

/-- The positive semidefinite square root is unique. -/
theorem posSemidef_mul_self_unique {n : Type*} [Fintype n]
    {M B B' : Matrix n n ℝ} (hB : B.PosSemidef) (hB' : B'.PosSemidef)
    (h : B * B = M) (h' : B' * B' = M) : B = B' := by
  classical
  refine (CFC.sq_eq_sq_iff B B' hB.nonneg hB'.nonneg).1 ?_
  rw [sq, sq, h, h']

/-- Specification of `matSqrt` on positive semidefinite data. -/
theorem matSqrt_spec {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    (matSqrt M).PosSemidef ∧ matSqrt M * matSqrt M = M := by
  have hex : ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = M :=
    exists_posSemidef_mul_self hM
  rw [matSqrt, dite_eq_left hex]
  exact hex.choose_spec

/-- `matSqrt` is independent of the choice made in its definition: it is the
unique positive semidefinite square root. -/
theorem matSqrt_eq {n : Type*} [Fintype n] [DecidableEq n]
    {M B : Matrix n n ℝ} (hM : M.PosSemidef) (hB : B.PosSemidef) (h : B * B = M) :
    matSqrt M = B := by
  obtain ⟨h1, h2⟩ := matSqrt_spec hM
  exact posSemidef_mul_self_unique h1 hB h2 h

/-! ## Junk guards on the contrast constants -/

/-- The intrinsic contrast is nonnegative, junk branch included. -/
theorem blockContrast_nonneg (H : BlockMat d) : 0 ≤ blockContrast H :=
  Real.sInf_nonneg fun _ hx => hx.1

/-- The intrinsic contrast is a lower bound for the admissible Loewner
scalings. -/
theorem blockContrast_le {H : BlockMat d} {t : ℝ} (h0 : 0 ≤ t) {h : Mat d}
    (hskew : IsSkewMat h)
    (hle : MatLoewnerLE
      (schurSigma H +
        matTranspose (schurSkew H - h) * H.lowerRight * (schurSkew H - h))
      (t • schurSigmaStar H)) :
    blockContrast H ≤ t :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨h0, h, hskew, hle⟩

/-- `Λ_0` is nonnegative, junk branch included. -/
theorem bigLambdaRef_nonneg (E : BlockMat d) : 0 ≤ bigLambdaRef E :=
  Real.sInf_nonneg fun _ hx => hx.1

/-- The reference aspect ratio is nonnegative, so the logarithm of
`2 + Π K` in the entry theorem is taken at an argument at least `2`. -/
theorem aspectRatio_nonneg (E : BlockMat d) : 0 ≤ aspectRatio E :=
  div_nonneg (bigLambdaRef_nonneg E) (inv_nonneg.2 (specBound_nonneg _))

end

end HighContrast
end HCPolySupport
