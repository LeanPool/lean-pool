/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedDomainLocality
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Response
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Setup
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Existence
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.ExistenceDefinitions
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.GradientUniqueness
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Existence
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ

/-!
# High-contrast homogenization: Entry.Response.Core.AdaptedDomainBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adapted cells as admissible domains

This file shows that an adapted cell is an open, bounded, convex domain in the sense used
throughout the argument, and develops the matrix algebra that lets the recentred coefficients be
treated as elliptic fields on it. It proves that ellipticity of a field or a matrix survives
adding or subtracting a skew correction, that the response correction is itself skew, and the
accompanying facts about the Schur-swap skew congruence and the conversion between a block matrix
and its full matrix form. Together these identify the adapted cell, equipped with the recentred
coefficient, as a legitimate domain for the maximizer theory built on top of it. The module serves
the response transfer `p.response.transfer`.
-/

section
/-!
## HC bridge I, part 1 of 4: adapted cells as Chapter-2 domains (B1)

Section B1 only. See `AnnealedBlockIdentity.lean` for the closing docstring and
`AdaptedDomainBridge.lean` for the re-export.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (matSqrt matSqrt_eq schurSkew)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## B1. Adapted cells are Chapter-2 domains. -/

omit [NeZero d] in
/-- `U_t = q(centeredCube t)` is an open bounded convex domain
(`p.response.transfer`; old `DomainBridge.lean`).  Route:
`HCPoly/Entry/Annealed/AdaptedDomainLocality.lean` (`isOpenBoundedConvexDomain_affine_openCube`). -/
theorem adaptedCell_isOpenBoundedConvexDomain (q : Mat d) (hq : IsUnit q) (j : ℤ) :
    IsOpenBoundedConvexDomain (HighContrast.adaptedCell q j) := by
  have h := isOpenBoundedConvexDomain_affine_openCube q hq j 0
  simpa [HighContrast.adaptedCell, HighContrast.centeredCube, translateSet_zero] using h

omit [NeZero d] in
/-- The adapted cell as a Chapter-2 domain. -/
@[expose]
def adaptedDomain (q : Mat d) (hq : IsUnit q) (j : ℤ) : Book.Ch02.Domain d :=
  { carrier := HighContrast.adaptedCell q j
    isDomain := adaptedCell_isOpenBoundedConvexDomain q hq j
    nonempty := Recurrence.adaptedCell_nonempty q j }

-- ============================================================================
-- Private helpers for the skew-shift ellipticity lemmas.
-- ============================================================================

omit [NeZero d] in
private theorem vecNormSq_add (x y : Vec d) :
    vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
  unfold vecNormSq
  rw [vecDot_add_left, vecDot_add_right, vecDot_add_right, vecDot_comm y x]
  ring

omit [NeZero d] in
private theorem vecNormSq_sub (x y : Vec d) :
    vecNormSq (x - y) = vecNormSq x - 2 * vecDot x y + vecNormSq y := by
  have h := vecNormSq_add x (-y)
  have h1 : vecDot x (-y) = - vecDot x y := vecDot_neg_right x y
  have h2 : vecNormSq (-y) = vecNormSq y := by
    unfold vecNormSq; rw [vecDot_neg_left, vecDot_neg_right, neg_neg]
  rw [h1, h2] at h
  simpa [sub_eq_add_neg] using h

omit [NeZero d] in
private theorem vecDot_skew_self {g : Mat d} (hg : matTranspose g = -g) (ξ : Vec d) :
    vecDot ξ (matVecMul g ξ) = 0 := by
  have h1 := _root_.HCPolySupport.vecDot_matVecMul_transpose ξ ξ g
  rw [hg] at h1
  have hneg : matVecMul (-g) ξ = - matVecMul g ξ := by
    funext i; simp [matVecMul, Matrix.neg_apply, Finset.sum_neg_distrib]
  rw [hneg, vecDot_neg_right, vecDot_comm (matVecMul g ξ) ξ] at h1
  linarith only [h1]

omit [NeZero d] in
private theorem vecNormSq_matVecMul_le_opNormSq (M : Mat d) (v : Vec d) :
    vecNormSq (matVecMul M v) ≤ ‖M‖ ^ 2 * vecNormSq v := by
  simpa [matVecMul] using! Geometry.vecNormSq_mulVec_le_opNorm M v

omit [NeZero d] in
private theorem isUnit_det_of_coercive {lam : ℝ} (hlam : 0 < lam) {B : Mat d}
    (hlower : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul B ξ)) :
    IsUnit B.det := by
  have hinj : Function.Injective (matVecMul B) := by
    intro ξ η hξη
    have hzero : matVecMul B (ξ - η) = 0 := by
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg]; simp [hξη]
    have hl := hlower (ξ - η)
    rw [hzero] at hl
    have hzero' : vecDot (ξ - η) (0 : Vec d) = 0 := by simp [vecDot]
    rw [hzero'] at hl
    have hnorm_zero : vecNormSq (ξ - η) = 0 := by
      refine le_antisymm ?_ (vecNormSq_nonneg _)
      exact le_of_mul_le_mul_left (by simpa using hl) hlam
    exact sub_eq_zero.mp (vecNormSq_eq_zero hnorm_zero)
  have hinj' : Function.Injective (B.mulVec) := by simpa [matVecMul] using! hinj
  exact (B.isUnit_iff_isUnit_det).mp ((Matrix.mulVec_injective_iff_isUnit (A := B)).mp hinj')

omit [NeZero d] in
private theorem opBound_of_isEllipticMatrix {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (η : Vec d) :
    vecNormSq (matVecMul A η) ≤ Lam * vecDot η (matVecMul A η) := by
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  obtain ⟨hlam_pos, hlamLam, -, hInv⟩ := hA
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
  have hInvMul : matVecMul A⁻¹ (matVecMul A η) = η := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul A hdet]; funext i; simp [matVecMul, Matrix.one_apply]
  have hInvA : Lam⁻¹ * vecNormSq (matVecMul A η) ≤ vecDot (matVecMul A η) η := by
    simpa [hInvMul] using hInv (matVecMul A η)
  have hmul := mul_le_mul_of_nonneg_left hInvA (le_of_lt hLam_pos)
  have hLamInv : Lam * Lam⁻¹ = 1 := by field_simp
  calc vecNormSq (matVecMul A η)
      = (Lam * Lam⁻¹) * vecNormSq (matVecMul A η) := by rw [hLamInv, one_mul]
    _ = Lam * (Lam⁻¹ * vecNormSq (matVecMul A η)) := by ring
    _ ≤ Lam * vecDot (matVecMul A η) η := hmul
    _ = Lam * vecDot η (matVecMul A η) := by rw [vecDot_comm]

omit [NeZero d] in
private theorem isEllipticMatrix_sub_skew {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (g : Mat d) (hg : matTranspose g = -g) :
    IsEllipticMatrix lam (2 * Lam + 2 * ‖g‖ ^ 2 / lam) (A - g) := by
  obtain ⟨hlam_pos, hlamLam, hlower, hInv⟩ := hA
  have hA' : IsEllipticMatrix lam Lam A := ⟨hlam_pos, hlamLam, hlower, hInv⟩
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
  have hterm_nonneg : 0 ≤ 2 * ‖g‖ ^ 2 / lam := div_nonneg (by positivity) hlam_pos.le
  have hLam'_pos : 0 < 2 * Lam + 2 * ‖g‖ ^ 2 / lam := by
    linarith only [hLam_pos, hterm_nonneg]
  have hlam_le' : lam ≤ 2 * Lam + 2 * ‖g‖ ^ 2 / lam := by
    linarith only [hlamLam, hLam_pos, hterm_nonneg]
  have hsplit : ∀ η : Vec d, matVecMul (A - g) η = matVecMul A η - matVecMul g η := by
    intro η; change (A - g).mulVec η = A.mulVec η - g.mulVec η; exact Matrix.sub_mulVec A g η
  have hlower' : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul (A - g) ξ) := by
    intro ξ
    rw [hsplit ξ]
    have heq : vecDot ξ (matVecMul A ξ - matVecMul g ξ)
        = vecDot ξ (matVecMul A ξ) - vecDot ξ (matVecMul g ξ) := by
      have hh := vecDot_add_right ξ (matVecMul A ξ) (-(matVecMul g ξ))
      simpa [sub_eq_add_neg, vecDot_neg_right] using hh
    rw [heq, vecDot_skew_self hg ξ, sub_zero]
    exact hlower ξ
  have hB_unit : IsUnit (A - g).det := isUnit_det_of_coercive hlam_pos hlower'
  have hkey : ∀ η : Vec d,
      vecNormSq (matVecMul (A - g) η) ≤
        (2 * Lam + 2 * ‖g‖ ^ 2 / lam) * vecDot η (matVecMul (A - g) η) := by
    intro η
    have hAη := opBound_of_isEllipticMatrix hA' η
    have hgη : vecNormSq (matVecMul g η) ≤ (‖g‖ ^ 2 / lam) * vecDot η (matVecMul A η) := by
      have hb1 : vecNormSq (matVecMul g η) ≤ ‖g‖ ^ 2 * vecNormSq η :=
        vecNormSq_matVecMul_le_opNormSq g η
      have hb2 : vecNormSq η ≤ vecDot η (matVecMul A η) / lam := by
        rw [le_div_iff₀ hlam_pos]; linarith only [hlower η]
      have hb3 : ‖g‖ ^ 2 * vecNormSq η ≤ ‖g‖ ^ 2 * (vecDot η (matVecMul A η) / lam) :=
        mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)
      calc vecNormSq (matVecMul g η) ≤ ‖g‖ ^ 2 * vecNormSq η := hb1
        _ ≤ ‖g‖ ^ 2 * (vecDot η (matVecMul A η) / lam) := hb3
        _ = (‖g‖ ^ 2 / lam) * vecDot η (matVecMul A η) := by ring
    have hcross : -(2 * vecDot (matVecMul A η) (matVecMul g η))
        ≤ vecNormSq (matVecMul A η) + vecNormSq (matVecMul g η) := by
      have hnn := vecNormSq_nonneg (matVecMul A η + matVecMul g η)
      rw [vecNormSq_add] at hnn; linarith only [hnn]
    have hexpand : vecNormSq (matVecMul (A - g) η)
        = vecNormSq (matVecMul A η) - 2 * vecDot (matVecMul A η) (matVecMul g η)
          + vecNormSq (matVecMul g η) := by rw [hsplit η, vecNormSq_sub]
    rw [hexpand]
    have hq_eq : vecDot η (matVecMul (A - g) η) = vecDot η (matVecMul A η) := by
      rw [hsplit η]
      have hh := vecDot_add_right η (matVecMul A η) (-(matVecMul g η))
      simpa [sub_eq_add_neg, vecDot_neg_right, vecDot_skew_self hg η] using hh
    rw [hq_eq]
    have hqexp : (2 * Lam + 2 * ‖g‖ ^ 2 / lam) * vecDot η (matVecMul A η)
        = 2 * (Lam * vecDot η (matVecMul A η))
          + 2 * ((‖g‖ ^ 2 / lam) * vecDot η (matVecMul A η)) := by ring
    rw [hqexp]
    linarith only [hAη, hgη, hcross]
  have hCond4 : ∀ ξ : Vec d,
      (2 * Lam + 2 * ‖g‖ ^ 2 / lam)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (A - g)⁻¹ ξ) := by
    intro ξ
    have hBη : matVecMul (A - g) (matVecMul (A - g)⁻¹ ξ) = ξ := by
      rw [matVecMul_mul, Matrix.mul_nonsing_inv (A - g) hB_unit]
      funext i; simp [matVecMul, Matrix.one_apply]
    have hk := hkey (matVecMul (A - g)⁻¹ ξ)
    rw [hBη] at hk
    have hle : vecNormSq ξ ≤ (2 * Lam + 2 * ‖g‖ ^ 2 / lam) *
        vecDot (matVecMul (A - g)⁻¹ ξ) ξ := hk
    rw [vecDot_comm (matVecMul (A - g)⁻¹ ξ) ξ] at hle
    rw [inv_mul_eq_div, div_le_iff₀ hLam'_pos]
    linarith only [hle]
  exact ⟨hlam_pos, hlam_le', hlower', hCond4⟩

omit [NeZero d] in
private theorem isEllipticMatrix_add_skew {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (g : Mat d) (hg : matTranspose g = -g) :
    IsEllipticMatrix lam (2 * Lam + 2 * ‖g‖ ^ 2 / lam) (A + g) := by
  have hg' : matTranspose (-g) = -(-g) := by
    have hT : matTranspose (-g) = - matTranspose g := by
      funext i j; simp [matTranspose, Matrix.neg_apply]
    rw [hT, hg]
  have h := isEllipticMatrix_sub_skew hA (-g) hg'
  rw [norm_neg, sub_neg_eq_add] at h
  exact h

omit [NeZero d] in
/-- A constant skew shift preserves ellipticity: the symmetric part of `f - g` is that of
`f`, and `|f - g| ≤ |f| + |g|` (`p.response.transfer`, `a_- = a - g`).  The ellipticity
constant is `2 * Lam + 2 * ‖g‖ ^ 2 / lam`, not `Lam + ‖g‖`; the latter is false because
`IsEllipticMatrix`'s `A⁻¹` clause (`Ambient/CoefficientField.lean`) forces quadratic growth
in `‖g‖`. -/
theorem isEllipticFieldOn_sub_skew {lam Lam : ℝ} {U : Set (Vec d)} {f : CoeffField d}
    (hf : IsEllipticFieldOn lam Lam U f) (g : Mat d) (hg : matTranspose g = -g) :
    IsEllipticFieldOn lam (2 * Lam + 2 * ‖g‖ ^ 2 / lam) U (fun x => f x - g) := by
  classical
  have hUmeas : MeasurableSet U := measurableSet_of_isEllipticFieldOn hf
  refine ⟨?_, ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    have h1 : Measurable (fun x : Vec d => if x ∈ U then f x i j else 0) :=
      measurable_pi_iff.mp (measurable_pi_iff.mp hf.1 i) j
    have h2 : Measurable (fun x : Vec d => if x ∈ U then g i j else 0) :=
      Measurable.ite hUmeas measurable_const measurable_const
    have heq : (fun x : Vec d => if x ∈ U then (f x - g) i j else 0)
        = fun x => (if x ∈ U then f x i j else 0) - (if x ∈ U then g i j else 0) := by
      funext x; by_cases hx : x ∈ U <;> simp [hx, Matrix.sub_apply]
    rw [heq]; exact h1.sub h2
  · intro x hx
    exact isEllipticMatrix_sub_skew (hf.2 x hx) g hg

omit [NeZero d] in
/-- The transposed twin for `a_+ = a^t + g` (`p.response.transfer`).  Same
constant shape as above, `2 * Lam + 2 * ‖g‖ ^ 2 / lam`; the constant `Lam + ‖g‖` is false. -/
theorem isEllipticFieldOn_transpose_add_skew {lam Lam : ℝ} {U : Set (Vec d)} {f : CoeffField d}
    (hf : IsEllipticFieldOn lam Lam U f) (g : Mat d) (hg : matTranspose g = -g) :
    IsEllipticFieldOn lam (2 * Lam + 2 * ‖g‖ ^ 2 / lam) U (fun x => matTranspose (f x) + g) := by
  classical
  have hUmeas : MeasurableSet U := measurableSet_of_isEllipticFieldOn hf
  refine ⟨?_, ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    have h1 : Measurable (fun x : Vec d => if x ∈ U then f x j i else 0) :=
      measurable_pi_iff.mp (measurable_pi_iff.mp hf.1 j) i
    have h2 : Measurable (fun x : Vec d => if x ∈ U then g i j else 0) :=
      Measurable.ite hUmeas measurable_const measurable_const
    have heq : (fun x : Vec d => if x ∈ U then (matTranspose (f x) + g) i j else 0)
        = fun x => (if x ∈ U then f x j i else 0) + (if x ∈ U then g i j else 0) := by
      funext x; by_cases hx : x ∈ U <;> simp [hx, Matrix.add_apply, matTranspose]
    rw [heq]; exact h1.add h2
  · intro x hx
    have hT : IsEllipticMatrix lam Lam (matTranspose (f x)) := isEllipticMatrix_transpose (hf.2
      x hx)
    exact isEllipticMatrix_add_skew hT g hg

/-! ### Helpers for the response skewness -/

/-- `matSqrt` of the zero matrix is zero. -/
private theorem matSqrt_zero_eq {n : Type*} [Fintype n] [DecidableEq n] :
    matSqrt (0 : Matrix n n ℝ) = 0 :=
  matSqrt_eq Matrix.PosSemidef.zero Matrix.PosSemidef.zero (by simp)

/-- Off positive semidefinite data `matSqrt` takes its junk value `1`. -/
private theorem matSqrt_eq_one_of_not_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (h : ¬ M.PosSemidef) : matSqrt M = 1 := by
  have hne : ¬ ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = M := by
    rintro ⟨B, hB, hBB⟩
    refine h ?_
    have hq := Matrix.posSemidef_conjTranspose_mul_self B
    rw [hB.isHermitian.eq, hBB] at hq
    exact hq
  unfold matSqrt
  rw [dite_eq_right hne]

omit [NeZero d] in
private theorem toFullBlockMat_eq_fromBlocks (M : BlockMat d) :
    toFullBlockMat M =
      Matrix.fromBlocks M.upperLeft M.upperRight M.lowerLeft M.lowerRight := by
  ext (i | i) (j | j) <;> rfl

omit [NeZero d] in
private theorem toFullBlockMat_blockSwap_fromBlocks :
    toFullBlockMat (blockSwap d) = Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
  rw [toFullBlockMat_eq_fromBlocks]
  rfl

omit [NeZero d] in
private theorem toFullBlockMat_blockSwap_conjTranspose :
    (toFullBlockMat (blockSwap d))ᴴ = toFullBlockMat (blockSwap d) := by
  rw [toFullBlockMat_blockSwap_fromBlocks, Matrix.fromBlocks_conjTranspose]
  simp

omit [NeZero d] in
private theorem schurSkew_isSkew_of_lowerLeft_eq_zero {M : BlockMat d}
    (h : M.lowerLeft = 0) : matTranspose (schurSkew M) = -(schurSkew M) := by
  simp [schurSkew, h, matTranspose]

omit [NeZero d] in
/-- Swap self-duality `N * R * N = R` of a symmetric doubled block matrix forces its Schur
skew block to be skew.  Only the lower-right block of the self-duality identity is used, so no
invertibility side condition is needed: when `N.lowerRight` is singular Mathlib's
`N.lowerRight⁻¹ = 0` and the Schur skew block vanishes. -/
private theorem schurSkew_isSkew_of_swap_selfDual {N : FullBlockMat d} (hsymm : Nᵀ = N)
    (hswap : N * toFullBlockMat (blockSwap d) * N = toFullBlockMat (blockSwap d)) :
    matTranspose (schurSkew (ofFullBlockMat N)) = -(schurSkew (ofFullBlockMat N)) := by
  set M := ofFullBlockMat N with hMdef
  have hNM : toFullBlockMat M = N := toFullBlockMat_ofFullBlockMat N
  have hblocks : N =
      Matrix.fromBlocks M.upperLeft M.upperRight M.lowerLeft M.lowerRight := by
    rw [← hNM, toFullBlockMat_eq_fromBlocks]
  have hsymm' : Matrix.fromBlocks M.upperLeftᵀ M.lowerLeftᵀ M.upperRightᵀ M.lowerRightᵀ
      = Matrix.fromBlocks M.upperLeft M.upperRight M.lowerLeft M.lowerRight := by
    rw [← Matrix.fromBlocks_transpose, ← hblocks, hsymm, hblocks]
  obtain ⟨-, hCB, -, hDD⟩ := Matrix.fromBlocks_inj.mp hsymm'
  have hswap2 : Matrix.fromBlocks M.upperLeft M.upperRight M.lowerLeft M.lowerRight *
      Matrix.fromBlocks (0 : Mat d) 1 1 0 *
      Matrix.fromBlocks M.upperLeft M.upperRight M.lowerLeft M.lowerRight
      = Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
    rw [← toFullBlockMat_blockSwap_fromBlocks, ← hblocks]
    exact hswap
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hswap2
  obtain ⟨-, -, -, h4⟩ := Matrix.fromBlocks_inj.mp hswap2
  simp only [mul_zero, mul_one, zero_add, add_zero] at h4
  by_cases hD : IsUnit M.lowerRight.det
  · have hDl : M.lowerRight⁻¹ * M.lowerRight = 1 := Matrix.nonsing_inv_mul _ hD
    have hDr : M.lowerRight * M.lowerRight⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD
    have hkey : M.upperRight * M.lowerRight⁻¹ + M.lowerRight⁻¹ * M.lowerLeft = 0 := by
      have hexp : M.lowerRight⁻¹ *
          (M.lowerRight * M.upperRight + M.lowerLeft * M.lowerRight) * M.lowerRight⁻¹
          = (M.lowerRight⁻¹ * M.lowerRight) * M.upperRight * M.lowerRight⁻¹
            + M.lowerRight⁻¹ * M.lowerLeft * (M.lowerRight * M.lowerRight⁻¹) := by
        noncomm_ring
      rw [h4] at hexp
      rw [hDl, hDr] at hexp
      simpa using hexp.symm
    have h5 : M.upperRight * M.lowerRight⁻¹ = -(M.lowerRight⁻¹ * M.lowerLeft) := by
      rw [eq_neg_iff_add_eq_zero]; exact hkey
    have htr : matTranspose (schurSkew M) = -(M.upperRight * M.lowerRight⁻¹) := by
      simp only [schurSkew, matTranspose, Matrix.transpose_neg, Matrix.transpose_mul,
        Matrix.transpose_nonsing_inv, hDD, hCB]
    rw [htr, h5, neg_neg, schurSkew, neg_neg]
  · have hz : M.lowerRight⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hD
    simp [schurSkew, hz, matTranspose]

omit [NeZero d] in
/-- The Schur skew block of the swap geometric mean is skew, with NO hypothesis on `X`. -/
private theorem schurSkew_geoMean_swap_isSkew (X : FullBlockMat d) :
    matTranspose (schurSkew (ofFullBlockMat (GeometricMean.geoMean X
        (toFullBlockMat (blockSwap d) * X⁻¹ * toFullBlockMat (blockSwap d)))))
      = -(schurSkew (ofFullBlockMat (GeometricMean.geoMean X
        (toFullBlockMat (blockSwap d) * X⁻¹ * toFullBlockMat (blockSwap d))))) := by
  classical
  set R : FullBlockMat d := toFullBlockMat (blockSwap d) with hRdef
  have hRR : R * R = 1 := Analysis.toFullBlockMat_blockSwap_mul_self d
  have hRH : Rᴴ = R := toFullBlockMat_blockSwap_conjTranspose
  have hRu : IsUnit R :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hRR)
  by_cases hXu : IsUnit X.det
  · by_cases hXp : X.PosSemidef
    · -- genuine case: `X` is positive definite, and the mean is swap self-dual
      have hXd : X.PosDef :=
        (hXp.posDef_iff_isUnit).2 ((Matrix.isUnit_iff_isUnit_det X).2 hXu)
      have hBd : (R * X⁻¹ * R).PosDef := by
        have h := (Matrix.posDef_inv_iff.2 hXd).conjTranspose_mul_mul_same
          (Matrix.mulVec_injective_of_isUnit hRu)
        rwa [hRH] at h
      set N := GeometricMean.geoMean X (R * X⁻¹ * R) with hNdef
      have hNd : N.PosDef := GeometricMean.geoMeanPosDef hXd hBd
      have hNu : IsUnit N.det := GeometricMean.isUnit_det_of_posDef hNd
      have hric : N * X⁻¹ * N = R * X⁻¹ * R := GeometricMean.geoMean_riccati hXd hBd
      have hNid : (R * N⁻¹ * R).PosDef := by
        have h := (Matrix.posDef_inv_iff.2 hNd).conjTranspose_mul_mul_same
          (Matrix.mulVec_injective_of_isUnit hRu)
        rwa [hRH] at h
      have hinv : N⁻¹ * (R * X⁻¹ * R) * N⁻¹ = X⁻¹ := by
        rw [← hric]
        have hexp : N⁻¹ * (N * X⁻¹ * N) * N⁻¹
            = (N⁻¹ * N) * X⁻¹ * (N * N⁻¹) := by noncomm_ring
        rw [hexp, Matrix.nonsing_inv_mul _ hNu, Matrix.mul_nonsing_inv _ hNu]
        simp
      have hric2 : (R * N⁻¹ * R) * X⁻¹ * (R * N⁻¹ * R) = R * X⁻¹ * R := by
        have hexp : (R * N⁻¹ * R) * X⁻¹ * (R * N⁻¹ * R)
            = R * (N⁻¹ * (R * X⁻¹ * R) * N⁻¹) * R := by noncomm_ring
        rw [hexp, hinv]
      have hdual : R * N⁻¹ * R = N := GeometricMean.eq_geoMean_of_riccati hXd hNid hric2
      have h1 : N⁻¹ * R = R * N := by
        have hexp : (R * R) * N⁻¹ * R = R * (R * N⁻¹ * R) := by noncomm_ring
        rw [hdual] at hexp
        rw [hRR, Matrix.one_mul] at hexp
        exact hexp
      have hswap : N * R * N = R := by
        have hexp : N * R * N = N * (R * N) := by noncomm_ring
        rw [hexp, ← h1]
        have hexp2 : N * (N⁻¹ * R) = (N * N⁻¹) * R := by noncomm_ring
        rw [hexp2, Matrix.mul_nonsing_inv _ hNu, Matrix.one_mul]
      have hsym : Nᵀ = N := by
        have h := hNd.isHermitian.eq
        rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
      exact schurSkew_isSkew_of_swap_selfDual hsym hswap
    · -- junk branch: every `matSqrt` factor is `1`, so the mean is `1`
      have hXi : ¬ X⁻¹.PosSemidef := by
        intro hc
        exact hXp (by simpa [Matrix.nonsing_inv_nonsing_inv X hXu] using hc.inv)
      have hsX : matSqrt X = 1 := matSqrt_eq_one_of_not_posSemidef hXp
      have hsXi : matSqrt X⁻¹ = 1 := matSqrt_eq_one_of_not_posSemidef hXi
      have hBp : ¬ (R * X⁻¹ * R).PosSemidef := by
        intro hc
        refine hXi ?_
        have h2 := hc.conjTranspose_mul_mul_same R
        rw [hRH] at h2
        have hexp : R * (R * X⁻¹ * R) * R = (R * R) * X⁻¹ * (R * R) := by noncomm_ring
        rw [hexp, hRR, Matrix.one_mul, Matrix.mul_one] at h2
        exact h2
      have hsB : matSqrt (R * X⁻¹ * R) = 1 := matSqrt_eq_one_of_not_posSemidef hBp
      have hgeo : GeometricMean.geoMean X (R * X⁻¹ * R) = 1 := by
        rw [GeometricMean.geoMean, hsX, hsXi]
        simp [hsB]
      rw [hgeo]
      refine schurSkew_isSkew_of_lowerLeft_eq_zero ?_
      ext i j
      simp [ofFullBlockMat, Matrix.one_apply]
  · -- `X` is not invertible: `X⁻¹ = 0` and the mean collapses to `0`
    have hXi : X⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hXu
    have hgeo : GeometricMean.geoMean X (R * X⁻¹ * R) = 0 := by
      rw [GeometricMean.geoMean, hXi, matSqrt_zero_eq]
      simp [matSqrt_zero_eq]
    rw [hgeo]
    refine schurSkew_isSkew_of_lowerLeft_eq_zero ?_
    ext i j
    simp [ofFullBlockMat]

omit [NeZero d] in
/-- `respg F` is skew (`p.response.transfer`: `g` is the skew Schur coefficient of
`M(F)`). -/
theorem respg_isSkew (F : BlockMat d) : matTranspose (respg F) = -(respg F) :=
  schurSkew_geoMean_swap_isSkew (toFullBlockMat F)

/-! ## B2. Maximizer existence on adapted cells for the recentred coefficients.
CG provides `ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain`
(`CoarseGraining/ResponseIdentities/Existence.lean`) and
`HCPoly/Entry/Annealed/AdaptedDomainLocality.lean` supplies `lam Lam f` with `⇑a.1 =ᵐ f`.
The `sSup` in `respWeakEnergy` is over a nonempty set. -/

-- ============================================================================
-- B2 helpers (a.e.-equality transport).
-- ============================================================================

end

end HCPolySupport.HighContrast.Multiscale
end
