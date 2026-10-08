/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Analytic.ConvexDomains

/-!
# High-contrast homogenization: Analytic.DirichletDomain

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The domain class of the Dirichlet estimate is inhabited

The Dirichlet estimate `e.random.dirichlet`
is stated for a domain `U ⊆ E_1` whose constant depends on `U` only through the
shape of the adapted domain `s_bar^{-1/2}U`.  In the formalization the shape datum
is the concentric ball sandwich `HasBallSandwich`, so the hypothesis of the
estimate is the conjunction

* `U` is a nonempty bounded open convex domain;
* the adapted domain `s_bar^{-1/2}U` admits a concentric ball sandwich;
* `U ⊆ E_1`.

This module produces such a `U` from the positivity of the symmetric part of
`ā` alone, so the estimate is not read on an empty family of domains.

The witness is exact rather than approximate.  For `S = s_bar` positive definite
with square root `B`, the change of variables `y = B z` turns the ellipsoid
quadratic form into the Euclidean one, `(B z) · S⁻¹ (B z) = ‖z‖²`, so the
`B`-image of the Euclidean ball of radius `|s_bar⁻¹|^{1/2}` is carried into `E_1`
by an identity.  Its adapted image is that ball again, which sandwiches itself.

The degenerate dimension is treated separately: for `d = 0` the space is a
single point, every quadratic form vanishes and `s_bar^{-1/2}` acts as the
identity, so the Euclidean unit ball serves directly.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The unit Euclidean ball is contained in the unit ellipsoid, for every
`abar`. -/
theorem euclideanBallAt_zero_one_subset_ellipsoid (abar : Mat d) :
    euclideanBallAt (0 : Vec d) 1 ⊆ ellipsoid abar 1 :=
  euclideanBallAt_zero_subset_ellipsoid abar 1

/-! ## Invertibility of the adapted matrix -/

/-- The positive semidefinite square root of a positive definite matrix is
invertible. -/
theorem isUnit_det_matSqrt {M : Mat d} (hM : M.PosDef) : IsUnit (matSqrt M).det := by
  obtain ⟨-, hBB⟩ := matSqrt_spec hM.posSemidef
  have hinj : Function.Injective (matSqrt M).mulVec := by
    intro u w huw
    by_contra hne
    have hz : u - w ≠ 0 := sub_ne_zero.mpr hne
    have h0 : (matSqrt M).mulVec (u - w) = 0 := by
      rw [Matrix.mulVec_sub, huw, sub_self]
    have hMz : M.mulVec (u - w) = 0 := by
      rw [← hBB, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    have hpos := hM.dotProduct_mulVec_pos hz
    rw [hMz] at hpos
    simp at hpos
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)

/-- The inverse of the adapted matrix `s_bar^{1/2}` is invertible, so the adapted
domain `s_bar^{-1/2}U` is a linear image under an invertible matrix and the shape
lemmas for linear images apply. -/
theorem isUnit_det_matSqrt_inv {M : Mat d} (hM : M.PosDef) :
    IsUnit ((matSqrt M)⁻¹).det :=
  Matrix.isUnit_nonsing_inv_det _ (isUnit_det_matSqrt hM)

/-! ## The adapted image of a ball, computed exactly

For `S` positive definite with square root `B = matSqrt S`, the change of
variables `y = B z` turns the ellipsoid quadratic form into the Euclidean one:
`y · S⁻¹ y = ‖z‖²`, exactly.  So the `B`-image of a Euclidean ball is the
sublevel set of the ellipsoid form, and the inclusion into `ellipsoid abar 1` is
an identity rather than an estimate. -/

/-- `S⁻¹ B = B⁻¹` for `B` the square root of the positive definite `S`. -/
theorem matVecMul_inv_matVecMul_matSqrt {S : Mat d} (hS : S.PosDef) (z : Vec d) :
    matVecMul S⁻¹ (matVecMul (matSqrt S) z) = matVecMul (matSqrt S)⁻¹ z := by
  obtain ⟨-, hBB⟩ := matSqrt_spec hS.posSemidef
  have hu : IsUnit (matSqrt S).det := isUnit_det_matSqrt hS
  have hsplit : S⁻¹ = (matSqrt S)⁻¹ * (matSqrt S)⁻¹ := by
    conv_lhs => rw [← hBB]
    rw [Matrix.mul_inv_rev]
  have hmat : S⁻¹ * matSqrt S = (matSqrt S)⁻¹ := by
    rw [hsplit, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  rw [matVecMul_mul, hmat]

/-- **The change of variables.**  `(B z) · S⁻¹ (B z) = ‖z‖²`, exactly. -/
theorem vecDot_matVecMul_inv_matSqrt {S : Mat d} (hS : S.PosDef) (z : Vec d) :
    vecDot (matVecMul (matSqrt S) z)
        (matVecMul S⁻¹ (matVecMul (matSqrt S) z)) = vecNormSq z := by
  have hu : IsUnit (matSqrt S).det := isUnit_det_matSqrt hS
  have hBsymm : matTranspose (matSqrt S) = matSqrt S :=
    isSymm_of_isHermitian (matSqrt_spec hS.posSemidef).1.isHermitian
  rw [matVecMul_inv_matVecMul_matSqrt hS z, ← vecDot_matVecMul_transpose, hBsymm,
    matVecMul_mul, Matrix.mul_nonsing_inv _ hu, matVecMul_one]
  rfl

/-- **The adapted image of a small ball sits in the unit ellipsoid.**  The
radius constraint `r² ≤ |s_bar⁻¹|` is the exact one: the inclusion is the
identity `(B z) · s_bar⁻¹ (B z) = ‖z‖²` combined with `‖z‖² < r²`. -/
theorem matImage_matSqrt_euclideanBallAt_subset_ellipsoid {abar : Mat d}
    (hS : (symmPart abar).PosDef) {r : ℝ}
    (hr : r ^ 2 ≤ specBound ((symmPart abar)⁻¹)) :
    matImage (matSqrt (symmPart abar)) (euclideanBallAt (0 : Vec d) r) ⊆
      ellipsoid abar 1 := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : vecNormSq z < r ^ 2 := by
    have : vecNormSq (z - 0) < r ^ 2 := hz
    rwa [sub_zero] at this
  change vecDot (matVecMul (matSqrt (symmPart abar)) z)
      (matVecMul (symmPart abar)⁻¹ (matVecMul (matSqrt (symmPart abar)) z)) ≤
    specBound ((symmPart abar)⁻¹) * 1 ^ 2
  rw [vecDot_matVecMul_inv_matSqrt hS z, one_pow, mul_one]
  linarith only [hz', hr]

/-! ## Positivity of `|s_bar⁻¹|` -/

/-- A coordinate basis vector is nonzero. -/
theorem basisVec_ne_zero {i : Fin d} : (basisVec i : Vec d) ≠ 0 := by
  intro h
  have h1 : vecNormSq (basisVec i : Vec d) = 1 := vecNormSq_basisVec i
  rw [h] at h1
  simp [vecNormSq, vecDot] at h1

/-- **`|s_bar⁻¹| > 0` in positive dimension.**  The hypothesis `0 < d` is
necessary: in dimension `0` every quadratic form vanishes identically, so
`specBound M = 0` for every `M` and the conclusion is false.  The three lemmas
below record that failure explicitly. -/
theorem specBound_inv_symmPart_pos {abar : Mat d} (hd : 0 < d)
    (hS : (symmPart abar).PosDef) : 0 < specBound ((symmPart abar)⁻¹) := by
  have hpos : 0 < vecDot (basisVec ⟨0, hd⟩ : Vec d)
      (matVecMul ((symmPart abar)⁻¹) (basisVec ⟨0, hd⟩)) :=
    vecDot_matVecMul_pos_of_posDef hS.inv basisVec_ne_zero
  have hb := vecDot_matVecMul_le_specBound_mul_vecNormSq ((symmPart abar)⁻¹)
    (basisVec ⟨0, hd⟩ : Vec d)
  rw [vecNormSq_basisVec, mul_one] at hb
  linarith only [hpos, hb]

/-! ### `0 < specBound ((symmPart abar)⁻¹)` is false without `0 < d`

In dimension `0` the space `Vec 0` is a one-point space, every quadratic form is
identically zero, hence every scalar Loewner inequality holds at `t = 0` and
`specBound M = 0` for every `M`.  The positivity hypothesis on the symmetric
part is vacuously true there (there is no nonzero vector), so it cannot rescue
the statement: the hypothesis `0 < d` is necessary. -/

/-- In dimension zero every scalar Loewner bound holds at `0`. -/
theorem specBound_eq_zero_of_dim_zero (M : Mat 0) : specBound M = 0 := by
  refine le_antisymm (specBound_le le_rfl ?_) (specBound_nonneg M)
  intro x
  simp [vecDot]

/-- In dimension zero the positivity hypothesis on the symmetric part is
vacuous. -/
theorem vecDot_pos_of_dim_zero (abar : Mat 0) :
    ∀ x : Vec 0, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x) := by
  intro x hx
  exact absurd (funext fun i => i.elim0 : x = 0) hx

/-- **Counterexample.**  In dimension zero the positivity hypothesis holds and
`specBound ((symmPart abar)⁻¹) = 0`, so the implication from that hypothesis to
`0 < specBound ((symmPart abar)⁻¹)` is false as stated; `0 < d` is required. -/
theorem not_specBound_inv_symmPart_pos_of_dim_zero (abar : Mat 0) :
    (∀ x : Vec 0, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) ∧
      ¬ (0 < specBound ((symmPart abar)⁻¹)) := by
  refine ⟨vecDot_pos_of_dim_zero abar, ?_⟩
  rw [specBound_eq_zero_of_dim_zero]
  exact lt_irrefl 0

/-! ## The assembly -/

/-- Applying the inverse to the image undoes it. -/
theorem matImage_inv_matImage {M : Mat d} (hM : IsUnit M.det) (S : Set (Vec d)) :
    matImage M⁻¹ (matImage M S) = S := by
  have h := matImage_matImage_inv (M := M⁻¹) (Matrix.isUnit_nonsing_inv_det M hM) S
  rwa [Matrix.nonsing_inv_nonsing_inv M hM] at h

/-- In dimension zero every linear image is the identity. -/
theorem matImage_of_dim_zero (M : Mat 0) (U : Set (Vec 0)) : matImage M U = U := by
  have hid : ∀ x : Vec 0, matVecMul M x = x := fun _ => funext fun i => i.elim0
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [hid x]
  · intro hy
    exact ⟨y, hy, hid y⟩

/-- **The domain class of the Dirichlet estimate is inhabited.**  There is a
nonempty bounded open convex domain `U` inside the unit ellipsoid whose adapted
image `s_bar^{-1/2}U` carries a concentric ball sandwich.

All three domain conjuncts of
`e.random.dirichlet` appear.  The only
hypothesis is the positivity of the symmetric part of `ā`, which the theorem
statement already asserts. -/
theorem exists_domain_of_dirichlet_clause {abar : Mat d}
    (hpd : ∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) :
    ∃ (U : Set (Vec d)) (ρ Rad : ℝ),
      IsOpenBoundedConvexDomain U ∧ U.Nonempty ∧
        HasBallSandwich (matImage ((matSqrt (symmPart abar))⁻¹) U) ρ Rad ∧
        U ⊆ ellipsoid abar 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨euclideanBallAt (0 : Vec 0) 1, 1, 1,
      isOpenBoundedConvexDomain_euclideanBallAt (0 : Vec 0) one_pos,
      ⟨0, center_mem_euclideanBallAt (0 : Vec 0) one_pos⟩, ?_,
      euclideanBallAt_zero_one_subset_ellipsoid abar⟩
    rw [matImage_of_dim_zero]
    exact hasBallSandwich_euclideanBallAt (0 : Vec 0) one_pos
  · have hS : (symmPart abar).PosDef := posDef_symmPart_of_vecDot_pos hpd
    have hc : 0 < specBound ((symmPart abar)⁻¹) := specBound_inv_symmPart_pos hd hS
    have hu : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
    set r : ℝ := Real.sqrt (specBound ((symmPart abar)⁻¹)) with hrdef
    have hr0 : 0 < r := Real.sqrt_pos.mpr hc
    have hr2 : r ^ 2 = specBound ((symmPart abar)⁻¹) := Real.sq_sqrt hc.le
    refine ⟨matImage (matSqrt (symmPart abar)) (euclideanBallAt (0 : Vec d) r), r, r,
      isOpenBoundedConvexDomain_matImage hu
        (isOpenBoundedConvexDomain_euclideanBallAt (0 : Vec d) hr0),
      nonempty_matImage ⟨(0 : Vec d), center_mem_euclideanBallAt (0 : Vec d) hr0⟩, ?_,
      matImage_matSqrt_euclideanBallAt_subset_ellipsoid hS (le_of_eq hr2)⟩
    rw [matImage_inv_matImage hu]
    exact hasBallSandwich_euclideanBallAt (0 : Vec d) hr0

end

end HighContrast
end HCPolySupport
