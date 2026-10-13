/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.HomogenizationErrorControl

/-!
# ToLambdas

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: comparing the homogenization error with the ellipticity constants

This file proves a local version of the lower half of Lemma
`l.mathcal.E.to.Lambdas` of
ABK26:

> For every `m ∈ ℤ`, `q ∈ [1,∞]`, `s ∈ (0,∞)`, coefficient field `a` and scalar
> `σ₀ ∈ (0,∞)`,
> `(1/2) 𝓔_{s,∞,q}(□_m; a, σ₀)²
>    ≤ max{σ₀^{-1} Λ_{s,q}(□_m;a), σ₀ λ_{s,q}^{-1}(□_m;a)}
>    ≤ 1 + 2 𝓔_{s,∞,q}(□_m;a,σ₀)² + 2^{1/2} 𝓔_{s,∞,q}(□_m;a,σ₀)`,
> and moreover, in the case `q = 2`,
> `1 + (1/2) 𝓔_{s,∞,2}(□_m;a,σ₀)²
>    ≤ max{σ₀^{-1} Λ_{s,2}(□_m;a), σ₀ λ_{s,2}^{-1}(□_m;a)}`.

## Scope

Proved here, for `q = 2`:

* the sharp one-cube estimate behind the second inequality of the printed
  `e.J.by.f`, namely
  `max_{|e|=1} J(U, A₀^{-1/2}e, A₀^{1/2}e; a) ≤ σ₀^{-1}|b(U;a)| + σ₀|σ_*^{-1}(U;a)| - 2`
  for the scalar comparator `a₀ = σ₀ Id`;
* its geometric aggregation
  `𝓔_{s,∞,2}² + 2 ≤ σ₀^{-1} Λ_{s,2} + σ₀ λ_{s,2}^{-1}`;
* the display `e.bound.Lambdas.by.Es.q2`, and the first inequality of
  `e.bound.Lambdas.by.Es`, both at `q = 2`.

**Not** proved here: the second inequality of `e.bound.Lambdas.by.Es` (the
upper bound `max{…} ≤ 1 + 2𝓔² + 2^{1/2}𝓔`), whose printed proof runs
through the operator inequalities `e.xminusonetimesxminusonesquared.sstar`
and `e.xminusonetimesxminusonesquared.b` and an eigenvector analysis of
`f(x) = x^{-1}(x-1)^2`; and the aggregation for general `q ∈ [1,∞]`, whose
printed "triangle inequality" step is Minkowski's inequality in `L^{q/2}`
and is available in that direction only for `q ≥ 2`.

## Main results

* `normalizedBlockResponseMax_scalarMatrix_le_weightedCoarseEllipticity_sub_two`
* `homogenizationErrorOnCube_infinity_two_sq_add_two_le_weightedEllipticity`
* `one_add_half_homogenizationErrorOnCube_infinity_two_sq_le_max_weightedEllipticity`
  (the display `e.bound.Lambdas.by.Es.q2`)
* `half_homogenizationErrorOnCube_infinity_two_sq_le_max_weightedEllipticity`
  (the first inequality of `e.bound.Lambdas.by.Es` at `q = 2`)

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

/-! ## Suprema over finite sets -/

/-- A value of `f` on a finite set is below the `finsetSupReal` supremum. -/
theorem le_finsetSupReal {α : Type*} (s : Finset α) (f : α → ℝ) {x : α}
    (hx : x ∈ s) : f x ≤ Book.Ch02.finsetSupReal s f := by
  classical
  unfold Book.Ch02.finsetSupReal
  exact le_csSup ((s.finite_toSet.image f).bddAbove) ⟨x, hx, rfl⟩

/-! ## The doubled response with scalar normalizers -/

/-- Reflecting the second half of the normalized probe flips exactly the
off-diagonal contributions to the doubled response, so the two responses add up
to the diagonal quadratic form of `b(U;a)` and `σ_*^{-1}(U;a)`.

This is the block-algebra content of the printed identity `e.J.by.f` for a
scalar comparator, written with the scaling parameter `c` (which will be
`σ₀^{1/2}`). -/
theorem doubledResponseJ_scaledNormalizers_add_reflect_eq {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) {c : ℝ} (hc : c ≠ 0)
    (u v : Vec d) :
    Book.Ch02.doubledResponseJ U a (c⁻¹ • u, c • v) (c • u, c⁻¹ • v) +
        Book.Ch02.doubledResponseJ U a (c⁻¹ • u, c • (-v)) (c • u, c⁻¹ • (-v)) =
      c⁻¹ * c⁻¹ *
          (vecDot u (matVecMul (Book.Ch02.bCoarse U a) u) +
            vecDot v (matVecMul (Book.Ch02.bCoarse U a) v)) +
        c * c *
          (vecDot u (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) +
            vecDot v (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) v)) -
        2 * (vecNormSq u + vecNormSq v) := by
  have hthy := Book.Ch02.blockCoarseMatrixTheory U a
  rw [hthy.doubled_response_splitting, hthy.doubled_response_splitting,
    hthy.starred_inverse_formula]
  simp only [blockVecDot, blockMatVecMul, blockReflect,
    Book.Ch02.coarseBlockMatrix_upperLeft, Book.Ch02.coarseBlockMatrix_upperRight,
    Book.Ch02.coarseBlockMatrix_lowerLeft, Book.Ch02.coarseBlockMatrix_lowerRight,
    smul_neg, matVecMul_smul, matVecMul_neg, vecDot_add_right, vecDot_smul_left,
    vecDot_smul_right, vecDot_neg_left, vecDot_neg_right, vecNormSq]
  field_simp
  ring

/-- The sharp one-cube bound of `e.J.by.f` (ABK26) for a scalar comparator: the
normalized doubled response of a unit probe is bounded by the `σ₀`-weighted
coarse ellipticity norms, minus `2`. -/
theorem doubledResponseJ_scalarNormalized_le {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) {σ : ℝ} (hσ : 0 < σ) (u v : Vec d)
    (hnorm : vecNormSq u + vecNormSq v = 1) :
    Book.Ch02.doubledResponseJ U a
        ((Real.sqrt σ)⁻¹ • u, Real.sqrt σ • v)
        (Real.sqrt σ • u, (Real.sqrt σ)⁻¹ • v) ≤
      σ⁻¹ * Book.Ch02.matrixNorm (Book.Ch02.bCoarse U a) +
        σ * Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U a) - 2 := by
  have hcpos : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  have hc : Real.sqrt σ ≠ 0 := ne_of_gt hcpos
  have hcc : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ.le
  have hcinv : (Real.sqrt σ)⁻¹ * (Real.sqrt σ)⁻¹ = σ⁻¹ := by
    rw [← mul_inv, hcc]
  have hkey := doubledResponseJ_scaledNormalizers_add_reflect_eq U a hc u v
  rw [hcc, hcinv, hnorm] at hkey
  have hreflect_nonneg :
      0 ≤ Book.Ch02.doubledResponseJ U a ((Real.sqrt σ)⁻¹ • u, Real.sqrt σ • (-v))
        (Real.sqrt σ • u, (Real.sqrt σ)⁻¹ • (-v)) :=
    Book.Ch02.doubledResponseJ_nonneg U a _ _
  have hquad : ∀ (A : Mat d) (x : Vec d),
      vecDot x (matVecMul A x) ≤ Book.Ch02.matrixNorm A * vecNormSq x := by
    intro A x
    have habs := Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq A x
    rw [Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
    exact le_trans (le_abs_self _) habs
  have hb :
      vecDot u (matVecMul (Book.Ch02.bCoarse U a) u) +
          vecDot v (matVecMul (Book.Ch02.bCoarse U a) v) ≤
        Book.Ch02.matrixNorm (Book.Ch02.bCoarse U a) := by
    have h1 := hquad (Book.Ch02.bCoarse U a) u
    have h2 := hquad (Book.Ch02.bCoarse U a) v
    have hcomb :
        Book.Ch02.matrixNorm (Book.Ch02.bCoarse U a) * vecNormSq u +
            Book.Ch02.matrixNorm (Book.Ch02.bCoarse U a) * vecNormSq v =
          Book.Ch02.matrixNorm (Book.Ch02.bCoarse U a) := by
      rw [← mul_add, hnorm, mul_one]
    linarith
  have hs :
      vecDot u (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) +
          vecDot v (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) v) ≤
        Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U a) := by
    have h1 := hquad (Book.Ch02.sigmaStarInvCoarse U a) u
    have h2 := hquad (Book.Ch02.sigmaStarInvCoarse U a) v
    have hcomb :
        Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U a) * vecNormSq u +
            Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U a) * vecNormSq v =
          Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U a) := by
      rw [← mul_add, hnorm, mul_one]
    linarith
  have hbm :
      σ⁻¹ *
          (vecDot u (matVecMul (Book.Ch02.bCoarse U a) u) +
            vecDot v (matVecMul (Book.Ch02.bCoarse U a) v)) ≤
        σ⁻¹ * Book.Ch02.matrixNorm (Book.Ch02.bCoarse U a) :=
    mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hσ.le)
  have hsm :
      σ *
          (vecDot u (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) +
            vecDot v (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) v)) ≤
        σ * Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U a) :=
    mul_le_mul_of_nonneg_left hs hσ.le
  linarith

/-! ## The one-cube estimate for the public normalized response -/

/-- Coordinates of the scalar inverse-square-root normalizer. -/
theorem ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix {d : ℕ}
    {σ : ℝ} (hσ : 0 < σ) (e : FullBlockVec d) :
    ofFullBlockVec
        (Matrix.mulVec
          (Book.Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) σ)) e) =
      ((Real.sqrt σ)⁻¹ • (fun i => e (Sum.inl i)),
        Real.sqrt σ • (fun i => e (Sum.inr i))) := by
  rw [Book.Ch05.Section57.constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt
    hσ]
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp [ofFullBlockVec, Matrix.mulVec_diagonal,
      Book.Ch04.scalarFullBlockInvSqrtDiag]

/-- Coordinates of the scalar square-root normalizer. -/
theorem ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix {d : ℕ}
    {σ : ℝ} (hσ : 0 < σ) (e : FullBlockVec d) :
    ofFullBlockVec
        (Matrix.mulVec
          (Book.Ch02.constantFullBlockMatrixSqrt (scalarMatrix (d := d) σ)) e) =
      (Real.sqrt σ • (fun i => e (Sum.inl i)),
        (Real.sqrt σ)⁻¹ • (fun i => e (Sum.inr i))) := by
  rw [Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
    hσ]
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp [ofFullBlockVec, Matrix.mulVec_diagonal,
      Book.Ch05.Section56.scalarFullBlockSqrtDiag]

/-- The squared Euclidean norm of a doubled vector splits into the two halves. -/
theorem fullBlockVecNormSq_eq_add {d : ℕ} (e : FullBlockVec d) :
    Book.Ch02.fullBlockVecNormSq e =
      vecNormSq (fun i => e (Sum.inl i)) + vecNormSq (fun i => e (Sum.inr i)) := by
  unfold Book.Ch02.fullBlockVecNormSq vecNormSq vecDot
  rw [Fintype.sum_sum_type]
  simp [pow_two]

/-- The one-cube estimate: for the scalar comparator `σ Id`, the normalized
block-response maximum is bounded by the weighted coarse ellipticity norms minus
`2`.  This is the sharp form of the second inequality of `e.J.by.f` (ABK26). -/
theorem normalizedBlockResponseMax_scalarMatrix_le_weightedCoarseEllipticity_sub_two
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    {σ : ℝ} (hσ : 0 < σ) :
    Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) ≤
      σ⁻¹ * Book.Ch02.coarseBMatrixNorm Q F +
        σ * Book.Ch02.coarseSigmaStarInvMatrixNorm Q F - 2 := by
  unfold Book.Ch02.normalizedBlockResponseMax
  refine csSup_le
    (Book.Ch02.normalizedBlockResponseValueSet_nonempty Q F (scalarMatrix (d := d) σ))
    ?_
  rintro y ⟨e, he, rfl⟩
  have hnorm :
      vecNormSq (fun i => e (Sum.inl i)) + vecNormSq (fun i => e (Sum.inr i)) = 1 := by
    rw [← fullBlockVecNormSq_eq_add]
    exact he
  rw [ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix hσ,
    ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix hσ]
  exact doubledResponseJ_scalarNormalized_le (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
    hσ _ _ hnorm

/-- Descendant-scale form of the one-cube estimate. -/
theorem maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le_sub_two
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
        (scalarMatrix (d := d) σ) ≤
      σ⁻¹ * Book.Ch02.maxDescendantBMatrixNormAtScale Q k F +
        σ * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F - 2 := by
  refine Book.Ch02.finsetSupReal_le (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  have hone :=
    normalizedBlockResponseMax_scalarMatrix_le_weightedCoarseEllipticity_sub_two R F hσ
  have hb : Book.Ch02.coarseBMatrixNorm R F ≤
      Book.Ch02.maxDescendantBMatrixNormAtScale Q k F :=
    le_finsetSupReal (descendantsAtScale Q k)
      (fun S => Book.Ch02.coarseBMatrixNorm S F) hR
  have hs : Book.Ch02.coarseSigmaStarInvMatrixNorm R F ≤
      Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F :=
    le_finsetSupReal (descendantsAtScale Q k)
      (fun S => Book.Ch02.coarseSigmaStarInvMatrixNorm S F) hR
  have hbm :
      σ⁻¹ * Book.Ch02.coarseBMatrixNorm R F ≤
        σ⁻¹ * Book.Ch02.maxDescendantBMatrixNormAtScale Q k F :=
    mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hσ.le)
  have hsm :
      σ * Book.Ch02.coarseSigmaStarInvMatrixNorm R F ≤
        σ * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F :=
    mul_le_mul_of_nonneg_left hs hσ.le
  linarith

/-! ## Aggregation at `q = 2` -/

/-- The geometric aggregation of the one-cube estimate: `𝓔_{s,∞,2}² + 2` is
bounded by the `σ₀`-weighted sum of the two coarse ellipticity constants.  This
is the content of the first inequality of `e.bound.Lambdas.by.Es` (ABK26) at `q
= 2`. -/
theorem homogenizationErrorOnCube_infinity_two_sq_add_two_le_weightedEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) :
    (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
        (scalarMatrix (d := d) σ)) ^ 2 + 2 ≤
      σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 2) F +
        σ * (Book.Ch02.lambdaSq Q s (.finite 2) F)⁻¹ := by
  have hs2 : (0 : ℝ) < s * 2 := by nlinarith
  set w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s 2 n with hwdef
  set M : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) F
      (scalarMatrix (d := d) σ) with hMdef
  set B : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F with hBdef
  set S : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F
    with hSdef
  have hw_nonneg : ∀ n : ℕ, 0 ≤ w n := by
    intro n
    rw [hwdef]
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) n hs2.le
  have hscale : ∀ n : ℕ, Q.scale - (n : ℤ) ≤ Q.scale := by
    intro n
    exact sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)
  have hsumW : Summable w := by
    rw [hwdef]
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.summable_geometricWeight (s := s) (q := 2) hs2
  have htsumW : (∑' n : ℕ, w n) = 1 := by
    rw [hwdef]
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.tsum_geometricWeight_eq_one (s := s) (q := 2) hs2
  have hsumM : Summable fun n : ℕ => w n * M n := by
    rw [hwdef, hMdef]
    exact
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q F (scalarMatrix (d := d) σ) hs
  have hsumB : Summable fun n : ℕ => w n * B n := by
    have h := Book.Ch02.summable_B_series_pointwiseCoeffField Q F hs
      (by norm_num : (0 : ℝ) < 2)
    rw [hwdef, hBdef]
    simpa [Real.rpow_one] using h
  have hsumS : Summable fun n : ℕ => w n * S n := by
    have h := Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q F hs
      (by norm_num : (0 : ℝ) < 2)
    rw [hwdef, hSdef]
    simpa [Real.rpow_one] using h
  have hLambda : Book.Ch02.LambdaSq Q s (.finite 2) F = ∑' n : ℕ, w n * B n := by
    have h := Book.Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 2 F
      (by norm_num : (0 : ℝ) < 2) hs2.le
    rw [hwdef, hBdef]
    simpa [Real.rpow_one] using h
  have hlambda :
      (Book.Ch02.lambdaSq Q s (.finite 2) F)⁻¹ = ∑' n : ℕ, w n * S n := by
    have h := Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 2 F
      (by norm_num : (0 : ℝ) < 2) hs2.le
    rw [hwdef, hSdef]
    simpa [Real.rpow_one, Real.rpow_neg_one] using h
  have hE : (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
      (scalarMatrix (d := d) σ)) ^ 2 = ∑' n : ℕ, w n * M n := by
    rw [hwdef, hMdef]
    exact Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs F
      (scalarMatrix (d := d) σ)
  set r : ℕ → ℝ := fun n => σ⁻¹ * (w n * B n) + σ * (w n * S n) - 2 * w n with hrdef
  have hsumr : Summable r := by
    rw [hrdef]
    exact ((hsumB.mul_left σ⁻¹).add (hsumS.mul_left σ)).sub (hsumW.mul_left 2)
  have hterm : ∀ n : ℕ, w n * M n ≤ r n := by
    intro n
    have hpoint :=
      maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le_sub_two Q
        (hscale n) F hσ
    have hmul :
        w n * Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
            (Q.scale - (n : ℤ)) F (scalarMatrix (d := d) σ) ≤
          w n * (σ⁻¹ * Book.Ch02.maxDescendantBMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) F +
            σ * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) F - 2) :=
      mul_le_mul_of_nonneg_left hpoint (hw_nonneg n)
    simp only [hrdef, hMdef, hBdef, hSdef]
    linarith [hmul]
  have hle : (∑' n : ℕ, w n * M n) ≤ ∑' n : ℕ, r n :=
    Summable.tsum_le_tsum hterm hsumM hsumr
  have hrsum : (∑' n : ℕ, r n) =
      σ⁻¹ * (∑' n : ℕ, w n * B n) + σ * (∑' n : ℕ, w n * S n) - 2 := by
    rw [hrdef]
    rw [Summable.tsum_sub ((hsumB.mul_left σ⁻¹).add (hsumS.mul_left σ))
      (hsumW.mul_left 2)]
    rw [Summable.tsum_add (hsumB.mul_left σ⁻¹) (hsumS.mul_left σ)]
    rw [hsumB.tsum_mul_left, hsumS.tsum_mul_left, hsumW.tsum_mul_left, htsumW]
    ring
  rw [hE, hLambda, hlambda]
  have := hle
  rw [hrsum] at this
  linarith

/-- The display `e.bound.Lambdas.by.Es.q2` (ABK26). -/
theorem one_add_half_homogenizationErrorOnCube_infinity_two_sq_le_max_weightedEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) :
    1 + (1 / 2 : ℝ) *
        (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
          (scalarMatrix (d := d) σ)) ^ 2 ≤
      max (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 2) F)
        (σ * (Book.Ch02.lambdaSq Q s (.finite 2) F)⁻¹) := by
  have hsum :=
    homogenizationErrorOnCube_infinity_two_sq_add_two_le_weightedEllipticity Q F hs hσ
  have hle1 : σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 2) F ≤
      max (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 2) F)
        (σ * (Book.Ch02.lambdaSq Q s (.finite 2) F)⁻¹) := le_max_left _ _
  have hle2 : σ * (Book.Ch02.lambdaSq Q s (.finite 2) F)⁻¹ ≤
      max (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 2) F)
        (σ * (Book.Ch02.lambdaSq Q s (.finite 2) F)⁻¹) := le_max_right _ _
  linarith

/-- The first inequality of `e.bound.Lambdas.by.Es` (ABK26) at `q = 2`. -/
theorem half_homogenizationErrorOnCube_infinity_two_sq_le_max_weightedEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) :
    (1 / 2 : ℝ) *
        (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
          (scalarMatrix (d := d) σ)) ^ 2 ≤
      max (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 2) F)
        (σ * (Book.Ch02.lambdaSq Q s (.finite 2) F)⁻¹) := by
  have h :=
    one_add_half_homogenizationErrorOnCube_infinity_two_sq_le_max_weightedEllipticity
      Q F hs hσ
  linarith

end Algsuperdiff.Section3.Provider.ErrorComparison
