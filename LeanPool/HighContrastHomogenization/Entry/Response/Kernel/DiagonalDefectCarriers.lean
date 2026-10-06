/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Provider.Response.VariationalIdentities

/-!
# High-contrast homogenization: Entry.Response.Kernel.DiagonalDefectCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Carriers of the diagonal weak-norm defect

This file defines the average and cell defects `weakAverageDefect`, `weakCellDefect` and their
finite sums, and the pathwise optimizer energy `weakOptimizerEnergy`, of the diagonal weak-norm
estimate `p.response.transfer`, and proves the closed helper identities relating a cell average of
the doubled optimizer field to the block response mean. It also settles the degenerate-metric
branches of the estimate's primal bound, where the underlying block matrix fails to be a unit, and
records the real-arithmetic geometric-weight comparison and tail-weight selection used at the
branch cutoff `M = 1`.
-/

section
/-!
## HC bridge II: carriers and closed helpers for the diagonal weak-norm bound

Carriers and closed helpers for the diagonal weak-norm estimate of the paper
`p.response.transfer`, depending only on `ScaleAverageSeminorm.lean`.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter blockSub normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Carriers: the two finite sums and the pathwise optimizer energy.
Index convention: the absolute-scale carriers are indexed by the scale `k : ℤ`, over the aligned
index set `alignedIndex q k t`; the grid carriers used here are indexed by the DEPTH `n : ℕ` below
`t`, over `triadicIndexBox d n` (`ResponseBlockObjects.lean`), exactly as `besovSeminorm`
 and `respAllScaleMax` already are.  So `k = t - n` throughout, and
`alignedIndex q (t-n) t ↦ triadicIndexBox d n`. -/

/-- The recent cell defect `C_{k,t}(E)` at depth `n` (scale `k = t - n`).  The root-mean-square,
over the `3^{nd}` scale-`(t-n)` subcells of `U_t`, of the `E`-normalized difference between the
cell's coarse block and the coarse block of `U_t`.
The size carrier is the TWO-SIDED `‖E^{-1/2} D E^{-1/2}‖`, written here as
`‖toFullBlockMat (normalizedBlock D E)‖`.  The one-sided `blockSpecBound (normalizedBlock D E)`
controls only the upper spectral side and CANNOT carry the pointwise cell step: with `E = I₁₈`,
`D = diag(-1, 1/17, …, 1/17)` (`d = 9`), `blockSpecBound (normalizedBlock D E) = 1/17` while
`|D e₁| = 1 > 16/17`, so even the explicit constant `16` does not repair it.  `blockSpecBound`
remains correct for `respAllScaleMax` (`ResponseBlockObjects.lean`), which is the spectral
positive part
of `p.response.transfer`; the recent cell differences are bounded in their FULL norm at
`p.response.transfer`.
The defect is built from the coarse blocks of the RECENTRED field `b` (`b = respCoeffMinus F a`
at the call site) and normalized by the congruenced `E = respEhatMinus`; mixing the uncongruenced
numerator `coarseBlock … a` with the congruenced denominator is not the fixed-congruence invariant
carrier of `p.response.transfer`.
The sum `avsum` (`WeakNorm.lean`) is spelled out as `(card)⁻¹ * ∑`, as `besovSeminorm` does. -/
@[expose]
def weakCellDefect (q : Mat d) (t : ℤ) (n : ℕ) (E : BlockMat d) (b : CoeffField d) : ℝ :=
  Real.sqrt
    (((triadicIndexBox d n).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d n,
        ‖toFullBlockMat
            (normalizedBlock
              (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) E)‖ ^ 2)

/-- The recent averaged normalized defect `D_{k,t}(E)` at depth `n` (scale `k = t - n`).  The flat
average over the scale-`(t-n)` subcells of `U_t` of the `E`-normalized cell-minus-`U_t` block
differences, taken entrywise through `toFullBlockMat`.
The defect is built from the recentred field `b`, normalized by the congruenced `E`, as in
`weakCellDefect`. -/
@[expose]
def weakAverageDefect (q : Mat d) (t : ℤ) (n : ℕ) (E : BlockMat d) (b : CoeffField d) :
    BlockMat d :=
  ofFullBlockMat
    (((triadicIndexBox d n).card : ℝ)⁻¹ •
      ∑ w ∈ triadicIndexBox d n,
        toFullBlockMat
          (normalizedBlock
            (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
              (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) E))

/-- The recent cell sum `𝒰_cell`, the `3^{-n/2}`-weighted sum of the recent cell defects over
the finite window `n ≤ H`, at the exponent `s = 1/2`.
`Finset.range (H+1)` includes both endpoints. -/
@[expose]
def weakCellSum (q : Mat d) (t : ℤ) (H : ℕ) (E : BlockMat d) (b : CoeffField d) : ℝ :=
  ∑ n ∈ Finset.range (H + 1),
    (3 : ℝ) ^ (-((n : ℝ) / 2)) * weakCellDefect q t n E b

/-- The recent averaged-defect sum `𝒰_av`, the `3^{-(1/2 - rho/2)n}`-weighted sum of the square
roots of the sizes of the averaged recent defects over the finite window `n ≤ H`, at `s = 1/2`.
The inner size is the TWO-SIDED norm of `D`, here `‖toFullBlockMat D‖`; the one-sided
`blockSpecBound D` suffers the same loss as in `weakCellDefect`. -/
@[expose]
def weakAverageSum (q : Mat d) (t : ℤ) (H : ℕ) (rho : ℝ) (E : BlockMat d) (b : CoeffField d) :
    ℝ :=
  ∑ n ∈ Finset.range (H + 1),
    (3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ)) *
      Real.sqrt ‖toFullBlockMat (weakAverageDefect q t n E b)‖

/-- The pathwise normalized optimizer energy
`ℰ_t = (2 J_t)^{1/2} = ‖symm(b)^{1/2}∇v‖_{L_underlined²(U)}`
(`p.response.transfer`).  CoarseGraining's `variationEnergyValue` (`Book/Ch02/Response.lean`)
needs a `Domain d` together with a `CoeffOn` of it and a `Solution`, none of which the binders here
carry (they carry a bare `Set (Vec d)` and an `AHarmonicFunction`).  The integrand is therefore
written directly: `∇v · symm(b) ∇v = ∇v · b ∇v = (X x).1 · (X x).2` for the doubled optimizer
field `X = optimizerField b u` (`ResponseBlockObjects.lean`), so this is the same real number. -/
@[expose]
def weakOptimizerEnergy (U : Set (Vec d)) (b : CoeffField d) (u : AHarmonicFunction b U) : ℝ :=
  Real.sqrt
    (volumeAverage U fun x =>
      vecDot (optimizerField b u x).1 (optimizerField b u x).2)

/-! ## Helpers.  The pointwise comparison identity in the current carriers, the mean identity
generalized off the centred cell, child-maximizer existence on every aligned subcell, and the
nonnegativity facts. -/

omit [NeZero d] in
theorem matVecMul_sub_mat (M N : Mat d) (v : Vec d) :
    matVecMul (M - N) v = matVecMul M v - matVecMul N v := by
  funext i
  simp [matVecMul, sub_mul, Finset.sum_sub_distrib]

omit [NeZero d] in
theorem matVecMul_sub_vec (M : Mat d) (v w : Vec d) :
    matVecMul M (v - w) = matVecMul M v - matVecMul M w := by
  funext i
  simp [matVecMul, mul_sub, Finset.sum_sub_distrib]

omit [NeZero d] in
theorem blockMatVecMul_sub_vec (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  refine Prod.ext ?_ ?_ <;>
    simp [blockMatVecMul, matVecMul_sub_vec] <;> abel

omit [NeZero d] in
/-- The child-minus-parent mean difference is the reflected action of the block defect. -/
theorem blockResponseMean_sub_blockResponseMean (A B : BlockMat d) (x : BlockVec d) :
    blockResponseMean A x - blockResponseMean B x =
      blockMatVecMul (blockSwap d) (blockMatVecMul (blockSub A B) x) := by
  rw [Response.blockMatVecMul_blockSub, blockMatVecMul_sub_vec, blockResponseMean,
    blockResponseMean]
  abel

/-- The mean identity on a general open bounded convex domain of positive volume. -/
theorem cellAverage_optimizerField_eq_blockResponseMean_of_domain
    {U : Set (Vec d)} (hconv : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal)
    {lam Lam : ℝ} {b : CoeffField d} (hb : IsEllipticFieldOn lam Lam U b)
    (p r : Vec d) (u : AHarmonicFunction b U) (hu : IsResponseMaximizer U p r b u) :
    cellAverage U (optimizerField b u) =
      blockResponseMean (coarseBlockMatrix U b) (-p, r) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  have hne : U.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hvol
    simp at hvol
  have hInt : ResponseLinearIntegrabilityData U b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hb
  have hA : IsCoarseBlockMatrix U b (coarseBlockMatrix U b) :=
    isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hconv hb hvol
  have hJ : ∀ x y : Vec d, ResponseJ U x y b =
      (1 / 2 : ℝ) * blockVecDot (-x, y)
        (blockMatVecMul (coarseBlockMatrix U b) (-x, y)) - vecDot x y := fun x y =>
    responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain hconv hb hvol x y
  set A : BlockMat d := coarseBlockMatrix U b with hAdef
  have hsym := hA.1
  have hURLL : ∀ i j, A.upperRight i j = A.lowerLeft j i := fun i j => hsym (Sum.inl i) (Sum.inr j)
  have hLRs : ∀ i j, A.lowerRight i j = A.lowerRight j i := fun i j => hsym (Sum.inr i) (Sum.inr j)
  have hULs : ∀ i j, A.upperLeft i j = A.upperLeft j i := fun i j => hsym (Sum.inl i) (Sum.inl j)
  have hsw : ∀ x y : Vec d, vecDot x (matVecMul A.upperRight y) =
      vecDot y (matVecMul A.lowerLeft x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hURLL x y
  have hlr : ∀ x y : Vec d, vecDot x (matVecMul A.lowerRight y) =
      vecDot y (matVecMul A.lowerRight x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hLRs x y
  have hul : ∀ x y : Vec d, vecDot x (matVecMul A.upperLeft y) =
      vecDot y (matVecMul A.upperLeft x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hULs x y
  have hQ : ∀ x y : Vec d, ResponseJ U x y b =
      (1 / 2 : ℝ) * (vecDot x (matVecMul A.upperLeft x) - vecDot x (matVecMul A.upperRight y)
        - vecDot y (matVecMul A.lowerLeft x) + vecDot y (matVecMul A.lowerRight y))
        - vecDot x y := by
    intro x y
    rw [hJ x y]
    simp only [blockVecDot, blockMatVecMul, vecDot_add_right, vecDot_neg_left, matVecMul_neg,
      vecDot_neg_right]
    ring
  have hgrad : ∀ i : Fin d, volumeAverage U (fun x => u.toH1.grad x i) =
      -p i + (matVecMul A.lowerRight r) i - (matVecMul A.lowerLeft p) i := by
    intro i
    obtain ⟨ug⟩ := ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hconv hb 0
      (Pi.single i 1)
    rw [basic_cg_identities_average_gradient_coordinate_of_isResponseMaximizer U b p r hInt u hu i
      (ug : AHarmonicFunction b U) ug.isResponseMaximizer]
    have e1 : vecDot p (matVecMul A.upperRight (Pi.single i 1)) = (matVecMul A.lowerLeft p) i := by
      rw [hsw p (Pi.single i 1), vecDot_single_left]
    have e3 : vecDot r (matVecMul A.lowerRight (Pi.single i 1)) = (matVecMul A.lowerRight r) i := by
      rw [hlr r (Pi.single i 1), vecDot_single_left]
    have e4 : vecDot (Pi.single i 1) (matVecMul A.lowerLeft p) = (matVecMul A.lowerLeft p) i :=
      vecDot_single_left _ _
    have e2 : vecDot (Pi.single i 1) (matVecMul A.lowerRight r) = (matVecMul A.lowerRight r) i :=
      vecDot_single_left _ _
    have e5 : vecDot p (Pi.single i 1) = p i := vecDot_single_right _ _
    rw [hQ p r, hQ 0 (Pi.single i 1), hQ p (r - Pi.single i 1)]
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right, vecDot_add_left,
      vecDot_neg_right, vecDot_neg_left, matVecMul_zero, vecDot_zero_left, vecDot_zero_right]
    linarith only [e1, e2, e3, e4, e5]
  have hflux : ∀ i : Fin d, volumeAverage U (fun x => matVecMul (b x) (u.toH1.grad x) i) =
      r i + (matVecMul A.upperRight r) i - (matVecMul A.upperLeft p) i := by
    intro i
    obtain ⟨uf⟩ := ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hconv hb
      (Pi.single i 1) 0
    rw [basic_cg_identities_average_flux_coordinate_of_isResponseMaximizer U b p r hInt u hu i
      (uf : AHarmonicFunction b U) uf.isResponseMaximizer]
    have f1 : vecDot p (matVecMul A.upperLeft (Pi.single i 1)) = (matVecMul A.upperLeft p) i := by
      rw [hul p (Pi.single i 1), vecDot_single_left]
    have f2 : vecDot (Pi.single i 1) (matVecMul A.upperLeft p) = (matVecMul A.upperLeft p) i :=
      vecDot_single_left _ _
    have f3 : vecDot (Pi.single i 1) (matVecMul A.upperRight r) = (matVecMul A.upperRight r) i :=
      vecDot_single_left _ _
    have f4 : vecDot r (matVecMul A.lowerLeft (Pi.single i 1)) = (matVecMul A.upperRight r) i := by
      rw [← hsw (Pi.single i 1) r, vecDot_single_left]
    have f5 : vecDot (Pi.single i 1) r = r i := vecDot_single_left _ _
    rw [hQ (p - Pi.single i 1) r, hQ p r, hQ (Pi.single i 1) 0]
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right, vecDot_add_left,
      vecDot_neg_right, vecDot_neg_left, matVecMul_zero, vecDot_zero_left, vecDot_zero_right]
    linarith only [f1, f2, f3, f4, f5]
  have hrhs1 : (blockResponseMean A (-p, r)).1 =
      fun i => -p i + (matVecMul A.lowerRight r) i - (matVecMul A.lowerLeft p) i := by
    funext i
    simp only [blockResponseMean, Prod.fst_add, blockMatVecMul_blockSwap_fst]
    simp [blockMatVecMul, matVecMul_neg]
    ring
  have hrhs2 : (blockResponseMean A (-p, r)).2 =
      fun i => r i + (matVecMul A.upperRight r) i - (matVecMul A.upperLeft p) i := by
    funext i
    simp only [blockResponseMean, Prod.snd_add, blockMatVecMul_blockSwap_snd]
    simp [blockMatVecMul, matVecMul_neg]
    ring
  refine Prod.ext ?_ ?_
  · rw [hrhs1]; funext i; exact hgrad i
  · rw [hrhs2]; funext i; exact hflux i

/-- The mean identity for a field that is only a.e. equal to an elliptic representative. -/
theorem cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    {U : Set (Vec d)} (hconv : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal)
    {lam Lam : ℝ} {b f : CoeffField d} (hf : IsEllipticFieldOn lam Lam U f)
    (hae : b =ᵐ[volumeMeasureOn U] f)
    (p r : Vec d) (u : AHarmonicFunction b U) (hu : IsResponseMaximizer U p r b u) :
    cellAverage U (optimizerField b u) =
      blockResponseMean (coarseBlockMatrix U b) (-p, r) := by
  have huT : IsResponseMaximizer U p r f (Response.aHarmonicOfAEEq hae u) := by
    intro z
    have key := hu (Response.aHarmonicOfAEEq hae.symm z)
    have h1 : volumeAverage U (scalarResponseIntegrand U f p r z) =
        volumeAverage U (scalarResponseIntegrand U b p r
          (Response.aHarmonicOfAEEq hae.symm z)) :=
      volumeAverage_scalarResponseIntegrand_congr hae.symm p r z _ (fun _ => rfl)
    have h2 : volumeAverage U (scalarResponseIntegrand U b p r u) =
        volumeAverage U (scalarResponseIntegrand U f p r
          (Response.aHarmonicOfAEEq hae u)) :=
      volumeAverage_scalarResponseIntegrand_congr hae p r u _ (fun _ => rfl)
    rw [h1, ← h2]
    exact key
  have hkey := cellAverage_optimizerField_eq_blockResponseMean_of_domain hconv hvol hf p r
    (Response.aHarmonicOfAEEq hae u) huT
  have hof : optimizerField b u =ᵐ[volumeMeasureOn U]
      optimizerField f (Response.aHarmonicOfAEEq hae u) := by
    filter_upwards [hae] with x hx
    simp [optimizerField, Response.aHarmonicOfAEEq, hx]
  rw [cellAverage_congr_ae (subset_refl U) hof, hkey, coarseBlockMatrix_congr_of_ae_eq hae]

/-- Every aligned adapted cell is an open bounded convex domain. -/
theorem isOpenBoundedConvexDomain_adaptedCellAtCenter (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) : IsOpenBoundedConvexDomain (adaptedCellAtCenter q k w) := by
  show IsOpenBoundedConvexDomain (HighContrast.adaptedCellTranslate q k (adaptedCellCenter q k w))
  rw [Annealed.adaptedCellTranslate_eq_cg_affine]
  exact isOpenBoundedConvexDomain_affine_openCube q hq k _

/-- Every aligned adapted cell has positive volume. -/
theorem volume_adaptedCellAtCenter_toReal_pos (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) : 0 < (volume (adaptedCellAtCenter q k w)).toReal := by
  show 0 < (volume (HighContrast.adaptedCellTranslate q k (adaptedCellCenter q k w))).toReal
  rw [Annealed.adaptedCellTranslate_eq_cg_affine]
  exact volume_affine_openCube_toReal_pos q hq k _

/-- The mean identity for the recentred field `a_-` on an arbitrary aligned adapted cell. -/
theorem cellAverage_optimizerField_respCoeffMinus_eq_at
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) (u : AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter q k w))
    (hu : IsResponseMaximizer (adaptedCellAtCenter q k w) p r (respCoeffMinus F a) u) :
    cellAverage (adaptedCellAtCenter q k w) (optimizerField (respCoeffMinus F a) u) =
      blockResponseMean
        (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffMinus F a)) (-p, r) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (adaptedCellAtCenter q k w) (fun x => f x - respg F) :=
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F)
  refine cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w)
    (volume_adaptedCellAtCenter_toReal_pos q hq k w) hEll' ?_ p r u hu
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffMinus, hx]

/-- The mean identity for the recentred field `a_-` on the centred cell `U_t`. -/
theorem cellAverage_optimizerField_respCoeffMinus_eq
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u) :
    cellAverage (HighContrast.adaptedCell q t) (optimizerField (respCoeffMinus F a) u) =
      blockResponseMean
        (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (HighContrast.adaptedCell q t) (fun x => f x - respg F) :=
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F)
  refine cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (adaptedCell_isOpenBoundedConvexDomain q hq t) ?_ hEll' ?_ p r u hu
  · have hset : HighContrast.adaptedCell q t =
        translateSet 0 ((matVecMul q) '' (openCubeSet (originCube d t))) := by
      rw [← Annealed.adaptedCellTranslate_eq_cg_affine q t 0]
      simp [HighContrast.adaptedCellTranslate]
    rw [hset]; exact volume_affine_openCube_toReal_pos q hq t 0
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]

/-- POINTWISE COMPARISON, identity half.  The child-cell minus parent-cell optimizer mean
difference is exactly the reflected action of the coarse-block defect that `weakCellDefect`
normalizes. -/
theorem cellAverage_optimizerField_respCoeffMinus_sub_eq
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (k : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (v : AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter q k w))
    (hv : IsResponseMaximizer (adaptedCellAtCenter q k w) p r (respCoeffMinus F a) v)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u) :
    cellAverage (adaptedCellAtCenter q k w) (optimizerField (respCoeffMinus F a) v) -
        cellAverage (HighContrast.adaptedCell q t) (optimizerField (respCoeffMinus F a) u) =
      blockMatVecMul (blockSwap d)
        (blockMatVecMul
          (blockSub (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffMinus F a))
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a))) (-p, r)) := by
  rw [cellAverage_optimizerField_respCoeffMinus_eq_at q hq k w F a p r v hv,
    cellAverage_optimizerField_respCoeffMinus_eq q hq t F a p r u hu,
    blockResponseMean_sub_blockResponseMean]

/-- Nonemptiness of an aligned adapted cell. -/
private theorem adaptedCellAtCenter_nonempty (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) :
    (adaptedCellAtCenter q k w).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hpos := volume_adaptedCellAtCenter_toReal_pos q hq k w
  rw [h] at hpos
  simp at hpos

omit [NeZero d] in
/-- Nonnegativity of the recent cell defect. -/
private theorem weakCellDefect_nonneg (q : Mat d) (t : ℤ) (n : ℕ) (E : BlockMat d) (b :
  CoeffField d) :
    0 ≤ weakCellDefect q t n E b := Real.sqrt_nonneg _

omit [NeZero d] in
/-- Nonnegativity of the recent cell sum. -/
theorem weakCellSum_nonneg (q : Mat d) (t : ℤ) (H : ℕ) (E : BlockMat d) (b : CoeffField d) :
    0 ≤ weakCellSum q t H E b :=
  Finset.sum_nonneg fun n _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (weakCellDefect_nonneg q t n E b)

omit [NeZero d] in
/-- Nonnegativity of the recent averaged-defect sum. -/
theorem weakAverageSum_nonneg (q : Mat d) (t : ℤ) (H : ℕ) (rho : ℝ) (E : BlockMat d)
    (b : CoeffField d) : 0 ≤ weakAverageSum q t H rho E b :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)

omit [NeZero d] in
/-- The swap block exchanges the two slots. -/
theorem blockMatVecMul_blockSwap (X : BlockVec d) :
    blockMatVecMul (blockSwap d) X = (X.2, X.1) :=
  Prod.ext (blockMatVecMul_blockSwap_fst X) (blockMatVecMul_blockSwap_snd X)

omit [NeZero d] in
/-- Conjugating the metric block `M_0 = diag(m, m^{-1})` by the swap `R` inverts it:
`R^t M_0 R = diag(m^{-1}, m)`.  This is the step that turns the reflected mean difference
`R D x` of the pointwise comparison into the `M_0^{-1}` quadratic form. -/
theorem blockVecDot_blockSwap_respM0 (F : BlockMat d) (y : BlockVec d) :
    blockVecDot (blockMatVecMul (blockSwap d) y)
        (blockMatVecMul (respM0 F) (blockMatVecMul (blockSwap d) y)) =
      blockVecDot y
        (blockMatVecMul
          ⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ y) := by
  rw [blockMatVecMul_blockSwap]
  simp [blockVecDot, blockMatVecMul, respM0, matVecMul, vecDot]
  ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The degenerate metric branches of the diagonal weak-norm primal bound

The binders of `diagonalWeakNorm_primal_le`
(`DiagonalWeakNormBound.lean`) give an ARBITRARY `F : BlockMat d`, so neither
`(explicitCanonicalMetric F).PosDef` nor `(toFullBlockMat (respM0 F)).PosDef` is available, while
the pointwise cell-defect estimates were stated with both.  The degenerate branches are
settled WITHOUT a statement change, by showing that they are harmless.
This file does the metric half of that, from the bottom up: it identifies exactly which junk
value `matSqrt` (`HCPoly/Setup/BlockAlgebra.lean`) returns in each degeneration of
`respM0 F = diag(m, m⁻¹)`, `m = explicitCanonicalMetric F`
(`HCPoly/Entry/Setup/ProjectiveDistance.lean`).

The structural fact that makes the classification finite is that `explicitCanonicalMetric F` is the
Mathlib inverse of a matrix, so it is EITHER a unit OR literally `0` — there is no
"singular but nonzero" metric.  Hence exactly three branches:

* `m` a unit and `toFullBlockMat (respM0 F)` positive definite — the nondegenerate branch, the
  one the pointwise cell-defect estimate already covers;
* `m = 0` — then `toFullBlockMat (respM0 F) = 0` and `blockSqrt (respM0 F) = 0`, so the
  left-hand side of the diagonal weak-norm bound is identically `0`;
* `m` a unit but `toFullBlockMat (respM0 F)` NOT positive definite (equivalently: not positive
  semidefinite, since a unit PSD matrix is PosDef) — then `matSqrt` falls through on BOTH
  `respM0 F` and its inverse, so `blockSqrt (respM0 F)` is the identity and
  `normalizedBlock E (respM0 F)` is `E` itself.  The metric simply disappears from both
  sides, and the cell step becomes its own `M_0 = I` instance.

These degenerations are self-consistent, and the lemmas below establish that fact.

With an explicit hypothesis `hm : m.PosDef` on the metric, these branches cannot arise; they are
exactly the cost of the binder-free carrier map `respM0 F`.
-/

open HCPolySupport.HighContrast (matSqrt normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

/-! ## The two junk values of `matSqrt` -/

/-- `matSqrt M` is the junk value `1` as soon as `M` is not positive semidefinite: a
positive semidefinite `B` with `B * B = M` would exhibit `M = Bᴴ * B` as positive semidefinite. -/
theorem matSqrt_eq_one_of_not_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : ¬ M.PosSemidef) : matSqrt M = 1 := by
  have hno : ¬ ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = M := by
    rintro ⟨B, hB, hBB⟩
    refine hM ?_
    have hBH : Bᴴ * B = M := by rw [hB.isHermitian.eq]; exact hBB
    rw [← hBH]
    exact Matrix.posSemidef_conjTranspose_mul_self B
  simp only [matSqrt, dite_eq_right hno]

/-- `matSqrt 0 = 0`. -/
theorem matSqrt_zero {n : Type*} [Fintype n] [DecidableEq n] :
    matSqrt (0 : Matrix n n ℝ) = 0 := by
  rw [matSqrt_eq_cfc_sqrt Matrix.PosSemidef.zero]
  exact CFC.sqrt_zero

/-- `matSqrt 1 = 1`, the nondegenerate companion of the previous result. -/
theorem matSqrt_one {n : Type*} [Fintype n] [DecidableEq n] :
    matSqrt (1 : Matrix n n ℝ) = 1 := by
  rw [matSqrt_eq_cfc_sqrt Matrix.PosSemidef.one]
  exact CFC.sqrt_one

variable {d : ℕ}

/-! ## The dichotomy of the canonical metric -/

/-- `explicitCanonicalMetric F` is a Mathlib matrix inverse, so it is either invertible or
literally `0`: there is no "singular but nonzero" canonical metric.  This is what makes the
degenerate classification finite. -/
theorem explicitCanonicalMetric_eq_zero_of_not_isUnit {F : BlockMat d}
    (h : ¬ IsUnit (explicitCanonicalMetric F).det) : explicitCanonicalMetric F = 0 := by
  rw [explicitCanonicalMetric] at h ⊢
  refine Matrix.nonsing_inv_apply_not_isUnit _ ?_
  intro hu
  exact h (Matrix.isUnit_nonsing_inv_det _ hu)

/-- When the canonical metric degenerates, the entire metric block does. -/
theorem toFullBlockMat_respM0_eq_zero {F : BlockMat d} (h : explicitCanonicalMetric F = 0) :
    toFullBlockMat (respM0 F) = 0 := by
  ext (i | i) (j | j) <;>
    simp [toFullBlockMat, respM0, h, Matrix.inv_zero]

/-- `blockSqrt` of a vanishing metric block vanishes. -/
theorem blockSqrt_respM0_eq_zero {F : BlockMat d} (h : explicitCanonicalMetric F = 0) :
    blockSqrt (respM0 F) = ofFullBlockMat 0 := by
  rw [blockSqrt, toFullBlockMat_respM0_eq_zero h, matSqrt_zero]

/-- Consequently every `M_0^{1/2}`-transported vector vanishes, so the left-hand side of the
diagonal weak-norm bound is identically `0` in this branch. -/
theorem blockMatVecMul_blockSqrt_respM0_eq_zero {F : BlockMat d} (h : explicitCanonicalMetric F = 0)
    (Y : BlockVec d) : blockMatVecMul (blockSqrt (respM0 F)) Y = 0 := by
  rw [blockSqrt_respM0_eq_zero h]
  ext i <;> simp [blockMatVecMul, matVecMul, ofFullBlockMat]

/-! ## The indefinite branch: the metric disappears from both sides -/

/-- If the metric block is not positive semidefinite, `blockSqrt (respM0 F)` is the junk
identity, so `M_0^{1/2}` acts trivially on the left-hand side of the diagonal weak-norm bound. -/
theorem toFullBlockMat_blockSqrt_respM0_eq_one {F : BlockMat d}
    (h : ¬ (toFullBlockMat (respM0 F)).PosSemidef) :
    toFullBlockMat (blockSqrt (respM0 F)) = 1 := by
  rw [blockSqrt, toFullBlockMat_ofFullBlockMat, matSqrt_eq_one_of_not_posSemidef h]

/-- In the same branch the INVERSE metric block is not positive semidefinite either, as
soon as the metric is a unit, so `normalizedBlock E (respM0 F)` is `E` itself: the printed
constant `K_0` degenerates to `‖E‖` and nothing is lost. -/
theorem toFullBlockMat_normalizedBlock_respM0_eq_self {F : BlockMat d} (E : BlockMat d)
    (hu : IsUnit (toFullBlockMat (respM0 F)).det)
    (h : ¬ (toFullBlockMat (respM0 F)).PosSemidef) :
    toFullBlockMat (normalizedBlock E (respM0 F)) = toFullBlockMat E := by
  have hinv : ¬ ((toFullBlockMat (respM0 F))⁻¹).PosSemidef := by
    intro hpsd
    refine h ?_
    have : (toFullBlockMat (respM0 F))⁻¹⁻¹ = toFullBlockMat (respM0 F) :=
      Matrix.nonsing_inv_nonsing_inv _ hu
    rw [← this]
    exact hpsd.inv
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, matSqrt_eq_one_of_not_posSemidef hinv,
    one_mul, mul_one]

/-! ## Invertibility and the metric restriction on the unit branch -/

/-- The explicit left inverse of the flattened metric block on the unit branch.  This is
the computational core of the metric inverse lemma (`toFullBlockMat_respM0_inv`,
`DiagonalWeakNormBound.lean`), isolated here because it needs only `IsUnit` of the metric
determinant, not positive definiteness. -/
theorem toFullBlockMat_respM0_left_inv {F : BlockMat d}
    (hu : IsUnit (explicitCanonicalMetric F).det) :
    toFullBlockMat (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ : BlockMat d) *
        toFullBlockMat (respM0 F) = 1 := by
  have hmm : (explicitCanonicalMetric F)⁻¹ * explicitCanonicalMetric F = 1 :=
    Matrix.nonsing_inv_mul _ hu
  have hmm' : explicitCanonicalMetric F * (explicitCanonicalMetric F)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hu
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have hij : ∑ k : Fin d, (explicitCanonicalMetric F)⁻¹ i k * explicitCanonicalMetric F k j
          = ((explicitCanonicalMetric F)⁻¹ * explicitCanonicalMetric F) i j :=
            (Matrix.mul_apply).symm
      simp only [toFullBlockMat, respM0]
      rw [show (∑ k : Fin d, (explicitCanonicalMetric F)⁻¹ i k * explicitCanonicalMetric F k j) +
          (∑ k : Fin d, (0 : Mat d) i k * (0 : Mat d) k j) = _ from rfl]
      simp [hij, hmm, Matrix.one_apply]
    | inr j =>
      simp [toFullBlockMat, respM0]
  | inr i =>
    cases b with
    | inl j =>
      simp [toFullBlockMat, respM0]
    | inr j =>
      have hij : ∑ k : Fin d, explicitCanonicalMetric F i k * (explicitCanonicalMetric F)⁻¹ k j
          = (explicitCanonicalMetric F * (explicitCanonicalMetric F)⁻¹) i j :=
            (Matrix.mul_apply).symm
      simp only [toFullBlockMat, respM0]
      rw [show (∑ k : Fin d, (0 : Mat d) i k * (0 : Mat d) k j) +
          (∑ k : Fin d, explicitCanonicalMetric F i k * (explicitCanonicalMetric F)⁻¹ k j) = _
            from rfl]
      simp [hij, hmm', Matrix.one_apply]

/-- Hence on the unit branch the flattened metric block is invertible, with NO
positivity assumption whatsoever. -/
theorem isUnit_det_toFullBlockMat_respM0 {F : BlockMat d}
    (hu : IsUnit (explicitCanonicalMetric F).det) : IsUnit (toFullBlockMat (respM0 F)).det :=
  Matrix.isUnit_det_of_left_inverse (toFullBlockMat_respM0_left_inv hu)

/-- The canonical metric inherits positive semidefiniteness from the flattened metric
block: restrict the quadratic form to the first slot. -/
theorem posSemidef_explicitCanonicalMetric_of_respM0 {F : BlockMat d}
    (h : (toFullBlockMat (respM0 F)).PosSemidef) : (explicitCanonicalMetric F).PosSemidef := by
  have hherm : (explicitCanonicalMetric F).IsHermitian := by
    have hH := h.1
    ext i j
    have := congrFun (congrFun hH (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.conjTranspose_apply, toFullBlockMat, respM0] using this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm ?_
  intro v
  have hq := h.dotProduct_mulVec_nonneg (toFullBlockVec ((v, 0) : BlockVec d))
  have hblock : blockMatVecMul (respM0 F) ((v, 0) : BlockVec d)
      = (matVecMul (explicitCanonicalMetric F) v, 0) := by
    ext i <;> simp [blockMatVecMul, respM0, matVecMul]
  have hrw : star (toFullBlockVec ((v, 0) : BlockVec d)) ⬝ᵥ
        toFullBlockMat (respM0 F) *ᵥ toFullBlockVec ((v, 0) : BlockVec d)
      = v ⬝ᵥ explicitCanonicalMetric F *ᵥ v := by
    rw [star_trivial, ← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec, hblock]
    simp [blockVecDot, vecDot, dotProduct, Matrix.mulVec, matVecMul]
  rwa [hrw] at hq

/-! ## The `Ehat` degeneration

The OTHER degenerate side is the one where the congruenced annealed block
`Ehat_t^- = respEhatMinus P jStar F t` is singular; the statements recorded here do not close it. -/

/-! ## The load collapse, one sub-case of the `Ehat` degeneration

If `respEhatMinus` is singular then `respLsqMinus = 0` forces the loads to vanish.  That is TRUE
in the sub-case where the degeneration sits in the lower-right block of the annealed mean — but
only there; the remaining sub-case resists. -/

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The bad-branch weight arithmetic of the cell-average estimate

On the event `{M > 1}` of the all-scale maximum `M`, the cell-average estimate is absorbed by
its tail term, and the only remaining input is the geometric comparison of the weights
`3^{-a j}`.  This file records that comparison as plain real arithmetic: a geometric series with
ratio `3^{-a}`, the reciprocal bound `(1 - 3^{-a})^{-1} ≤ 3/a` on `0 < a ≤ 1`, its value
`(1 - 3^{-1/2})^{-1} ≤ 3` at `a = 1/2`, and the assembled bad-branch weight bound in terms of the
response parameters `Quenched.contrastAlpha` and `Quenched.contrastRho`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The tail weights `3^{-(a j)}` sum to the geometric series with ratio `3^{-a}`. -/
theorem geom_sum_rpow (a : ℝ) (ha : 0 < a) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) = (1 - (3 : ℝ) ^ (-a))⁻¹ := by
  have hterm : ∀ j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) = ((3 : ℝ) ^ (-a)) ^ j := by
    intro j
    rw [show -(a * (j : ℝ)) = (-a) * (j : ℝ) by ring]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  rw [tsum_congr hterm]
  exact tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr ha))

/-- On `0 < a ≤ 1` the reciprocal of `1 - 3^{-a}` is at most `3 / a`. -/
theorem inv_one_sub_rpow_le (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (1 - (3 : ℝ) ^ (-a))⁻¹ ≤ 3 / a := by
  have hexp1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr hexp1
  have hlog0 : 0 < Real.log 3 := lt_trans zero_lt_one hlog
  set x : ℝ := a * Real.log 3 with hxdef
  have hx_pos : 0 < x := by
    rw [hxdef]
    exact mul_pos ha0 hlog0
  have hx_le : x ≤ Real.log 3 := by
    rw [hxdef]
    have h := mul_le_mul_of_nonneg_right ha1 hlog0.le
    simpa using h
  have hxa : a ≤ x := by
    rw [hxdef]
    have h := mul_le_mul_of_nonneg_left hlog.le ha0.le
    simpa using h
  have hrpow : (3 : ℝ) ^ (-a) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    dsimp only [x]
    ring
  have hexp_log3 : Real.exp (-(Real.log 3)) = (1 : ℝ) / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3), one_div]
  have hexp_lower : (1 : ℝ) / 3 ≤ Real.exp (-x) := by
    rw [← hexp_log3]
    exact Real.exp_le_exp.mpr (neg_le_neg hx_le)
  have he : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hxle : x ≤ Real.exp x - 1 := by linarith only [Real.add_one_le_exp x]
  have hkey : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
    calc x * Real.exp (-x) ≤ (Real.exp x - 1) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hxle (Real.exp_pos (-x)).le
      _ = 1 - Real.exp (-x) := by rw [sub_mul, one_mul, he]
  have hmul2 : a * (1 / 3) ≤ x * Real.exp (-x) :=
    mul_le_mul hxa hexp_lower (by norm_num) hx_pos.le
  have ha3 : a / 3 ≤ 1 - Real.exp (-x) := by
    have h1 : a / 3 = a * (1 / 3) := by ring
    rw [h1]
    exact hmul2.trans hkey
  have hmain : a / 3 ≤ 1 - (3 : ℝ) ^ (-a) := by
    rw [hrpow]
    exact ha3
  have hden : 0 < a / 3 := by positivity
  calc (1 - (3 : ℝ) ^ (-a))⁻¹ = 1 / (1 - (3 : ℝ) ^ (-a)) := by
        rw [div_eq_mul_inv, one_mul]
    _ ≤ 1 / (a / 3) := one_div_le_one_div_of_le hden hmain
    _ = 3 / a := by rw [one_div_div]

/-- At `a = 1/2` the reciprocal bound sharpens to `3`. -/
theorem inv_one_sub_rpow_half_le : (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ ≤ 3 := by
  have hsq : ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 : ℝ) / 3 := by
    rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (-(1 / 2 : ℝ)) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  have hle : ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ ((2 : ℝ) / 3) ^ 2 := by
    rw [hsq]
    norm_num
  have hr : (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) / 3 :=
    le_of_sq_le_sq hle (by norm_num)
  have hden : (1 : ℝ) / 3 ≤ 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith only [hr]
  have hpos : 0 < 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith only [hr]
  rw [inv_le_iff_one_le_mul₀' hpos]
  linarith only [hden]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The tail weight of the cell-average estimate, both branches at once

The cell-average estimate `e.response.weak.estimate` prints its older-scale tail weight as a
single `if` at the cutoff `1`: the branch `1 < M` contributes the recent-scale value `√M`, and its
complement the older-scale weight `3^{-(Quenched.contrastAlpha γ * H)}`.  The two branches are
discharged by
different lemmas elsewhere in the development; this file packages the case split once and for all,
so that a consumer carrying `M` need not first decide which branch it lies on.
-/

namespace HCPolySupport.HighContrast.Multiscale

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- On either branch of the cutoff `1 < M`, the smaller of `Real.sqrt M` and `θ` is at most the
branch value the cell-average estimate prints. -/
theorem le_tail_branch (M θ : ℝ) (_hM : 0 ≤ M) (_hθ : 0 ≤ θ) :
    min (Real.sqrt M) θ ≤ (if 1 < M then Real.sqrt M else θ) := by
  by_cases h : 1 < M
  · simp only [ite_eq_left h]
    exact min_le_left _ _
  · simp only [ite_eq_right h]
    exact min_le_right _ _

/-- The branch-free tail comparison behind `e.response.weak.estimate`: a value `Agood` bounded by
`cgood` times the older-scale weight on `M ≤ 1`, and a value `Abad` bounded by `cbad` times `√M`
on `1 < M`, are together dominated by `max cgood cbad` times the printed `if` tail weight. -/
theorem branchfree_tail_le (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (H : ℕ) (M : ℝ)
    (_hM : 0 ≤ M) (cgood cbad : ℝ) (_hcgood : 0 ≤ cgood) (_hcbad : 0 ≤ cbad)
    (Agood Abad : ℝ)
    (hgood : M ≤ 1 → Agood ≤ cgood * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))))
    (hbad : 1 < M → Abad ≤ cbad * Real.sqrt M) :
    (if 1 < M then Abad else Agood)
      ≤ max cgood cbad * (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(Quenched.contrastAlpha γ *
        (H : ℝ)))) := by
  by_cases h : 1 < M
  · simp only [ite_eq_left h]
    calc Abad ≤ cbad * Real.sqrt M := hbad h
      _ ≤ max cgood cbad * Real.sqrt M :=
          mul_le_mul_of_nonneg_right (le_max_right cgood cbad) (Real.sqrt_nonneg M)
  · simp only [ite_eq_right h]
    have hr : 0 ≤ (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    calc Agood ≤ cgood * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) := hgood (not_lt.mp h)
      _ ≤ max cgood cbad * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left cgood cbad) hr

end

end HCPolySupport.HighContrast.Multiscale
end
