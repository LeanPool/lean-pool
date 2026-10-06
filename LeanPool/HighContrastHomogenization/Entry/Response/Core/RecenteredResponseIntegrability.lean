/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Geometry.CanonicalMetricBounds
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalReadoutMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.IntegratedWeakEnergyBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.OptimizerEnergyIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Entry.Source.BoundedWindowFiniteness
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# High-contrast homogenization: Entry.Response.Core.RecenteredResponseIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Law integrability of the recentred and adjoint pathwise response

The pathwise response `J(U_u, p, q; b)` of a sample coefficient agrees, on an adapted cell where
`b` is elliptic, with the quadratic expression `½ x · 𝐀(U_u; b) x - p · q` of the coarse block;
using the deterministic congruence linking the coarse block of a recentred coefficient to that of
the sample, this file shows that `J(U_u; a_-)`, `J(U_u; a_+)` and their squares are `P`-integrable
under the coarse ellipticity assumption. It records the square-integrability the weak-norm
estimate needs of the doubled optimizer state on an adapted cell, and the affine invariance of the
scale-average seminorm of a doubled field under a constant block change of variables. It closes
with the singular-grid branch of the cutoff-pairing bound of `e.response.cutoff.estimate`: the
relevant cell average and its integral both vanish when the selected grid is degenerate, and the
weak response energy `respWeakEnergy` is nonnegative and realized by any admissible family.
-/

section
/-!
## Law integrability of the adjoint recentred pathwise response

The pathwise response `J(U, p, q; b)` of a sample coefficient is a supremum, and on an adapted
cell it agrees with the quadratic expression `½ x · 𝐀(U; b) x - p · q` of the coarse block
whenever `b` is elliptic.  This file records that agreement for the adjoint recentred
coefficient `a₊ = aᵗ + g`, where `g` is the skew Schur half of the self-dual splitting, and
deduces that the annealed response `a ↦ J(U, p, q; a₊)` is integrable for the law as soon as
the entries of the coarse block `𝐀(U; a)` are.

The two structural facts are:

* the adjoint of a coefficient reflects its coarse block in the flux slot, and recentring by
  the skew half `g` is the constant shear congruence `G` of the self-dual splitting, so
  `𝐀(U; a₊) = (G·D)ᵀ 𝐀(U; a) (G·D)`;
* the doubled quadratic form of a constant congruence is a finite linear combination of the
  entries of `𝐀(U; a)`, hence inherits their integrability.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Coarse block of the adjoint recentred coefficient.**  For every sample `a` the coarse
block of the adjoint recentred coefficient `a₊ = aᵗ + g` is the constant congruence, by the
shear `G` of the self-dual splitting and the flux reflection `D = diag(Id, -Id)`, of the coarse
block of `a`.  The adjoint transpose reflects the coarse block in the flux slot and the
recentring by the skew Schur half `g` shears it. -/
theorem coarseBlockMatrix_respCoeffPlus_eq_blockCongr {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (u : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffPlus F a)
      = blockCongr (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
          (coarseBlock (HighContrast.adaptedCell q u) a) := by
  have hgskew : matTranspose (respg F) = -(respg F) := respg_isSkew F
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    ext i j
    have h := congrFun (congrFun hgskew i) j
    simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at h ⊢
    linarith only [h]
  have hquad := hasQuadraticMu_adaptedCell q hq u a
  have h1 : respCoeffPlus F a
      = fun x => (adjointCoeffField (⇑a.1 : CoeffField d)) x - (-(respg F)) := by
    funext x
    simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
  have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := HighContrast.adaptedCell q u)
    (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
    (hasQuadraticMu_adjointCoeffField hquad)
  have h3 : coarseBlockMatrix (HighContrast.adaptedCell q u)
        (adjointCoeffField (⇑a.1 : CoeffField d))
      = blockCongr (blockD d) (coarseBlock (HighContrast.adaptedCell q u) a) := by
    rw [coarseBlockMatrix_adjointCoeffField_of_exists
      (exists_coarseBlockMatrix_of_hasQuadraticMu hquad), ← blockCongr_blockD]
    rfl
  rw [h1, h2, h3, blockCongr_blockCongr, blockD_mul_shear_neg (respg F)]
  rfl

/-- **The pathwise response of the adjoint recentred coefficient.**  On the adapted cell the
pathwise response of `a₊ = aᵗ + g` is the quadratic expression of the coarse block: the
coefficient is almost everywhere equal to a uniformly elliptic representative, and the response
and the coarse block depend only on the almost everywhere class. -/
theorem respJ_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (u : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    respJ q u p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffPlus F a))
            (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, -, -, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq u F a
  have hConv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q u) :=
    adaptedCell_isOpenBoundedConvexDomain q hq u
  have hvol : 0 < (volume (HighContrast.adaptedCell q u)).toReal :=
    ENNReal.toReal_pos (hConv.isOpen.measure_ne_zero volume (Recurrence.adaptedCell_nonempty q u))
      hConv.volume_lt_top.ne
  have hJ : respJ q u p r (respCoeffPlus F a) = respJ q u p r f := by
    unfold respJ
    exact responseJ_congr_of_ae_eq hae p r
  have hblock : coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffPlus F a)
      = coarseBlockMatrix (HighContrast.adaptedCell q u) f :=
    coarseBlockMatrix_congr_of_ae_eq hae
  rw [hJ]
  unfold respJ
  rw [responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain hConv hEll hvol p r, hblock]

/-- **Law integrability of the adjoint recentred pathwise response.**  For the adjoint recentred
coefficient `a₊ = aᵗ + g` of a sample `a`, the pathwise response of the adapted cell is
integrable for the law as soon as the entries of the coarse block `𝐀(U; a)` are: the recentring
is a constant congruence of that coarse block, and the quadratic form of a constant congruence
is a finite combination of its entries. -/
theorem integrable_respJ_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsFiniteMeasure P]
    (jStar : ℕ) (F : BlockMat d) (u : ℤ) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) (p q' : Vec d) :
    MeasureTheory.Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffPlus F a)) P := by
  refine integrable_respJ_of_pathwise P (respGrid jStar F) u p q' (respCoeffPlus F)
    (fun a => respJ_respCoeffPlus_eq (respGrid jStar F) hq u F a p q') ?_
  exact integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr
    (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
    hint (fun a => coarseBlockMatrix_respCoeffPlus_eq_blockCongr (respGrid jStar F) hq u F a)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Law integrability of the pathwise response on an adapted cell

Let `P` be a stationary law satisfying the coarse ellipticity assumption, and let `U_u` be the
adapted cell of generation `u` on a selected grid.  This file proves that for each of the two
recentred coefficients `a_- = a - g` and `a_+ = a^t + g` of the self-dual recentring the pathwise
response `J(U_u, p, q'; a_\pm)` is `P`-integrable.

The route has three steps.  The response of an elliptic field on a bounded open convex domain is
the fixed quadratic `\tfrac12 (-p, q') \cdot \mathbf A(U; a)(-p, q') - p \cdot q'` of the coarse
block; the coarse block of a recentred field is a *deterministic* congruence of the coarse block
of the sample, so its entries are fixed linear combinations of the entries of `\mathbf A(U; a)`;
and those entries are `P`-integrable for every law satisfying the coarse ellipticity assumption.

The only dimensional hypothesis used is `d \neq 0`.

Paper: `p.response.transfer`, Step 3 and Step 6; the recentring is the one of `e.self.dual`.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix)
open HCPolySupport.HighContrast (adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

variable {d : ℕ}

/-! ## Step 1: the coarse block of an adapted cell is law integrable in every dimension -/

/-- Every finite moment of the Schatten norm of the coarse block of an adapted cell is finite,
for any law satisfying the coarse ellipticity assumption.  This is the statement of the
bounded-window source estimate with the dimensional hypothesis relaxed to `d \neq 0`, which is
all its proof uses. -/
theorem memLqSchatten_coarseBlock_adaptedCellTranslate [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) (y : Vec d)
    (N : ℝ) (hN : 1 ≤ N) :
    SchattenMemLp P N
      (fun a => coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) a) := by
  set q := explicitRoundedGrid jStar m with hqdef
  have hq : IsUnit q := isUnit_roundedGrid hj hm
  set W := adaptedCellTranslate q j y with hWdef
  have hW : Bornology.IsBounded W := by
    rw [hWdef, Annealed.adaptedCellTranslate_eq_cg_affine]
    exact (isOpenBoundedConvexDomain_affine_openCube q hq j y).isBoundedDomain.isBounded
  obtain ⟨J, X, _, _, hXN, hbound⟩ := Source.bounded_source_envelope P γ E Ψ K S hstat hdag W hW
  have hmeas : HasMeasurableBlock P (fun a => coarseBlock W a) := fun α β =>
    ((Annealed.measurable_coarseBlock_entry_adapted q hq j y α β).mono
      (Annealed.coeffSigma_le_global _) le_rfl).aestronglyMeasurable
  set D : ℝ := (12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))) *
    (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) with hDdef
  apply Source.memLqSchatten_of_order_envelope hN hmeas
    (ae_of_all _ (fun a => isSymmetricBlockMat_coarseBlockMatrix W (⇑a.1)))
    (ae_of_all _ (fun a => Annealed.blockPosDef_coarseBlock_adapted q hq j y a)) (hXN N hN) D
  filter_upwards [hbound] with a ha
  have hb := ha q (inverseNormLE_roundedGrid hj hm) j y Set.Subset.rfl
  convert hb using 1
  congr 1
  rw [hDdef]
  ring

/-- Every entry of the coarse block of an adapted cell is `P`-integrable, in every dimension
`d \neq 0`. -/
theorem hasIntegrableCoarseBlock_adaptedCell [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    HasIntegrableCoarseBlock P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) := by
  have h := (memLqSchatten_coarseBlock_adaptedCellTranslate P γ E Ψ K S hstat hdag jStar hj
    m hm j 0 1 le_rfl).integrable_entry le_rfl
  rwa [Annealed.adaptedCellTranslate_zero] at h

/-- The same at the selected grid of the response argument. -/
theorem hasIntegrableCoarseBlock_respCell [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (u : ℤ) :
    HasIntegrableCoarseBlock P (respCell jStar F u) :=
  hasIntegrableCoarseBlock_adaptedCell P γ E Ψ K S hstat hdag jStar hj (explicitCanonicalMetric
    F) hm u

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Square integrability of the recentred pathwise response

On an adapted cell the pathwise response `J(U_u; a_-(a))` of the recentred coefficient is the
fixed quadratic form `AK.HC (2.15)` of the coarse block `𝐀(U_u; a_-(a))`, and that coarse block is
a deterministic congruence `Gᵀ 𝐀(U_u; a) G` of the coarse block of the sample.  Hence the response
is an affine function of the entries of `𝐀(U_u; a)`, and the square of the response is a finite
combination of products of pairs of those entries.

This file records the two consequences used by the cutoff rows:

* each entry of `𝐀(U_u; ·)` is square integrable as soon as the coarse block lies in every
  Schatten moment `L^N(S_N)`, because the operator norm — and so each entry — is dominated by the
  Schatten norm;
* consequently the square of the pathwise response is `P`-integrable for both recentrings
  `a_- = a - g` and `a_+ = aᵗ + g`, with the Schatten-moment hypothesis discharged from the
  stationary law and the coarse ellipticity assumption.

Paper: `AK.HC (2.15)`, and the bounded-window source estimate for the Schatten moments.
-/

open HCPolySupport.HighContrast (CoeffSpace blockVecDot_blockMatVecMul_eq_sum coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

variable {d : ℕ}

/-! ## Entrywise square integrability of the coarse block -/

/-- Each entry of the coarse block is square integrable for the law as soon as the coarse block
lies in every Schatten moment.  The entry is dominated by the operator norm, which the Schatten
norm dominates, so an `L²(S₂)` membership transfers to the entry. -/
private theorem memLp_two_blockMatEntry_of_memLqSchatten
    (P : Measure (CoeffSpace d)) (V : Set (Vec d))
    (hmem : ∀ N : ℝ, 1 ≤ N → SchattenMemLp P N (fun a => coarseBlock V a))
    (α β : BlockCoord d) :
    MemLp (fun a => blockMatEntry (coarseBlock V a) α β) 2 P := by
  have hH := hmem 2 (by norm_num)
  have hsn : MemLp (fun a => absSchattenNorm 2 (coarseBlock V a)) 2 P := by
    simpa only [ENNReal.ofReal_ofNat] using hH.memLp_absSchattenNorm (by norm_num)
  refine MemLp.of_le hsn (hH.measurable α β) ?_
  filter_upwards [hH.symmetric] with a ha
  have hHerm : (toFullBlockMat (coarseBlock V a)).IsHermitian :=
    (Analysis.toFullBlockMat_isHermitian_iff (coarseBlock V a)).2 ha
  have hnn : 0 ≤ absSchattenNorm 2 (coarseBlock V a) :=
    Analysis.absSchattenNorm_nonneg hHerm (by norm_num)
  calc
    ‖blockMatEntry (coarseBlock V a) α β‖
        = |blockMatEntry (coarseBlock V a) α β| := Real.norm_eq_abs _
    _ ≤ blockOpNorm (coarseBlock V a) :=
        SchattenMemLp.abs_blockMatEntry_le_blockOpNorm _ α β
    _ ≤ absSchattenNorm 2 (coarseBlock V a) :=
        Analysis.blockOpNorm_le_absSchattenNorm hHerm (by norm_num)
    _ = ‖absSchattenNorm 2 (coarseBlock V a)‖ := (Real.norm_of_nonneg hnn).symm

/-! ## Square integrability of the pathwise response -/

/-- Square integrability of the pathwise response when its coarse block is a constant congruence
of the sample coarse block.  The response is the block quadratic `AK.HC (2.15)` of the recentred
block, so it is an affine function of the entries of the coarse block; being a finite combination
of square integrable entries it is square integrable, and its square is integrable. -/
private theorem integrable_respJ_sq_of_blockCongr {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (G : BlockMat d) (V : Set (Vec d)) (qq : Mat d) (u : ℤ) (b : CoeffSpace d → CoeffField d)
    (p q' : Vec d)
    (hpath : ∀ a : CoeffSpace d, respJ qq u p q' (b a)
      = (1 / 2 : ℝ) * blockVecDot (-p, q')
          (blockMatVecMul (coarseBlockMatrix V (b a)) (-p, q')) - vecDot p q')
    (hcongr : ∀ a : CoeffSpace d,
      coarseBlockMatrix V (b a) = blockCongr G (coarseBlock V a))
    (hmem : ∀ N : ℝ, 1 ≤ N → SchattenMemLp P N (fun a => coarseBlock V a)) :
    Integrable (fun a => respJ qq u p q' (b a) ^ 2) P := by
  let X : BlockVec d := (-p, q')
  let Y : BlockVec d := blockMatVecMul G X
  let Q : CoeffSpace d → ℝ := fun a =>
    ∑ κ : BlockCoord d, ∑ β : BlockCoord d,
      toFullBlockVec Y κ *
        (blockMatEntry (coarseBlock V a) κ β * toFullBlockVec Y β)
  have hQ : MemLp Q 2 P := by
    dsimp only [Q]
    refine memLp_finsetSum _ (fun κ _ => ?_)
    refine memLp_finsetSum _ (fun β _ => ?_)
    exact ((memLp_two_blockMatEntry_of_memLqSchatten P V hmem κ β).const_mul
      (toFullBlockVec Y κ * toFullBlockVec Y β)).ae_eq
      (Filter.Eventually.of_forall fun a => by ring)
  have hpoint : ∀ a : CoeffSpace d,
      respJ qq u p q' (b a) = (1 / 2 : ℝ) * Q a - vecDot p q' := by
    intro a
    rw [hpath a, hcongr a, blockVecDot_blockCongr, blockVecDot_blockMatVecMul_eq_sum]
  have hres : MemLp (fun a => respJ qq u p q' (b a)) 2 P :=
    ((hQ.const_mul (1 / 2 : ℝ)).sub (memLp_const (vecDot p q'))).ae_eq
      (Filter.Eventually.of_forall fun a => (hpoint a).symm)
  exact hres.integrable_sq

/-- **Square integrability of the recentred pathwise response.**  For the recentred coefficient
`a_- = a - g` of the self-dual splitting, whose coarse block is the fixed shear congruence
`Gᵀ 𝐀(U_u; a) G`, the square of the pathwise response is `P`-integrable as soon as the coarse
block of the sample lies in every Schatten moment.  The response is the block quadratic
`AK.HC (2.15)` of that congruence, hence an affine function of the entries of `𝐀(U_u; ·)`; each
entry is square integrable because it is dominated by the operator norm, which the Schatten norm
dominates. -/
theorem integrable_respJ_sq_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (u : ℤ)
    (hq : IsUnit (respGrid jStar F))
    (hmem : ∀ N : ℝ, 1 ≤ N → SchattenMemLp P N (fun a => coarseBlock (respCell jStar F u) a))
    (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffMinus F a) ^ 2) P :=
  integrable_respJ_sq_of_blockCongr P (respG F) (respCell jStar F u) (respGrid jStar F) u
    (respCoeffMinus F) p q'
    (fun a => respJ_respCoeffMinus_eq (respGrid jStar F) hq u F a p q')
    (fun a => coarseBlockMatrix_respCoeffMinus_eq_blockCongr (respGrid jStar F) hq u F a)
    hmem

/-- **Square integrability of the adjoint recentred pathwise response.**  For the adjoint recentred
coefficient `a_+ = aᵗ + g`, whose coarse block is the fixed congruence `(G·D)ᵀ 𝐀(U_u; a) (G·D)`,
the square of the pathwise response is `P`-integrable as soon as the coarse block of the sample
lies in every Schatten moment.  The proof is the adjoint twin of
`integrable_respJ_sq_respCoeffMinus`. -/
theorem integrable_respJ_sq_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (u : ℤ)
    (hq : IsUnit (respGrid jStar F))
    (hmem : ∀ N : ℝ, 1 ≤ N → SchattenMemLp P N (fun a => coarseBlock (respCell jStar F u) a))
    (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffPlus F a) ^ 2) P :=
  integrable_respJ_sq_of_blockCongr P
    (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
    (respCell jStar F u) (respGrid jStar F) u (respCoeffPlus F) p q'
    (fun a => respJ_respCoeffPlus_eq (respGrid jStar F) hq u F a p q')
    (fun a => coarseBlockMatrix_respCoeffPlus_eq_blockCongr (respGrid jStar F) hq u F a)
    hmem

/-! ## Discharging the Schatten-moment hypothesis -/

/-- **Square integrability of the recentred pathwise response from the law hypotheses.**  For a
stationary law satisfying the coarse ellipticity assumption, the coarse block of the response cell
lies in every Schatten moment `L^N(S_N)` by the bounded-window source estimate, so
`integrable_respJ_sq_respCoeffMinus` applies and the square of the recentred pathwise response is
`P`-integrable. -/
theorem integrable_respJ_sq_respCoeffMinus_of_dagger {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (u : ℤ) (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffMinus F a) ^ 2) P := by
  have hq : IsUnit (respGrid jStar F) := isUnit_roundedGrid hj hm
  have hmem : ∀ N : ℝ, 1 ≤ N →
      SchattenMemLp P N (fun a => coarseBlock (respCell jStar F u) a) := by
    intro N hN
    have h := memLqSchatten_coarseBlock_adaptedCellTranslate P γ E Ψ K S hstat hdag
      jStar hj (explicitCanonicalMetric F) hm u 0 N hN
    simpa only [respCell, respGrid, adaptedCellTranslate_zero] using h
  exact integrable_respJ_sq_respCoeffMinus P jStar F u hq hmem p q'

/-- **Square integrability of the adjoint recentred pathwise response from the law hypotheses.**
The adjoint twin of `integrable_respJ_sq_respCoeffMinus_of_dagger`: the coarse block of the response
cell lies in every Schatten moment, and `integrable_respJ_sq_respCoeffPlus` applies. -/
theorem integrable_respJ_sq_respCoeffPlus_of_dagger {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (u : ℤ) (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffPlus F a) ^ 2) P := by
  have hq : IsUnit (respGrid jStar F) := isUnit_roundedGrid hj hm
  have hmem : ∀ N : ℝ, 1 ≤ N →
      SchattenMemLp P N (fun a => coarseBlock (respCell jStar F u) a) := by
    intro N hN
    have h := memLqSchatten_coarseBlock_adaptedCellTranslate P γ E Ψ K S hstat hdag
      jStar hj (explicitCanonicalMetric F) hm u 0 N hN
    simpa only [respCell, respGrid, adaptedCellTranslate_zero] using h
  exact integrable_respJ_sq_respCoeffPlus P jStar F u hq hmem p q'

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Square integrability of the doubled optimizer state on an adapted cell

The scale-average seminorm bound of `e.response.weak.estimate` is applied to the doubled
optimizer state `M_0^{1/2}\bigl((\nabla v, a\nabla v) - Y\bigr)` on an adapted cell.  Its
hypothesis is that the squared Euclidean length of that state is integrable on the cell, and
this file supplies that hypothesis.

The gradient slot is square integrable because the optimizer is an `H^1` function; the flux slot
is square integrable because the coefficient is uniformly elliptic on the cell after modification
on a null set, which is the form in which a qualitatively locally uniformly elliptic sample
provides ellipticity; the constant `Y` is square integrable because the cell has finite measure;
and a constant block matrix carries square integrable coordinates to square integrable
coordinates.

Paper: `e.response.weak.estimate`, and the normalization of the doubled state that precedes it.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Coordinatewise square integrability -/

/-- If every coordinate of a doubled field is square integrable, its squared Euclidean length is
integrable. -/
theorem memLp_one_blockVecDot_self_of_coords {V : Set (Vec d)} {W : Vec d → BlockVec d}
    (h1 : ∀ i, MemLp (fun x => (W x).1 i) 2 (volume.restrict V))
    (h2 : ∀ i, MemLp (fun x => (W x).2 i) 2 (volume.restrict V)) :
    MemLp (fun x => blockVecDot (W x) (W x)) 1 (volume.restrict V) := by
  rw [memLp_one_iff_integrable]
  have hs1 : Integrable (fun x => ∑ i, (W x).1 i * (W x).1 i) (volume.restrict V) := by
    refine integrable_finsetSum _ fun i _ => ?_
    simpa [Pi.mul_def] using (h1 i).integrable_mul (h1 i)
  have hs2 : Integrable (fun x => ∑ i, (W x).2 i * (W x).2 i) (volume.restrict V) := by
    refine integrable_finsetSum _ fun i _ => ?_
    simpa [Pi.mul_def] using (h2 i).integrable_mul (h2 i)
  simpa only [blockVecDot, vecDot] using! hs1.add hs2

/-- A constant block matrix carries a doubled field with square integrable coordinates to a
doubled field with square integrable coordinates. -/
theorem memLp_two_coords_blockMatVecMul {V : Set (Vec d)} (S : BlockMat d)
    {Z : Vec d → BlockVec d}
    (h1 : ∀ i, MemLp (fun x => (Z x).1 i) 2 (volume.restrict V))
    (h2 : ∀ i, MemLp (fun x => (Z x).2 i) 2 (volume.restrict V)) :
    (∀ i, MemLp (fun x => (blockMatVecMul S (Z x)).1 i) 2 (volume.restrict V)) ∧
      ∀ i, MemLp (fun x => (blockMatVecMul S (Z x)).2 i) 2 (volume.restrict V) := by
  have key : ∀ (A B : Mat d) (i : Fin d),
      MemLp (fun x => (∑ j, A i j * (Z x).1 j) + ∑ j, B i j * (Z x).2 j) 2
        (volume.restrict V) := by
    intro A B i
    refine MemLp.add ?_ ?_
    · exact memLp_finsetSum _ (fun j _ => (h1 j).const_mul (A i j))
    · exact memLp_finsetSum _ (fun j _ => (h2 j).const_mul (B i j))
  constructor
  · intro i
    simpa only [blockMatVecMul, matVecMul, Pi.add_apply] using key S.upperLeft S.upperRight i
  · intro i
    simpa only [blockMatVecMul, matVecMul, Pi.add_apply] using key S.lowerLeft S.lowerRight i

/-! ## The doubled optimizer state -/

/-- Both slots of the centred doubled optimizer field are square integrable on an adapted cell,
for a coefficient that agrees almost everywhere on the cell with a uniformly elliptic field. -/
theorem memLp_two_coords_optimizerField_sub_const [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hbf : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t)) (Y : BlockVec d) :
    (∀ i, MemLp (fun x => (optimizerField b u x - Y).1 i) 2
        (volume.restrict (HighContrast.adaptedCell q t))) ∧
      ∀ i, MemLp (fun x => (optimizerField b u x - Y).2 i) 2
        (volume.restrict (HighContrast.adaptedCell q t)) := by
  have : IsFiniteMeasure (volume.restrict (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using
      (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  have hgrad : ∀ i, MemLp (fun x => u.toH1.grad x i) 2
      (volume.restrict (HighContrast.adaptedCell q t)) := fun i => u.toH1.gradMemL2 i
  have hfluxf : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x))
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        fun x => matVecMul (b x) (u.toH1.grad x) := by
    filter_upwards [hbf] with x hx
    rw [hx]
  have hfluxb : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (b x) (u.toH1.grad x)) := (memLp_congr_ae hae).mp hfluxf
  have hflux : ∀ i, MemLp (fun x => matVecMul (b x) (u.toH1.grad x) i) 2
      (volume.restrict (HighContrast.adaptedCell q t)) := fun i =>
    (memLp_pi_iff.mp hfluxb) i
  constructor
  · intro i
    simpa only [optimizerField, Prod.fst_sub, Pi.sub_apply] using!
      (hgrad i).sub (memLp_const (Y.1 i))
  · intro i
    simpa only [optimizerField, Prod.snd_sub, Pi.sub_apply] using!
      (hflux i).sub (memLp_const (Y.2 i))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The scale-average seminorm of a recentred doubled field

The scale averages that enter the weak quantity of `e.response.weak.estimate` are the cell
averages of a doubled field after an affine change `Z \mapsto S(Z - Y)` with a constant block
matrix `S` and a constant doubled vector `Y`.  Because the cell average is linear, those averages
are the affine images of the cell averages of the field itself, so the Jensen/partition bound
applies verbatim to the recentred family.

The affine identity needs the two side conditions of an average over a cell: the cell has finite
nonzero volume, and each of the `2d` coordinates of the field is integrable on it.  Both are
supplied here from square integrability on the ambient cell.

Paper: `e.response.weak.estimate`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Linearity of the cell average under a constant affine map -/

/-- The average of `c (g - k)` over a cell of finite nonzero volume is `c` times the average of
`g` minus `k`. -/
theorem volumeAverage_const_mul_sub_const {V : Set (Vec d)} (hfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) (c k : ℝ) {g : Vec d → ℝ} (hg : IntegrableOn g V) :
    volumeAverage V (fun x => c * (g x - k)) = c * (volumeAverage V g - k) := by
  have hk : IntegrableOn (fun _ : Vec d => k) V := integrableOn_const hfin
  have hsub : volumeAverage V (fun x => g x - k) = volumeAverage V g - k := by
    have h := volumeAverage_sub (U := V) (f := g) (g := fun _ => k) hg hk
    simpa [volumeAverage_const hvol] using! h
  have hsm := volumeAverage_smul V c (fun x => g x - k)
  rw [show (fun x => c * (g x - k)) = (fun x => c • ((fun y => g y - k) x)) from rfl]
  simpa [hsub] using! hsm

/-- Linearity of the doubled cell average under the constant affine map `Z \mapsto S(Z - Y)`. -/
theorem cellAverage_blockMatVecMul_sub_const {V : Set (Vec d)} (hfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) (S : BlockMat d) (Y : BlockVec d) {Z : Vec d → BlockVec d}
    (h1 : ∀ i, IntegrableOn (fun x => (Z x).1 i) V)
    (h2 : ∀ i, IntegrableOn (fun x => (Z x).2 i) V) :
    cellAverage V (fun x => blockMatVecMul S (Z x - Y))
      = blockMatVecMul S (cellAverage V Z - Y) := by
  classical
  have hintterm : ∀ (c k : ℝ) (g : Vec d → ℝ), IntegrableOn g V →
      IntegrableOn (fun x => c * (g x - k)) V :=
    fun c k g hg => ((hg.sub (integrableOn_const hfin)).const_mul c)
  have hsum1 : ∀ (A : Mat d) (i : Fin d),
      volumeAverage V (fun x => ∑ j, A i j * ((Z x).1 j - Y.1 j))
        = ∑ j, A i j * (volumeAverage V (fun x => (Z x).1 j) - Y.1 j) := by
    intro A i
    rw [volumeAverage_sum Finset.univ (fun j x => A i j * ((Z x).1 j - Y.1 j))
      (fun j _ => hintterm _ _ _ (h1 j))]
    exact Finset.sum_congr rfl fun j _ => volumeAverage_const_mul_sub_const hfin hvol _ _ (h1 j)
  have hsum2 : ∀ (A : Mat d) (i : Fin d),
      volumeAverage V (fun x => ∑ j, A i j * ((Z x).2 j - Y.2 j))
        = ∑ j, A i j * (volumeAverage V (fun x => (Z x).2 j) - Y.2 j) := by
    intro A i
    rw [volumeAverage_sum Finset.univ (fun j x => A i j * ((Z x).2 j - Y.2 j))
      (fun j _ => hintterm _ _ _ (h2 j))]
    exact Finset.sum_congr rfl fun j _ => volumeAverage_const_mul_sub_const hfin hvol _ _ (h2 j)
  have hslot : ∀ (A B : Mat d) (i : Fin d),
      volumeAverage V (fun x =>
          (matVecMul A (Z x - Y).1 + matVecMul B (Z x - Y).2) i)
        = (matVecMul A ((fun i => volumeAverage V (fun x => (Z x).1 i)) - Y.1)
            + matVecMul B ((fun i => volumeAverage V (fun x => (Z x).2 i)) - Y.2)) i := by
    intro A B i
    have hrw : (fun x => (matVecMul A (Z x - Y).1 + matVecMul B (Z x - Y).2) i)
        = fun x => (∑ j, A i j * ((Z x).1 j - Y.1 j)) + ∑ j, B i j * ((Z x).2 j - Y.2 j) := by
      funext x
      simp [matVecMul, Prod.fst_sub, Prod.snd_sub]
    rw [hrw, show (fun x => (∑ j, A i j * ((Z x).1 j - Y.1 j))
          + ∑ j, B i j * ((Z x).2 j - Y.2 j))
        = ((fun x => ∑ j, A i j * ((Z x).1 j - Y.1 j))
          + (fun x => ∑ j, B i j * ((Z x).2 j - Y.2 j))) from rfl]
    rw [volumeAverage_add
      (by exact (MeasureTheory.integrable_finsetSum _ fun j _ => hintterm _ _ _ (h1 j)))
      (by exact (MeasureTheory.integrable_finsetSum _ fun j _ => hintterm _ _ _ (h2 j)))]
    rw [hsum1 A i, hsum2 B i]
    simp [matVecMul]
  refine Prod.ext ?_ ?_ <;> · funext i; simpa [cellAverage, blockMatVecMul] using hslot _ _ i

/-! ## The squared seminorm bound for a recentred family -/

variable [NeZero d]

/-! ## The two recentred response coefficients -/

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The singular-grid branch of the cutoff pairing bound

The selected grid is `respGrid jStar F = Geometry.explicitRoundedGrid jStar
(explicitCanonicalMetric F)`, and
every entry of `Geometry.explicitRoundedGrid` carries a factor built from the inverse of its metric
argument.  Mathlib's matrix inverse of a singular matrix is `0`
(`Matrix.nonsing_inv_apply_not_isUnit`), so when the canonical metric is singular the selected
grid degenerates to the zero matrix and the adapted cell carries no Lebesgue volume.  This file
records those degenerations: every volume average over a degenerate adapted cell is the junk value
`0`, and the determinant of the degenerate selected grid vanishes.

-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- On a singular grid `q` the adapted cell `HighContrast.adaptedCell q t` is Lebesgue null, so
every
volume average over it is the junk value `0`.  Indeed
`Geometry.volume_adaptedCell_toReal` gives
`(volume (HighContrast.adaptedCell q t)).toReal = |q.det| * ((3 : ℝ) ^ t) ^ d`, which vanishes when
`q.det = 0`, and `volumeAverage` multiplies by the inverse of that volume. -/
theorem volumeAverage_adaptedCell_eq_zero_of_det_eq_zero {d : ℕ} {q : Mat d} (hq : q.det = 0)
    (t : ℤ) (f : Vec d → ℝ) : volumeAverage (HighContrast.adaptedCell q t) f = 0 := by
  unfold volumeAverage
  rw [Geometry.volume_adaptedCell_toReal q t, hq]
  simp

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Elementary facts about the weak response energy

The weak response energy `respWeakEnergy` is the supremum, over all families of cell
maximizers of the response functional, of the weak energies
`3^{-t} ∫ [M_0^{1/2}(X_t - Y)]^2 dP`.  This file records the two facts used whenever it is
consumed as an upper bound: the supremum is nonnegative, and any single admissible family of
maximizers realizes a member of the defining set, so its weak energy lies below the supremum
once that set is bounded above.  These are the elementary parts of the weak estimate
`e.response.weak.estimate`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Every admissible family of cell maximizers realizes a member of the defining set of the
weak response energy `W`; consequently its weak energy is at most `W` whenever that set is
bounded above.  This is the direction in which `W` is consumed as an upper bound. -/
theorem le_respWeakEnergy {d : ℕ} (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ)
    (M0 : BlockMat d) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hbdd : BddAbove (respWeakEnergySet P qq t M0 p q' b Y))
    (u : (a : CoeffSpace d) → AHarmonicFunction (b a) (HighContrast.adaptedCell qq t))
    (hu : ∀ a, IsResponseMaximizer (HighContrast.adaptedCell qq t) p q' (b a) (u a)) :
    (3 : ℝ) ^ (-(t : ℝ)) * ∫ a, besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt M0)
          (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
            (optimizerField (b a) (u a)) - Y)) ^ 2 ∂P
      ≤ respWeakEnergy P qq t M0 p q' b Y := by
  rw [respWeakEnergy_eq_sSup_respWeakEnergySet]
  exact le_csSup hbdd ⟨u, hu, rfl⟩

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The singular-grid branch of the annealed cutoff pairing bound

The cutoff pairing of the response estimate is an expectation of absolute volume averages of an
adapted cell.  When the selected grid is singular the adapted cell is Lebesgue null, so every such
average is the junk value `0` and the expectation vanishes.  Together with the metric dichotomy
for the canonical metric, which always places an arbitrary doubled block on either the positive
definite branch or the singular-grid branch, this disposes of the branch on which the change of
variables underlying the cutoff argument is unavailable.

Paper: `e.response.cutoff.estimate`, `e.scale.selection.canonical.metric`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- On a singular grid `q` every adapted cell is Lebesgue null, so the absolute volume average of
any function over it is the junk value `0`; consequently the integral of those absolute averages
against any measure vanishes.  This is the degenerate branch of the cutoff pairing of
`e.response.cutoff.estimate`. -/
theorem integral_abs_volumeAverage_adaptedCell_eq_zero_of_det_eq_zero {d : ℕ}
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.det = 0) (t : ℤ)
    (f : CoeffSpace d → Vec d → ℝ) :
    (∫ a, |volumeAverage (HighContrast.adaptedCell q t) (f a)| ∂P) = 0 := by
  have h : ∀ a, |volumeAverage (HighContrast.adaptedCell q t) (f a)| = 0 := fun a => by
    rw [volumeAverage_adaptedCell_eq_zero_of_det_eq_zero hq t (f a), abs_zero]
  simp only [h, integral_zero]

/-- The canonical metric of an arbitrary doubled block is either positive definite or so
degenerate that the selected grid it produces is singular.  No symmetry or positivity hypothesis is
needed, because the junk values of the square root and of the matrix inverse are themselves
positive semidefinite.  This is the dichotomy of `e.scale.selection.canonical.metric` that selects
the branch of `e.response.cutoff.estimate`. -/
theorem metric_posDef_or_respGrid_det_eq_zero {d : ℕ} [NeZero d] (jStar : ℕ) (F : BlockMat d) :
    (explicitCanonicalMetric F).PosDef ∨ (respGrid jStar F).det = 0 :=
  Geometry.explicitCanonicalMetric_posDef_or_det_roundedGrid_eq_zero jStar F

end

end HCPolySupport.HighContrast.Multiscale
end
