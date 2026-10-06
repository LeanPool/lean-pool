/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ResponseFieldSize

/-!
# High-contrast homogenization: Entry.Response.Kernel.CoarseBlockPerCellInput

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coarse-block identification and the per-cell energy-map input

This file identifies the Chapter-2 coarse-block matrix of a recentred coefficient on an aligned
adapted cell with the shear congruence of the cell's set-level coarse block, for both signs. It
reduces the diagonal weak-norm estimate's remaining analytic hypothesis to two real-arithmetic
facts, and packages its per-cell hypothesis from either a bound by fixed constants or a bound by
the metric and the cell size. It then composes the recent-difference energy map with this
bookkeeping on an aligned cell, for the recentred sample and, tracking the extra congruence the
flux flip introduces, for its adjoint twin.  It serves the weak-norm estimate
`e.response.weak.estimate`.
-/

section
/-!
## The Chapter-2 coarse block of an adapted cell is the shear congruence

This module discharges the identification that the recent-difference and parent energy maps carry
as an explicit hypothesis: the Chapter-2 coarse block matrix of the recentred coefficient on an
aligned adapted cell is the shear congruence of the cell's set-level coarse block.

The two coarse-block carriers are not syntactically the same object.  Chapter 2 builds the block
from the doubled variational quantity `𝐀(U; a)` through the `sigma`/`kappa` recovery package,
while the set-level block is assembled directly from `Mu` by polarization.  The two constructions
agree on every Chapter-2 domain: Chapter-2's `doubledMu` is the set-level `Mu` of the coefficient
field (`book_doubledMu_eq_Mu`), and a block is determined by its `Mu` quadratic form
(`IsCoarseBlockMatrix` and `eq_coarseBlockMatrix_of_isCoarseBlockMatrix`).  That is the content of
`coarseBlockMatrix_domain_eq_set`.

The shear congruence itself is the set-level identity for a field recentred by a skew matrix: the
quadratic form of `a x - g` is the quadratic form of `a` at the sheared state
`(p, g p + q)`, so the recentred block is `Gᵀ 𝐀 G`.  This is `isCoarseBlockMatrix_respCoeffMinus`;
the adjoint twin
`isCoarseBlockMatrix_respCoeffPlus` composes it with the flux sign flip `D = diag(Id, -Id)`.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace Mu_congr_ae adaptedCellCenter coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- **The Chapter-2 coarse block of a `Domain` is the set-level coarse block of its
representative.**  Chapter-2's `doubledMu` is the set-level `Mu` of the coefficient field, and a
symmetric block is determined by its `Mu` quadratic form, so the two constructions coincide. -/
theorem coarseBlockMatrix_domain_eq_set {U : Book.Ch02.Domain d}
    (aU : Book.Ch02.CoeffOn U) :
    Book.Ch02.coarseBlockMatrix U aU = coarseBlockMatrix (U : Set (Vec d)) aU.toCoeffField := by
  refine eq_coarseBlockMatrix_of_isCoarseBlockMatrix ⟨?_, ?_⟩
  · exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U aU
  · intro P
    exact (HCPolySupport.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu U aU P).symm.trans
      ((Book.Ch02.doubledMuTheory U aU).doubledMu_eq_coarseBlockMatrix P)

/-- **The coarse block of a field on an aligned adapted cell satisfies the variational
characterization.**  A pointwise elliptic representative exists on the cell; CG's convex-domain
recovery supplies the `Mu` quadratic form for that representative, and `Mu` is insensitive to
changing the field on a null set. -/
theorem isCoarseBlockMatrix_adaptedCellAtCenter [NeZero d] (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) :
    IsCoarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d)
      (coarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d)) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  have hConv : IsOpenBoundedConvexDomain (adaptedCellAtCenter q k w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w
  have hvol : 0 < (volume (adaptedCellAtCenter q k w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos q hq k w
  have hA : IsCoarseBlockMatrix (adaptedCellAtCenter q k w) f
      (coarseBlockMatrix (adaptedCellAtCenter q k w) f) :=
    isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hConv hEll hvol
  refine ⟨isSymmetricBlockMat_coarseBlockMatrix _ _, ?_⟩
  intro P
  rw [Mu_congr_ae hae P, hA.2 P,
    coarseBlockMatrix_congr_of_ae_eq (U := adaptedCellAtCenter q k w) (ae_restrict_of_ae hae)]

/-- **The set-level shear identity from the variational characterization.**  If the set-level
coarse block of `a` is characterized by `Mu`, then recentring by a skew matrix `g` turns the
recentred block into the congruence of the block by `G = ((1, 0), (g, 1))`.  This is the
`IsCoarseBlockMatrix` form of the shear step, which avoids a separate quadraticity hypothesis. -/
theorem coarseBlockMatrix_sub_skew_of_isCoarseBlockMatrix {U : Set (Vec d)} {a : CoeffField d}
    {g : Mat d} {A : BlockMat d} (hg : matTranspose g = -g) (hA : IsCoarseBlockMatrix U a A) :
    coarseBlockMatrix U (fun x => a x - g) = blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A := by
  have hnew : IsCoarseBlockMatrix U (fun x => a x - g)
      (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) := by
    refine ⟨isSymmetricBlockMat_blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) hA.1, ?_⟩
    intro P
    rw [Mu_sub_skew hg U P a, hA.2 (blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P),
      blockVecDot_blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A P]
  exact (eq_coarseBlockMatrix_of_isCoarseBlockMatrix hnew).symm

/-- **The recentred coarse block of an aligned cell is the shear congruence of the cell's coarse
block, minus sign.**  This is the identity the recent-difference energy map consumes: the
Chapter-2 block of the recentred coefficient equals `Gᵀ 𝐀 G` for the cell's set-level coarse
block. -/
theorem isCoarseBlockMatrix_respCoeffMinus [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (aU : Book.Ch02.CoeffOn (adaptedDomainAt q hq k w))
    (haU : aU.toCoeffField = respCoeffMinus F a) :
    Book.Ch02.coarseBlockMatrix (adaptedDomainAt q hq k w) aU
      = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q k w) a) := by
  rw [coarseBlockMatrix_domain_eq_set aU, adaptedDomainAt_carrier, haU]
  exact coarseBlockMatrix_sub_skew_of_isCoarseBlockMatrix (respg_isSkew F)
    (isCoarseBlockMatrix_adaptedCellAtCenter q hq k w a)

/-- **The recentred coarse block of an aligned cell is the composed congruence of the cell's
coarse block, plus sign.**  The recentred adjoint field is `respCoeffPlus F a = aᵀ + g`, so the
shear identity applies at the adjoint field with skew `-g`, and the adjoint block is the flux
sign flip `D` of the primal block.  This matches the `hcoarse` shape of the adjoint energy map. -/
theorem isCoarseBlockMatrix_respCoeffPlus [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (aU : Book.Ch02.CoeffOn (adaptedDomainAt q hq k w))
    (haU : aU.toCoeffField = respCoeffPlus F a) :
    Book.Ch02.coarseBlockMatrix (adaptedDomainAt q hq k w) aU
      = blockCongr (blockD d)
          (blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q k w) a)) := by
  rw [coarseBlockMatrix_domain_eq_set aU, adaptedDomainAt_carrier, haU]
  have hA_a : IsCoarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d)
      (coarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d)) :=
    isCoarseBlockMatrix_adaptedCellAtCenter q hq k w a
  have hex : ∃ A : BlockMat d,
      IsCoarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d) A :=
    ⟨_, hA_a⟩
  have hA_b : IsCoarseBlockMatrix (adaptedCellAtCenter q k w)
      (adjointCoeffField (⇑a.1 : CoeffField d))
      (coarseBlockMatrix (adaptedCellAtCenter q k w) (adjointCoeffField (⇑a.1 : CoeffField d))) := by
    have h := IsCoarseBlockMatrix.adjointCoeffField_symm hA_a
    rw [← blockCongr_blockD] at h
    rw [coarseBlockMatrix_adjointCoeffField_of_exists hex, ← blockCongr_blockD]
    exact h
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    show (-(respg F) : Mat d)ᵀ = -(-(respg F))
    rw [Matrix.transpose_neg]
    exact congrArg Neg.neg (respg_isSkew F)
  have hplus : respCoeffPlus F a
      = fun x => adjointCoeffField (⇑a.1 : CoeffField d) x - (-(respg F)) := by
    funext x
    simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
  rw [hplus, coarseBlockMatrix_sub_skew_of_isCoarseBlockMatrix (U := adaptedCellAtCenter q k w)
      (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew hA_b,
    coarseBlockMatrix_adjointCoeffField_of_exists hex, ← blockCongr_blockD,
    blockCongr_blockCongr, blockD_mul_shear_neg, ← blockCongr_blockCongr]
  rfl

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The analytic per-scale input, reduced to its two analytic facts

## What this file does and does not do

`recentHead_actual_le` (`DiagonalWeakNormAssembly.lean`) has exactly ONE
remaining hypothesis, its `hscale`: the analytic per-scale bound on the average-defect family.
That bound is `diagonalWeak_recent_average_bound`.

Reading the proof of that theorem, its content splits cleanly in two:

* an **algebraic spine** — per-cell bound, average, Cauchy–Schwarz-free `√` algebra — which is
  pure real arithmetic over a `Finset`; and
* two **analytic inputs**, `metricBlockNormSq_recent_difference_le` and
  `diagonalWeak_recent_difference_energy_le`, which are PDE facts about the doubled response
  space.

**This file proves the spine and states the two analytic inputs as explicit hypotheses in
this tree's own language.**  It does NOT prove those two inputs; their root
`energy_map_metric_le` rests on
`doubledResponseValue_le` / `doubledResponseValue_zero_left_eq` and
on the reflection-order layer (`blockSharp`, 444 lines plus its
`VariationalIdentities.lean` base of 323), none of which exists in this tree OR in the
`CoarseGraining` dependency.

What is gained is nonetheless the substance of the bound: after this file, the per-scale bound
is reduced to TWO named inequalities, stated on this tree's carriers, whose
conjunction discharges `hscale` mechanically.

Nothing is imported from an external development and no file is copied; the spine is stated on
this tree's inline `√(|Z|⁻¹ ∑ ⟪·,·⟫)` carrier, which is
what `weakCellSum`, `h6a_besovSeminorm_head_tail_le` and `hscale` all spell.
-/

open HCPolySupport.HighContrast (CoeffSpace normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The algebraic spine of the per-scale input**, on an arbitrary index `Finset`.

This is `diagonalWeak_recent_average_bound`
with its two analytic inputs abstracted into the hypotheses `hcell` and `henergy`, and with
`blockAvsumL2` unfolded to this tree's inline `√(|Z|⁻¹ ∑ ⟪·,·⟫)`.

`hcell` is the per-cell bound assembled from `metricBlockNormSq_recent_difference_le`
together with the all-scale-maximum bound on the response size; `henergy` is
`diagonalWeak_recent_difference_energy_le`.  Everything after them is real arithmetic —
`Finset.sum_le_sum`, a nonnegative rescaling, and `√(c²x) = c√x`. -/
theorem scaleInput_spine_le {iota : Type*} (Z : Finset iota) (R : BlockMat d)
    (Δ : iota → BlockVec d) (G : iota → ℝ) (K B L D : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hcell : ∀ w ∈ Z,
      blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w)) ≤ (K * B) ^ 2 * G w)
    (henergy : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, G w ≤ 2 * L ^ 2 * D) :
    Real.sqrt ((Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w)))
      ≤ Real.sqrt 2 * K * B * L * Real.sqrt D := by
  have hcard : (0 : ℝ) ≤ (Z.card : ℝ)⁻¹ := by positivity
  -- the averaged per-cell bound
  have hsum : (Z.card : ℝ)⁻¹ *
      ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w))
      ≤ (K * B) ^ 2 * (2 * L ^ 2 * D) := by
    have hstep : ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w))
        ≤ ∑ w ∈ Z, (K * B) ^ 2 * G w := Finset.sum_le_sum hcell
    calc
      (Z.card : ℝ)⁻¹ *
          ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w))
          ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (K * B) ^ 2 * G w :=
        mul_le_mul_of_nonneg_left hstep hcard
      _ = (K * B) ^ 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, G w) := by
        rw [← Finset.mul_sum]; ring
      _ ≤ (K * B) ^ 2 * (2 * L ^ 2 * D) :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg (K * B))
  -- the right-hand side is the square root of that bound
  have hC0 : 0 ≤ Real.sqrt 2 * K * B * L * Real.sqrt D := by positivity
  have hradicand : (K * B) ^ 2 * (2 * L ^ 2 * D)
      = (Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2 := by
    have hroot2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hrootD : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
    calc
      (K * B) ^ 2 * (2 * L ^ 2 * D)
          = Real.sqrt 2 ^ 2 * (K * B * L) ^ 2 * Real.sqrt D ^ 2 := by
        rw [hroot2, hrootD]; ring
      _ = (Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2 := by ring
  calc
    Real.sqrt ((Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w)))
        ≤ Real.sqrt ((K * B) ^ 2 * (2 * L ^ 2 * D)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt ((Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2) := by rw [hradicand]
    _ = Real.sqrt 2 * K * B * L * Real.sqrt D := Real.sqrt_sq hC0

/-! ## The spine at the exact shape of `hscale`. -/

omit [NeZero d] in
/-- **The per-scale input, reduced to its two analytic inputs.**  This is `scaleInput_spine_le`
instantiated at exactly the shape of the remaining hypothesis `hscale`
(`recentHead_actual_le`, `DiagonalWeakNormAssembly.lean`): the index set is
`triadicIndexBox d n`, the root is `blockSqrt (respM0 F)`, and the four scalars are the printed
ones —

* `K = √(blockSpecBound (normalizedBlock Ê⁻ M₀))`, the `diagonalWeakMetricFactor m E`;
* `B = 1 + √(respAllScaleMax) · 3^{ρn/2}`, the all-scale-maximum factor;
* `L = √(respLsqMinus)`, the `diagonalWeakLoadMinus E p r`;
* `D = ‖weakAverageDefect …‖`, the `blockSize (diagonalWeakAverageDefect …) (blockIdentity d)`.

The field family `Y` is left abstract: `recentHead_actual_le` instantiates it at
`Y w = fun x => optimizerField b u x - optimizerField b (V n w) x`, which matches definitionally.

**The two hypotheses are precisely the two analytic inputs**, in this tree's language:

* `hcell` is `metricBlockNormSq_recent_difference_le`
  composed with the response-size bound `blockSize (adaptedResponse …) E ≤ B²`, which is
  derived from `sqrt_blockSize_adaptedResponse_le_of_maximum_finite`;
* `henergy` is `diagonalWeak_recent_difference_energy_le`.

Neither is proved in this tree.  What this theorem establishes is that NOTHING ELSE is needed:
given those two, `hscale` follows mechanically, and with it the entire first printed
summand of `diagonalWeakNorm_primal_le`. -/
theorem scaleInput_of_analytic
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (a : CoeffSpace d) (n : ℕ)
    (Y : (Fin d → ℤ) → Vec d → BlockVec d) (G : (Fin d → ℤ) → ℝ)
    (hLsq : 0 ≤ respLsqMinus P jStar F t e)
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 * G w)
    (henergy : ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
      ≤ 2 * respLsqMinus P jStar F t e
          * ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
              (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqMinus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatMinus P jStar F t) (respCoeffMinus F a))‖ := by
  have hB : (0 : ℝ) ≤ 1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
    add_nonneg zero_le_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hLsq' : Real.sqrt (respLsqMinus P jStar F t e) ^ 2 = respLsqMinus P jStar F t e :=
    Real.sq_sqrt hLsq
  refine scaleInput_spine_le (triadicIndexBox d n) (blockSqrt (respM0 F))
    (fun w => cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)) G
    _ _ _ _ (Real.sqrt_nonneg _) hB (Real.sqrt_nonneg _) (norm_nonneg _) hcell ?_
  rw [hLsq']
  exact henergy

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The per-cell hypothesis of the per-scale input, from its two inputs

The per-scale input `scaleInput_of_analytic` consumes a per-cell hypothesis bounding the
metric square of a cell average by a fixed printed constant times a weight `G`.  The energy-map
layer delivers that bound with a different constant: a product `k * e` of two Loewner sizes.
This file is the bookkeeping that turns the second shape into the first, given the numerical
comparison between the two constants.

Both statements are monotonicity of multiplication by a nonnegative weight.  No matrix identity
is used beyond the nonnegativity of the quantities involved, and the first statement is the
generic core of the second.
-/

open HCPolySupport.HighContrast (CoeffSpace normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

/-- Monotonicity of a per-cell bound in its constant.  If `V w ≤ c₁ * G w` for every `w` in a
finite index set and the weight `G` is nonnegative there, then the same bound holds with any
larger constant `c₂`.  The nonnegativity of `c₁` is carried because the constant in the analytic
per-scale input is a product of Loewner sizes, but the monotonicity step itself needs only
`c₁ ≤ c₂` and `0 ≤ G w`. -/
theorem perCellHypothesis_of_constants {iota : Type*} (Z : Finset iota) (V : iota → ℝ) (G : iota → ℝ)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hG : ∀ w ∈ Z, 0 ≤ G w) (hcc : c₁ ≤ c₂)
    (hmetric : ∀ w ∈ Z, V w ≤ c₁ * G w) :
    ∀ w ∈ Z, V w ≤ c₂ * G w := by
  have _ := hc₁
  intro w hw
  exact le_trans (hmetric w hw) (mul_le_mul_of_nonneg_right hcc (hG w hw))

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The per-cell hypothesis of the per-scale input, obtained from the energy-map bound.  The
cell-average metric square is bounded by `(k * e) * G w` for the two Loewner sizes `k` and `e`;
the comparison `hsize` turns the product into the printed square
`(√K₀ · (1 + √M · 3^{ρn/2}))²`, and the nonnegative weight yields the conclusion.  The index set
is `triadicIndexBox d n`, the root is `blockSqrt (respM0 F)`, and the two constants and the
response sample are those of the weak-norm estimate (`e.response.weak.estimate`). -/
theorem perCellHypothesis_of_metric_and_size
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d)
    (n : ℕ) (Y : (Fin d → ℤ) → Vec d → BlockVec d) (G : (Fin d → ℤ) → ℝ) (k e : ℝ)
    (hk : 0 ≤ k) (he : 0 ≤ e)
    (hG : ∀ w ∈ triadicIndexBox d n, 0 ≤ G w)
    (hsize : k * e ≤
      (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2)
    (hmetric : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
        ≤ (k * e) * G w) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 * G w := by
  exact perCellHypothesis_of_constants (triadicIndexBox d n)
    (fun w => blockVecDot
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w))))
    G (k * e)
    ((Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2)
    (mul_nonneg hk he) hG hsize hmetric

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The recent-difference energy map on an aligned cell

This composes the recent-difference energy map on the doubled response space with the per-cell
bookkeeping of the weak-norm estimate.  The response-size input is taken at the square of the
printed geometric factor, and the metric factor is the operator norm of the normalized reference
block, which on positive definite carriers is the printed spectral bound.

The remaining input is the identification of the Chapter-2 coarse block with the shear
congruence of the cell's coarse block.  The two coarse-block carriers used here — the Chapter-2
`coarseBlockMatrix` on a `Domain` and the set-level `coarseBlockMatrix` on the cell — are not
identified by any declaration in this module's import closure, so that identification is carried
as an explicit hypothesis.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The recent-difference energy map on an aligned cell, with the response-size factor supplied
through the shear congruence.  For every index `w` in the triadic box, the metric square of the
cell average of the doubled difference of two optimizers is bounded by the printed geometric
square times the actual difference energy on that cell.

The hypothesis `hcoarse` identifies the Chapter-2 coarse block of the recentred coefficient with
the shear congruence of the cell's coarse block; it is the shape the shear identity produces and
the one input this module cannot discharge from its own imports. -/
theorem recentEnergyMap_port
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (a : CoeffSpace d) (n : ℕ)
    (aU : (w : Fin d → ℤ) →
      Book.Ch02.CoeffOn (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w))
    (u v : (w : Fin d → ℤ) →
      Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
    (hEll : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hcoarse : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) =
        blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a))
    (hG : ∀ w ∈ triadicIndexBox d n, 0 ≤ Book.Ch02.average
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
      (fun x => blockVecDot
        (optimizerField (aU w).toCoeffField (u w) x -
          optimizerField (aU w).toCoeffField (v w) x)
        (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
          (optimizerField (aU w).toCoeffField (u w) x -
            optimizerField (aU w).toCoeffField (v w) x)))) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => optimizerField (aU w).toCoeffField (u w) x -
              optimizerField (aU w).toCoeffField (v w) x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => optimizerField (aU w).toCoeffField (u w) x -
              optimizerField (aU w).toCoeffField (v w) x)))
      ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2
        * Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
            (fun x => blockVecDot
              (optimizerField (aU w).toCoeffField (u w) x -
                optimizerField (aU w).toCoeffField (v w) x)
              (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
                (optimizerField (aU w).toCoeffField (u w) x -
                  optimizerField (aU w).toCoeffField (v w) x))) := by
  have hNpd : (toFullBlockMat
      (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))).PosDef :=
    Annealed.normalizedBlock_posDef _ _ hEhat hM0
  have hnorm_pos : 0 < ‖toFullBlockMat
      (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ :=
    norm_pos_iff.mpr hNpd.isUnit.ne_zero
  have hBpos : 0 < 1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
      * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hsize : ‖toFullBlockMat
        (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2
      ≤ (Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 := by
    rw [blockSpecBound_eq_norm_of_posSemidef _ hNpd.posSemidef, mul_pow,
      Real.sq_sqrt (norm_nonneg _)]
  refine perCellHypothesis_of_metric_and_size (P := P) (γ := γ) (jStar := jStar) (F := F) (t := t)
    (a := a) (n := n)
    (Y := fun w x => optimizerField (aU w).toCoeffField (u w) x -
      optimizerField (aU w).toCoeffField (v w) x)
    (G := fun w => Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
      (fun x => blockVecDot
        (optimizerField (aU w).toCoeffField (u w) x -
          optimizerField (aU w).toCoeffField (v w) x)
        (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
          (optimizerField (aU w).toCoeffField (u w) x -
            optimizerField (aU w).toCoeffField (v w) x))))
    (k := ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖)
    (e := (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
        * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2)
    (hk := hnorm_pos.le) (he := (pow_pos hBpos 2).le) (hG := hG) (hsize := hsize) (hmetric := ?_)
  intro w hw
  have hAE : toFullBlockMat
        (Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w))
      ≤ (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
          * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2
        • toFullBlockMat (respEhatMinus P jStar F t) := by
    rw [hcoarse w hw]
    exact coarseBlock_congr_le_sq_smul_respEhatMinus P γ jStar F t a n hw hbdd hEmean
  have hEM : toFullBlockMat (respEhatMinus P jStar F t)
      ≤ ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖
        • toFullBlockMat (respM0 F) :=
    le_smul_of_normalizedBlock hEhat.posSemidef hM0
  have hmain := recent_difference_metric_le
    (U := adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (a := aU w)
    (hEll w) (u w) (v w) hm hEhat hnorm_pos (pow_pos hBpos 2) hEM hAE
  simpa only using! hmain

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The recent-difference energy map, adjoint sign, as a split proof

The energy map of `CoarseBlockPerCellInput` is stated for the recentred sample
`respEhatMinus`.  The `+` copy of the cell-average estimate needs the adjoint twin, whose sample
is `respEhatPlus = blockAdjoint (respEhatMinus …)`.  Because the adjoint adds one congruence by
the flux flip `D`, the response-size input is no longer a bound for the shear factor `respG F`
alone: it is the composed factor `D ∘ respG F`.  This file splits the port in two so that the
large block terms are elaborated once each: the per-cell step carries the two Loewner constants
abstract, and the second theorem feeds it the adjoint size inputs.

The remaining input of the second theorem is the identification of the Chapter-2 coarse block of
the recentred adjoint field with the composed congruence of the cell's coarse block; the two
coarse-block carriers used here — the Chapter-2 `coarseBlockMatrix` on a `Domain` and the set-level
`coarseBlock` on the cell — are not identified by any declaration in this module's import closure,
so that identification is carried as an explicit hypothesis, exactly as for the minus sign.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The per-cell step of the recent-difference energy map for the adjoint sample, with the two
Loewner constants abstract.  This is `recent_difference_metric_le`
(`ResponseFieldSize.lean`) instantiated at an aligned child cell and the doubled
optimizer difference: the reference sample is `respEhatPlus`, the root is `blockSqrt (respM0 F)`,
and arbitrary positive `k`, `e` are supplied through the two Loewner hypotheses `hEM`, `hAE`. -/
theorem recentEnergyMap_cell_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (n : ℕ)
    (aU : (w : Fin d → ℤ) →
      Book.Ch02.CoeffOn (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w))
    (u v : (w : Fin d → ℤ) →
      Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
    (hEll : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (k e : ℝ) (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat (respEhatPlus P jStar F t) ≤ k • toFullBlockMat (respM0 F))
    (hAE : ∀ w ∈ triadicIndexBox d n,
      toFullBlockMat (Book.Ch02.coarseBlockMatrix
          (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
        ≤ e • toFullBlockMat (respEhatPlus P jStar F t)) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (fun x => optimizerField (aU w).toCoeffField (u w) x -
                optimizerField (aU w).toCoeffField (v w) x)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (fun x => optimizerField (aU w).toCoeffField (u w) x -
                optimizerField (aU w).toCoeffField (v w) x)))
        ≤ (k * e) * Book.Ch02.average
            (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
            (fun x => blockVecDot
              (optimizerField (aU w).toCoeffField (u w) x -
                optimizerField (aU w).toCoeffField (v w) x)
              (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
                (optimizerField (aU w).toCoeffField (u w) x -
                  optimizerField (aU w).toCoeffField (v w) x))) := by
  intro w hw
  simpa only using! recent_difference_metric_le
    (U := adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
    (a := aU w) (hEll w) (u w) (v w) hm (hE := hEhat) hk he hEM (hAE w hw)

/-- The recent-difference energy map on an aligned cell for the adjoint sample.  This is the
adjoint twin of `recentEnergyMap_port` (`CoarseBlockPerCellInput.lean`): the
sample is `respEhatPlus`, and the response-size input `hcoarse` identifies the Chapter-2 coarse
block of the recentred field with the composed congruence `D ∘ respG F`, the factor the adjoint
carries.  The per-cell step is `recentEnergyMap_cell_plus` above. -/
theorem recentEnergyMap_port_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (a : CoeffSpace d) (n : ℕ)
    (aU : (w : Fin d → ℤ) →
      Book.Ch02.CoeffOn (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w))
    (u v : (w : Fin d → ℤ) →
      Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
    (hEll : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hcoarse : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) =
        blockCongr (blockD d)
          (blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)))
    (hG : ∀ w ∈ triadicIndexBox d n, 0 ≤ Book.Ch02.average
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
      (fun x => blockVecDot
        (optimizerField (aU w).toCoeffField (u w) x -
          optimizerField (aU w).toCoeffField (v w) x)
        (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
          (optimizerField (aU w).toCoeffField (u w) x -
            optimizerField (aU w).toCoeffField (v w) x)))) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => optimizerField (aU w).toCoeffField (u w) x -
              optimizerField (aU w).toCoeffField (v w) x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => optimizerField (aU w).toCoeffField (u w) x -
              optimizerField (aU w).toCoeffField (v w) x)))
      ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2
        * Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
            (fun x => blockVecDot
              (optimizerField (aU w).toCoeffField (u w) x -
                optimizerField (aU w).toCoeffField (v w) x)
              (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
                (optimizerField (aU w).toCoeffField (u w) x -
                  optimizerField (aU w).toCoeffField (v w) x))) := by
  have hNpd : (toFullBlockMat
      (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))).PosDef :=
    Annealed.normalizedBlock_posDef _ _ hEhat hM0
  have hnorm_pos : 0 < ‖toFullBlockMat
      (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ :=
    norm_pos_iff.mpr hNpd.isUnit.ne_zero
  have hBpos : 0 < 1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
      * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hsize : ‖toFullBlockMat
        (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2
      ≤ (Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 := by
    rw [blockSpecBound_eq_norm_of_posSemidef _ hNpd.posSemidef, mul_pow,
      Real.sq_sqrt (norm_nonneg _)]
  refine perCellHypothesis_of_constants (triadicIndexBox d n)
    (fun w => blockVecDot
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (fun x => optimizerField (aU w).toCoeffField (u w) x -
            optimizerField (aU w).toCoeffField (v w) x)))
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (fun x => optimizerField (aU w).toCoeffField (u w) x -
            optimizerField (aU w).toCoeffField (v w) x))))
    (fun w => Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
      (fun x => blockVecDot
        (optimizerField (aU w).toCoeffField (u w) x -
          optimizerField (aU w).toCoeffField (v w) x)
        (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
          (optimizerField (aU w).toCoeffField (u w) x -
            optimizerField (aU w).toCoeffField (v w) x))))
    (‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
      * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
          * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2)
    ((Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2)
    (mul_nonneg hnorm_pos.le (pow_pos hBpos 2).le) hG hsize ?_
  exact recentEnergyMap_cell_plus P jStar F t hgrid n aU u v hEll hm hEhat
    ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
    ((1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
        * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2)
    hnorm_pos (pow_pos hBpos 2)
    (le_smul_of_normalizedBlock hEhat.posSemidef hM0)
    (fun w hw => by
      rw [hcoarse w hw]
      exact blockCongr_le_smul (blockD d)
        (coarseBlock_congr_le_sq_smul_respEhatMinus P γ jStar F t a n hw hbdd hEmean))

end

end HCPolySupport.HighContrast.Multiscale
end
