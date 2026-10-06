/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Setup.Contrast
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import LeanPool.HighContrastHomogenization.Setup.Attainment
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.SpectralBound
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.DriftAdvance

/-!
# High-contrast homogenization: Entry.Geometry.CanonicalMetricBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positivity of the canonical metric

This proves positive definiteness of the closed printed definition of
`explicitCanonicalMetric`; it does not introduce a geometric-mean characterization or
the metric-loss estimate, which belong to the global selection.  The positivity of the
canonical metric, and its specialization to the rounded adapted means, underlies the
projective-distance geometry serving `p.global.selection` and `p.scale.selection`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCell adaptedMean matSqrt posDef_lowerRight)
namespace HCPolySupport.HighContrast.Geometry

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

noncomputable section

private theorem toFullBlockMat_blockSwap_conjTranspose (d : ℕ) :
    (toFullBlockMat (blockSwap d))ᴴ = toFullBlockMat (blockSwap d) := by
  ext α β
  cases α <;> cases β <;>
    simp [blockSwap, Book.Ch02.blockR, toFullBlockMat, Matrix.conjTranspose,
      Matrix.one_apply, eq_comm]

private theorem toFullBlockMat_blockSwap_mul_self (d : ℕ) :
    toFullBlockMat (blockSwap d) * toFullBlockMat (blockSwap d) = 1 := by
  ext α β
  cases α <;> cases β <;>
    simp [blockSwap, Book.Ch02.blockR, toFullBlockMat, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Finset.sum_ite_eq, eq_comm]

private theorem blockSwap_mulVec_injective (d : ℕ) :
    Function.Injective (toFullBlockMat (blockSwap d)).mulVec := by
  intro x y hxy
  have h := congrArg (fun z => toFullBlockMat (blockSwap d) *ᵥ z) hxy
  simpa [mulVec_mulVec, toFullBlockMat_blockSwap_mul_self d] using h

private theorem matSqrt_posDef_full {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    (matSqrt M).PosDef := by
  rw [matSqrt_eq_cfc_sqrt hM.posSemidef]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (Matrix.isStrictlyPositive_iff_posDef.mpr hM).sqrt

private theorem posDef_conj_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (B * A * B).PosDef := by
  have hBinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hB.isUnit
  have h := hA.conjTranspose_mul_mul_same (B := B) hBinj
  have hBt : Bᵀ = B := by
    ext i j
    have hij := congrFun (congrFun hB.isHermitian.eq j) i
    simpa [Matrix.conjTranspose, starRingEnd_apply] using hij.symm
  simpa [Matrix.conjTranspose, hBt] using! h

private theorem blockPosDef_of_full_posDef {M : FullBlockMat d}
    (hM : M.PosDef) : Book.Ch02.BlockPosDef (ofFullBlockMat M) := by
  intro X hX
  have hfull_ne : toFullBlockVec X ≠ 0 := by
    intro hfull
    apply hX
    rw [← ofFullBlockVec_toFullBlockVec X, hfull]
    rfl
  have hq := hM.dotProduct_mulVec_pos hfull_ne
  rw [← dotProduct_toFullBlockVec X (blockMatVecMul (ofFullBlockMat M) X),
    toFullBlockVec_blockMatVecMul, toFullBlockMat_ofFullBlockMat]
  simpa only [star_trivial] using hq

/-- The reflected inverse `𝐑F⁻¹𝐑` is positive definite for a positive block `F`. -/
theorem swapConj_inv_posDef [NeZero d] {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : Book.Ch02.BlockPosDef F) :
    (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
      toFullBlockMat (blockSwap d)).PosDef := by
  let A : FullBlockMat d := toFullBlockMat F
  let R : FullBlockMat d := toFullBlockMat (blockSwap d)
  have hA : A.PosDef := by
    simpa [A] using posDef_toFullBlockMat hsymm hpos
  have h := hA.inv.conjTranspose_mul_mul_same (B := R) (by
    simpa [R] using blockSwap_mulVec_injective d)
  have hRt : Rᵀ = R := by
    simpa [R, Matrix.conjTranspose] using! toFullBlockMat_blockSwap_conjTranspose d
  simpa [A, R, Matrix.conjTranspose, hRt, mul_assoc] using! h

/-- The inner square-root argument in `explicitCanonicalMetric` is positive definite. -/
theorem explicitCanonicalMetric_inner_posDef [NeZero d] {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : Book.Ch02.BlockPosDef F) :
    (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) *
      (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) *
      matSqrt ((toFullBlockMat F)⁻¹)).PosDef := by
  let A : FullBlockMat d := toFullBlockMat F
  let R : FullBlockMat d := toFullBlockMat (blockSwap d)
  let S : FullBlockMat d := matSqrt A⁻¹
  have hA : A.PosDef := by
    simpa [A] using posDef_toFullBlockMat hsymm hpos
  have hRAR : (R * A⁻¹ * R).PosDef := by
    simpa [A, R] using swapConj_inv_posDef (d := d) hsymm hpos
  have hS : S.PosDef := by
    simpa [S, A] using HCPolySupport.HighContrast.Multiscale.matSqrt_inv_posDef_full hA
  have h := posDef_conj_same hRAR hS
  simpa [A, R, S, mul_assoc] using h

/-- The middle square root in `explicitCanonicalMetric` is positive definite. -/
theorem explicitCanonicalMetric_middleSqrt_posDef [NeZero d] {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : Book.Ch02.BlockPosDef F) :
    (matSqrt
      (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) *
        (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) *
        matSqrt ((toFullBlockMat F)⁻¹))).PosDef :=
  matSqrt_posDef_full (explicitCanonicalMetric_inner_posDef hsymm hpos)

/-- The full matrix before taking the lower-right block in `explicitCanonicalMetric` is positive
definite. -/
theorem explicitCanonicalMetric_outer_posDef [NeZero d] {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : Book.Ch02.BlockPosDef F) :
    (matSqrt (toFullBlockMat F) *
      matSqrt
        (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) *
          (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) *
          matSqrt ((toFullBlockMat F)⁻¹)) *
      matSqrt (toFullBlockMat F)).PosDef := by
  let A : FullBlockMat d := toFullBlockMat F
  let T : FullBlockMat d := matSqrt A
  let M : FullBlockMat d :=
    matSqrt
      (matSqrt A⁻¹ * toFullBlockMat (blockSwap d) * A⁻¹ *
        toFullBlockMat (blockSwap d) * matSqrt A⁻¹)
  have hA : A.PosDef := by
    simpa [A] using posDef_toFullBlockMat hsymm hpos
  have hT : T.PosDef := by
    simpa [T, A] using matSqrt_posDef_full hA
  have hM : M.PosDef := by
    simpa [M, A] using explicitCanonicalMetric_middleSqrt_posDef (d := d) hsymm hpos
  have h := posDef_conj_same hM hT
  simpa [A, T, M, mul_assoc] using h

/-- The lower-right block before the final inverse in `explicitCanonicalMetric` is positive
definite. -/
theorem explicitCanonicalMetric_lowerRight_posDef [NeZero d] {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : Book.Ch02.BlockPosDef F) :
    (ofFullBlockMat
      (matSqrt (toFullBlockMat F) *
        matSqrt
          (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) *
            (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) *
            matSqrt ((toFullBlockMat F)⁻¹)) *
        matSqrt (toFullBlockMat F))).lowerRight.PosDef := by
  let M : FullBlockMat d :=
    matSqrt (toFullBlockMat F) *
      matSqrt
        (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) *
          (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) *
          matSqrt ((toFullBlockMat F)⁻¹)) *
      matSqrt (toFullBlockMat F)
  have hM : M.PosDef := by
    simpa [M] using explicitCanonicalMetric_outer_posDef (d := d) hsymm hpos
  have hblock : Book.Ch02.BlockPosDef (ofFullBlockMat M) :=
    blockPosDef_of_full_posDef hM
  have hsymmBlock : IsSymmetricBlockMat (ofFullBlockMat M) :=
    (HCPolySupport.HighContrast.Analysis.toFullBlockMat_isHermitian_iff (ofFullBlockMat M)).1
      (by simpa using hM.isHermitian)
  simpa [M] using posDef_lowerRight hsymmBlock hblock

/-- **O4.** The closed printed canonical metric is positive definite on symmetric
positive doubled blocks. -/
theorem explicitCanonicalMetric_posDef [NeZero d] {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : Book.Ch02.BlockPosDef F) :
    (explicitCanonicalMetric F).PosDef := by
  unfold explicitCanonicalMetric
  exact (explicitCanonicalMetric_lowerRight_posDef hsymm hpos).inv

/-! ## The unconditional dichotomy

Everything above carries the printed hypotheses `hsymm`/`hpos`.  The block below carries
none.  `matSqrt` takes the junk value `1` -- not `0` -- off the positive semidefinite data
(`HCPoly/Setup/BlockAlgebra.lean`, `matSqrt`), so every factor of the closed expression defining
`explicitCanonicalMetric` is positive semidefinite whatever `F` is; a congruence, a principal
submatrix and Mathlib's `Matrix.inv` (which is `0` off the units) all preserve that.  Hence
`explicitCanonicalMetric F` is positive semidefinite for **every** `F`, so it is either positive
definite or singular, and in the singular case the rounded grid built from it collapses to
the zero matrix.  That dichotomy is what lets the response cutoff kernel dispose of the
degenerate branch without adding a hypothesis to its statement. -/

/-- `matSqrt` is positive semidefinite on **every** input: on positive semidefinite data it is
the canonical square root, and off that data it is the junk value `1`.  Stated in the
project's root namespace, beside `matSqrt` itself. -/
theorem _root_.HCPolySupport.HighContrast.matSqrt_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : (matSqrt M).PosSemidef := by
  by_cases h : ∃ B : Matrix ι ι ℝ, B.PosSemidef ∧ B * B = M
  · rw [matSqrt, dite_eq_left h]
    exact h.choose_spec.1
  · rw [matSqrt, dite_eq_right h]
    exact Matrix.PosSemidef.one

/-- The congruence `B A B` of a positive semidefinite `A` by a positive semidefinite `B`;
`B` is then Hermitian, so this is `Bᴴ A B`.  The positive definite companion is
`posDef_conj_same` above. -/
private theorem posSemidef_conj_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (B * A * B).PosSemidef := by
  have h := hA.conjTranspose_mul_mul_same B
  rwa [hB.isHermitian.eq] at h

/-- The lower-right block of a doubled matrix is its principal submatrix along `Sum.inr`. -/
private theorem lowerRight_ofFullBlockMat (M : FullBlockMat d) :
    (ofFullBlockMat M).lowerRight = M.submatrix Sum.inr Sum.inr := rfl

/-- **The positive semidefinite link.**  The canonical metric is positive semidefinite for
every doubled block, with no symmetry and no positivity hypothesis: the junk values of
`matSqrt` and of `Matrix.inv` are themselves positive semidefinite. -/
theorem explicitCanonicalMetric_posSemidef (F : BlockMat d) : (explicitCanonicalMetric F).PosSemidef := by
  have hM :=
    posSemidef_conj_same
      (matSqrt_posSemidef
        (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) *
          (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) *
          matSqrt ((toFullBlockMat F)⁻¹)))
      (matSqrt_posSemidef (toFullBlockMat F))
  rw [explicitCanonicalMetric]
  refine Matrix.PosSemidef.inv ?_
  rw [lowerRight_ofFullBlockMat]
  exact hM.submatrix Sum.inr

/-- A positive semidefinite matrix is positive definite exactly when it is a unit, so the
canonical metric is either positive definite or has vanishing inverse.  No hypothesis. -/
theorem explicitCanonicalMetric_posDef_or_inv_eq_zero (F : BlockMat d) :
    (explicitCanonicalMetric F).PosDef ∨ (explicitCanonicalMetric F)⁻¹ = 0 := by
  by_cases h : IsUnit (explicitCanonicalMetric F)
  · exact Or.inl ((explicitCanonicalMetric_posSemidef F).posDef_iff_isUnit.mpr h)
  · exact Or.inr (Matrix.nonsing_inv_apply_not_isUnit _ fun hd =>
      h ((Matrix.isUnit_iff_isUnit_det _).mpr hd))

/-- Every entry of `𝒬(𝔪)` carries the factor `|𝔪⁻¹|^{1/2}`, so the rounded grid of a matrix
with vanishing inverse is the zero matrix. -/
theorem explicitRoundedGrid_eq_zero_of_inv_eq_zero (jStar : ℕ) {m : Mat d} (hm : m⁻¹ = 0) :
    explicitRoundedGrid jStar m = 0 := by
  ext a b
  simp [explicitRoundedGrid, hm]

/-- The determinant of the rounded grid of a matrix with vanishing inverse is zero. -/
theorem det_roundedGrid_eq_zero_of_inv_eq_zero [NeZero d] (jStar : ℕ) {m : Mat d}
    (hm : m⁻¹ = 0) : (explicitRoundedGrid jStar m).det = 0 := by
  rw [explicitRoundedGrid_eq_zero_of_inv_eq_zero jStar hm]
  exact Matrix.det_zero

/-- **The metric dichotomy.**  For every doubled block `F` -- no symmetry, no positivity --
either the canonical metric `m(F)` is positive definite, or the rounded grid `𝒬(m(F))` built
from it is singular. -/
theorem explicitCanonicalMetric_posDef_or_det_roundedGrid_eq_zero [NeZero d] (jStar : ℕ)
    (F : BlockMat d) :
    (explicitCanonicalMetric F).PosDef ∨ (explicitRoundedGrid jStar (explicitCanonicalMetric F)).det = 0 :=
  (explicitCanonicalMetric_posDef_or_inv_eq_zero F).imp id (det_roundedGrid_eq_zero_of_inv_eq_zero jStar)

/-- O4 at the rounded adapted means used by scale selection. -/
theorem explicitCanonicalMetric_adaptedMean_posDef (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    (explicitCanonicalMetric (adaptedMean P (explicitRoundedGrid jStar m) j)).PosDef := by
  let : NeZero d := ⟨by omega⟩
  have hsymm : IsSymmetricBlockMat (adaptedMean P (explicitRoundedGrid jStar m) j) := by
    simpa [adaptedMean] using
      isSymmetricBlockMat_annealedBlock P
        (adaptedCell (explicitRoundedGrid jStar m) j)
  have hfull :=
    HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag
      jStar hjStar m hm j
  have hblock : Book.Ch02.BlockPosDef (adaptedMean P (explicitRoundedGrid jStar m) j) := by
    have hconverted :=
      blockPosDef_of_full_posDef (d := d) (M := toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) j))
        hfull
    simpa using hconverted
  exact explicitCanonicalMetric_posDef hsymm hblock

end

end HCPolySupport.HighContrast.Geometry
