/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Matrices
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Representatives
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.EllipticBounds
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuOperator.HilbertOperator
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Integrals
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-!
# AveragedBlock

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the volume-averaged doubled coefficient matrix

The chain `e.CG.bounds.2` in ABK26,

`(⨍_U bfA⁻¹(x) dx)⁻¹ ≤ bfA_*(U) ≤ bfA(U) ≤ ⨍_U bfA(x) dx`,

compares the coarse block matrices with volume averages of the pointwise
doubled coefficient field.  CoarseGraining names the pointwise field
`Homogenization.Book.Ch02.blockMatrixField` and its pointwise inverse
`Homogenization.Book.Ch02.blockMatrixInverseField`, but has no averaged block
matrix; this file introduces them, following the `averageMat` conventions of
`Homogenization/Book/Ch02/Matrices.lean`.

The analytic content of the file is the exchange of the volume average with the
doubled quadratic form,

`⨍_U X ⬝ bfA(x) X dx = X ⬝ (⨍_U bfA(x) dx) X`,

which needs integrability of the `2d × 2d` entries of `bfA(x)` on `U`.  That is
discharged entirely from the `CoeffOn` carrier: `CoeffOn.aeElliptic` gives a.e.
ellipticity of the representative on `U`, which bounds every doubled entry by
`Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam)`, and the pointwise-good
representative `Internal.Ch02.BookCh02.pointwiseCoeffOn` supplies a genuinely
measurable coefficient field a.e. equal to `a`, whence a.e. strong measurability
of the doubled entries.  Chapter 2 domains carry finite volume, so bounded plus
a.e. strongly measurable is integrable.
-/

namespace Algsuperdiff.Section3.Provider.Block

open HCPolySupport HCPolySupport.Book.Ch02

variable {d : ℕ}

/-! ## The averaged doubled coefficient matrices -/

/-- The volume average `⨍_U bfA(x) dx` of the pointwise doubled coefficient
field over a Chapter 2 domain. -/
noncomputable def averagedBlockMatrix (U : Domain d) (a : CoeffOn U) : BlockMat d where
  upperLeft := averageMat U fun x => (blockMatrixField a x).upperLeft
  upperRight := averageMat U fun x => (blockMatrixField a x).upperRight
  lowerLeft := averageMat U fun x => (blockMatrixField a x).lowerLeft
  lowerRight := averageMat U fun x => (blockMatrixField a x).lowerRight

/-! ### The pointwise inverse field really is the pointwise inverse

`blockMatrixInverseField` is *defined* as an explicit block formula, so its
name alone does not certify that it inverts `blockMatrixField`.  The two lemmas
below record the genuine two-sided identification, a.e. on the Chapter 2
domain, from `CoeffOn.aeElliptic` and CoarseGraining's pointwise block Fenchel
inverse identity
`Homogenization.blockMatMul_blockReflect_blockMatrixOfCoeff_eq_id`.  They
document the left-hand term `⨍_U bfA⁻¹(x) dx` of `e.CG.bounds.2` as the average
of the genuine pointwise inverse. -/

/-- Entries of the averaged doubled matrix are the averages of the entries. -/
theorem toFullBlockMat_averagedBlockMatrix (U : Domain d) (a : CoeffOn U)
    (alpha beta : BlockCoord d) :
    toFullBlockMat (averagedBlockMatrix U a) alpha beta =
      average U fun x => toFullBlockMat (blockMatrixField a x) alpha beta := by
  cases alpha <;> cases beta <;> rfl

/-! ## The doubled quadratic form as a sum over doubled coordinates -/

/-- The doubled quadratic form written out over the `2d` doubled coordinates. -/
theorem blockVecDot_blockMatVecMul_eq_sum (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d,
        toFullBlockVec X alpha * toFullBlockMat A alpha beta * toFullBlockVec X beta := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, dotProduct]
  refine Finset.sum_congr rfl fun alpha _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun beta _ => by ring

/-! ## Integrability of the doubled entries -/

/-- Every entry of the pointwise doubled coefficient matrix is integrable on a
Chapter 2 domain.

Measurability comes from the pointwise-good representative
`Internal.Ch02.BookCh02.pointwiseCoeffOn`, whose coefficient field is genuinely
measurable and a.e. equal to `a`; the bound comes from `CoeffOn.aeElliptic`. -/
theorem integrable_toFullBlockMat_blockMatrixField (U : Domain d) (a : CoeffOn U)
    (alpha beta : BlockCoord d) :
    MeasureTheory.Integrable
      (fun x => toFullBlockMat (blockMatrixField a x) alpha beta)
      (volumeMeasureOn (U : Set (Vec d))) := by
  classical
  have hmemU : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), x ∈ (U : Set (Vec d)) :=
    MeasureTheory.ae_restrict_mem U.measurableSet
  -- the pointwise-good representative
  set b : CoeffOn U := Internal.Ch02.BookCh02.pointwiseCoeffOn U a with hbdef
  have hba : CoeffOn.AEEq b a := Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hEll : IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  set A0 : Vec d → Fin d → Fin d → ℝ :=
    fun x i j => if x ∈ (U : Set (Vec d)) then b.toCoeffField x i j else 0 with hA0def
  have hA0 : Measurable A0 := hEll.1
  -- measurability of the doubled entries of the representative
  have hfull :
      Measurable fun x => fun alpha beta =>
        toFullBlockMat (blockMatrixOfCoeff (A0 x)) alpha beta :=
    measurable_toFullBlockMat_blockCoeffField hA0
  have hentry :
      Measurable fun x => toFullBlockMat (blockMatrixOfCoeff (A0 x)) alpha beta :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hfull alpha) beta
  have hmeas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => toFullBlockMat (blockMatrixField a x) alpha beta)
        (volumeMeasureOn (U : Set (Vec d))) := by
    refine (hentry.aestronglyMeasurable (μ := volumeMeasureOn (U : Set (Vec d)))).congr ?_
    filter_upwards [hmemU, hba] with x hxU hxab
    have hxA0 : A0 x = b.toCoeffField x := by
      funext i j
      simp [hA0def, hxU]
    simp [hxA0, hxab, blockMatrixField, blockMatrixOfCoeff]
  -- the a.e. entry bound from ellipticity of the carrier
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
        ‖toFullBlockMat (blockMatrixField a x) alpha beta‖ ≤
          Real.sqrt (blockMatrixOfCoeffNormSqBound a.lam a.Lam) := by
    filter_upwards [a.aeElliptic] with x hx
    have hentryBound :
        |toFullBlockMat (blockMatrixOfCoeff (a.toCoeffField x)) alpha beta| ≤
          Real.sqrt (blockMatrixOfCoeffNormSqBound a.lam a.Lam) :=
      abs_toFullBlockMat_blockMatrixOfCoeff_entry_le_of_isEllipticMatrix hx alpha beta
    simpa [Real.norm_eq_abs, blockMatrixField, blockMatrixOfCoeff] using hentryBound
  exact
    MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const
        (Real.sqrt (blockMatrixOfCoeffNormSqBound a.lam a.Lam)))
      hmeas hbound

/-! ## Linearity of the normalized average -/

private theorem average_finset_sum {iota : Type*} (U : Domain d) (s : Finset iota)
    (f : iota → Vec d → ℝ)
    (hf : ∀ i ∈ s, MeasureTheory.Integrable (f i) (volumeMeasureOn (U : Set (Vec d)))) :
    average U (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, average U (f i) := by
  unfold average
  rw [MeasureTheory.integral_finsetSum s hf, Finset.mul_sum]

/-- The normalized average is homogeneous. -/
theorem average_const_mul (U : Domain d) (c : ℝ) (f : Vec d → ℝ) :
    average U (fun x => c * f x) = c * average U f := by
  unfold average
  rw [MeasureTheory.integral_const_mul]
  ring

private theorem average_const_mul_mul_const (U : Domain d) (c₁ c₂ : ℝ) (f : Vec d → ℝ) :
    average U (fun x => c₁ * f x * c₂) = c₁ * average U f * c₂ := by
  have hrw : (fun x => c₁ * f x * c₂) = fun x => (c₁ * c₂) * f x := by
    funext x
    ring
  rw [hrw, average_const_mul]
  ring

/-! ## The average commutes with the doubled quadratic form -/

/-- Exchanging the volume average with the doubled quadratic form: the average
of the pointwise doubled energy is the doubled energy of the averaged matrix. -/
theorem average_blockVecDot_blockMatVecMul_blockMatrixField (U : Domain d) (a : CoeffOn U)
    (X : BlockVec d) :
    average U (fun x => blockVecDot X (blockMatVecMul (blockMatrixField a x) X)) =
      blockVecDot X (blockMatVecMul (averagedBlockMatrix U a) X) := by
  classical
  set g : BlockCoord d → BlockCoord d → Vec d → ℝ := fun alpha beta x =>
    toFullBlockVec X alpha * toFullBlockMat (blockMatrixField a x) alpha beta *
      toFullBlockVec X beta with hgdef
  have hgint : ∀ alpha beta : BlockCoord d,
      MeasureTheory.Integrable (g alpha beta) (volumeMeasureOn (U : Set (Vec d))) := by
    intro alpha beta
    exact
      ((integrable_toFullBlockMat_blockMatrixField U a alpha beta).const_mul
        (toFullBlockVec X alpha)).mul_const (toFullBlockVec X beta)
  have hgavg : ∀ alpha beta : BlockCoord d,
      average U (g alpha beta) =
        toFullBlockVec X alpha * toFullBlockMat (averagedBlockMatrix U a) alpha beta *
          toFullBlockVec X beta := by
    intro alpha beta
    rw [hgdef, average_const_mul_mul_const, toFullBlockMat_averagedBlockMatrix]
  have hpointwise :
      (fun x => blockVecDot X (blockMatVecMul (blockMatrixField a x) X)) =
        fun x => ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d, g alpha beta x := by
    funext x
    exact blockVecDot_blockMatVecMul_eq_sum (blockMatrixField a x) X
  rw [hpointwise,
    average_finset_sum U Finset.univ (fun alpha x => ∑ beta : BlockCoord d, g alpha beta x)
      (fun alpha _ =>
        MeasureTheory.integrable_finsetSum Finset.univ fun beta _ => hgint alpha beta),
    blockVecDot_blockMatVecMul_eq_sum]
  refine Finset.sum_congr rfl fun alpha _ => ?_
  rw [average_finset_sum U Finset.univ (fun beta => g alpha beta)
    fun beta _ => hgint alpha beta]
  exact Finset.sum_congr rfl fun beta _ => hgavg alpha beta

/-- The average over `U` of the pointwise doubled energy density at a fixed
doubled load is the doubled energy of the averaged matrix. -/
theorem average_blockEnergyDensityAt (U : Domain d) (a : CoeffOn U) (X : BlockVec d) :
    average U (fun x => blockEnergyDensityAt a X x) =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (averagedBlockMatrix U a) X) := by
  have hpt : (fun x => blockEnergyDensityAt a X x) =
      fun x => (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (blockMatrixField a x) X) := rfl
  rw [hpt, average_const_mul, average_blockVecDot_blockMatVecMul_blockMatrixField]

/-- The pointwise doubled energy at a fixed load is integrable on `U`. -/
theorem integrable_blockVecDot_blockMatVecMul_blockMatrixField (U : Domain d) (a : CoeffOn U)
    (X : BlockVec d) :
    MeasureTheory.Integrable
      (fun x => blockVecDot X (blockMatVecMul (blockMatrixField a x) X))
      (volumeMeasureOn (U : Set (Vec d))) := by
  classical
  have hpointwise :
      (fun x => blockVecDot X (blockMatVecMul (blockMatrixField a x) X)) =
        fun x => ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d,
          toFullBlockVec X alpha * toFullBlockMat (blockMatrixField a x) alpha beta *
            toFullBlockVec X beta := by
    funext x
    exact blockVecDot_blockMatVecMul_eq_sum (blockMatrixField a x) X
  rw [hpointwise]
  refine MeasureTheory.integrable_finsetSum Finset.univ fun alpha _ => ?_
  refine MeasureTheory.integrable_finsetSum Finset.univ fun beta _ => ?_
  exact
    ((integrable_toFullBlockMat_blockMatrixField U a alpha beta).const_mul
      (toFullBlockVec X alpha)).mul_const (toFullBlockVec X beta)

end Algsuperdiff.Section3.Provider.Block
