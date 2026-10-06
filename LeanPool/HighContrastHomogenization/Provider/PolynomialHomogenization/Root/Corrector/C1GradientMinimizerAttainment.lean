/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientResidual
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeMap
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorWeightedGradientBridge
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.HilbertMinimization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroCore
public import LeanPool.HighContrastHomogenization.Support.PDE.HarmonicHilbert

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1GradientMinimizerAttainment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Attainment of the finite affine-gradient excess

The affine-gradient candidates form a finite-dimensional subspace of the
Hilbert realization of harmonic gradients.  Coercive Hilbert minimization
therefore selects an exact best candidate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped ENNReal

noncomputable section

@[expose]
public noncomputable def finiteAffineHarmonicGradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m) (e : Vec d) :=
  AHarmonicGradientHilbert.ofAHarmonicFunction
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (openCubeSet (originCube d n)))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d n) a)
    (finiteCubeSolutionRestriction a hnm
      (finiteAffineCubeSolution a m e)).toPointwiseAHarmonic

private theorem finiteAffineHarmonicGradient_add
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m) (e e' : Vec d) :
    finiteAffineHarmonicGradient a hnm (e + e') =
      finiteAffineHarmonicGradient a hnm e +
        finiteAffineHarmonicGradient a hnm e' := by
  apply Subtype.ext
  simp only [finiteAffineHarmonicGradient,
    AHarmonicGradientHilbert.field_ofAHarmonicFunction]
  change
    (finiteCubeSolutionRestriction a hnm
        (finiteAffineCubeSolution a m (e + e'))).toH1.gradToHilbertVectorL2 =
      (finiteCubeSolutionRestriction a hnm
        (finiteAffineCubeSolution a m e)).toH1.gradToHilbertVectorL2 +
      (finiteCubeSolutionRestriction a hnm
        (finiteAffineCubeSolution a m e')).toH1.gradToHilbertVectorL2
  apply MeasureTheory.Lp.ext
  have hadd := finiteAffineSolution_grad_add a m e e'
  have hsub : openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le hnm
  have hadd' := ae_mono
    (Measure.restrict_mono hsub (le_refl volume)) hadd
  filter_upwards
      [(finiteCubeSolutionRestriction a hnm
          (finiteAffineCubeSolution a m (e + e'))).toH1.coeFn_gradToHilbertVectorL2,
        (finiteCubeSolutionRestriction a hnm
          (finiteAffineCubeSolution a m e)).toH1.coeFn_gradToHilbertVectorL2,
        (finiteCubeSolutionRestriction a hnm
          (finiteAffineCubeSolution a m e')).toH1.coeFn_gradToHilbertVectorL2,
        MeasureTheory.Lp.coeFn_add
          (finiteCubeSolutionRestriction a hnm
            (finiteAffineCubeSolution a m e)).toH1.gradToHilbertVectorL2
          (finiteCubeSolutionRestriction a hnm
            (finiteAffineCubeSolution a m e')).toH1.gradToHilbertVectorL2,
        hadd'] with x hx hxe hxe' hsum haddx
  simp only [finiteCubeSolutionRestriction_grad] at hx hxe hxe'
  rw [hx, hsum, Pi.add_apply, hxe, hxe']
  simp only [finiteAffineCubeSolution, hilbertifyVecField]
  rw [haddx]
  simp

private theorem finiteAffineHarmonicGradient_smul
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m) (c : ℝ) (e : Vec d) :
    finiteAffineHarmonicGradient a hnm (c • e) =
      c • finiteAffineHarmonicGradient a hnm e := by
  apply Subtype.ext
  simp only [finiteAffineHarmonicGradient,
    AHarmonicGradientHilbert.field_ofAHarmonicFunction]
  change
    (finiteCubeSolutionRestriction a hnm
        (finiteAffineCubeSolution a m (c • e))).toH1.gradToHilbertVectorL2 =
      c • (finiteCubeSolutionRestriction a hnm
        (finiteAffineCubeSolution a m e)).toH1.gradToHilbertVectorL2
  apply MeasureTheory.Lp.ext
  have hsmul := finiteAffineSolution_grad_smul a m c e
  have hsub : openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le hnm
  have hsmul' := ae_mono
    (Measure.restrict_mono hsub (le_refl volume)) hsmul
  filter_upwards
      [(finiteCubeSolutionRestriction a hnm
          (finiteAffineCubeSolution a m (c • e))).toH1.coeFn_gradToHilbertVectorL2,
        (finiteCubeSolutionRestriction a hnm
          (finiteAffineCubeSolution a m e)).toH1.coeFn_gradToHilbertVectorL2,
        MeasureTheory.Lp.coeFn_smul c
          (finiteCubeSolutionRestriction a hnm
            (finiteAffineCubeSolution a m e)).toH1.gradToHilbertVectorL2,
        hsmul'] with x hx hxe hcoe hsmulx
  simp only [finiteCubeSolutionRestriction_grad] at hx hxe
  rw [hx, hcoe, Pi.smul_apply, hxe]
  simp only [finiteAffineCubeSolution, hilbertifyVecField]
  rw [hsmulx]
  simp

@[expose]
public noncomputable def finiteAffineHarmonicGradientLinearMap
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m) :
    Vec d →ₗ[ℝ]
      AHarmonicGradientHilbert.Space
        (PotentialSolenoidalL2Data.ofSubmoduleClosures
          (openCubeSet (originCube d n)))
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d n) a) where
  toFun := finiteAffineHarmonicGradient a hnm
  map_add' := finiteAffineHarmonicGradient_add a hnm
  map_smul' := finiteAffineHarmonicGradient_smul a hnm

@[expose]
public noncomputable def restrictedSolutionHarmonicGradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :=
  AHarmonicGradientHilbert.ofAHarmonicFunction
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (openCubeSet (originCube d n)))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d n) a)
    (finiteCubeSolutionRestriction a hnm u).toPointwiseAHarmonic

@[expose]
public noncomputable def affineResidualHarmonicGradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :=
  AHarmonicGradientHilbert.ofAHarmonicFunction
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (openCubeSet (originCube d n)))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d n) a)
    (finiteAffineGradientResidual a hnm u e).toPointwiseAHarmonic

private theorem affineResidualHarmonicGradient_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :
    affineResidualHarmonicGradient a hnm u e =
      restrictedSolutionHarmonicGradient a hnm u -
        finiteAffineHarmonicGradientLinearMap a hnm e := by
  apply Subtype.ext
  simp only [affineResidualHarmonicGradient, restrictedSolutionHarmonicGradient,
    finiteAffineHarmonicGradientLinearMap, finiteAffineHarmonicGradient,
    AHarmonicGradientHilbert.field_ofAHarmonicFunction, LinearMap.coe_mk,
    AddHom.coe_mk]
  change
    (finiteAffineGradientResidual a hnm u e).toH1.gradToHilbertVectorL2 =
      (finiteCubeSolutionRestriction a hnm u).toH1.gradToHilbertVectorL2 -
        (finiteCubeSolutionRestriction a hnm
          (finiteAffineCubeSolution a m e)).toH1.gradToHilbertVectorL2
  apply MeasureTheory.Lp.ext
  filter_upwards
      [(finiteAffineGradientResidual a hnm u e).toH1.coeFn_gradToHilbertVectorL2,
        (finiteCubeSolutionRestriction a hnm u).toH1.coeFn_gradToHilbertVectorL2,
        (finiteCubeSolutionRestriction a hnm
          (finiteAffineCubeSolution a m e)).toH1.coeFn_gradToHilbertVectorL2,
        MeasureTheory.Lp.coeFn_sub
          (finiteCubeSolutionRestriction a hnm u).toH1.gradToHilbertVectorL2
          (finiteCubeSolutionRestriction a hnm
            (finiteAffineCubeSolution a m e)).toH1.gradToHilbertVectorL2]
    with x hr hu hw hsub
  simp only [finiteAffineGradientResidual_grad,
    finiteCubeSolutionRestriction_grad] at hr hu hw
  rw [hr, hsub, Pi.sub_apply, hu, hw]
  simp [finiteAffineCubeSolution, hilbertifyVecField]

private theorem candidate_sq_eq_normalized_energy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :
    weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m e).toH1.grad x) ^ 2 =
      ENNReal.ofReal
        (normalizedLocalSymmetricEnergy
          (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
            (originCube d n) a)
          (AHarmonicGradientHilbert.field
            (affineResidualHarmonicGradient a hnm u e))) := by
  let r := finiteAffineGradientResidual a hnm u e
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d n) a
  have hcoeff := Book.Ch03.publicCoeffField_ae_eq_openCubeSet
    (originCube d n) a
  rw [weightedGradNorm_congr_coeff_ae_on
    (fun x ↦ u.toH1.grad x - (finiteAffineSolution a m e).toH1.grad x)
    hcoeff.symm]
  have hraw := ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq
    hEll r.toH1.grad_memVectorL2
  rw [← finiteAffineGradientResidual_grad a hnm u e]
  rw [← hraw]
  congr 2

/-- The finite affine-gradient excess has an exact minimizing slope. -/
theorem exists_finiteAffineGradientExcess_candidate_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    ∃ b : Vec d,
      weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m b).toH1.grad x) ≤
        finiteAffineGradientExcess a n m u := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let bField : CoeffField d := Book.Ch03.publicCoeffField (originCube d n) a
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d n) a
  let M : PotentialSolenoidalL2Data U :=
    PotentialSolenoidalL2Data.ofSubmoduleClosures U
  let H := AHarmonicGradientHilbert.Space M hEll
  let T : Vec d →ₗ[ℝ] H := finiteAffineHarmonicGradientLinearMap a hnm
  let Ksub : Submodule ℝ H := LinearMap.range T
  let : FiniteDimensional ℝ Ksub := T.finiteDimensional_range
  have hKclosed : IsClosed (Ksub : Set H) := Ksub.closed_of_finiteDimensional
  let K : ClosedSubmodule ℝ H := ⟨Ksub, hKclosed⟩
  let B : H →L[ℝ] H →L[ℝ] ℝ :=
    AHarmonicGradientHilbert.symmCoeffBilin M hEll
  have hU : Set.Nonempty U := by
    exact Book.Ch02.openCubeSet_nonempty (originCube d n)
  have hB : IsCoercive B := by
    exact AHarmonicGradientHilbert.isCoercive_symmCoeffBilin hU hEll
  have hBsymm : ∀ z w : H, B z w = B w z := by
    intro z w
    exact AHarmonicGradientHilbert.symmCoeffBilin_symm z w
  let x : H := restrictedSolutionHarmonicGradient a hnm u
  let z : H := affineMinimizerMap K B hB x
  have hzmem : z - x ∈ K :=
    sub_affineMinimizerMap_apply_mem K B hB x
  change z - x ∈ Ksub at hzmem
  rcases hzmem with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  have hz : z = affineResidualHarmonicGradient a hnm u (-c) := by
    rw [affineResidualHarmonicGradient_eq]
    change z = x - T (-c)
    rw [map_neg, hc]
    abel
  have hbest : ∀ e : Vec d,
      weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun y ↦ u.toH1.grad y -
            (finiteAffineSolution a m (-c)).toH1.grad y) ≤
        weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun y ↦ u.toH1.grad y -
            (finiteAffineSolution a m e).toH1.grad y) := by
    intro e
    let y : H := x - T e
    have hyK : y - x ∈ K := by
      change y - x ∈ Ksub
      refine ⟨-e, ?_⟩
      dsimp [y]
      rw [map_neg]
      abel
    have hq := affineMinimizerMap_minimizes_quadraticEnergy
      K hB hBsymm x y hyK
    have hbil : B z z ≤ B y y := by
      unfold quadraticEnergy at hq
      linarith only [hq]
    have henergy :
        normalizedLocalSymmetricEnergy hEll
            (AHarmonicGradientHilbert.field z) ≤
          normalizedLocalSymmetricEnergy hEll
            (AHarmonicGradientHilbert.field y) := by
      unfold normalizedLocalSymmetricEnergy
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
      exact hbil
    have hy : y = affineResidualHarmonicGradient a hnm u e := by
      dsimp [y, x, T]
      exact (affineResidualHarmonicGradient_eq a hnm u e).symm
    rw [hz, hy] at henergy
    have hsq :
        weightedGradNorm
            (a.coeffOn (originCube d n)).toCoeffField
            (openCubeSet (originCube d n))
            (fun y ↦ u.toH1.grad y -
              (finiteAffineSolution a m (-c)).toH1.grad y) ^ 2 ≤
          weightedGradNorm
            (a.coeffOn (originCube d n)).toCoeffField
            (openCubeSet (originCube d n))
            (fun y ↦ u.toH1.grad y -
              (finiteAffineSolution a m e).toH1.grad y) ^ 2 := by
      rw [candidate_sq_eq_normalized_energy a hnm u (-c),
        candidate_sq_eq_normalized_energy a hnm u e]
      exact ENNReal.ofReal_le_ofReal henergy
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp (by
      simpa only [ENNReal.rpow_two] using hsq)
  change
    weightedGradNorm
        (a.coeffOn (originCube d n)).toCoeffField
        (openCubeSet (originCube d n))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a m (-c)).toH1.grad x) ≤
      ⨅ e : Vec d,
        weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m e).toH1.grad x)
  exact le_iInf hbest

/-- A selected minimizing slope realizes the defining infimum exactly. -/
theorem exists_finiteAffineGradientExcess_candidate_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    ∃ b : Vec d,
      weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m b).toH1.grad x) =
        finiteAffineGradientExcess a n m u := by
  rcases exists_finiteAffineGradientExcess_candidate_le a hnm u with ⟨b, hb⟩
  refine ⟨b, le_antisymm hb ?_⟩
  exact finiteAffineGradientExcess_le a n m u b

end

end Root
end HighContrast
end HCPolySupport
