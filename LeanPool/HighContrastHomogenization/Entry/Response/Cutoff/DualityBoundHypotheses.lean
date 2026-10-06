/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalCutoffPairingMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.PathwiseToAnnealedAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.OptimizerEnergyIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.NormalizedAndGradient
public import LeanPool.HighContrastHomogenization.Support.PDE.Harmonic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.MeanZero
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas
public import Mathlib.Tactic.FunProp

/-!
# High-contrast homogenization: Entry.Response.Cutoff.DualityBoundHypotheses

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Hypotheses for the cutoff-pairing duality bound

This file assembles analytic hypotheses feeding the negative-Besov duality bound behind the
cutoff-pairing estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). It records that the
adapted cell is the image of the reference cube under the linear map `y ↦ q y`, so a cell average
there identifies with a cube average after this change of variables, and shows the pulled-back
cutoff gradient field `ξ` is smooth coordinatewise, uniformly bounded to second order, and
measurable. It supplies the square-integrability of the pulled-back optimizer flux under an
almost-everywhere elliptic representative, the integrability of the cutoff-weighted pairing on a
cell, and the weak solenoidality of the flux defect of an `A`-harmonic function. It also shows
that the affine defect of an `H¹` function is again `H¹` with the expected gradient, and that the
integrand of the weak quantity `W^\pm` of `e.response.weak.estimate` is almost-everywhere
strongly measurable in the coefficient sample.
-/

section
/-!
## Measurability of the weak-quantity integrand of the response estimate

The weak quantity `W^\pm` of `e.response.weak.estimate` is the sample expectation of the square of
the scale-average seminorm `besovSeminorm` of the recentred, canonically-metric-scaled cell averages
of the doubled optimizer state `X_t^\pm`.  This file records that this integrand is
`AEStronglyMeasurable` in the coefficient sample.

The doubled optimizer state of an arbitrary response maximizer is determined almost everywhere on
the response cell by the Chapter-2 canonical maximizer, by a.e. gradient uniqueness for response
maximizers (AK.HC (2.9)); the canonical choice depends measurably on the sample by the Galerkin
selection construction; and the scale-average seminorm is a countable sum of finite sums of
measurable terms.  The family is summed only over the triadic index box, so its entries outside the
box may be replaced by a constant before applying the sum-measurability result.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

private theorem aestronglyMeasurable_besovSeminorm_sq_minus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q'
      (respCoeffMinus F a) (u a)) :
    AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (respCoeffMinus F a) (u a)) - Y)) ^ 2) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  -- The canonical optimizer state is a.e. a function of the coefficient's a.e. class.
  have hstate_aeeq : ∀ {A B : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t)},
      Book.Ch02.CoeffOn.AEEq A B → ∀ p r : Vec d,
      canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p r
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) B p r := by
    intro A B hAB p r
    have hgrad : (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) A)
          p r).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) B)
          p r).toSolution.toH1.grad := by
      simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
        (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
    filter_upwards [hgrad, hAB] with x hgradx hcoeffx
    simp only [canonicalOptimizerBlockState]
    rw [hgradx, hcoeffx]
  have hcell_eq : ∀ (a : CoeffSpace d) (V : Set (Vec d)),
      V ⊆ (adaptedDomain (respGrid jStar F) hq t : Set (Vec d)) →
      cellAverage V (optimizerField (respCoeffMinus F a) (u a))
        = cellAverage V (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q') := by
    intro a V hVU
    obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    let A : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t) :=
      coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll
    have hAB : Book.Ch02.CoeffOn.AEEq A
        (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) := by
      filter_upwards [hbf.symm] with x hx
      simpa only [canonicalRespCoeffMinusOn_toFun] using! hx
    calc cellAverage V (optimizerField (respCoeffMinus F a) (u a))
        = cellAverage V (optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p q')) :=
          cellAverage_optimizerField_eq_canonical (U := adaptedDomain (respGrid jStar F) hq t)
            hVU hlam hle hEll hbf p q' (u a) (hu a)
      _ = cellAverage V
            (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p q') := by
          apply congrArg (cellAverage V)
          funext x
          rfl
      _ = cellAverage V (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q') :=
          cellAverage_congr_ae hVU (hstate_aeeq hAB p q')
  have hcoord : ∀ (n : ℕ) (w : Fin d → ℤ), w ∈ triadicIndexBox d n → ∀ i : Fin d,
      Measurable (fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffMinus F a) (u a))).1 i) ∧
      Measurable (fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffMinus F a) (u a))).2 i) := by
    intro n w hw i
    have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w
        ⊆ (adaptedDomain (respGrid jStar F) hq t : Set (Vec d)) :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
      (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
    constructor
    · have h1 : (fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffMinus F a) (u a))).1 i)
          = fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q')).1 i := by
        funext a
        rw [hcell_eq a _ hVU]
      rw [h1]
      simpa only [toFullBlockVec, cellAverage] using
        (measurable_cellAverage_canonicalRespCoeffMinus (respGrid jStar F) hq t F p q'
          (Sum.inl i) hVmeas hVU)
    · have h1 : (fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffMinus F a) (u a))).2 i)
          = fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q')).2 i := by
        funext a
        rw [hcell_eq a _ hVU]
      rw [h1]
      simpa only [toFullBlockVec, cellAverage] using
        (measurable_cellAverage_canonicalRespCoeffMinus (respGrid jStar F) hq t F p q'
          (Sum.inr i) hVmeas hVU)
  set avg : CoeffSpace d → ℕ → (Fin d → ℤ) → BlockVec d :=
    (fun a n w => if w ∈ triadicIndexBox d n
      then blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (u a)) - Y)
      else 0) with havg
  have havg1 : ∀ n w i, Measurable fun a : CoeffSpace d => (avg a n w).1 i := by
    intro n w i
    by_cases hw : w ∈ triadicIndexBox d n
    · have hsplit : (fun a : CoeffSpace d => (avg a n w).1 i)
          = fun a : CoeffSpace d => (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffMinus F a) (u a)) - Y)).1 i := by
        funext a
        simp only [havg, ite_eq_left hw]
      rw [hsplit]
      have hW : Measurable fun a : CoeffSpace d =>
          cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffMinus F a) (u a)) :=
        Measurable.prod
          (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).1))
          (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).2))
      have hZ : Measurable fun a : CoeffSpace d =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (u a)) - Y) :=
        (blockMatContinuousLinearMap (blockSqrt (respM0 F))).continuous.measurable.comp
          (hW.sub measurable_const)
      exact (measurable_pi_apply i).comp hZ.fst
    · have hsplit : (fun a : CoeffSpace d => (avg a n w).1 i) = fun _ => (0 : ℝ) := by
        funext a
        simp only [havg, ite_eq_right hw]
        rfl
      rw [hsplit]
      exact measurable_const
  have havg2 : ∀ n w i, Measurable fun a : CoeffSpace d => (avg a n w).2 i := by
    intro n w i
    by_cases hw : w ∈ triadicIndexBox d n
    · have hsplit : (fun a : CoeffSpace d => (avg a n w).2 i)
          = fun a : CoeffSpace d => (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffMinus F a) (u a)) - Y)).2 i := by
        funext a
        simp only [havg, ite_eq_left hw]
      rw [hsplit]
      have hW : Measurable fun a : CoeffSpace d =>
          cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffMinus F a) (u a)) :=
        Measurable.prod
          (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).1))
          (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).2))
      have hZ : Measurable fun a : CoeffSpace d =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (u a)) - Y) :=
        (blockMatContinuousLinearMap (blockSqrt (respM0 F))).continuous.measurable.comp
          (hW.sub measurable_const)
      exact (measurable_pi_apply i).comp hZ.snd
    · have hsplit : (fun a : CoeffSpace d => (avg a n w).2 i) = fun _ => (0 : ℝ) := by
        funext a
        simp only [havg, ite_eq_right hw]
        rfl
      rw [hsplit]
      exact measurable_const
  refine Measurable.aestronglyMeasurable ?_
  have hgoal : (fun a : CoeffSpace d => besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (respCoeffMinus F a) (u a)) - Y)) ^ 2)
      = fun a : CoeffSpace d => besovSeminorm t (avg a) ^ 2 := by
    funext a
    exact congrArg (fun x : ℝ => x ^ 2)
      (besovSeminorm_congr (fun n w hw => by simp only [havg, ite_eq_left hw]))
  rw [hgoal]
  have hbase := measurable_besovSeminorm t havg1 havg2
  simpa only [pow_two] using! hbase.mul hbase


private theorem aestronglyMeasurable_besovSeminorm_sq_plus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q'
      (respCoeffPlus F a) (u a)) :
    AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (respCoeffPlus F a) (u a)) - Y)) ^ 2) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  -- The canonical optimizer state is a.e. a function of the coefficient's a.e. class.
  have hstate_aeeq : ∀ {A B : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t)},
      Book.Ch02.CoeffOn.AEEq A B → ∀ p r : Vec d,
      canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p r
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) B p r := by
    intro A B hAB p r
    have hgrad : (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) A)
          p r).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) B)
          p r).toSolution.toH1.grad := by
      simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
        (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
    filter_upwards [hgrad, hAB] with x hgradx hcoeffx
    simp only [canonicalOptimizerBlockState]
    rw [hgradx, hcoeffx]
  have hcell_eq : ∀ (a : CoeffSpace d) (V : Set (Vec d)),
      V ⊆ (adaptedDomain (respGrid jStar F) hq t : Set (Vec d)) →
      cellAverage V (optimizerField (respCoeffPlus F a) (u a))
        = cellAverage V (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q') := by
    intro a V hVU
    obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    let A : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t) :=
      coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll
    have hAB : Book.Ch02.CoeffOn.AEEq A
        (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) := by
      filter_upwards [hbf.symm] with x hx
      simpa only [canonicalRespCoeffPlusOn_toFun] using! hx
    calc cellAverage V (optimizerField (respCoeffPlus F a) (u a))
        = cellAverage V (optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p q')) :=
          cellAverage_optimizerField_eq_canonical (U := adaptedDomain (respGrid jStar F) hq t)
            hVU hlam hle hEll hbf p q' (u a) (hu a)
      _ = cellAverage V
            (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p q') := by
          apply congrArg (cellAverage V)
          funext x
          rfl
      _ = cellAverage V (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q') :=
          cellAverage_congr_ae hVU (hstate_aeeq hAB p q')
  have hcoord : ∀ (n : ℕ) (w : Fin d → ℤ), w ∈ triadicIndexBox d n → ∀ i : Fin d,
      Measurable (fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffPlus F a) (u a))).1 i) ∧
      Measurable (fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffPlus F a) (u a))).2 i) := by
    intro n w hw i
    have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w
        ⊆ (adaptedDomain (respGrid jStar F) hq t : Set (Vec d)) :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
      (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
    constructor
    · have h1 : (fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffPlus F a) (u a))).1 i)
          = fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q')).1 i := by
        funext a
        rw [hcell_eq a _ hVU]
      rw [h1]
      simpa only [toFullBlockVec, cellAverage] using
        (measurable_cellAverage_canonicalRespCoeffPlus (respGrid jStar F) hq t F p q'
          (Sum.inl i) hVmeas hVU)
    · have h1 : (fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffPlus F a) (u a))).2 i)
          = fun a : CoeffSpace d =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q')).2 i := by
        funext a
        rw [hcell_eq a _ hVU]
      rw [h1]
      simpa only [toFullBlockVec, cellAverage] using
        (measurable_cellAverage_canonicalRespCoeffPlus (respGrid jStar F) hq t F p q'
          (Sum.inr i) hVmeas hVU)
  set avg : CoeffSpace d → ℕ → (Fin d → ℤ) → BlockVec d :=
    (fun a n w => if w ∈ triadicIndexBox d n
      then blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (u a)) - Y)
      else 0) with havg
  have havg1 : ∀ n w i, Measurable fun a : CoeffSpace d => (avg a n w).1 i := by
    intro n w i
    by_cases hw : w ∈ triadicIndexBox d n
    · have hsplit : (fun a : CoeffSpace d => (avg a n w).1 i)
          = fun a : CoeffSpace d => (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffPlus F a) (u a)) - Y)).1 i := by
        funext a
        simp only [havg, ite_eq_left hw]
      rw [hsplit]
      have hW : Measurable fun a : CoeffSpace d =>
          cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffPlus F a) (u a)) :=
        Measurable.prod
          (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).1))
          (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).2))
      have hZ : Measurable fun a : CoeffSpace d =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (u a)) - Y) :=
        (blockMatContinuousLinearMap (blockSqrt (respM0 F))).continuous.measurable.comp
          (hW.sub measurable_const)
      exact (measurable_pi_apply i).comp hZ.fst
    · have hsplit : (fun a : CoeffSpace d => (avg a n w).1 i) = fun _ => (0 : ℝ) := by
        funext a
        simp only [havg, ite_eq_right hw]
        rfl
      rw [hsplit]
      exact measurable_const
  have havg2 : ∀ n w i, Measurable fun a : CoeffSpace d => (avg a n w).2 i := by
    intro n w i
    by_cases hw : w ∈ triadicIndexBox d n
    · have hsplit : (fun a : CoeffSpace d => (avg a n w).2 i)
          = fun a : CoeffSpace d => (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffPlus F a) (u a)) - Y)).2 i := by
        funext a
        simp only [havg, ite_eq_left hw]
      rw [hsplit]
      have hW : Measurable fun a : CoeffSpace d =>
          cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffPlus F a) (u a)) :=
        Measurable.prod
          (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).1))
          (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).2))
      have hZ : Measurable fun a : CoeffSpace d =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (u a)) - Y) :=
        (blockMatContinuousLinearMap (blockSqrt (respM0 F))).continuous.measurable.comp
          (hW.sub measurable_const)
      exact (measurable_pi_apply i).comp hZ.snd
    · have hsplit : (fun a : CoeffSpace d => (avg a n w).2 i) = fun _ => (0 : ℝ) := by
        funext a
        simp only [havg, ite_eq_right hw]
        rfl
      rw [hsplit]
      exact measurable_const
  refine Measurable.aestronglyMeasurable ?_
  have hgoal : (fun a : CoeffSpace d => besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (respCoeffPlus F a) (u a)) - Y)) ^ 2)
      = fun a : CoeffSpace d => besovSeminorm t (avg a) ^ 2 := by
    funext a
    exact congrArg (fun x : ℝ => x ^ 2)
      (besovSeminorm_congr (fun n w hw => by simp only [havg, ite_eq_left hw]))
  rw [hgoal]
  have hbase := measurable_besovSeminorm t havg1 havg2
  simpa only [pow_two] using! hbase.mul hbase


/-- The integrand `a ↦ [M_0^{1/2} (X_t^\pm(a) - Y)]^2` of the weak quantity
`e.response.weak.estimate` is almost-everywhere strongly measurable in the coefficient sample, for
an arbitrary family of response maximizers `u`.  The cell averages entering the doubled optimizer
state are the canonically selected ones up to a null set, and the canonical selection is measurable
in the sample. -/
theorem aestronglyMeasurable_besovSeminorm_sq_of_maximizer {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (c : CoeffSpace d → CoeffField d)
    (hc : c = respCoeffMinus F ∨ c = respCoeffPlus F)
    (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a)) :
    AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  classical
  rcases hc with rfl | rfl
  · exact aestronglyMeasurable_besovSeminorm_sq_minus P jStar F t hjStar hm p q' Y u hu
  · exact aestronglyMeasurable_besovSeminorm_sq_plus P jStar F t hjStar hm p q' Y u hu
end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The affine defect of an `H¹` function

Given an `H¹` function `u` on a bounded open convex domain `U`, a vector `P` and a
constant `c`, the affine defect `x ↦ u x - P · x - c` is again `H¹`, with gradient
`∇u - P`.  In the cutoff argument for `e.response.cutoff.estimate` the gradient
defect `∇v - P` of an optimizer is paired against a flux defect, and integration
by parts requires that this defect be the gradient of an `H¹` function: namely of
the affine defect of `v`, since the linear function `x ↦ P · x` and the constants
are `H¹` on a bounded domain and `H¹` is closed under subtraction.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The affine defect `x ↦ u x - vecDot P x - c` of an `H¹` function `u`,
packaged as an `H¹` function on `U`.  The linear function `x ↦ vecDot P x` is
globally smooth, hence `H¹` on the bounded domain `U`
(`H1Function.ofContDiffOnIsOpenBoundedConvexDomain`), and constants are `H¹` on
a finite-measure domain (`H1Function.const`). -/
@[expose]
def affineDefectH1 {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (P : Vec d) (c : ℝ) : H1Function U :=
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  u - H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
        (f := fun x => vecDot P x) (by unfold vecDot; fun_prop)
    - H1Function.const c

/-- The underlying function of the affine defect is `x ↦ u x - vecDot P x - c`. -/
@[simp] theorem affineDefectH1_toFun {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (P : Vec d) (c : ℝ) :
    (affineDefectH1 hU u P c).toFun = fun x => u x - vecDot P x - c := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hlin :
      (H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
        (f := fun x => vecDot P x) (by unfold vecDot; fun_prop)).toFun =
        fun x => vecDot P x :=
    rfl
  funext x
  simp only [affineDefectH1, H1Function.sub_toFun, H1Function.const_apply, hlin]

/-- The gradient of the affine defect is `∇u - P`. -/
@[simp] theorem affineDefectH1_grad {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (P : Vec d) (c : ℝ) :
    (affineDefectH1 hU u P c).grad = fun x => u.grad x - P := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hlin_grad :
      (H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
        (f := fun x => vecDot P x) (by unfold vecDot; fun_prop)).grad = fun _ => P := by
    funext x i
    change (fderiv ℝ (fun y : Vec d => vecDot P y) x) (basisVec i) = P i
    have hfd :
        fderiv ℝ (fun y : Vec d => vecDot P y) x =
          (∑ j : Fin d, P j • ContinuousLinearMap.proj (R := ℝ) j) := by
      rw [show (fun y : Vec d => vecDot P y) =
            (fun y => (∑ j : Fin d, P j • ContinuousLinearMap.proj (R := ℝ) j) y) by
          funext y
          simp only [vecDot, _root_.sum_apply, _root_.smul_apply,
            ContinuousLinearMap.proj_apply, smul_eq_mul]]
      exact ContinuousLinearMap.fderiv _
    rw [hfd]
    simp only [_root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [basisVec_apply, hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  funext x i
  simp only [affineDefectH1, H1Function.sub_grad, H1Function.grad_const, hlin_grad,
    Pi.sub_apply, Pi.zero_apply, sub_zero]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The change of variables from an adapted cell to the reference cube

The adapted cell `HighContrast.adaptedCell q t` of generation `t` is the image of the reference open
cube `openCubeSet (originCube d t)` under the linear map `y ↦ q y`
(`image_openCubeSet_originCube_eq_adaptedCell`).  This file records the two elementary facts that
let the normalized averages on the two sides be identified: the aligned cell at lattice index `0`
is the centred adapted cell, and translating the reference cube by the zero lattice index fixes it.
Together with `cubeAverage_comp_matVecMul`, these transport a normalized average on the adapted
cell to the reference cube, which is the change of variables behind the adapted-to-Euclidean
comparison, HC Lemma 2.15, (2.127)--(2.128).
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Translating the reference cube `originCube d t` by the zero lattice index leaves the cube
unchanged. -/
theorem translateCube_zero {d : ℕ} (t : ℤ) :
    translateCube (0 : Fin d → ℤ) (originCube d t) = originCube d t := by
  unfold translateCube
  have h : (fun i => (originCube d t).index i + (0 : Fin d → ℤ) i) = (originCube d t).index := by
    funext i; simp
  rw [h]

/-- The normalized average of `f` over the adapted cell `HighContrast.adaptedCell q t` equals the
normalized average of the pulled-back function `y ↦ f (matVecMul q y)` over the reference cube
`originCube d t`.  This is the change of variables `x = q y` for normalized averages, behind the
adapted-to-Euclidean comparison of HC Lemma 2.15, (2.127)--(2.128). -/
theorem volumeAverage_adaptedCell_eq_cubeAverage_comp {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (f : Vec d → ℝ) :
    volumeAverage (HighContrast.adaptedCell q t) f
      = cubeAverage (originCube d t) (fun y => f (matVecMul q y)) := by
  have hcov := cubeAverage_comp_matVecMul hq t (0 : Fin d → ℤ) f
  rw [adaptedCellAtCenter_zero q t, translateCube_zero (d := d) t] at hcov
  exact hcov.symm

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The pulled-back flux on the reference cube, with the elliptic datum packaged existentially

The two inputs below restate the square-integrability of the optimizer flux and of its pullback to
the reference cube in the form in which the cutoff argument consumes them: the coefficient is only
assumed to agree almost everywhere on the adapted cell with a field uniformly elliptic there, and
the elliptic constants and representative are introduced by an existential rather than carried as
separate hypotheses.  The a.e.-representative shape is forced by the coefficient carrier, whose
points are a.e. classes, and is enough for every `MemLp` consumer, all of which are a.e. invariant.

Paper: the cutoff estimate `e.response.cutoff.estimate` and its negative-Besov duality bound
(`AK.HC` Lemma A.1, (A.4)), whose flux slot is supplied here.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The pulled-back flux is `L²` on the reference cube, elliptic datum existentially
quantified.**  If the coefficient `b` agrees almost everywhere on the adapted cell
`HighContrast.adaptedCell q t` with a field `f` uniformly elliptic there, then the pulled-back
centred
flux defect `y ↦ q⁻¹ ((optimizerField b u (q y) − Y).2)` of an `b`-harmonic optimizer `u` is square
integrable for the normalized measure of the reference cube.  This is the `hflux` slot of the
generic CG product bridge `abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct`
used in the cutoff estimate `e.response.cutoff.estimate`. -/
theorem memLp_two_pullback_flux_of_exists {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {b : CoeffField d}
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t)) (Y : BlockVec d) :
    MemLp (fun y => matVecMul q⁻¹ ((optimizerField b u (matVecMul q y) - Y).2)) 2
      (normalizedCubeMeasure (originCube d t)) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hbf⟩ := hb
  exact memLp_two_normalizedCubeMeasure_pullback_flux hq t hEll hbf u Y

/-- **The flux of an optimizer is `L²` on the cell, elliptic datum existentially quantified.**
If the coefficient `b` agrees almost everywhere on the adapted cell `HighContrast.adaptedCell q t`
with
a field `f` uniformly elliptic there, then the flux `x ↦ b x · u.toH1.grad x` of a `b`-harmonic
optimizer `u` is square integrable on the cell.  This is the `hflux` hypothesis of the
integration-by-parts step in the negative-Besov duality bound (`AK.HC` Lemma A.1, (A.4)) behind
the cutoff estimate `e.response.cutoff.estimate`. -/
theorem memVectorL2_flux_of_exists {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {b : CoeffField d}
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t)) :
    MemVectorL2 (HighContrast.adaptedCell q t) (fun x => matVecMul (b x) (u.toH1.grad x)) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hbf⟩ := hb
  have _ := hq
  have hfluxf : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x))
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        fun x => matVecMul (b x) (u.toH1.grad x) := by
    filter_upwards [hbf] with x hx
    rw [hx]
  exact (memLp_congr_ae hae).mp hfluxf

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of the cutoff-weighted pairing on a cell

The integration-by-parts form of the cutoff pairing `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) integrates the product of a bounded cutoff with the Euclidean pairing of
two square-integrable vector fields against the cell measure.  This file supplies the
integrability side conditions for that pairing, and the integrability of the squared Euclidean
length of a square-integrable vector field.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A bounded measurable weight times the Euclidean pairing of two coordinatewise square
integrable vector fields is integrable on a cell.  This is the integrability side condition of
the cutoff-weighted pairing `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem integrableOn_cutoff_pairing_of_coords {d : ℕ} {V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict V)]
    {A B : Vec d → Vec d}
    (hA : ∀ i, MeasureTheory.MemLp (fun x => A x i) 2 (MeasureTheory.volume.restrict V))
    (hB : ∀ i, MeasureTheory.MemLp (fun x => B x i) 2 (MeasureTheory.volume.restrict V))
    {φ : Vec d → ℝ} (hφb : ∃ M : ℝ, ∀ x, |φ x| ≤ M)
    (hφm : MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.volume.restrict V)) :
    MeasureTheory.IntegrableOn (fun x => φ x * vecDot (A x) (B x)) V := by
  rw [MeasureTheory.IntegrableOn]
  have hpair : Integrable (fun x => vecDot (A x) (B x)) (volume.restrict V) := by
    have hsum : Integrable (fun x => ∑ i, A x i * B x i) (volume.restrict V) := by
      refine integrable_finsetSum _ fun i _ => ?_
      simpa only [Pi.mul_def] using (hA i).integrable_mul (hB i)
    simpa only [vecDot] using hsum
  obtain ⟨M, hM⟩ := hφb
  exact hpair.bdd_mul hφm (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact hM x)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The flux defect of an `A`-harmonic function is solenoidal

For a set `U ⊆ ℝ^d`, a vector field is weakly solenoidal on `U` when its pairing with the
gradient of every compactly supported `H¹₀(U)` test function vanishes
(`HCPolySupport.IsSolenoidalOn`).  The flux `x ↦ b(x) ∇u(x)` of an `A`-harmonic function is
solenoidal by the definition of `A`-harmonicity, and a constant field is solenoidal against
`H¹₀(U)` tests because the componentwise average of a zero-trace `H¹` gradient vanishes.
Consequently the flux defect obtained by subtracting a constant vector from the flux is again
solenoidal; this is the field that the cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) pairs against.

The constant-field statement and the defect statement need integrability of the fields being
paired, which in this library is supplied by finiteness of the restricted volume measure (for the
constant) and by an explicit `L²(U)` witness (for the flux); the corresponding hypotheses appear
on the two refined statements below.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A constant vector field is weakly solenoidal on a finite-measure domain: every zero-trace
`H¹` test gradient has vanishing componentwise integral, so pairing it with a constant vector
gives zero. -/
theorem isSolenoidalOn_const_of_finiteMeasure {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (Q : Vec d) :
    IsSolenoidalOn U (fun _ => Q) := by
  intro φ
  exact CorrectionFieldData.integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
    (U := U) Q φ.toH1Function.grad_memVectorL2
    (IsPotentialZeroTraceOn.integral_eq_zero φ.isPotentialZeroTraceOn)

/-- On a finite-measure domain, the flux defect `x ↦ b(x) ∇u(x) - Q` is weakly solenoidal
whenever the flux has an `L²(U)` representative: the flux is solenoidal, the constant field is
solenoidal, and both pairings are integrable, so their sum is solenoidal. -/
theorem isSolenoidalOn_fluxDefect_of_finiteMeasure {d : ℕ} {U : Set (Vec d)} {b : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction b U)
    (hflux : MemVectorL2 U (fun x => matVecMul (b x) (u.toH1.grad x))) (Q : Vec d) :
    IsSolenoidalOn U (fun x => matVecMul (b x) (u.toH1.grad x) - Q) := by
  have hconst : MemVectorL2 U (fun _ : Vec d => Q) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := Q)
  have hdef : (fun x => matVecMul (b x) (u.toH1.grad x) - Q) =
      (fun x => matVecMul (b x) (u.toH1.grad x)) + (-1 : ℝ) • (fun _ : Vec d => Q) := by
    funext x
    simp [Pi.add_apply, sub_eq_add_neg]
  rw [hdef]
  exact isSolenoidalOn_add_of_memVectorL2 hflux (hconst.const_smul (-1))
    u.isHarmonic.2
    (isSolenoidalOn_smul (isSolenoidalOn_const_of_finiteMeasure (U := U) Q) (-1))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The pulled-back cutoff gradient as an admissible weight field

For a cutoff `φ` and a matrix `qq`, the pulled-back cutoff is `ψ(y) = φ (qq · y)`.  Its gradient
field `scalarCutoffGradientField ψ` is the weight field `ξ` consumed by the negative-Besov duality
bound for the product term of the cutoff estimate (`e.response.cutoff.estimate`), which needs three
facts about `ξ`: it is smooth coordinatewise, each coordinate field has derivative bounded by the
second-derivative bound carried by the cutoff class, and `ξ` is bounded by the Lipschitz constant
of the pulled-back cutoff.  The three declarations below record exactly those facts.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The continuous linear map underlying the pullback `y ↦ qq · y`, used to move between the
pulled-back cutoff and `φ`. -/
@[expose]
public def matVecMulCLM (qq : Mat d) : Vec d →L[ℝ] Vec d :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin qq)

private theorem matVecMulCLM_apply (qq : Mat d) (y : Vec d) :
    matVecMulCLM qq y = matVecMul qq y := by
  simp only [matVecMulCLM, LinearMap.coe_toContinuousLinearMap',
    Matrix.mulVecLin_apply, Geometry.matVecMul_eq_mulVec]

/-- Coordinatewise smoothness of the gradient field of the pulled-back cutoff
(`e.response.cutoff.estimate`; the cutoff class of `IsResponseCutoff`). -/
theorem contDiff_scalarCutoffGradientField_comp {d : ℕ} (qq : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec d => scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y i) := by
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => φ (matVecMul qq y)) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => matVecMul qq y) := by
      have heq : (fun y : Vec d => matVecMul qq y) = fun y => matVecMulCLM qq y := by
        funext y
        exact (matVecMulCLM_apply qq y).symm
      rw [heq]
      exact (matVecMulCLM qq).contDiff
    exact hφ.comp hlin
  exact contDiff_scalarCutoffGradientField_component hcomp i

/-- Bound on the derivative of a coordinate of the gradient field of the pulled-back cutoff by the
second-derivative bound the cutoff class carries (`e.response.cutoff.estimate`; the cutoff class
of `IsResponseCutoff`). -/
theorem norm_fderiv_scalarCutoffGradientField_comp_le {d : ℕ} (qq : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {B : ℝ}
    (hφ2 : ∀ x : Vec d,
      ‖iteratedFDeriv ℝ 2 (fun y : Vec d => φ (matVecMul qq y)) x‖ ≤ B) (i : Fin d) (z : Vec d) :
    ‖fderiv ℝ
        (fun y : Vec d => scalarCutoffGradientField (fun w : Vec d => φ (matVecMul qq w)) y i)
        z‖ ≤ B := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => φ (matVecMul qq y)) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => matVecMul qq y) := by
      have heq : (fun y : Vec d => matVecMul qq y) = fun y => matVecMulCLM qq y := by
        funext y
        exact (matVecMulCLM_apply qq y).symm
      rw [heq]
      exact (matVecMulCLM qq).contDiff
    exact hφ.comp hlin
  exact fderiv_scalarCutoffGradientField_component_le_of_hessian_bound hψ i (hφ2 z)

/-- Bound on the gradient field of the pulled-back cutoff by the Lipschitz constant of the
pullback (`e.response.cutoff.estimate`; the cutoff class of `IsResponseCutoff`). -/
theorem norm_scalarCutoffGradientField_comp_le {d : ℕ} (qq : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {K : NNReal}
    (hlip : LipschitzWith K (fun y : Vec d => φ (matVecMul qq y))) (y : Vec d) :
    ‖scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y‖ ≤ (K : ℝ) := by
  have _ := hφ
  calc
    ‖scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y‖
        ≤ ‖fderiv ℝ (fun z : Vec d => φ (matVecMul qq z)) y‖ :=
          norm_scalarCutoffGradientField_le_fderiv _ _
    _ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz (𝕜 := ℝ) hlip

end

end HCPolySupport.HighContrast.Multiscale
end
