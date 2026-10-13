/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Block.AveragedChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualPerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperMoments

/-!
# SplitObligationsQuadratic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cube coarse quadratic upper bound at the genuine cutoff

ABK26, `l.approximate.recurrence.formula`, Steps 1--2; the coarse-graining chain
`e.CG.bounds.2`.

## What this module supplies

Both surviving integrability obligations of
`Closure.SplitProducerFold.SplitScaleObligations` need one and the same
*pathwise* dominator: an upper bound for a doubled coarse quadratic form by an
explicit multiple of the two squared component lengths, whose random constant is
the realised upper ellipticity constant `Cutoff.coefficientCutoffCubeEllipticityUpper`
of the cell.  This module proves it.

The route is the proved right leg of `e.CG.bounds.2`:

```
  X . bfA(U; a) X  <=  X . ( fint_U bfA(x) dx ) X
                    =  fint_U  X . bfA(x) X  dx
                    <=  ( Lam + 2 lam^{-1} Lam^2 ) |X_1|^2 + 2 lam^{-1} |X_2|^2 ,
```

the first step being
`Provider.Block.coarseBlockMatrix_blockMatLoewnerLE_averagedBlockMatrix`, the
second `Provider.Block.average_blockVecDot_blockMatVecMul_blockMatrixField`,
and the third CoarseGraining's pointwise
`Homogenization.blockMatrixOfCoeff_quadratic_plainUpperBound_of_isEllipticMatrix`
under `CoeffOn.aeElliptic`.

At the genuine cutoff family the two ellipticity constants of the cell are
`lam = M.nu` and `Lam = Cutoff.coefficientCutoffCubeEllipticityUpper M m omega R`,
both definitionally (`Cutoff.coefficientCutoffCoeffOn`), so
`switchCubeEnergy_le_ellipticityUpper` reads the bound directly at the Step-3
switch energy.

## Binders

Only the typing binders.  Every statement below is unconditional: no smallness,
moment, measurability or selection proposition occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `e.CG.bounds.2`, `l.approximate.recurrence.formula`, Steps 1--3, the
  switch display.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Block
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## Normalized averages against a constant -/

/-- A Chapter 2 domain has positive finite volume. -/
theorem volume_domain_toReal_pos (U : Domain d) :
    0 < (MeasureTheory.volume (U : Set (Vec d))).toReal := by
  have hpos : 0 < MeasureTheory.volume (U : Set (Vec d)) :=
    U.isOpen.measure_pos MeasureTheory.volume U.nonempty
  have hfin : volumeMeasureOn (U : Set (Vec d)) Set.univ < ⊤ :=
    MeasureTheory.measure_lt_top _ _
  have hlt : MeasureTheory.volume (U : Set (Vec d)) < ⊤ := by
    simpa [MeasureTheory.Measure.restrict_apply_univ] using hfin
  exact ENNReal.toReal_pos hpos.ne' hlt.ne

/-- The normalized average of an integrable function almost everywhere below a
constant is below that constant. -/
theorem average_le_of_ae_le {U : Domain d} {f : Vec d → ℝ} {c : ℝ}
    (hf : MeasureTheory.Integrable f (volumeMeasureOn (U : Set (Vec d))))
    (hle : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), f x ≤ c) :
    average U f ≤ c := by
  have hvol := volume_domain_toReal_pos U
  have hmono : ∫ x, f x ∂(volumeMeasureOn (U : Set (Vec d))) ≤
      ∫ _x, c ∂(volumeMeasureOn (U : Set (Vec d))) :=
    MeasureTheory.integral_mono_ae hf (MeasureTheory.integrable_const c) hle
  have hconst : ∫ _x, c ∂(volumeMeasureOn (U : Set (Vec d))) =
      (MeasureTheory.volume (U : Set (Vec d))).toReal * c := by
    rw [MeasureTheory.integral_const]
    simp only [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply_univ,
      smul_eq_mul]
  rw [hconst] at hmono
  have hstep := mul_le_mul_of_nonneg_left hmono (inv_pos.2 hvol).le
  calc average U f
      = (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x, f x ∂(volumeMeasureOn (U : Set (Vec d))) := rfl
    _ ≤ (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
        ((MeasureTheory.volume (U : Set (Vec d))).toReal * c) := hstep
    _ = c := by field_simp

/-! ## The coarse quadratic upper bound -/

/-- **The doubled coarse quadratic form is bounded by the plain elliptic upper
bound of its own carrier.**

`e.CG.bounds.2`'s right leg followed by CoarseGraining's pointwise doubled upper
bound.  Unconditional: the two constants are the ones the `CoeffOn` carrier
itself records. -/
theorem blockVecDot_coarseBlockMatrix_le_plainUpperBound (U : Domain d) (a : CoeffOn U)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Ch02.coarseBlockMatrix U a) X) ≤
      (a.Lam + 2 * a.lam⁻¹ * a.Lam ^ 2) * vecNormSq X.1 + 2 * a.lam⁻¹ * vecNormSq X.2 := by
  have hLoew := coarseBlockMatrix_blockMatLoewnerLE_averagedBlockMatrix U a X
  have hcoarse : blockVecDot X (blockMatVecMul (Ch02.coarseBlockMatrix U a) X) ≤
      blockVecDot X (blockMatVecMul (averagedBlockMatrix U a) X) := by linarith
  have havg := average_blockVecDot_blockMatVecMul_blockMatrixField U a X
  have hbound : average U (fun x => blockVecDot X (blockMatVecMul (blockMatrixField a x) X)) ≤
      (a.Lam + 2 * a.lam⁻¹ * a.Lam ^ 2) * vecNormSq X.1 + 2 * a.lam⁻¹ * vecNormSq X.2 := by
    refine average_le_of_ae_le
      (integrable_blockVecDot_blockMatVecMul_blockMatrixField U a X) ?_
    filter_upwards [a.aeElliptic] with x hx
    exact blockMatrixOfCoeff_quadratic_plainUpperBound_of_isEllipticMatrix hx X.1 X.2
  rw [havg] at hbound
  linarith

/-! ## The bound at the genuine cutoff cell -/

/-- **The Step-3 switch energy, bounded by the realised upper ellipticity
constant of its own cell.**

`(meshCellCoeff M m R omega).lam = M.nu` and
`.Lam = Cutoff.coefficientCutoffCubeEllipticityUpper M m omega R` hold
definitionally, so the previous bound reads verbatim at the switch energy.
Unconditional. -/
theorem switchCubeEnergy_le_ellipticityUpper (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (X : BlockVec d) (omega : CutoffSample d) :
    switchCubeEnergy M m R X omega ≤
      (coefficientCutoffCubeEllipticityUpper M m omega R +
          2 * M.nu⁻¹ * coefficientCutoffCubeEllipticityUpper M m omega R ^ 2) *
          vecNormSq X.1 +
        2 * M.nu⁻¹ * vecNormSq X.2 :=
  blockVecDot_coarseBlockMatrix_le_plainUpperBound (Ch02.cubeDomain R)
    ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R) X

/-- The realised upper ellipticity constant of a cell is nonnegative. -/
theorem coefficientCutoffCubeEllipticityUpper_nonneg (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (R : TriadicCube d) :
    0 ≤ coefficientCutoffCubeEllipticityUpper M m omega R := by
  unfold coefficientCutoffCubeEllipticityUpper
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  positivity

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
