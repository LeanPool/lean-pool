/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.BallDirichletPoincare
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.EquationRestriction

/-!
# ScalarForcing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Bounds for a bounded scalar source
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support
open HCPolySupport.Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

theorem memScalarL2_of_memScalarLInfOn_of_subset
    {U W : Set (Vec d)} {g : Vec d → ℝ}
    [IsFiniteMeasure (volume.restrict W)]
    (hWU : W ⊆ U) (hg : MemScalarLInfOn U g) :
    MemLp g 2 (volume.restrict W) :=
  (hg.mono_measure (Measure.restrict_mono hWU le_rfl)).mono_exponent (by simp)

/-- A normalized `L²` average is bounded by the essential supremum. -/
theorem normalizedL2On_le_scalarLInfSizeOn
    {U W : Set (Vec d)} {g : Vec d → ℝ}
    (hWU : W ⊆ U) (hW : 0 < (volume W).toReal)
    (hg : MemScalarLInfOn U g) :
    normalizedL2On W g ≤ scalarLInfSizeOn U g := by
  have hWtop : volume W ≠ ⊤ := (ENNReal.toReal_ne_zero.mp hW.ne').2
  let finiteVolumeW : IsFiniteMeasure (volume.restrict W) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hWtop⟩
  have hgWtop : MemLp g ⊤ (volume.restrict W) :=
    hg.mono_measure (Measure.restrict_mono hWU le_rfl)
  have hgW2 : MemLp g 2 (volume.restrict W) := hgWtop.mono_exponent (by simp)
  have hraw := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict W) (f := g) (p := (2 : ENNReal)) (q := (⊤ : ENNReal))
    (by simp) hgWtop.aestronglyMeasurable
  have hrightTop : eLpNorm g ⊤ (volume.restrict W) *
      (volume.restrict W) Set.univ ^
        (1 / (2 : ENNReal).toReal - 1 / (⊤ : ENNReal).toReal) ≠ ⊤ := by
    apply ENNReal.mul_ne_top hgWtop.eLpNorm_ne_top
    apply ENNReal.rpow_ne_top_of_nonneg
    · norm_num
    · rw [Measure.restrict_apply_univ]
      exact hWtop
  have hreal := ENNReal.toReal_mono hrightTop hraw
  rw [normalizedL2On_eq_toReal_eLpNorm_div hgW2]
  have hmono : (eLpNorm g ⊤ (volume.restrict W)).toReal ≤
      (eLpNorm g ⊤ (volume.restrict U)).toReal := by
    exact ENNReal.toReal_mono hg.eLpNorm_ne_top
      (eLpNorm_mono_measure g (Measure.restrict_mono hWU le_rfl))
  unfold scalarLInfSizeOn
  rw [Measure.restrict_apply_univ, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat, ENNReal.toReal_top] at hreal
  norm_num at hreal
  have hsqrt : (volume W).toReal ^ (1 / 2 : ℝ) = Real.sqrt ((volume W).toReal) := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hreal
  have hspos : 0 < Real.sqrt ((volume W).toReal) := Real.sqrt_pos.2 hW
  apply (div_le_iff₀ hspos).2
  exact hreal.trans (mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg _))

/-- Restriction of the equation with a scalar zeroth-order source. -/
theorem isMatrixDivFormWeakSolutionZerothOrderOn_restrict
    {a : CoeffField d} {W V : Set (Vec d)}
    (hW : IsOpen W) (hV : IsOpen V) (hVW : V ⊆ W)
    {u : H1Function W} {g : Vec d → ℝ} {f : Vec d → Vec d}
    (h : IsMatrixDivFormWeakSolutionZerothOrderOn a W u g f) :
    IsMatrixDivFormWeakSolutionZerothOrderOn a V (u.restrict hV hVW) g f := by
  intro phi
  have hflux := setIntegral_vecDot_extendByZero hW hV hVW
    (fun p => matVecMul (a p) (u.grad p)) phi
  have hforce := setIntegral_vecDot_extendByZero hW hV hVW f phi
  have hvalue :
      ∫ p in W, g p *
          (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.toFun p
          ∂volume =
        ∫ p in V, g p * phi.toH1Function.toFun p ∂volume := by
    have hind : (fun p => g p *
        (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.toFun p) =
        Set.indicator V (fun p => g p * phi.toH1Function.toFun p) := by
      funext p
      rw [H10Function.extendByZeroToOpenSuperset_toFun]
      by_cases hp : p ∈ V
      · simp [hp]
      · simp [hp, H10Function.zeroExtension_apply_of_not_mem]
    rw [hind, integral_indicator hV.measurableSet,
      Measure.restrict_restrict hV.measurableSet, Set.inter_eq_left.mpr hVW]
  calc
    ∫ p in V, vecDot (matVecMul (a p) ((u.restrict hV hVW).grad p))
          (phi.toH1Function.grad p) ∂volume =
        ∫ p in W, vecDot (matVecMul (a p) (u.grad p))
          ((phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.grad p)
          ∂volume := hflux.symm
    _ = (∫ p in W, g p *
          (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.toFun p
          ∂volume) -
        ∫ p in W, vecDot (f p)
          ((phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.grad p)
          ∂volume := h (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW)
    _ = (∫ p in V, g p * phi.toH1Function.toFun p ∂volume) -
        ∫ p in V, vecDot (f p) (phi.toH1Function.grad p) ∂volume := by
      rw [hvalue, hforce]

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
