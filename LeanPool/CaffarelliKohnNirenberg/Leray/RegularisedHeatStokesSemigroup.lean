/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatSemigroup
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierLeray
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Heat propagation of the Stokes operator

Applying heat flow after a Stokes operator adds the two elapsed times in the
Fourier symbol. This is the kernel identity for splitting a Duhamel integral
at a restart time.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The Gaussian factor of the Stokes symbol composes with heat flow. -/
theorem heatSymbol_smul_stokesFrequencySymbol
    (s t : ℝ) (ξ : L2Vec3) (z : ComplexTensor3) :
    heatSymbol s ξ • stokesFrequencySymbol t ξ z =
      stokesFrequencySymbol (s + t) ξ z := by
  simp only [stokesFrequencySymbol, smul_apply, smul_smul, heatSymbol_add]
  congr 1
  ring

/-- Heat evolution of a Stokes output equals the Stokes output after the
combined elapsed time. -/
theorem regularisedHeatSemigroup_stokesL2Operator
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t)
    (F : ComplexTensorL2) :
    heatSemigroup s hs (stokesL2Operator ht F) =
      stokesL2Operator (show 0 < s + t by positivity) F := by
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  apply ℱV.injective
  change ℱV (ℱV.symm (heatMultiplier s hs •
      ℱV (ℱV.symm (stokesFourierMultiplier ht (ℱT F))))) =
    ℱV (ℱV.symm (stokesFourierMultiplier
      (show 0 < s + t by positivity) (ℱT F)))
  rw [ℱV.apply_symm_apply, ℱV.apply_symm_apply, ℱV.apply_symm_apply]
  apply Lp.ext
  have hheat : (heatMultiplier s hs : Lp (α := L2Vec3) ℂ ∞) =ᵐ[volume]
      heatSymbol s := by
    unfold heatMultiplier
    exact MemLp.coeFn_toLp _
  have hstokes (r : ℝ) (hr : 0 < r) :
      (stokesFourierMultiplier hr (ℱT F)) =ᵐ[volume]
        fun ξ => stokesApplyFormula r ξ (ℱT F ξ) :=
    measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula r p.1 p.2)
      (stokesApplyFormula_measurable r)
      (1 / Real.sqrt (2 * Real.exp 1 * r))
      (by intro ξ z; exact stokesApplyFormula_norm_le hr ξ z) (ℱT F)
  filter_upwards
    [Lp.coeFn_lpSMul (r := 2) (heatMultiplier s hs)
      (stokesFourierMultiplier ht (ℱT F)),
      hheat, hstokes t ht,
      hstokes (s + t) (show 0 < s + t by positivity)]
    with ξ hmul hheatξ hst hsum
  rw [hmul]
  change heatMultiplier s hs ξ • stokesFourierMultiplier ht (ℱT F) ξ =
    stokesFourierMultiplier (show 0 < s + t by positivity) (ℱT F) ξ
  rw [hheatξ, hst, hsum,
    ← stokesFrequencySymbol_apply_eq_formula,
    ← stokesFrequencySymbol_apply_eq_formula]
  exact heatSymbol_smul_stokesFrequencySymbol s t ξ (ℱT F ξ)

end CKN.Leray

end
