/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.LIHLocalSigma
public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.Actions
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.RegCoeffFieldOperations

/-!
# LocalScaling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Spatial transport of the integral-local sigma-fields

The marginal scaling action reads a field at `r • x`.  This module proves, at
the generators of `LocalSigmaR`, that information on `U` after that action is
information on `r • U` before it.  No restriction sigma-field is used here.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open scoped Pointwise

noncomputable section

variable {d : ℕ}

private theorem support_comp_inv_smul_subset_smul (r : ℝ) (hr : r ≠ 0)
    {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : Function.support φ ⊆ U) :
    Function.support (φ ∘ fun y : Vec d => r⁻¹ • y) ⊆ r • U := by
  intro y hy
  have hy' : r⁻¹ • y ∈ U := hφ hy
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr]
  exact hy'

/-- Spatial rescaling transports CoarseGraining's integral-local sigma-field by the
corresponding image of the observation set. -/
theorem measurable_smulReg_local (r : ℝ) (hr : r ≠ 0) (U : Set (Vec d)) :
    @Measurable (RegCoeffField d) (RegCoeffField d)
      (LocalSigmaR (r • U)) (LocalSigmaR U) (smulReg r hr) := by
  refine @measurable_generateFrom (RegCoeffField d) (RegCoeffField d)
    (LocalSigmaR (r • U)) _ _ ?_
  rintro s ⟨i, j, φ, hφ, hφU, t, ht, rfl⟩
  let ψ : Vec d → ℝ := φ ∘ fun y : Vec d => r⁻¹ • y
  have hψ : IsProbeR ψ := by
    exact hφ.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))
  have hψsupp : Function.support ψ ⊆ r • U := by
    exact support_comp_inv_smul_subset_smul r hr hφU
  have hentry : @Measurable (RegCoeffField d) ℝ (LocalSigmaR (r • U)) (borel ℝ)
      (entryTestR i j ψ) := by
    intro w hw
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, j, ψ, hψ, hψsupp, w, hw, rfl⟩
  have hEq : entryTestR i j φ ∘ smulReg r hr =
      fun a => |(r ^ Module.finrank ℝ (Vec d))⁻¹| * entryTestR i j ψ a := by
    funext a
    exact entryTestR_smulReg i j φ r hr a
  change @MeasurableSet (RegCoeffField d) (LocalSigmaR (r • U))
    ((entryTestR i j φ ∘ smulReg r hr) ⁻¹' t)
  rw [hEq]
  exact (hentry.const_mul _ ) ht

/-- The literal triadic shell scaling action transports integral-local shell
information from the contracted observation set to the original one. -/
theorem measurable_triadicScale_local (gamma : ℝ) (k : ℤ) (U : Set (Vec d)) :
    @Measurable (ShellField d) (ShellField d)
      (ShellField.lihLocalSigma (((3 : ℝ) ^ k)⁻¹ • U))
      (ShellField.lihLocalSigma U) (ShellField.triadicScale gamma k) := by
  have hforget : @Measurable (ShellField d) (RegCoeffField d)
      (ShellField.lihLocalSigma (((3 : ℝ) ^ k)⁻¹ • U))
      (LocalSigmaR (((3 : ℝ) ^ k)⁻¹ • U)) ShellField.forgetShell :=
    Measurable.of_comap_le le_rfl
  have hscale : @Measurable (RegCoeffField d) (RegCoeffField d)
      (LocalSigmaR (((3 : ℝ) ^ k)⁻¹ • U)) (LocalSigmaR U)
      (Algsuperdiff.Probability.triadicLayerScaleReg gamma k) := by
    let r : ℝ := ((3 : ℝ) ^ k)⁻¹
    have hr : r ≠ 0 := by
      dsimp [r]
      exact inv_ne_zero (zpow_ne_zero _ (by norm_num))
    change @Measurable (RegCoeffField d) (RegCoeffField d)
      (LocalSigmaR (r • U)) (LocalSigmaR U)
      (Algsuperdiff.Probability.scaleReg (Real.rpow 3 (gamma * (k : ℝ))) ∘ smulReg r hr)
    have hvalue : @Measurable (RegCoeffField d) (RegCoeffField d)
        (LocalSigmaR U) (LocalSigmaR U)
        (Algsuperdiff.Probability.scaleReg (Real.rpow 3 (gamma * (k : ℝ)))) := by
      refine @measurable_generateFrom (RegCoeffField d) (RegCoeffField d)
        (LocalSigmaR U) _ _ ?_
      rintro s ⟨i, j, φ, hφ, hφU, t, ht, rfl⟩
      have hentry : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) (borel ℝ)
          (entryTestR i j φ) := by
        intro w hw
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨i, j, φ, hφ, hφU, w, hw, rfl⟩
      have hEq : entryTestR i j φ ∘
          Algsuperdiff.Probability.scaleReg (Real.rpow 3 (gamma * (k : ℝ))) =
          fun a => Real.rpow 3 (gamma * (k : ℝ)) * entryTestR i j φ a := by
        funext a
        exact entryTestR_smul i j _ a
      change @MeasurableSet (RegCoeffField d) (LocalSigmaR U) ((entryTestR i j φ ∘
        Algsuperdiff.Probability.scaleReg (Real.rpow 3 (gamma * (k : ℝ)))) ⁻¹' t)
      rw [hEq]
      exact (hentry.const_mul _) ht
    exact hvalue.comp (measurable_smulReg_local r hr U)
  change @Measurable (ShellField d) (ShellField d)
    (MeasurableSpace.comap ShellField.forgetShell (LocalSigmaR (((3 : ℝ) ^ k)⁻¹ • U)))
    (MeasurableSpace.comap ShellField.forgetShell (LocalSigmaR U))
    (ShellField.triadicScale gamma k)
  rw [measurable_comap_iff]
  have h := hscale.comp hforget
  simpa only [Function.comp_apply, ShellField.forgetShell_triadicScale] using! h

end

end Algsuperdiff.Section3.Cutoff
