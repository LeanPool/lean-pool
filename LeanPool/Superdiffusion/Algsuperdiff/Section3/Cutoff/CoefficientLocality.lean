/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LocalLimit

/-!
# CoefficientLocality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Integral-locality of the actual coefficient cutoff

The deterministic `nu I` shift is handled at local entry-test generators.  It
therefore preserves the exact `LocalSigmaR` information of the genuine cutoff.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- Addition of a deterministic regular field preserves every
integral-generated local sigma-field. -/
theorem measurable_const_add_local (c : RegCoeffField d) (U : Set (Vec d)) :
    @Measurable (RegCoeffField d) (RegCoeffField d) (LocalSigmaR U) (LocalSigmaR U)
      (fun a => c + a) := by
  refine @measurable_generateFrom (RegCoeffField d) (RegCoeffField d) (LocalSigmaR U) _ _ ?_
  rintro s ⟨i, j, φ, hφ, hφU, t, ht, rfl⟩
  have hentry : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) (borel ℝ)
      (entryTestR i j φ) := by
    intro w hw
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, j, φ, hφ, hφU, w, hw, rfl⟩
  have hEq : entryTestR i j φ ∘ (fun a : RegCoeffField d => c + a) =
      fun a => entryTestR i j φ c + entryTestR i j φ a := by
    funext a
    exact entryTestR_add i j hφ c a
  change @MeasurableSet (RegCoeffField d) (LocalSigmaR U)
    ((entryTestR i j φ ∘ fun a : RegCoeffField d => c + a) ⁻¹' t)
  rw [hEq]
  exact (measurable_const.add hentry) ht

/-- The actual coefficient field `a_m = nu I + k_m` reads only the same local
integral information as the lower-infinite cutoff. -/
theorem measurable_coefficientCutoff_local (M : ABKModel d) (m : ℤ)
    (U : Set (Vec d)) :
    @Measurable (CutoffSample d) (RegCoeffField d) (cutoffSampleLocalSigma M m U)
      (LocalSigmaR U) (coefficientCutoff M.nu m) := by
  change @Measurable (CutoffSample d) (RegCoeffField d) (cutoffSampleLocalSigma M m U)
    (LocalSigmaR U) (fun omega =>
      RegCoeffField.constRegCoeffField (M.nu • (1 : Mat d)) + cutoff m omega)
  exact (measurable_const_add_local
    (RegCoeffField.constRegCoeffField (M.nu • (1 : Mat d)) ) U).comp
      (measurable_cutoff_local M m U)

end

end Algsuperdiff.Section3.Cutoff
