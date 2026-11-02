/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.Basic

/-!
# LIHLocalSigma

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The local integral sigma-field for shell fields

`lihLocalSigma U` is the pullback of CoarseGraining's integral-generated
`Homogenization.LocalSigmaR U` along `ShellField.forgetShell`.  It carries the
measurability of supported CoarseGraining entry-test observables and is
dominated by the canonical Borel sigma-field on shell fields.

The definition deliberately contains no point-evaluation or restriction
sigma-fields.
-/

namespace Algsuperdiff.Frozen.Assumptions.ShellField

open Filter HCPolySupport MeasureTheory Topology

noncomputable section

variable {d : ℕ}

/-- The shell-field pullback of CoarseGraining's local integral sigma-field. -/
abbrev lihLocalSigma (U : Set (Vec d)) : MeasurableSpace (ShellField d) :=
  MeasurableSpace.comap (forgetShell (d := d)) (LocalSigmaR U)

/-- A supported CoarseGraining entry-test observable, pulled back to shell fields,
is measurable from `lihLocalSigma U`. -/
theorem measurable_entryTestR_forgetShell_lihLocalSigma (U : Set (Vec d))
    (i k : Fin d) {psi : Vec d → ℝ} (hpsi : IsProbeR psi)
    (hpsiSupport : Function.support psi ⊆ U) :
    @Measurable (ShellField d) ℝ (lihLocalSigma U) (borel ℝ)
      (fun j ↦ entryTestR i k psi (forgetShell j)) := by
  have hentry : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) (borel ℝ)
      (entryTestR i k psi) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, k, psi, hpsi, hpsiSupport, t, ht, rfl⟩
  have hforget : @Measurable (ShellField d) (RegCoeffField d)
      (lihLocalSigma U) (LocalSigmaR U) forgetShell := by
    exact Measurable.of_comap_le le_rfl
  exact hentry.comp hforget

/-- CoarseGraining's pulled-back local integral sigma-field is contained in the
canonical Borel sigma-field on shell fields. -/
theorem lihLocalSigma_le_borel (U : Set (Vec d)) :
    lihLocalSigma U ≤
      (inferInstance : MeasurableSpace (ShellField d)) := by
  calc
    lihLocalSigma U
        ≤ MeasurableSpace.comap forgetShell
            (inferInstance : MeasurableSpace (RegCoeffField d)) :=
      MeasurableSpace.comap_mono (LocalSigmaR_le U)
    _ ≤ (inferInstance : MeasurableSpace (ShellField d)) :=
      measurable_forgetShell.comap_le

end

end Algsuperdiff.Frozen.Assumptions.ShellField
