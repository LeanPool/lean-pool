/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Control

/-!
# Scaling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact scaling of local cube controls

The local value control is homogeneous under the shell scaling action.  This
is a deterministic statement; probabilistic transport belongs in
`LawTransport`.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open scoped Pointwise

noncomputable section

variable {d : ℕ}

private theorem unitCubeValueNorm_scale_of_nonneg (c : ℝ) (hc : 0 ≤ c)
    (j : ShellField d) :
    ShellField.unitCubeValueNorm (ShellField.scale c j) =
      c * ShellField.unitCubeValueNorm j := by
  unfold ShellField.unitCubeValueNorm
  change sSup (Set.range fun o : Option (ShellField.UnitOpenCubePoint d) =>
    match o with
    | none => (0 : ℝ)
    | some x => HCPolySupport.Book.Ch02.matrixOperatorNorm
        ((ShellField.scale c j) x.1)) =
      c * sSup (Set.range fun o : Option (ShellField.UnitOpenCubePoint d) =>
        match o with
        | none => (0 : ℝ)
        | some x => HCPolySupport.Book.Ch02.matrixOperatorNorm (j x.1))
  rw [show (fun o : Option (ShellField.UnitOpenCubePoint d) =>
      match o with
      | none => (0 : ℝ)
      | some x => HCPolySupport.Book.Ch02.matrixOperatorNorm
          ((ShellField.scale c j) x.1)) =
      fun o => c * (match o with
      | none => (0 : ℝ)
      | some x => HCPolySupport.Book.Ch02.matrixOperatorNorm (j x.1)) by
        funext o
        cases o with
        | none => simp
        | some x =>
          simp only
          rw [ShellField.scale_apply]
          change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (c • j x.1)‖ =
            c * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (j x.1)‖
          rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]]
  let f : Option (ShellField.UnitOpenCubePoint d) → ℝ := fun o =>
    match o with
    | none => (0 : ℝ)
    | some x => HCPolySupport.Book.Ch02.matrixOperatorNorm (j x.1)
  have hrange : Set.range (fun o => c * f o) = c • Set.range f := by
    ext y
    constructor
    · rintro ⟨o, rfl⟩
      exact ⟨f o, ⟨o, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨o, rfl⟩, rfl⟩
      exact ⟨o, rfl⟩
  rw [show (fun o : Option (ShellField.UnitOpenCubePoint d) =>
      c * (match o with
      | none => (0 : ℝ)
      | some x => HCPolySupport.Book.Ch02.matrixOperatorNorm (j x.1))) =
      fun o => c * f o by rfl, hrange]
  simpa only [smul_eq_mul] using (Real.sSup_smul_of_nonneg hc (Set.range f))

private theorem spatialScale_triadicScale (gamma : ℝ) (ell k : ℤ)
    (j : ShellField d) :
    ShellField.spatialScale ((3 : ℝ) ^ ell) (ShellField.triadicScale gamma k j) =
      ShellField.scale (Real.rpow 3 (gamma * (k : ℝ)))
        (ShellField.spatialScale ((3 : ℝ) ^ (ell - k)) j) := by
  apply ShellField.ext
  intro x
  simp only [ShellField.spatialScale_apply, ShellField.triadicScale_apply,
    ShellField.scale_apply]
  have hscale : ((3 : ℝ) ^ k)⁻¹ * (3 : ℝ) ^ ell =
      (3 : ℝ) ^ (ell - k) := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rw [smul_smul, hscale]

/-- A triadically scaled shell has local control equal to its amplitude
factor times the control of the original shell on the shifted cube scale
`ell - k`. -/
theorem localCubeControl_triadicScale (gamma : ℝ) (ell k : ℤ)
    (j : ShellField d) :
    localCubeControl ell (ShellField.triadicScale gamma k j) =
      Real.rpow 3 (gamma * (k : ℝ)) * localCubeControl (ell - k) j := by
  unfold localCubeControl
  rw [cubeScaleFactor_originCube, cubeScaleFactor_originCube,
    spatialScale_triadicScale]
  exact unitCubeValueNorm_scale_of_nonneg _ (Real.rpow_nonneg (by norm_num) _) _

end

end Algsuperdiff.Section3.Cutoff
