/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ComplexShellChart
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Actual local shell charts and their Lorentz transports

The target retains both the positive real eliminated coordinate and
the positive real radicand condition. The transported ambient chart
has an explicit continuous-linear left inverse; hence its genuine
complex derivative is injective. Induced Euclidean volume is separate.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Local coordinate chart on the complex mass shell. -/
noncomputable def complexShellLocalChart (m : ℝ) :
    OpenPartialHomeomorph (Fin 3 → ℂ) (complexShell m) where
  toFun w := ⟨complexShellChart m w, complexShellChart_mem_shell m w⟩
  invFun z := complexShellCoordinates z.1
  source := complexShellChartDomain m
  target := {z | 0 < (z.1.2 1).re ∧ complexShellCoordinates z.1 ∈ complexShellChartDomain m}
  map_source' := by
    intro w hw
    exact ⟨complexShellChart_second_re_pos hw, by
      simpa only [complexShellCoordinates_chart] using hw⟩
  map_target' := fun _ hz => hz.2
  left_inv' := fun _ _ => complexShellCoordinates_chart m _
  right_inv' := fun z hz => Subtype.ext (complexShellChart_coordinates z.2 hz.1)
  open_source := isOpen_complexShellChartDomain m
  open_target :=
    (isOpen_lt (continuous_const : Continuous (fun _ : complexShell m => (0 : ℝ)))
      (show Continuous (fun z : complexShell m => (z.1.2 1).re) by fun_prop)).inter
      ((isOpen_complexShellChartDomain m).preimage
        (complexShellCoordinates.continuous.comp continuous_subtype_val))
  continuousOn_toFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    intro w hw
    exact (differentiableAt_complexShellChart hw).continuousAt.continuousWithinAt
  continuousOn_invFun :=
    (complexShellCoordinates.continuous.comp continuous_subtype_val).continuousOn

/-- Complex Lorentz shell homeomorph. -/
noncomputable def complexLorentzShellHomeomorph (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) :
    complexShell m ≃ₜ complexShell m where
  toFun z := ⟨complexifiedSpacetimeMap Λ z.1, complexifiedSpacetimeMap_mem_shell Λ hΛ z.2⟩
  invFun z := ⟨complexifiedSpacetimeMap Λ.symm z.1,
    complexifiedSpacetimeMap_mem_shell Λ.symm hΛ.symm z.2⟩
  left_inv z := Subtype.ext (complexifiedSpacetimeMap_inverse Λ z.1)
  right_inv z := Subtype.ext (by
    simpa only [ContinuousLinearEquiv.symm_symm] using
      complexifiedSpacetimeMap_inverse Λ.symm z.1)
  continuous_toFun :=
    ((complexifiedSpacetimeMap Λ).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((complexifiedSpacetimeMap Λ.symm).continuous.comp continuous_subtype_val).subtype_mk _

/-- Lorentz complex shell local chart. -/
noncomputable def lorentzComplexShellLocalChart (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) :
    OpenPartialHomeomorph (Fin 3 → ℂ) (complexShell m) :=
  (complexShellLocalChart m).transHomeomorph (complexLorentzShellHomeomorph m Λ hΛ)

/-- Lorentz complex shell chart defined as `complexifiedSpacetimeMap Λ (complexShellChart m w)`. -/
noncomputable def lorentzComplexShellChart (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (w : Fin 3 → ℂ) : ComplexSpacetime :=
  complexifiedSpacetimeMap Λ (complexShellChart m w)

/-- Continuous linear map for the lorentz complex shell coordinates, of type `ComplexSpacetime
→L[ℂ] (Fin 3 → ℂ)`. -/
noncomputable def lorentzComplexShellCoordinates (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ComplexSpacetime →L[ℂ] (Fin 3 → ℂ) :=
  complexShellCoordinates.comp (complexifiedSpacetimeMap Λ.symm)

theorem lorentzComplexShellCoordinates_chart (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (w : Fin 3 → ℂ) :
    lorentzComplexShellCoordinates Λ (lorentzComplexShellChart m Λ w) = w := by
  change complexShellCoordinates (complexifiedSpacetimeMap Λ.symm
    (complexifiedSpacetimeMap Λ (complexShellChart m w))) = w
  rw [complexifiedSpacetimeMap_inverse, complexShellCoordinates_chart]

theorem differentiableAt_lorentzComplexShellChart {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {w : Fin 3 → ℂ}
    (hw : w ∈ complexShellChartDomain m) :
    DifferentiableAt ℂ (lorentzComplexShellChart m Λ) w :=
  (complexifiedSpacetimeMap Λ).differentiableAt.comp w (differentiableAt_complexShellChart hw)

theorem lorentzComplexShellChart_derivative_left_inverse {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {w : Fin 3 → ℂ}
    (hw : w ∈ complexShellChartDomain m) :
    (lorentzComplexShellCoordinates Λ).comp (fderiv ℂ (lorentzComplexShellChart m Λ) w) =
      ContinuousLinearMap.id ℂ (Fin 3 → ℂ) := by
  have h := (lorentzComplexShellCoordinates Λ).hasFDerivAt.comp w
    (differentiableAt_lorentzComplexShellChart Λ hw).hasFDerivAt
  have he : (fun z => lorentzComplexShellCoordinates Λ (lorentzComplexShellChart m Λ z)) = id :=
    funext (lorentzComplexShellCoordinates_chart m Λ)
  simp only [Function.comp_def] at h
  rw [he] at h
  exact h.unique (hasFDerivAt_id w)

theorem lorentzComplexShellChart_derivative_injective {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {w : Fin 3 → ℂ}
    (hw : w ∈ complexShellChartDomain m) :
    Function.Injective (fderiv ℂ (lorentzComplexShellChart m Λ) w) := by
  intro x y hxy
  have h := congrArg (lorentzComplexShellCoordinates Λ) hxy
  change ((lorentzComplexShellCoordinates Λ).comp
    (fderiv ℂ (lorentzComplexShellChart m Λ) w)) x =
    ((lorentzComplexShellCoordinates Λ).comp
    (fderiv ℂ (lorentzComplexShellChart m Λ) w)) y at h
  simpa only [lorentzComplexShellChart_derivative_left_inverse Λ hw,
    ContinuousLinearMap.id_apply] using h

end VacuumBellSeparation
