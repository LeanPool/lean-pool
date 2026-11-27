/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ComplexShellLocalChart
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Genuine Euclidean carriers for shell chart volumes

The ambient norm is the Euclidean norm on four complex coordinates,
hence eight real coordinates. The chart domain is three complex
Euclidean coordinates, hence six real coordinates. We transport the
actual shell chart through continuous linear equivalences; no product
maximum norm is used as an induced Euclidean metric.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Shell Euclidean domain with underlying type `EuclideanSpace ℂ (Fin 3) abbrev
ShellEuclideanAmbient : Type := EuclideanSpace ℂ (Fin 4)`. -/
abbrev ShellEuclideanDomain : Type := EuclideanSpace ℂ (Fin 3)
/-- Shell Euclidean ambient with underlying type `EuclideanSpace ℂ (Fin 4)`. -/
abbrev ShellEuclideanAmbient : Type := EuclideanSpace ℂ (Fin 4)

/-- Linear equivalence between complex spacetime and a time coordinate followed by three spatial
coordinates. -/
noncomputable def complexSpacetimeCoordinateEquiv :
    ComplexSpacetime ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun z := Fin.cons z.1 z.2
  invFun z := (z 0, Fin.tail z)
  left_inv z := rfl
  right_inv z := Fin.cons_self_tail z
  map_add' z w := by ext i; fin_cases i <;> rfl
  map_smul' a z := by ext i; fin_cases i <;> rfl

/-- Complex spacetime Euclidean equivalence of type `ComplexSpacetime ≃L[ℂ]
ShellEuclideanAmbient`. -/
noncomputable def complexSpacetimeEuclideanEquiv :
    ComplexSpacetime ≃L[ℂ] ShellEuclideanAmbient :=
  complexSpacetimeCoordinateEquiv.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => ℂ)).symm

/-- Shell Euclidean coordinates given by `PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)`. -/
noncomputable def shellEuclideanCoordinates :
    ShellEuclideanDomain ≃L[ℂ] (Fin 3 → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)

theorem complexSpacetimeEuclideanEquiv_norm_sq (z : ComplexSpacetime) :
    ‖complexSpacetimeEuclideanEquiv z‖ ^ 2 = euclidSq z := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  rfl

theorem shellEuclideanDomain_real_finrank : Module.finrank ℝ ShellEuclideanDomain = 6 := by
  rw [finrank_real_of_complex]
  simp [ShellEuclideanDomain]

theorem shellEuclideanAmbient_real_finrank : Module.finrank ℝ ShellEuclideanAmbient = 8 := by
  rw [finrank_real_of_complex]
  simp [ShellEuclideanAmbient]

/-- Euclidean Lorentz shell chart defined as `complexSpacetimeEuclideanEquiv
(lorentzComplexShellChart m Λ (shellEuclideanCoordinates w))`. -/
noncomputable def euclideanLorentzShellChart (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (w : ShellEuclideanDomain) : ShellEuclideanAmbient :=
  complexSpacetimeEuclideanEquiv
    (lorentzComplexShellChart m Λ (shellEuclideanCoordinates w))

/-- Euclidean shell chart domain defined as `shellEuclideanCoordinates ⁻¹' complexShellChartDomain
m`. -/
noncomputable def euclideanShellChartDomain (m : ℝ) : Set ShellEuclideanDomain :=
  shellEuclideanCoordinates ⁻¹' complexShellChartDomain m

theorem isOpen_euclideanShellChartDomain (m : ℝ) : IsOpen (euclideanShellChartDomain m) :=
  (isOpen_complexShellChartDomain m).preimage shellEuclideanCoordinates.continuous

/-- Continuous linear map for the euclidean Lorentz shell coordinates, of type
`ShellEuclideanAmbient →L[ℂ] ShellEuclideanDomain`. -/
noncomputable def euclideanLorentzShellCoordinates (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ShellEuclideanAmbient →L[ℂ] ShellEuclideanDomain :=
  shellEuclideanCoordinates.symm.toContinuousLinearMap.comp
    ((lorentzComplexShellCoordinates Λ).comp
      complexSpacetimeEuclideanEquiv.symm.toContinuousLinearMap)

theorem euclideanLorentzShellCoordinates_chart (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (w : ShellEuclideanDomain) :
    euclideanLorentzShellCoordinates Λ (euclideanLorentzShellChart m Λ w) = w := by
  simp only [euclideanLorentzShellCoordinates, euclideanLorentzShellChart,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, lorentzComplexShellCoordinates_chart]

theorem differentiableAt_euclideanLorentzShellChart {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    DifferentiableAt ℂ (euclideanLorentzShellChart m Λ) w :=
  complexSpacetimeEuclideanEquiv.differentiableAt.comp w
    ((differentiableAt_lorentzComplexShellChart Λ hw).comp w
      shellEuclideanCoordinates.differentiableAt)

theorem euclideanLorentzShellChart_real_derivative_left_inverse {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    ((euclideanLorentzShellCoordinates Λ).restrictScalars ℝ).comp
      (fderiv ℝ (euclideanLorentzShellChart m Λ) w) =
        ContinuousLinearMap.id ℝ ShellEuclideanDomain := by
  have hd := ((differentiableAt_euclideanLorentzShellChart Λ hw).restrictScalars ℝ).hasFDerivAt
  have h := ((euclideanLorentzShellCoordinates Λ).hasFDerivAt.restrictScalars ℝ).comp w hd
  have he : (fun z => euclideanLorentzShellCoordinates Λ (euclideanLorentzShellChart m Λ z)) = id :=
    funext (euclideanLorentzShellCoordinates_chart m Λ)
  simp only [Function.comp_def] at h
  rw [he] at h
  exact h.unique (hasFDerivAt_id w)

theorem euclideanLorentzShellChart_real_derivative_injective {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    Function.Injective (fderiv ℝ (euclideanLorentzShellChart m Λ) w) := by
  intro x y hxy
  have h := congrArg (euclideanLorentzShellCoordinates Λ) hxy
  change (((euclideanLorentzShellCoordinates Λ).restrictScalars ℝ).comp
      (fderiv ℝ (euclideanLorentzShellChart m Λ) w)) x =
    (((euclideanLorentzShellCoordinates Λ).restrictScalars ℝ).comp
      (fderiv ℝ (euclideanLorentzShellChart m Λ) w)) y at h
  simpa only [euclideanLorentzShellChart_real_derivative_left_inverse Λ hw,
    ContinuousLinearMap.id_apply] using h

end VacuumBellSeparation
