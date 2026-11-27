/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.FiniteCoordinateDerivative
public import LeanPool.VacuumBellSeparation.Shell.RadialContourDerivative
public import LeanPool.VacuumBellSeparation.Shell.ReferenceContourRank

/-!
# The reference rank is the derivative of the actual contour map

Five genuine Lorentz variations and the radial second momentum coordinate
supply the six real parameters. Joint smoothness is established before
coordinate-curve derivatives identify the full real derivative.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Keep the first five Lorentz parameters and set the unused sixth coordinate to zero. -/
noncomputable def activeLorentzParameters (a : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![a 0, a 1, a 2, a 3, a 4, 0]

/-- Reference contour map. -/
noncomputable def referenceContourMap (m B θ : ℝ) (a : Fin 6 → ℝ) : Fin 3 → ℂ :=
  complexShellCoordinates (complexLorentzFamilyAction (activeLorentzParameters a)
    (radialShellContour m B θ (a 5)))

theorem contDiff_activeLorentzParameters : ContDiff ℝ ⊤ activeLorentzParameters := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 0
  · exact contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 1
  · exact contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 2
  · exact contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 3
  · exact contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 4
  · exact contDiff_const

theorem contDiffAt_referenceContourMap {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    ContDiffAt ℝ ⊤ (referenceContourMap m B θ) 0 := by
  have hp : ContDiff ℝ ⊤ (fun a : Fin 6 → ℝ => a 5) := by fun_prop
  have hr : ContDiffAt ℝ ⊤
      (fun a : Fin 6 → ℝ => radialShellContour m B θ (a 5)) 0 :=
    (contDiffAt_radialShellContour hB m θ).comp
      (f := fun a : Fin 6 → ℝ => a 5) 0 hp.contDiffAt
  have hf : ContDiffAt ℝ ⊤
      (fun a : Fin 6 → ℝ => complexLorentzFamilyAction (activeLorentzParameters a)
        (radialShellContour m B θ (a 5))) 0 :=
    contDiff_complexLorentzFamilyAction.comp₂_contDiffAt
      contDiff_activeLorentzParameters.contDiffAt hr
  unfold referenceContourMap
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hf.fst
  · exact contDiffAt_pi.mp hf.snd 0
  · exact contDiffAt_pi.mp hf.snd 2

theorem referenceContourMap_single_lorentz (m B θ : ℝ) (j : Fin 5) (r : ℝ) :
    referenceContourMap m B θ (Pi.single j.castSucc r) =
      complexShellCoordinates (complexLorentzParameterAction j.castSucc r
        (radialShellContour m B θ 0)) := by
  have ha : activeLorentzParameters (Pi.single j.castSucc r) = Pi.single j.castSucc r := by
    ext k
    fin_cases j <;> fin_cases k <;> simp [activeLorentzParameters]
  have hr : (Pi.single j.castSucc r : Fin 6 → ℝ) 5 = 0 := by
    fin_cases j <;> simp
  rw [referenceContourMap, ha, hr, complexLorentzFamilyAction_single]

theorem referenceContourMap_single_radial (m B θ r : ℝ) :
    referenceContourMap m B θ (Pi.single 5 r) =
      complexShellCoordinates (radialShellContour m B θ r) := by
  have ha : activeLorentzParameters (Pi.single 5 r) = 0 := by
    ext k
    fin_cases k <;> simp [activeLorentzParameters]
  rw [referenceContourMap, ha, complexLorentzFamilyAction_zero]
  simp

/-- Continuous linear map for the reference contour derivative, of type `(Fin 6 → ℝ) →L[ℝ] (Fin 3 →
ℂ)`. -/
noncomputable def referenceContourDerivative (m B θ : ℝ) :
    (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℂ) :=
  (referenceContourTangentLinear
    (radialShellEnergy m B 0 * Real.cos θ) B (radialShellEnergy m B 0 * Real.sin θ)
    (B / radialShellEnergy m B 0 * Real.cos θ)
    (B / radialShellEnergy m B 0 * Real.sin θ)).toContinuousLinearMap

theorem referenceContourDerivative_lorentz_column (m B θ : ℝ) (j : Fin 5) :
    referenceContourDerivative m B θ (Pi.single j.castSucc 1) =
      complexShellCoordinates (lorentzParameterGenerator j.castSucc
        (radialShellContour m B θ 0)) := by
  ext i
  fin_cases j <;> fin_cases i <;>
    simp [referenceContourDerivative, referenceContourTangentLinear,
      complexShellCoordinates_apply, lorentzParameterGenerator, radialShellContour,
      Complex.ofReal_mul]

theorem referenceContourDerivative_radial_column (m B θ : ℝ) :
    referenceContourDerivative m B θ (Pi.single 5 1) =
      complexShellCoordinates
        (((B / radialShellEnergy m B 0 * Real.cos θ : ℝ) : ℂ),
          ![Complex.I * (B / radialShellEnergy m B 0 * Real.sin θ : ℝ), 1, 0]) := by
  ext i
  fin_cases i <;>
    simp [referenceContourDerivative, referenceContourTangentLinear,
      complexShellCoordinates_apply, Complex.ofReal_mul]

theorem hasFDerivAt_referenceContourMap {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    HasFDerivAt (referenceContourMap m B θ) (referenceContourDerivative m B θ) 0 := by
  apply hasFDerivAt_zero_of_coordinate_curves
    ((contDiffAt_referenceContourMap hB m θ).differentiableAt (by simp))
  intro i
  have hcoords {f : ℝ → ComplexSpacetime} {v : ComplexSpacetime}
      (h : HasDerivAt f v 0) :
      HasDerivAt (fun r => complexShellCoordinates (f r))
        (complexShellCoordinates v) 0 := by
    apply hasDerivAt_pi.mpr
    intro k
    -- Restrict scalars only after projecting to the scalar complex codomain.
    -- This avoids the competing Pi real-module structures on Fin 3 → ℂ.
    let L : ComplexSpacetime →L[ℝ] ℂ :=
      (((ContinuousLinearMap.proj k : (Fin 3 → ℂ) →L[ℂ] ℂ).comp
        complexShellCoordinates).restrictScalars ℝ)
    have hd := L.hasFDerivAt.comp_hasDerivAt 0 h
    change HasDerivAt (fun r => complexShellCoordinates (f r) k)
      (complexShellCoordinates v k) 0 at hd
    exact hd
  have hl (j : Fin 5) : HasDerivAt
      (fun r : ℝ => referenceContourMap m B θ (Pi.single j.castSucc r))
      (referenceContourDerivative m B θ (Pi.single j.castSucc 1)) 0 := by
    rw [referenceContourDerivative_lorentz_column]
    simpa only [referenceContourMap_single_lorentz, Function.comp_apply] using
      hcoords (hasDerivAt_complexLorentzParameterAction_zero j.castSucc
        (radialShellContour m B θ 0))
  have hr : HasDerivAt (fun r : ℝ => referenceContourMap m B θ (Pi.single 5 r))
      (referenceContourDerivative m B θ (Pi.single 5 1)) 0 := by
    rw [referenceContourDerivative_radial_column]
    simpa only [referenceContourMap_single_radial, Function.comp_apply] using
      hcoords (hasDerivAt_radialShellContour hB m θ)
  fin_cases i
  · exact hl 0
  · exact hl 1
  · exact hl 2
  · exact hl 3
  · exact hl 4
  · exact hr

/-- The full derivative of the literal six-parameter contour chart is bijective.
There is no positive-mass premise: B>0 excludes the cone vertex. -/
theorem referenceContourMap_derivative_bijective {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (m : ℝ) :
    Function.Bijective (fderiv ℝ (referenceContourMap m B θ) 0) := by
  rw [(hasFDerivAt_referenceContourMap hB m θ).fderiv]
  exact canonicalContourTangent_bijective (radialShellEnergy m B 0) B θ
    (radialShellEnergy_pos hB m) hB hθ

end VacuumBellSeparation
