/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ComplexLorentzParameters

/-! # Smoothness of the actual complexified six-parameter Lorentz family -/

@[expose] public section

namespace VacuumBellSeparation

/-- Complex Lorentz family action obtained from `complexifiedSpacetimeMap`. -/
noncomputable def complexLorentzFamilyAction (s : Fin 6 → ℝ)
    (z : ComplexSpacetime) : ComplexSpacetime :=
  complexifiedSpacetimeMap (lorentzParameterFamily s) z

theorem complexLorentzFamilyAction_factors (s : Fin 6 → ℝ) (z : ComplexSpacetime) :
    complexLorentzFamilyAction s z =
      complexLorentzParameterAction 5 (s 5)
        (complexLorentzParameterAction 4 (s 4)
          (complexLorentzParameterAction 3 (s 3)
            (complexLorentzParameterAction 2 (s 2)
              (complexLorentzParameterAction 1 (s 1)
                (complexLorentzParameterAction 0 (s 0) z))))) := by
  simp only [complexLorentzFamilyAction, lorentzParameterFamily,
    complexifiedSpacetimeMap_trans, complexified_lorentzParameterFactor]

theorem contDiff_complexLorentzFamilyAction :
    ContDiff ℝ ⊤ (fun q : (Fin 6 → ℝ) × ComplexSpacetime =>
      complexLorentzFamilyAction q.1 q.2) := by
  have hs (j : Fin 6) : ContDiff ℝ ⊤
      (fun q : (Fin 6 → ℝ) × ComplexSpacetime => q.1 j) :=
    (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) j).comp contDiff_fst
  have step (j : Fin 6)
      (z : ((Fin 6 → ℝ) × ComplexSpacetime) → ComplexSpacetime)
      (hz : ContDiff ℝ ⊤ z) :
      ContDiff ℝ ⊤ (fun q => complexLorentzParameterAction j (q.1 j) (z q)) := by
    exact (contDiff_complexLorentzParameterAction j).comp₂ (hs j) hz
  simp only [complexLorentzFamilyAction_factors]
  apply step 5
  apply step 4
  apply step 3
  apply step 2
  apply step 1
  apply step 0
  exact contDiff_snd

theorem complexLorentzFamilyAction_zero (z : ComplexSpacetime) :
    complexLorentzFamilyAction 0 z = z := by
  rw [complexLorentzFamilyAction_factors]
  apply Prod.ext
  · simp [complexLorentzParameterAction]
  · ext i
    fin_cases i <;> simp [complexLorentzParameterAction]

theorem lorentzParameterFamily_single (j : Fin 6) (r : ℝ) :
    lorentzParameterFamily (Pi.single j r) = lorentzParameterFactor j r := by
  apply ContinuousLinearEquiv.ext
  funext x
  fin_cases j <;> simp [lorentzParameterFamily, lorentzParameterFactor_zero]

theorem complexLorentzFamilyAction_single (j : Fin 6) (r : ℝ)
    (z : ComplexSpacetime) :
    complexLorentzFamilyAction (Pi.single j r) z = complexLorentzParameterAction j r z := by
  rw [complexLorentzFamilyAction, lorentzParameterFamily_single,
    complexified_lorentzParameterFactor]

end VacuumBellSeparation
