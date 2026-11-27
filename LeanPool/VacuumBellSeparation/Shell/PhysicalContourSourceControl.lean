/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourDensity
public import LeanPool.VacuumBellSeparation.Shell.FixedMassContourImage
public import LeanPool.VacuumBellSeparation.Shell.FullContourPoint

/-! # Physical parameter images and their actual local controls -/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

theorem norm_fullContourLorentzParameters_le (q : ShellContourParameters) :
    ‖fullContourLorentzParameters q‖ ≤ ‖q‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
  intro i
  have ha (j : Fin 6) : ‖q.1 j‖ ≤ ‖q‖ :=
    (norm_le_pi_norm q.1 j).trans (norm_fst_le q)
  have hn : ‖q.2.2 0‖ ≤ ‖q‖ :=
    (norm_le_pi_norm q.2.2 0).trans ((norm_snd_le q.2).trans (norm_snd_le q))
  fin_cases i
  · exact ha 0
  · exact ha 1
  · exact ha 2
  · exact ha 3
  · exact ha 4
  · exact hn

/-- Physical contour homeomorph defined as `contourParameterReorder.toHomeomorph.trans
(Homeomorph.addRight (0, WithLp.toLp 2 ![0, B, 0]))`. -/
noncomputable def physicalContourHomeomorph (B : ℝ) :
    ShellPhysicalParameters ≃ₜ LorentzMomentumParameters :=
  contourParameterReorder.toHomeomorph.trans
    (Homeomorph.addRight (0, WithLp.toLp 2 ![0, B, 0]))

theorem physicalContourHomeomorph_apply (B : ℝ) (q : ShellPhysicalParameters) :
    physicalContourHomeomorph B q = physicalContourParameters B q := rfl

theorem isOpen_physicalContourSmallImage (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (r τ : ℝ) :
    IsOpen (physicalContourParameters B '' fixedMassContourSmallDomain m hB hθ r τ) :=
  (physicalContourHomeomorph B).isOpenMap _
    (isOpen_fixedMassContourSmallDomain m hB hθ r τ)

theorem physicalContourSmallImage_control (m : ℝ) {B θ r ρ R : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (hrρ : r ≤ ρ / 2)
    (henergy : ∀ q : ShellContourParameters, ‖q‖ < r →
      0 < fullContourEnergy m B q ∧ fullContourEnergy m B q ≤ R)
    (τ : ℝ) :
    ∀ y ∈ physicalContourParameters B '' fixedMassContourSmallDomain m hB hθ r τ,
      ‖y.1‖ ≤ ρ / 2 ∧ 0 < dispersion (m + τ) y.2 ∧ dispersion (m + τ) y.2 ≤ R := by
  rintro y ⟨q, hq, rfl⟩
  have he := henergy (fixedMassContourEmbedding τ q) hq.2
  rw [physicalContourParameters_lorentz B τ, physicalContourParameters_momentum B τ]
  refine ⟨(norm_fullContourLorentzParameters_le _).trans (hq.2.le.trans hrρ), ?_⟩
  simpa only [fullContourEnergy_eq_dispersion, fixedMassContourEmbedding] using he

theorem physicalContourSmallImage_chart_identity (m : ℝ) {B θ r : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ)
    (hbranch : ∀ q : ShellContourParameters, ‖q‖ < r →
      0 < ((fullContourPoint m B θ q).2 1).re)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (τ : ℝ)
    {q : ShellPhysicalParameters} (hq : q ∈ fixedMassContourSmallDomain m hB hθ r τ) :
    lorentzComplexShellChart (m + τ) Λ
        (fullContourMap m B θ (fixedMassContourEmbedding τ q)) =
      complexifiedSpacetimeMap
        ((lorentzParameterFamily (physicalContourParameters B q).1).trans Λ)
        (complexShellBoost (m + τ) ((θ : ℂ) * Complex.I) (physicalContourParameters B q).2) := by
  rw [physicalContourParameters_lorentz B τ, physicalContourParameters_momentum B τ]
  exact lorentzComplexShellChart_fullContourMap Λ (hbranch _ hq.2)

end VacuumBellSeparation
