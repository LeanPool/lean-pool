/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.LocalInducedVolumeComparison
public import LeanPool.VacuumBellSeparation.Shell.UniformLocalShellDensity

/-! # Open chart neighbourhoods in the mass-shell family -/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Metric Set

/-- Ambient shell coordinates defined as `shellEuclideanCoordinates.symm
(lorentzComplexShellCoordinates Λ z)`. -/
noncomputable def ambientShellCoordinates (Λ : Spacetime ≃L[ℝ] Spacetime)
    (z : ComplexSpacetime) : ShellEuclideanDomain :=
  shellEuclideanCoordinates.symm (lorentzComplexShellCoordinates Λ z)

theorem continuous_ambientShellCoordinates (Λ : Spacetime ≃L[ℝ] Spacetime) :
    Continuous (ambientShellCoordinates Λ) :=
  shellEuclideanCoordinates.symm.continuous.comp (lorentzComplexShellCoordinates Λ).continuous

/-- Local shell coordinate set. -/
noncomputable def localShellCoordinateSet (t : ℝ) (w : Fin 3 → ℂ) (δ ε : ℝ) :
    Set ShellEuclideanDomain :=
  euclideanShellChartDomain t ∩
    (shellEuclideanCoordinates ⁻¹' ball w δ) ∩
      ball (shellEuclideanCoordinates.symm w) ε

theorem isOpen_localShellCoordinateSet (t : ℝ) (w : Fin 3 → ℂ) (δ ε : ℝ) :
    IsOpen (localShellCoordinateSet t w δ ε) :=
  ((isOpen_euclideanShellChartDomain t).inter
    (isOpen_ball.preimage shellEuclideanCoordinates.continuous)).inter isOpen_ball

/-- Set of points satisfying the regular shell family neighborhood condition. -/
def regularShellFamilyNeighborhood (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (w : Fin 3 → ℂ) (δ ε : ℝ) : Set (ℝ × ComplexSpacetime) :=
  {q | |q.1 - m| < min δ ε ∧
    0 < ((complexifiedSpacetimeMap Λ.symm q.2).2 1).re ∧
    ambientShellCoordinates Λ q.2 ∈ localShellCoordinateSet q.1 w δ ε}

theorem isOpen_regularShellFamilyNeighborhood (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (w : Fin 3 → ℂ) (δ ε : ℝ) :
    IsOpen (regularShellFamilyNeighborhood m Λ w δ ε) := by
  have hcoord : Continuous (fun q : ℝ × ComplexSpacetime =>
      ambientShellCoordinates Λ q.2) := (continuous_ambientShellCoordinates Λ).comp continuous_snd
  have hD : IsOpen {q : ℝ × ComplexSpacetime |
      ambientShellCoordinates Λ q.2 ∈ euclideanShellChartDomain q.1} :=
    isOpen_euclideanShellJointDomain.preimage (continuous_fst.prodMk hcoord)
  have hf : IsOpen {q : ℝ × ComplexSpacetime |
      shellEuclideanCoordinates (ambientShellCoordinates Λ q.2) ∈ ball w δ} :=
    isOpen_ball.preimage (shellEuclideanCoordinates.continuous.comp hcoord)
  have he : IsOpen {q : ℝ × ComplexSpacetime |
      ambientShellCoordinates Λ q.2 ∈ ball (shellEuclideanCoordinates.symm w) ε} :=
    isOpen_ball.preimage hcoord
  have hmass : IsOpen {q : ℝ × ComplexSpacetime | |q.1 - m| < min δ ε} :=
    isOpen_lt (by fun_prop) continuous_const
  have hsign : IsOpen {q : ℝ × ComplexSpacetime |
      0 < ((complexifiedSpacetimeMap Λ.symm q.2).2 1).re} :=
    isOpen_lt continuous_const (by fun_prop)
  exact hmass.inter (hsign.inter ((hD.inter hf).inter he))

theorem regularShellFamilyNeighborhood_fiber {m t δ ε : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) (w : Fin 3 → ℂ)
    (ht : |t - m| < min δ ε) :
    {z : complexShell t | (t, z.1) ∈ regularShellFamilyNeighborhood m Λ w δ ε} =
      regularShellCoordinatePatch t Λ (localShellCoordinateSet t w δ ε) := by
  ext z
  simp only [regularShellFamilyNeighborhood, mem_ofPred_eq, ht, true_and,
    regularShellCoordinatePatch, mem_inter_iff, mem_preimage,
    inducedShellPatch, localShellCoordinateSet, ambientShellCoordinates, shellPatchCoordinates]
  tauto

theorem regularShellFamilyNeighborhood_fiber_empty {m t δ ε : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) (w : Fin 3 → ℂ)
    (ht : ¬ |t - m| < min δ ε) :
    {z : complexShell t | (t, z.1) ∈ regularShellFamilyNeighborhood m Λ w δ ε} = ∅ := by
  ext z
  simp only [regularShellFamilyNeighborhood, mem_ofPred_eq, ht, false_and, mem_empty_iff_false]

theorem regularShellFamilyNeighborhood_mem_center {m δ ε : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {z : ComplexSpacetime}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hz : 0 < ((complexifiedSpacetimeMap Λ.symm z).2 1).re)
    (hw : lorentzComplexShellCoordinates Λ z ∈ complexShellChartDomain m) :
    (m, z) ∈ regularShellFamilyNeighborhood m Λ
      (lorentzComplexShellCoordinates Λ z) δ ε := by
  refine ⟨by simpa using lt_min hδ hε, hz, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [ambientShellCoordinates, euclideanShellChartDomain] using hw
  · simp [ambientShellCoordinates, hδ]
  · exact mem_ball_self (x := ambientShellCoordinates Λ z) hε

end VacuumBellSeparation
