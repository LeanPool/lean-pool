/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellMassContinuity
public import LeanPool.VacuumBellSeparation.Shell.InducedShellPatchCoordinates

/-!
# Actual uniform chart balls in an ambient open shell neighbourhood

Joint mass-coordinate continuity supplies a radius and a positive Gram
lower bound before the nearby mass or target is chosen. The moving
center is the genuine linear chart coordinate of the target; the
positive-root branch and reconstruction are proved on an open set.
-/

@[expose] public section

namespace VacuumBellSeparation

open Metric Set Filter
open scoped Topology

/-- Continuous linear map for the shell ambient coordinates, of type `ComplexSpacetime →L[ℂ]
ShellEuclideanDomain`. -/
noncomputable def shellAmbientCoordinates (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ComplexSpacetime →L[ℂ] ShellEuclideanDomain :=
  shellEuclideanCoordinates.symm.toContinuousLinearMap.comp (lorentzComplexShellCoordinates Λ)

theorem shellAmbientCoordinates_chart (t : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (w : ShellEuclideanDomain) :
    shellAmbientCoordinates Λ
      (lorentzComplexShellChart t Λ (shellEuclideanCoordinates w)) = w := by
  simp only [shellAmbientCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, lorentzComplexShellCoordinates_chart,
    ContinuousLinearEquiv.symm_apply_apply]

theorem shell_submean_local_neighborhood {t₀ : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    {w₀ : ShellEuclideanDomain} (hw₀ : w₀ ∈ euclideanShellChartDomain t₀)
    {V : Set (ℝ × ComplexSpacetime)} (hV : IsOpen V)
    (hv₀ : (t₀, lorentzComplexShellChart t₀ Λ (shellEuclideanCoordinates w₀)) ∈ V) :
    ∃ W : Set (ℝ × ComplexSpacetime), IsOpen W ∧
      (t₀, lorentzComplexShellChart t₀ Λ (shellEuclideanCoordinates w₀)) ∈ W ∧
      ∃ R d : ℝ, 0 < R ∧ 0 < d ∧
        ∀ t z, (t, z) ∈ W → z ∈ complexShell t →
          lorentzComplexShellChart t Λ (shellEuclideanCoordinates
            (shellAmbientCoordinates Λ z)) = z ∧
          ∀ w ∈ ball (shellAmbientCoordinates Λ z) (2 * R),
            w ∈ euclideanShellChartDomain t ∧ d ≤ inducedShellChartDensity t Λ w ∧
            (t, lorentzComplexShellChart t Λ (shellEuclideanCoordinates w)) ∈ V := by
  let q₀ : ℝ × ShellEuclideanDomain := (t₀, w₀)
  let z₀ := lorentzComplexShellChart t₀ Λ (shellEuclideanCoordinates w₀)
  let d := inducedShellChartDensity t₀ Λ w₀ / 2
  have hd : 0 < d := half_pos (inducedShellChartDensity_pos Λ hw₀)
  have hJ : ContinuousAt (fun q : ℝ × ShellEuclideanDomain =>
      inducedShellChartDensity q.1 Λ q.2) q₀ :=
    (continuousOn_inducedShellChartDensity_joint Λ q₀ hw₀).continuousAt
      (isOpen_euclideanShellJointDomain.mem_nhds hw₀)
  have hchart : ContinuousAt (fun q : ℝ × ShellEuclideanDomain =>
      euclideanLorentzShellChart q.1 Λ q.2) q₀ :=
    ((contDiffOn_euclideanLorentzShellChart_joint Λ).continuousOn q₀ hw₀).continuousAt
      (isOpen_euclideanShellJointDomain.mem_nhds hw₀)
  have hF : ContinuousAt (fun q : ℝ × ShellEuclideanDomain =>
      (q.1, lorentzComplexShellChart q.1 Λ (shellEuclideanCoordinates q.2))) q₀ := by
    have h := continuous_fst.continuousAt.prodMk
      (complexSpacetimeEuclideanEquiv.symm.continuousAt.comp hchart)
    simpa only [euclideanLorentzShellChart, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using h
  have hdlt : d < inducedShellChartDensity q₀.1 Λ q₀.2 := by
    change inducedShellChartDensity t₀ Λ w₀ / 2 < inducedShellChartDensity t₀ Λ w₀
    exact half_lt_self (inducedShellChartDensity_pos Λ hw₀)
  have hJN : ∀ᶠ q in 𝓝 q₀, d < inducedShellChartDensity q.1 Λ q.2 :=
    hJ (isOpen_Ioi.mem_nhds hdlt)
  have hFN := hF (hV.mem_nhds hv₀)
  have hN : {q : ℝ × ShellEuclideanDomain | q ∈ euclideanShellJointDomain ∧
      d ≤ inducedShellChartDensity q.1 Λ q.2 ∧
      (q.1, lorentzComplexShellChart q.1 Λ (shellEuclideanCoordinates q.2)) ∈ V} ∈ 𝓝 q₀ := by
    filter_upwards [isOpen_euclideanShellJointDomain.mem_nhds hw₀, hJN, hFN] with q hq hj hv
    exact ⟨hq, hj.le, hv⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hN
  let W : Set (ℝ × ComplexSpacetime) := {p |
    dist p.1 t₀ < ε / 4 ∧ dist (shellAmbientCoordinates Λ p.2) w₀ < ε / 4 ∧
      0 < ((complexifiedSpacetimeMap Λ.symm p.2).2 1).re}
  have hW : IsOpen W := by
    have hsign : Continuous (fun p : ℝ × ComplexSpacetime =>
        ((complexifiedSpacetimeMap Λ.symm p.2).2 1).re) :=
      Complex.continuous_re.comp ((continuous_apply (1 : Fin 3)).comp
        (((complexifiedSpacetimeMap Λ.symm).continuous.comp continuous_snd).snd))
    change IsOpen ({p : ℝ × ComplexSpacetime | dist p.1 t₀ < ε / 4} ∩
      ({p : ℝ × ComplexSpacetime | dist (shellAmbientCoordinates Λ p.2) w₀ < ε / 4} ∩
        {p : ℝ × ComplexSpacetime | 0 < ((complexifiedSpacetimeMap Λ.symm p.2).2 1).re}))
    exact (isOpen_lt (continuous_fst.dist continuous_const) continuous_const).inter
      ((isOpen_lt (((shellAmbientCoordinates Λ).continuous.comp continuous_snd).dist
        continuous_const) continuous_const).inter (isOpen_lt continuous_const hsign))
  have hz₀ : 0 < ((complexifiedSpacetimeMap Λ.symm z₀).2 1).re := by
    dsimp only [z₀, lorentzComplexShellChart]
    rw [complexifiedSpacetimeMap_inverse]
    exact complexShellChart_second_re_pos hw₀
  refine ⟨W, hW, ?_, ε / 8, d, by positivity, hd, ?_⟩
  · change dist t₀ t₀ < ε / 4 ∧
      dist (shellAmbientCoordinates Λ z₀) w₀ < ε / 4 ∧ _
    rw [show shellAmbientCoordinates Λ z₀ = w₀ from shellAmbientCoordinates_chart t₀ Λ w₀]
    exact ⟨by simpa using (show 0 < ε / 4 by positivity),
      by simpa using (show 0 < ε / 4 by positivity), hz₀⟩
  · intro t z hp hz
    constructor
    · simpa only [shellAmbientCoordinates, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
        lorentzComplexShellChart_reconstruct Λ hΛ hz hp.2.2
    · intro w hw
      have htw : (t, w) ∈ ball q₀ ε := by
        rw [mem_ball, Prod.dist_eq, max_lt_iff]
        constructor
        · exact hp.1.trans (by linarith)
        · have hw' : dist w (shellAmbientCoordinates Λ z) < 2 * (ε / 8) := hw
          have ht := dist_triangle w (shellAmbientCoordinates Λ z) w₀
          change dist w w₀ < ε
          linarith [hp.2.1]
      have hq := hεsub htw
      exact ⟨hq.1, hq.2.1, hq.2.2⟩

end VacuumBellSeparation
