/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ControlledContourNeighborhood
public import LeanPool.VacuumBellSeparation.Shell.ComplexShellLocalChart

/-!
# Reconstruction of the actual contour in the shell chart

The free-coordinate map comes from a point on the original complex
mass shell. Near the canonical preimage its second spatial coordinate
stays on the positive square-root branch. Both branch conditions are
proved on a genuine parameter ball, including the mass coordinate.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped Topology

/-- Full contour point obtained from `complexLorentzFamilyAction`. -/
noncomputable def fullContourPoint (m B θ : ℝ) (q : ShellContourParameters) :
    ComplexSpacetime :=
  complexLorentzFamilyAction (fullContourLorentzParameters q) (fullContourSeed m B θ q)

theorem fullContourPoint_mem_shell (m B θ : ℝ) (q : ShellContourParameters) :
    fullContourPoint m B θ q ∈ complexShell (m + q.2.1) := by
  apply complexifiedSpacetimeMap_mem_shell _ (lorentzParameterFamily_isProper _).1
  rw [fullContourSeed_eq_boost]
  exact complexShellBoost_mem_shell _ _ _

theorem fullContourPoint_zero (m B θ : ℝ) :
    fullContourPoint m B θ 0 = radialShellContour m B θ 0 := by
  have hp : fullContourLorentzParameters 0 = 0 := by ext i; fin_cases i <;> rfl
  rw [fullContourPoint, hp, complexLorentzFamilyAction_zero]
  apply Prod.ext
  · simp [fullContourSeed, radialShellContour, fullContourEnergy, radialShellEnergy]
  · ext i
    fin_cases i <;>
      simp [fullContourSeed, radialShellContour, fullContourEnergy, radialShellEnergy]

theorem contDiffAt_fullContourPoint {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    ContDiffAt ℝ ⊤ (fullContourPoint m B θ) 0 := by
  have hp : ContDiff ℝ ⊤ fullContourLorentzParameters := by
    unfold fullContourLorentzParameters
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 0)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 0).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 1)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 1).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 2)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 2).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 3)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 3).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 4)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 4).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.2.2 0)
      exact (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 0).comp (contDiff_snd.comp contDiff_snd)
  exact contDiff_complexLorentzFamilyAction.comp₂_contDiffAt
    hp.contDiffAt (contDiffAt_fullContourSeed hB m θ)

theorem fullContourPoint_chart {m B θ : ℝ} {q : ShellContourParameters}
    (hq : 0 < ((fullContourPoint m B θ q).2 1).re) :
    complexShellChart (m + q.2.1) (fullContourMap m B θ q) = fullContourPoint m B θ q :=
  complexShellChart_coordinates (fullContourPoint_mem_shell m B θ q) hq

theorem fullContourPoint_branch_ball {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    ∃ r > 0, ∀ q : ShellContourParameters, ‖q‖ < r →
      0 < ((fullContourPoint m B θ q).2 1).re ∧
      fullContourMap m B θ q ∈ complexShellChartDomain (m + q.2.1) := by
  have hc : ContinuousAt (fun q => (fullContourPoint m B θ q).2 1) 0 :=
    (continuous_apply (1 : Fin 3)).continuousAt.comp
      (contDiffAt_fullContourPoint hB m θ).continuousAt.snd
  have h0 : (fullContourPoint m B θ 0).2 1 = (B : ℂ) := by
    rw [fullContourPoint_zero]
    simp [radialShellContour]
  have hp : 0 < ((fullContourPoint m B θ 0).2 1).re := by simpa [h0] using hB
  have hs : 0 < (((fullContourPoint m B θ 0).2 1) ^ 2).re := by
    simpa [h0, ← Complex.ofReal_pow] using sq_pos_of_pos hB
  have hcr : ContinuousAt (fun q => ((fullContourPoint m B θ q).2 1).re) 0 :=
    Complex.continuous_re.continuousAt.comp hc
  have hcsr : ContinuousAt (fun q => (((fullContourPoint m B θ q).2 1) ^ 2).re) 0 :=
    Complex.continuous_re.continuousAt.comp (hc.pow 2)
  have hall : ∀ᶠ q in 𝓝 (0 : ShellContourParameters),
      0 < ((fullContourPoint m B θ q).2 1).re ∧
      0 < (((fullContourPoint m B θ q).2 1) ^ 2).re := by
    filter_upwards [continuousAt_const.eventually_lt hcr hp,
      continuousAt_const.eventually_lt hcsr hs] with q hqp hqs
    exact ⟨hqp, hqs⟩
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r, hr, fun q hq => ?_⟩
  have h := hh (by simpa only [dist_zero_right] using hq)
  refine ⟨h.1, ?_⟩
  change 0 < (complexShellRadicand (m + q.2.1)
    (complexShellCoordinates (fullContourPoint m B θ q))).re
  rw [complexShellRadicand_coordinates (fullContourPoint_mem_shell m B θ q)]
  exact h.2

theorem fullContourPoint_prefixed (Λ : Spacetime ≃L[ℝ] Spacetime)
    (m B θ : ℝ) (q : ShellContourParameters) :
    complexifiedSpacetimeMap Λ (fullContourPoint m B θ q) =
      complexifiedSpacetimeMap (fullContourLorentzMap Λ q)
        (complexShellBoost (m + q.2.1) ((θ : ℂ) * Complex.I) (fullContourMomentum B q)) := by
  rw [fullContourLorentzMap, complexifiedSpacetimeMap_trans]
  change complexifiedSpacetimeMap Λ
      (complexLorentzFamilyAction _ (fullContourSeed m B θ q)) = _
  rw [fullContourSeed_eq_boost]
  rfl

theorem lorentzComplexShellChart_fullContourMap (Λ : Spacetime ≃L[ℝ] Spacetime)
    {m B θ : ℝ} {q : ShellContourParameters}
    (hq : 0 < ((fullContourPoint m B θ q).2 1).re) :
    lorentzComplexShellChart (m + q.2.1) Λ (fullContourMap m B θ q) =
      complexifiedSpacetimeMap (fullContourLorentzMap Λ q)
        (complexShellBoost (m + q.2.1) ((θ : ℂ) * Complex.I) (fullContourMomentum B q)) := by
  rw [lorentzComplexShellChart, fullContourPoint_chart hq, fullContourPoint_prefixed]

end VacuumBellSeparation
