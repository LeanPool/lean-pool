/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov.Perturbation
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.ProjectionLimit

/-!
# BesovCongr

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Almost-everywhere congruence for the positive `q = 2` Besov quantities

The frozen `D_h` statement speaks about the *actual* coefficient fields, while
every regularity estimate available for them is proved for a Lipschitz
representative that agrees with the field only almost everywhere.  All the
positive Besov quantities are built from `cubeLpNorm` and `cubeAverage`, both
integral quantities, so they are insensitive to a.e. modification.  This module
records that insensitivity once.

The only nontrivial step is that a.e. equality on a parent cube descends to
every descendant cube, which follows from
`normalizedCubeMeasure_descendant_eq_smul_restrict`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open HCPolySupport MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The normalized cube measure and the restricted volume have the same
null sets -/

theorem ae_normalizedCubeMeasure_of_ae_cubeMeasure {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) {f g : Vec d → E}
    (h : f =ᵐ[volumeMeasureOn (cubeSet Q)] g) :
    f =ᵐ[normalizedCubeMeasure Q] g := by
  rw [normalizedCubeMeasure]
  exact MeasureTheory.Measure.ae_smul_measure h _

/-- An a.e. identity on a parent cube holds a.e. on every descendant cube. -/
theorem ae_eq_on_descendant {E : Type*} [NormedAddCommGroup E]
    {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    {f g : Vec d → E} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    f =ᵐ[normalizedCubeMeasure R] g := by
  rw [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
  exact MeasureTheory.Measure.ae_smul_measure (MeasureTheory.ae_restrict_of_ae h) _

/-! ## Congruence of the basic normalized quantities -/

theorem cubeLpNorm_congr_ae {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) {f g : Vec d → E}
    (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeLpNorm Q p f = cubeLpNorm Q p g := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae h]

theorem cubeAverage_congr_ae (Q : TriadicCube d) {f g : Vec d → ℝ}
    (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeAverage Q f = cubeAverage Q g := by
  have h' : f =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] g := by
    have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.mpr (cubeVolume_pos Q)
    have h2 : ∀ᵐ x ∂(ENNReal.ofReal ((cubeVolume Q)⁻¹) •
        MeasureTheory.volume.restrict (cubeSet Q)), f x = g x := h
    exact (MeasureTheory.Measure.ae_ennreal_smul_measure_iff hc).mp h2
  unfold cubeAverage
  rw [MeasureTheory.integral_congr_ae h']

theorem cubeAverageVec_congr_ae (Q : TriadicCube d) {f g : Vec d → Vec d}
    (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeAverageVec Q f = cubeAverageVec Q g := by
  funext i
  refine cubeAverage_congr_ae Q ?_
  filter_upwards [h] with x hx using congrFun hx i

theorem cubeFluctuationVec_congr_ae (Q : TriadicCube d) {f g : Vec d → Vec d}
    (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeFluctuationVec Q f =ᵐ[normalizedCubeMeasure Q] cubeFluctuationVec Q g := by
  have havg : cubeAverageVec Q f = cubeAverageVec Q g := cubeAverageVec_congr_ae Q h
  filter_upwards [h] with x hx
  simp [cubeFluctuationVec, hx, havg]

/-! ## Congruence of the vector positive Besov quantities -/

theorem cubeBesovPositiveVectorDepthAverage_congr_ae (Q : TriadicCube d) (j : ℕ)
    {f g : Vec d → Vec d} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeBesovPositiveVectorDepthAverage Q f j =
      cubeBesovPositiveVectorDepthAverage Q g j := by
  have hpt : ∀ R ∈ descendantsAtDepth Q j,
      (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R f)) ^ 2 =
        (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g)) ^ 2 := by
    intro R hR
    rw [cubeLpNorm_congr_ae R (2 : ℝ≥0∞)
      (cubeFluctuationVec_congr_ae R (ae_eq_on_descendant hR h))]
  unfold cubeBesovPositiveVectorDepthAverage
  refine le_antisymm ?_ ?_
  · exact descendantsAverage_le_descendantsAverage Q j fun R hR => (hpt R hR).le
  · exact descendantsAverage_le_descendantsAverage Q j fun R hR => (hpt R hR).ge

theorem cubeBesovPositiveVectorDepthSeminorm_congr_ae (Q : TriadicCube d) (s : ℝ)
    (j : ℕ) {f g : Vec d → Vec d} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeBesovPositiveVectorDepthSeminorm Q s f j =
      cubeBesovPositiveVectorDepthSeminorm Q s g j := by
  unfold cubeBesovPositiveVectorDepthSeminorm
  rw [cubeBesovPositiveVectorDepthAverage_congr_ae Q j h]

theorem cubeBesovPositiveVectorPartialSeminormTwo_congr_ae (Q : TriadicCube d)
    (s : ℝ) (N : ℕ) {f g : Vec d → Vec d} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N f =
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun j _ => ?_)
  rw [cubeBesovPositiveVectorDepthSeminorm_congr_ae Q s j h]

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
