/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Domination.Ball
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Ball averages of finite-dimensional measures

Compact subsets of the support have a uniform positive lower bound on fixed-radius ball
masses. This is a local measure lemma; it does not assert that the measure has a density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set Topology

namespace FunctionalInequalities.Probability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [BorelSpace E] in
/-- On a compact subset of the support, every fixed-radius open ball has mass bounded
below by the same positive number. No absolute continuity is required. -/
theorem exists_pos_le_measure_ball_on_isCompact (μ : Measure E) {K : Set E} (hK : IsCompact K)
    (hKs : K ⊆ μ.support) (r : ℝ) (hr : 0 < r) :
    ∃ c : ENNReal, 0 < c ∧ ∀ y ∈ K, c ≤ μ (ball y r) := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨s, hs⟩ :=
      hK.elim_finite_subcover (fun y : K => ball (y : E) (r / 2)) (fun _ => isOpen_ball)
        (by
          intro y hy
          exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (by linarith)⟩)
    have hcover (y : E) (hy : y ∈ K) : ∃ i ∈ s, dist y (i : E) < r / 2 := by
      simpa only [mem_iUnion, mem_ball, exists_prop] using hs hy
    have hsne : s.Nonempty := by
      obtain ⟨y, hy⟩ := hne
      obtain ⟨i, hi, _⟩ := hcover y hy
      exact ⟨i, hi⟩
    let c := s.inf' hsne (fun y : K => μ (ball (y : E) (r / 2)))
    refine ⟨c, ?_, ?_⟩
    · apply (Finset.lt_inf'_iff hsne).mpr
      intro y _
      exact
        (Measure.mem_support_iff_forall (y : E)).mp (hKs y.property) _
          (ball_mem_nhds _ (by linarith))
    · intro y hy
      obtain ⟨i, his, hiy⟩ := hcover y hy
      refine (Finset.inf'_le _ his).trans (measure_mono ?_)
      intro z hz
      apply mem_ball.mpr
      calc
        dist z y ≤ dist z (i : E) + dist (i : E) y := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add (mem_ball.mp hz) (by simpa only [dist_comm] using hiy)
        _ = r := by ring
  · exact ⟨1, zero_lt_one, fun y hy => (hne ⟨y, hy⟩).elim⟩

variable [FiniteDimensional ℝ E] [SecondCountableTopology E]

/-- The unnormalized ball-average kernel preserves total mass under Haar integration. -/
theorem lintegral_measure_closedBall (μ m : Measure E) [SFinite μ] [Measure.IsAddHaarMeasure m]
    (r : ℝ) : (∫⁻ x, μ (closedBall x r) ∂m) = m (closedBall (0 : E) r) * μ Set.univ := by
  let F : E × E → ENNReal := {p | dist p.1 p.2 ≤ r}.indicator (fun _ => 1)
  have hF : Measurable F :=
    measurable_const.indicator (isClosed_le continuous_dist continuous_const).measurableSet
  have hxy (x y : E) : F (x, y) = (closedBall x r).indicator (fun _ => (1 : ENNReal)) y := by
    change (if dist x y ≤ r then 1 else 0) = (if dist y x ≤ r then 1 else 0)
    rw [dist_comm]
  have hyx (x y : E) : F (x, y) = (closedBall y r).indicator (fun _ => (1 : ENNReal)) x := by
    rfl
  calc
    _ = ∫⁻ x, ∫⁻ y, F (x, y) ∂μ ∂m := by
      congr 1; funext x
      simp_rw [hxy]
      convert!
        (lintegral_indicator_one (μ := μ) (s := closedBall x r)
            measurableSet_closedBall).symm using
        1
    _ = ∫⁻ y, ∫⁻ x, F (x, y) ∂m ∂μ := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ y, m (closedBall y r) ∂μ := by
      congr 1; funext y
      simp_rw [hyx]
      convert!
        (lintegral_indicator_one (μ := m) (s := closedBall y r) measurableSet_closedBall) using
        1
    _ = _ := by simp only [Measure.addHaar_closedBall_center m, lintegral_const]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Tonelli symmetry for the closed-ball incidence kernel. -/
theorem lintegral_measure_closedBall_swap (μ m : Measure E) [SFinite μ] [SFinite m] (r : ℝ) :
    (∫⁻ x, μ (closedBall x r) ∂m) = ∫⁻ y, m (closedBall y r) ∂μ := by
  let F : E × E → ENNReal := {p | dist p.1 p.2 ≤ r}.indicator (fun _ => 1)
  have hF : Measurable F :=
    measurable_const.indicator (isClosed_le continuous_dist continuous_const).measurableSet
  have hxy (x y : E) : F (x, y) = (closedBall x r).indicator (fun _ => (1 : ENNReal)) y := by
    change (if dist x y ≤ r then 1 else 0) = (if dist y x ≤ r then 1 else 0)
    rw [dist_comm]
  have hyx (x y : E) : F (x, y) = (closedBall y r).indicator (fun _ => (1 : ENNReal)) x := rfl
  calc
    _ = ∫⁻ x, ∫⁻ y, F (x, y) ∂μ ∂m := by
      congr 1; funext x
      simp_rw [hxy]
      convert!
        (lintegral_indicator_one (μ := μ) (s := closedBall x r)
            measurableSet_closedBall).symm using
        1
    _ = ∫⁻ y, ∫⁻ x, F (x, y) ∂m ∂μ := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      congr 1; funext y
      simp_rw [hyx]
      convert!
        (lintegral_indicator_one (μ := m) (s := closedBall y r) measurableSet_closedBall) using
        1

/-- Mass in an inner ball contributes its entire small-ball average to a larger ball. -/
theorem measure_ball_mul_closedBall_le_lintegral (μ m : Measure E) [SFinite μ]
    [Measure.IsAddHaarMeasure m] (y : E) {δ r : ℝ} (hr : r ≤ δ) :
    m (closedBall (0 : E) r) * μ (ball y δ) ≤ ∫⁻ z in ball y (2 * δ), μ (closedBall z r) ∂m := by
  rw [lintegral_measure_closedBall_swap]
  calc
    _ = ∫⁻ w, (ball y δ).indicator (fun _ => m (closedBall (0 : E) r)) w ∂μ := by
      simp only [lintegral_indicator measurableSet_ball, lintegral_const,
        Measure.restrict_apply_univ]
    _ ≤ _ := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ ball y δ
      · simp only [indicator_of_mem hw]
        rw [Measure.restrict_apply measurableSet_closedBall]
        have hsub : closedBall w r ⊆ ball y (2 * δ) := by
          intro z hz
          apply mem_ball.mpr
          calc
            dist z y ≤ dist z w + dist w y := dist_triangle _ _ _
            _ < r + δ := add_lt_add_of_le_of_lt (mem_closedBall.mp hz) (mem_ball.mp hw)
            _ ≤ 2 * δ := by linarith
        simp only [inter_eq_left.mpr hsub, Measure.addHaar_closedBall_center m, le_refl]
      · simp only [indicator_of_notMem hw, zero_le]

end FunctionalInequalities.Probability
