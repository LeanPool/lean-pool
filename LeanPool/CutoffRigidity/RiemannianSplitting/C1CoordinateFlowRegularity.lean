/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.C1CoordinateFlowDerivative
public import LeanPool.CutoffRigidity.RiemannianSplitting.LinearVariationContinuity

/-! # C¹ initial-point regularity of genuine coordinate ODE families
Actual linear variations are constructed, identified with actual Fréchet
derivatives, and proved continuous from the actual coefficient equations.
-/

@[expose] public section
open Set Filter Metric Function
open scoped Topology NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- On a short window, an actual Picard family has C¹ time slices. Coefficient
bounds concern the actual vector field; neither differentiability nor
continuity of the derivative of the solution map is a premise. -/
theorem contDiffOn_coordinateFlow_short_of_bound
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x₀ : E) {r T : ℝ} (_hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ closedBall x₀ r, α y 0 = y)
    (hαD : ∀ y ∈ closedBall x₀ r, ∀ s ∈ Icc (-T) T,
      HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y s) (closedBall x₀ r))
    (hαC : ContinuousOn (uncurry α) (closedBall x₀ r ×ˢ Icc (-T) T))
    {M : ℝ≥0} (hM : ∀ y ∈ closedBall x₀ r, ∀ s ∈ Icc (-T) T,
      ‖fderiv ℝ F (α y s)‖ ≤ M)
    (hshort : 2 * (M : ℝ) * T ≤ 1) {t : ℝ} (ht : t ∈ Icc 0 (T / 2)) :
    ContDiffOn ℝ 1 (fun y ↦ α y t) (ball x₀ r) := by
  classical
  let S := closedBall x₀ r
  have hex (p : E) (hp : p ∈ S) : ∃ J : ℝ → E →L[ℝ] E,
      J 0 = ContinuousLinearMap.id ℝ E ∧ ContinuousOn J (Icc (-T) T) ∧
      ∀ s ∈ Icc (-T) T,
        HasDerivWithinAt J ((fderiv ℝ F (α p s)).comp (J s)) (Icc (-T) T) s := by
    apply exists_linear_variation_short_interval hT.le _ (hM p hp) hshort
    exact (hF.continuous_fderiv one_ne_zero).comp_continuousOn
      (fun s hs ↦ (hαD p hp s hs).continuousAt.continuousWithinAt)
  choose J hJzero hJC hJD using hex
  let j : E → ℝ → E →L[ℝ] E := fun p ↦
    if hp : p ∈ S then J p hp else fun _ ↦ ContinuousLinearMap.id ℝ E
  have hjzero (p : E) (hp : p ∈ S) : j p 0 = ContinuousLinearMap.id ℝ E := by
    simpa only [j, dite_eq_left hp] using hJzero p hp
  have hsub : Icc 0 t ⊆ Icc (-T) T := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2, ht.2]
  have hjD (p : E) (hp : p ∈ S) (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt (j p) ((fderiv ℝ F (α p s)).comp (j p s)) s := by
    have hsT : s ∈ Ioo (-T) T := by
      constructor <;> linarith [hs.1, hs.2, ht.2]
    simpa only [j, dite_eq_left hp] using
      (hJD p hp s (Ioo_subset_Icc_self hsT)).hasDerivAt (Icc_mem_nhds hsT.1 hsT.2)
  have hJA : ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ F (α p.1 p.2)) (S ×ˢ Icc 0 t) :=
    (hF.continuous_fderiv one_ne_zero).comp_continuousOn
      (hαC.mono (Set.prod_mono Subset.rfl hsub))
  have hjcont : ContinuousOn (fun p ↦ j p t) S :=
    continuousOn_linearVariation_parameter (isCompact_closedBall x₀ r) ht.1
      hJA hjzero hjD (fun p hp s hs ↦ hM p hp s (hsub hs))
  have hderiv (p : E) (hp : p ∈ ball x₀ r) :
      HasFDerivAt (fun y ↦ α y t) (j p t) p := by
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hp)
    have hδS : ball p δ ⊆ S := hδsub.trans ball_subset_closedBall
    apply hasFDerivAt_coordinateFlow_of_variation hF p hδ ht.1
      (fun y hy ↦ hαzero y (hδS hy))
      (fun y hy s hs ↦ hαD y (hδS hy) s (hsub hs))
      (fun s hs ↦ (hαLip s (hsub hs)).mono hδS)
      (hjzero p (ball_subset_closedBall hp))
      (hjD p (ball_subset_closedBall hp))
  intro p hp
  have hC1 : ContDiffAt ℝ 1 (fun y ↦ α y t) p := by
    apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨fun y ↦ j y t, ⟨ball x₀ r, isOpen_ball.mem_nhds hp, hderiv⟩, ?_⟩
    change ContDiffAt ℝ 0 (fun y ↦ j y t) p
    exact contDiffAt_zero.mpr ⟨ball x₀ r, isOpen_ball.mem_nhds hp,
      hjcont.mono ball_subset_closedBall⟩
  exact hC1.contDiffWithinAt

/-- Actual C¹ initial-point regularity holds on the negative as well as the
positive short-time window, by reversal of the actual ODE. -/
theorem contDiffOn_coordinateFlow_symmetric_short_of_bound
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x₀ : E) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ closedBall x₀ r, α y 0 = y)
    (hαD : ∀ y ∈ closedBall x₀ r, ∀ s ∈ Icc (-T) T,
      HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y s) (closedBall x₀ r))
    (hαC : ContinuousOn (uncurry α) (closedBall x₀ r ×ˢ Icc (-T) T))
    {M : ℝ≥0} (hM : ∀ y ∈ closedBall x₀ r, ∀ s ∈ Icc (-T) T,
      ‖fderiv ℝ F (α y s)‖ ≤ M)
    (hshort : 2 * (M : ℝ) * T ≤ 1) {t : ℝ} (ht : |t| ≤ T / 2) :
    ContDiffOn ℝ 1 (fun y ↦ α y t) (ball x₀ r) := by
  by_cases htpos : 0 ≤ t
  · exact contDiffOn_coordinateFlow_short_of_bound hF x₀ hr hT hαzero hαD
      hαLip hαC hM hshort ⟨htpos, (le_abs_self t).trans ht⟩
  · have hreflect (s : ℝ) (hs : s ∈ Icc (-T) T) : -s ∈ Icc (-T) T :=
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hD : ∀ y ∈ closedBall x₀ r, ∀ s ∈ Icc (-T) T,
        HasDerivAt (fun u ↦ α y (-u)) (-F (α y (-s))) s := by
      intro y hy s hs
      simpa only [Function.comp_def, neg_one_smul] using
        (hαD y hy (-s) (hreflect s hs)).scomp s (hasDerivAt_neg s)
    have hC : ContinuousOn (uncurry (fun y s ↦ α y (-s)))
        (closedBall x₀ r ×ˢ Icc (-T) T) := by
      apply hαC.comp (continuous_fst.prodMk continuous_snd.neg).continuousOn
      intro p hp
      exact ⟨hp.1, hreflect p.2 hp.2⟩
    have hMneg : ∀ y ∈ closedBall x₀ r, ∀ s ∈ Icc (-T) T,
        ‖fderiv ℝ (fun z ↦ -F z) (α y (-s))‖ ≤ M := by
      intro y hy s hs
      simpa only [fderiv_fun_neg, norm_neg] using hM y hy (-s) (hreflect s hs)
    have hh := contDiffOn_coordinateFlow_short_of_bound hF.neg x₀ hr hT
      (α := fun y s ↦ α y (-s)) (by simpa using hαzero) hD
      (fun s hs ↦ hαLip (-s) (hreflect s hs)) hC hMneg hshort
      (t := -t) ⟨by linarith, (neg_le_abs t).trans ht⟩
    simpa only [neg_neg] using hh

end CutoffRigidity
