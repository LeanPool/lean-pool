/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.C1CoordinateFlowDerivative

/-! # The true mixed time/initial derivative of actual coordinate ODE flows
The actual initial Fréchet derivative is identified on both sides of time zero
with a genuinely constructed linear variation. Its time derivative and the
infinitesimal metric-preservation formula follow without a mixed-derivative
or differentiable-flow premise.
-/

@[expose] public section
open Set Filter Metric
open scoped Topology NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- The same actual variational solution gives the actual initial derivative
on both sides of time zero. -/
theorem hasFDerivAt_coordinateFlow_of_symmetric_variation
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ s ∈ Icc (-T) T, HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y s) (ball x r))
    {J : ℝ → E →L[ℝ] E} (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ s ∈ Icc (-T) T, HasDerivAt J
      ((fderiv ℝ F (α x s)).comp (J s)) s)
    {t : ℝ} (ht : t ∈ Icc (-T) T) : HasFDerivAt (fun y ↦ α y t) (J t) x := by
  by_cases htpos : 0 ≤ t
  · have hsub : Icc 0 t ⊆ Icc (-T) T := Icc_subset_Icc (by linarith) ht.2
    exact hasFDerivAt_coordinateFlow_of_variation hF x hr htpos hαzero
      (fun y hy s hs ↦ hαD y hy s (hsub hs))
      (fun s hs ↦ hαLip s (hsub hs)) hJzero (fun s hs ↦ hJD s (hsub hs))
  · have hreflect (s : ℝ) (hs : s ∈ Icc 0 (-t)) : -s ∈ Icc (-T) T :=
      ⟨by linarith [hs.2, ht.1], by linarith [hs.1]⟩
    have hD : ∀ y ∈ ball x r, ∀ s ∈ Icc 0 (-t),
        HasDerivAt (fun u ↦ α y (-u)) (-F (α y (-s))) s := by
      intro y hy s hs
      simpa only [Function.comp_def, neg_one_smul] using
        (hαD y hy (-s) (hreflect s hs)).scomp s (hasDerivAt_neg s)
    have hJneg : ∀ s ∈ Icc 0 (-t), HasDerivAt (fun u ↦ J (-u))
        ((fderiv ℝ (fun z ↦ -F z) (α x (-s))).comp (J (-s))) s := by
      intro s hs
      simpa only [Function.comp_def, neg_one_smul, fderiv_fun_neg,
        ContinuousLinearMap.neg_comp] using
        (hJD (-s) (hreflect s hs)).scomp s (hasDerivAt_neg s)
    have hh := hasFDerivAt_coordinateFlow_of_variation hF.neg x hr (by linarith : 0 ≤ -t)
      (α := fun y s ↦ α y (-s)) (J := fun s ↦ J (-s)) (by simpa using hαzero)
      hD (fun s hs ↦ hαLip (-s) (hreflect s hs)) (by simpa using hJzero) hJneg
    simpa only [neg_neg] using hh

/-- The genuine initial-point Fréchet derivative has the true time derivative
`DF(x)` at time zero. The linear variation is constructed from the actual field. -/
theorem hasDerivAt_fderiv_coordinateFlow_zero
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ s ∈ Icc (-T) T, HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y s) (ball x r)) :
    HasDerivAt (fun t ↦ fderiv ℝ (fun y ↦ α y t) x) (fderiv ℝ F x) 0 := by
  have hx : x ∈ ball x r := mem_ball_self hr
  let A := fun s ↦ fderiv ℝ F (α x s)
  have hAC : ContinuousOn A (Icc (-T) T) :=
    (hF.continuous_fderiv one_ne_zero).comp_continuousOn
      (fun s hs ↦ (hαD x hx s hs).continuousAt.continuousWithinAt)
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hAC
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  let θ := min (T / 2) (1 / (4 * ((M : ℝ) + 1)))
  have hden : 0 < 4 * ((M : ℝ) + 1) := by positivity
  have hθ : 0 < θ := lt_min (half_pos hT) (div_pos zero_lt_one hden)
  have hθT : θ < T := (min_le_left _ _).trans_lt (half_lt_self hT)
  have hsub : Icc (-θ) θ ⊆ Icc (-T) T := Icc_subset_Icc (neg_le_neg hθT.le) hθT.le
  have hshort : 2 * (M : ℝ) * θ ≤ 1 := by
    have hb := (le_div_iff₀ hden).mp
      (min_le_right (T / 2) (1 / (4 * ((M : ℝ) + 1))))
    nlinarith [mul_nonneg M.coe_nonneg hθ.le]
  obtain ⟨J, hJzero, _, hJD⟩ := exists_linear_variation_short_interval hθ.le
    (hAC.mono hsub) (fun s hs ↦ (hM₀ s (hsub hs)).trans (le_max_left _ _)) hshort
  have hJDfull (s : ℝ) (hs : s ∈ Icc (-(θ / 2)) (θ / 2)) :
      HasDerivAt J ((fderiv ℝ F (α x s)).comp (J s)) s := by
    have hsin : s ∈ Ioo (-θ) θ := by constructor <;> linarith [hs.1, hs.2]
    exact (hJD s (Ioo_subset_Icc_self hsin)).hasDerivAt (Icc_mem_nhds hsin.1 hsin.2)
  have hhalf : Icc (-(θ / 2)) (θ / 2) ⊆ Icc (-T) T := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have heq : (fun t ↦ fderiv ℝ (fun y ↦ α y t) x) =ᶠ[𝓝 (0 : ℝ)] J := by
    filter_upwards [Ioo_mem_nhds (by linarith : -(θ / 2) < 0) (half_pos hθ)] with s hs
    exact (hasFDerivAt_coordinateFlow_of_symmetric_variation hF x hr (half_pos hθ)
      hαzero (fun y hy u hu ↦ hαD y hy u (hhalf hu))
      (fun u hu ↦ hαLip u (hhalf hu)) hJzero hJDfull (Ioo_subset_Icc_self hs)).fderiv
  have hDzero := hJDfull 0 ⟨by linarith, by linarith⟩
  rw [hαzero x hx, hJzero, ContinuousLinearMap.comp_id] at hDzero
  exact hDzero.congr_of_eventuallyEq heq

/-- The actual coordinate Killing identity at the initial point makes the
actual metric of the actual flow differential stationary at time zero. -/
theorem hasDerivAt_coordinateFlow_metric_zero_of_killing
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ s ∈ Icc (-T) T, HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y s) (ball x r))
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} (hg : DifferentiableAt ℝ g x)
    (hKill : ∀ u v : E,
      ((fderiv ℝ g x) (F x)) u v + g x ((fderiv ℝ F x) u) v +
        g x u ((fderiv ℝ F x) v) = 0) (u v : E) :
    HasDerivAt (fun t ↦ g (α x t)
      ((fderiv ℝ (fun y ↦ α y t) x) u) ((fderiv ℝ (fun y ↦ α y t) x) v)) 0 0 := by
  have hx : x ∈ ball x r := mem_ball_self hr
  have hz : fderiv ℝ (fun y ↦ α y 0) x = ContinuousLinearMap.id ℝ E := by
    have heq : (fun y ↦ α y 0) =ᶠ[𝓝 x] id := by
      filter_upwards [ball_mem_nhds x hr] with y hy
      exact hαzero y hy
    rw [heq.fderiv_eq]
    exact fderiv_id
  have hαzeroX := hαzero x hx
  have hgAt : DifferentiableAt ℝ g (α x 0) := hαzeroX.symm ▸ hg
  have hgD := HasFDerivAt.comp_hasDerivAt (l := g) 0 hgAt.hasFDerivAt
    (hαD x hx 0 ⟨by linarith, by linarith⟩)
  have hJ := hasDerivAt_fderiv_coordinateFlow_zero hF x hr hT hαzero hαD hαLip
  have hh := (hgD.clm_apply (hJ.clm_apply (hasDerivAt_const 0 u))).clm_apply
    (hJ.clm_apply (hasDerivAt_const 0 v))
  convert! hh using 1
  simp only [Function.comp_apply, hαzeroX, hz, ContinuousLinearMap.id_apply, map_zero, add_zero,
    add_apply]
  exact (hKill u v).symm

end CutoffRigidity
