/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedChartLip
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox

/-! # Local smoothing of a 1-Lipschitz function on a Riemannian manifold -/

@[expose] public section

open Bundle Filter Set Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology


namespace CutCur

private theorem exists_smooth_approx_linear_coordinates
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] (coordinates : E ≃L[ℝ] G) (s : Set E)
    (u : E → ℝ) {C : ℝ≥0}
    (hLip : ∀ a ∈ s, ∀ b ∈ s, |u a - u b| ≤ C * ‖coordinates (a - b)‖)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ ∀ a ∈ s,
      |g a - u a| ≤ δ ∧ ∀ w, |fderiv ℝ g a w| ≤ C * ‖coordinates w‖ := by
  let transported := u ∘ coordinates.symm
  have htransported : LipschitzOnWith C transported (coordinates.symm ⁻¹' s) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
    simpa only [transported, Function.comp_apply, Real.dist_eq, map_sub,
      coordinates.apply_symm_apply, dist_eq_norm, Real.norm_eq_abs] using
      hLip (coordinates.symm a) ha (coordinates.symm b) hb
  obtain ⟨extension, hextension, heq⟩ := htransported.extend_real
  obtain ⟨g, hgs, hgl, hga⟩ := hextension.exists_contDiff_lipschitzWith_dist_lt hδ
  refine ⟨g ∘ coordinates, hgs.comp coordinates.contDiff, fun a ha ↦ ⟨?_, ?_⟩⟩
  · have hmem : coordinates a ∈ coordinates.symm ⁻¹' s := by
      simpa only [mem_preimage, coordinates.symm_apply_apply] using ha
    have hvalue := (hga (coordinates a)).le
    rw [Real.dist_eq, ← heq hmem] at hvalue
    simpa only [transported, Function.comp_apply, coordinates.symm_apply_apply] using hvalue
  · intro w
    rw [fderiv_comp a (hgs.differentiable (by simp)).differentiableAt coordinates.differentiableAt,
      coordinates.fderiv, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs]
    exact ((fderiv ℝ g (coordinates a)).le_opNorm (coordinates w)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hgl) (norm_nonneg _))

section LocalSmooth

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]

include F

/-- Local smoothing: around each point there is an open set `V` with compact closure-ish
(`V ⊆ K`) on which, for every accuracy `δ`, a smooth function `g` approximates `f` within `δ`,
with differential of norm at most `4`. -/
theorem exists_local_smooth (hfin : ∀ x y : M, edist x y ≠ ⊤) {f : M → ℝ} (hf : LipschitzWith 1 f)
    (p : M) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ (∃ K, IsCompact K ∧ V ⊆ K) ∧ ∀ δ > 0, ∃ g : M → ℝ,
      (∀ x ∈ V, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g x) ∧ (∀ x ∈ V, |g x - f x| ≤ δ) ∧
      ∀ x ∈ V, ∀ v : TangentSpace 𝓘(ℝ, F) x, |mvfderiv 𝓘(ℝ, F) g x v| ≤ 4 * ‖v‖ := by
  have hfd : ∀ x y, |f x - f y| ≤ (edist x y).toReal := by
    intro x y
    have h1 : edist (f x) (f y) ≤ edist x y := by simpa using hf x y
    rw [edist_dist, Real.dist_eq] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal (hfin x y)).1 h1
  set e := extChartAt 𝓘(ℝ, F) p with he
  have hgoodev := eventually_symmAt_norm F p (r := 2) one_lt_two
  have hc : ContinuousAt e.symm (e p) := continuousAt_extChartAt_symm p
  have hsy : e.symm (e p) = p := e.left_inv (mem_extChartAt_source p)
  have hpre : e.symm ⁻¹' {y | y ∈ (chartAt F p).source ∧
      (∀ w, ‖symmAt F p y w‖ ≤ 2 * ‖symmAt F p p w‖) ∧
      (∀ w, ‖symmAt F p p w‖ ≤ 2 * ‖symmAt F p y w‖)} ∈ 𝓝 (e p) :=
    hc.preimage_mem_nhds (by rw [hsy]; exact hgoodev)
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (extChartAt_target_mem_nhds p) hpre)
  have hRt : Metric.ball (e p) R ⊆ e.target := fun z hz => (hball hz).1
  have hgoodb : ∀ ζ ∈ Metric.ball (e p) R, e.symm ζ ∈ (chartAt F p).source ∧
      (∀ w, ‖symmAt F p (e.symm ζ) w‖ ≤ 2 * ‖symmAt F p p w‖) ∧
      (∀ w, ‖symmAt F p p w‖ ≤ 2 * ‖symmAt F p (e.symm ζ) w‖) := fun ζ hζ => (hball hζ).2
  have hhalf : Metric.ball (e p) (R / 2) ⊆ Metric.ball (e p) R :=
    Metric.ball_subset_ball (by linarith)
  set u : F → ℝ := fun ζ => f (e.symm ζ) with hu
  let T := trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p
  have hp : p ∈ T.baseSet := by simp [T]
  let coordinates := (T.continuousLinearEquivAt ℝ p hp).symm
  have hcoordinates (w : F) : coordinates w = symmAt F p p w := (T.symmL_apply hp w).symm
  have hLip : ∀ a ∈ Metric.ball (e p) R, ∀ b ∈ Metric.ball (e p) R,
      |u a - u b| ≤ (2 : ℝ≥0) * ‖coordinates (a - b)‖ := by
    intro a ha b hb
    have hed := edist_extChartAt_symm_le F p (r := 2) (by norm_num) hRt
      (fun ζ hζ => (hgoodb ζ hζ).2.1) hb ha
    rw [edist_comm] at hed
    have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    rw [ENNReal.toReal_ofReal (by positivity)] at hbound
    simpa only [NNReal.coe_ofNat, hcoordinates] using (hfd (e.symm a) (e.symm b)).trans hbound
  refine ⟨((chartAt F p).source ∩ e ⁻¹' Metric.ball (e p) (R / 2)), isOpen_extChartAt_preimage p
      Metric.isOpen_ball,
    ⟨mem_chart_source F p, by simpa using half_pos hR⟩,
    ⟨e.symm '' Metric.closedBall (e p) (R / 2),
      (isCompact_closedBall (e p) (R / 2)).image_of_continuousOn
        ((continuousOn_extChartAt_symm p).mono ?_), ?_⟩, ?_⟩
  · exact (Metric.closedBall_subset_ball (by linarith)).trans hRt
  · intro x hx
    have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
    exact ⟨e x, Metric.ball_subset_closedBall hx.2, e.left_inv hxs⟩
  · intro δ hδ
    obtain ⟨G, hG, hGp⟩ := exists_smooth_approx_linear_coordinates coordinates _ u hLip hδ
    refine ⟨G ∘ e, ?_, ?_, ?_⟩
    · intro x hx
      exact (hG.contMDiff.contMDiffAt).comp x (contMDiffAt_extChartAt' (by simpa using hx.1))
    · intro x hx
      have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
      have := (hGp (e x) (hhalf hx.2)).1
      simpa [hu, e.left_inv hxs] using this
    · intro x hx
      have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
      have hxsrc : x ∈ (chartAt F p).source := hx.1
      have hGd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) G (e x) :=
        (hG.contMDiff.mdifferentiable (by simp)) _
      have hed : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) e x := mdifferentiableAt_extChartAt hxsrc
      have hcl : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) e x = T.continuousLinearMapAt ℝ x :=
        (TangentBundle.continuousLinearMapAt_trivializationAt hxsrc).symm
      have hxb : x ∈ T.baseSet := by simpa [T] using hxsrc
      intro v
      have hv0 : mvfderiv 𝓘(ℝ, F) (G ∘ e) x v =
          fderiv ℝ G (e x) (T.continuousLinearMapAt ℝ x v) := by
        rw [mvfderiv_comp_apply x hGd hed v, hcl, mvfderiv_eq_fderiv]
        rfl
      rw [hv0]
      set w := T.continuousLinearMapAt ℝ x v with hw
      have h1 := (hGp (e x) (hhalf hx.2)).2 w
      have hgood := (hgoodb (e x) (hhalf hx.2)).2.2 w
      rw [e.left_inv hxs] at hgood
      have hv : symmAt F p x w = v := Trivialization.symmL_continuousLinearMapAt T hxb v
      rw [hv] at hgood
      -- Convert the chart-center norm back to the tangent norm at x.
      calc |fderiv ℝ G (e x) w| ≤ 2 * ‖symmAt F p p w‖ := by
            simpa only [NNReal.coe_ofNat, hcoordinates] using h1
        _ ≤ 2 * (2 * ‖v‖) := by gcongr
        _ = 4 * ‖v‖ := by ring

end LocalSmooth

end CutCur
