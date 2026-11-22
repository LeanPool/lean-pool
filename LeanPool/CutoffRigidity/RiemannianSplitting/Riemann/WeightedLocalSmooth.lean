/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedChartLip
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedMollify

/-! # Local smoothing of a 1-Lipschitz function on a Riemannian manifold -/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal Topology


namespace CutCur

section LocalSmooth

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
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
  obtain ⟨R₁, hR₁, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (extChartAt_target_mem_nhds p) hpre)
  have hRt : Metric.ball (e p) R₁ ⊆ e.target := fun z hz => (hball hz).1
  have hgoodb : ∀ ζ ∈ Metric.ball (e p) R₁, e.symm ζ ∈ (chartAt F p).source ∧
      (∀ w, ‖symmAt F p (e.symm ζ) w‖ ≤ 2 * ‖symmAt F p p w‖) ∧
      (∀ w, ‖symmAt F p p w‖ ≤ 2 * ‖symmAt F p (e.symm ζ) w‖) := fun ζ hζ => (hball hζ).2
  set R := R₁ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRR : Metric.ball (e p) R ⊆ Metric.ball (e p) R₁ := Metric.ball_subset_ball (by linarith)
  have hcb : Metric.closedBall (e p) R ⊆ Metric.ball (e p) R₁ :=
    Metric.closedBall_subset_ball (by linarith)
  set u : F → ℝ := fun ζ => f (e.symm ζ) with hu
  have hucont : ContinuousOn u e.target :=
    hf.continuous.comp_continuousOn (continuousOn_extChartAt_symm p)
  have huint : IntegrableOn u (Metric.ball (e p) R) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (e p) R)
      ((hucont.mono (hcb.trans hRt)))).mono_set Metric.ball_subset_closedBall
  set N : F → ℝ := fun w => 2 * ‖symmAt F p p w‖ with hN
  have hLip : ∀ b ∈ Metric.ball (e p) R, ∀ (w : F) (h : ℝ), b + h • w ∈ Metric.ball (e p) R →
      |u (b + h • w) - u b| ≤ |h| * N w := by
    intro b hb w h hbh
    have hed := edist_extChartAt_symm_le F p (r := 2) (R := R₁) (by norm_num) hRt
      (fun ζ hζ => (hgoodb ζ hζ).2.1) (hRR hb) (hRR hbh)
    have h1 : |f (e.symm (b + h • w)) - f (e.symm b)| ≤ (edist (e.symm (b + h • w)) (e.symm
        b)).toReal := hfd _ _
    rw [edist_comm] at h1
    have h2 := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hed)
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    have h3 : b + h • w - b = h • w := by abel
    rw [h3, map_smul, norm_smul, Real.norm_eq_abs] at h2
    calc |u (b + h • w) - u b| ≤ _ := h1
      _ ≤ _ := h2
      _ = |h| * N w := by simp only [hN]; ring
  have hN0 : ∀ w, 0 ≤ N w := fun w => by positivity
  have hNC : ∀ w, N w ≤ (2 * ‖symmAt F p p‖) * ‖w‖ := fun w => by
    simp only [hN]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((symmAt F p p).le_opNorm w) (by norm_num)
  refine ⟨((chartAt F p).source ∩ e ⁻¹' Metric.ball (e p) (R / 2)), isOpen_extChartAt_preimage p
      Metric.isOpen_ball,
    ⟨mem_chart_source F p, by simpa using half_pos hR⟩,
    ⟨e.symm '' Metric.closedBall (e p) (R / 2),
      (isCompact_closedBall (e p) (R / 2)).image_of_continuousOn
        ((continuousOn_extChartAt_symm p).mono ?_), ?_⟩, ?_⟩
  · exact (Metric.closedBall_subset_closedBall (by linarith)).trans (hcb.trans hRt)
  · intro x hx
    have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
    exact ⟨e x, Metric.ball_subset_closedBall hx.2, e.left_inv hxs⟩
  · intro δ hδ
    obtain ⟨G, hG, hGp⟩ := exists_contDiff_approx_lip u (e p) hR huint N
      (2 * ‖symmAt F p p‖) (by positivity) hN0 hNC hLip hδ
    refine ⟨G ∘ e, ?_, ?_, ?_⟩
    · intro x hx
      exact (hG.contMDiff.contMDiffAt).comp x (contMDiffAt_extChartAt' (by simpa using hx.1))
    · intro x hx
      have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
      have := (hGp (e x) hx.2).1
      simpa [hu, e.left_inv hxs] using this
    · intro x hx
      have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
      have hxsrc : x ∈ (chartAt F p).source := hx.1
      have hGd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) G (e x) :=
        (hG.contMDiff.mdifferentiable (by simp)) _
      have hed : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) e x := mdifferentiableAt_extChartAt hxsrc
      set T := trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p with hT
      have hcl : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) e x = T.continuousLinearMapAt ℝ x :=
        (TangentBundle.continuousLinearMapAt_trivializationAt hxsrc).symm
      have hxb : x ∈ T.baseSet := by simpa [hT] using hxsrc
      intro v
      have hv0 : mvfderiv 𝓘(ℝ, F) (G ∘ e) x v =
          fderiv ℝ G (e x) (T.continuousLinearMapAt ℝ x v) := by
        rw [mvfderiv_comp_apply x hGd hed v, hcl, mvfderiv_eq_fderiv]
        rfl
      rw [hv0]
      set w := T.continuousLinearMapAt ℝ x v with hw
      have h1 := (hGp (e x) hx.2).2 w
      have hgood := (hgoodb (e x) (hRR (Metric.ball_subset_ball (by linarith) hx.2))).2.2 w
      rw [e.left_inv hxs] at hgood
      have hv : symmAt F p x w = v := Trivialization.symmL_continuousLinearMapAt T hxb v
      rw [hv] at hgood
      calc |fderiv ℝ G (e x) w| ≤ N w := h1
        _ = 2 * ‖symmAt F p p w‖ := rfl
        _ ≤ 2 * (2 * ‖v‖) := by gcongr
        _ = 4 * ‖v‖ := by ring

end LocalSmooth

end CutCur
