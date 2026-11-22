/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitFlowSmooth
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldJointC1LocalFlow

/-! # `C^k` local flows of smooth vector fields on manifolds
-/

@[expose] public section
open Bundle Set Filter Function
open scoped Manifold ContDiff Topology

namespace CutoffRigidity.Riemann
open CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- A `C^k` germ has a global `C^k` extension agreeing near the point (finite `k`). -/
theorem exists_contDiff_eventuallyEq_of_contDiffAt {n : ℕ} {F : E → E} {x₀ : E}
    (hF : ContDiffAt ℝ n F x₀) :
    ∃ G : E → E, ContDiff ℝ n G ∧ G =ᶠ[𝓝 x₀] F := by
  have hnear : {x | ContDiffAt ℝ n F x} ∈ 𝓝 x₀ := hF.eventually (by simp)
  obtain ⟨d, hd, hds⟩ := Euclidean.nhds_basis_closedBall.mem_iff.mp hnear
  let χ : ContDiffBump (toEuclidean x₀) :=
    ⟨d / 2, d, half_pos hd, half_lt_self hd⟩
  let φ : E → ℝ := χ ∘ toEuclidean
  have hφ : ContDiff ℝ n φ := (χ.contDiff (n := n)).comp (ContinuousLinearEquiv.contDiff _)
  have hsupp : tsupport φ ⊆ Euclidean.closedBall x₀ d := by
    rw [tsupport, ← Euclidean.closure_ball _ hd.ne']
    apply closure_mono
    intro x hx
    have hχ : toEuclidean x ∈ support χ := hx
    rwa [χ.support_eq] at hχ
  let G : E → E := fun x ↦ φ x • F x
  refine ⟨G, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact (hφ.contDiffAt.smul (hds (hsupp hx)))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [G, hy]
  · have hball : ∀ᶠ x in 𝓝 x₀, x ∈ Euclidean.closedBall x₀ (d / 2) :=
      Euclidean.nhds_basis_closedBall.mem_iff.mpr ⟨d / 2, half_pos hd, Subset.rfl⟩
    filter_upwards [hball] with x hx
    have hχ : χ (toEuclidean x) = 1 := χ.one_of_mem_closedBall hx
    simp [G, φ, Function.comp_apply, hχ]

theorem exists_contMDiff_localIntegralFlow_nat (m : ℕ)
    {X : (x : M) → TangentSpace I x} {x₀ : M}
    (hX : ContMDiffAt I I.tangent ((m + 1 : ℕ) : WithTop ℕ∞) (T% X) x₀) :
    ∃ ε > (0 : ℝ), ∃ U ∈ 𝓝 x₀, ∃ Φ : M × ℝ → M,
      ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) ∧
      (∀ x ∈ U, Φ (x, 0) = x ∧
        IsMIntegralCurveOn (fun t ↦ Φ (x, t)) X (Ioo (-ε) ε)) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ((m + 1 : ℕ) : WithTop ℕ∞) Φ (U ×ˢ Ioo (-ε) ε) := by
  let e := extChartAt I x₀
  let z := e x₀
  let F : E → E := fun y ↦ tangentCoordChange I (e.symm y) x₀ (e.symm y) (X (e.symm y))
  have hF : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) F z := by
    rw [contMDiffAt_iff] at hX
    exact (hX.2.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd
  obtain ⟨G, hG, hGF⟩ := exists_contDiff_eventuallyEq_of_contDiffAt (n := m + 1) hF
  obtain ⟨r, hr, θ, hθ, α, hαC1, hα⟩ := exists_contDiff_localFlow m E G hG z
  have hαC := hαC1.continuousOn
  have hzball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hαzero : α z 0 = z := (hα z hzball).1
  have hdomain : Metric.ball z r ×ˢ Ioo (-θ) θ ∈ 𝓝 (z, 0) :=
    (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hzball, by constructor <;> linarith⟩
  let W := interior e.target ∩ {y | G y = F y}
  have hW : W ∈ 𝓝 z := inter_mem
    (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))) hGF
  have hαW : (uncurry α) ⁻¹' W ∈ 𝓝 (z, 0) := by
    apply (hαC.continuousAt hdomain).preimage_mem_nhds
    simpa only [uncurry_apply_pair, hαzero] using hW
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (inter_mem hαW hdomain)
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.mp hv
  let U : Set M := {x | e x ∈ u ∧ x ∈ e.source}
  have hU : U ∈ 𝓝 x₀ := by
    filter_upwards [(continuousAt_extChartAt x₀).preimage_mem_nhds hu,
      extChartAt_source_mem_nhds (I := I) x₀] with x hx hs
    exact ⟨hx, hs⟩
  have hgood (x : M) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      α (e x) t ∈ W ∧ (e x ∈ Metric.ball z r ∧ t ∈ Ioo (-θ) θ) := by
    have htv : t ∈ v := by
      apply hεv
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨ht.1, ht.2⟩
    exact huv (show (e x, t) ∈ u ×ˢ v from ⟨hx.1, htv⟩)
  let Φ : M × ℝ → M := fun p ↦ e.symm (α (e p.1) p.2)
  have hΦC : ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) := by
    apply (continuousOn_extChartAt_symm x₀).comp
    · apply hαC.comp (f := fun p : M × ℝ ↦ (e p.1, p.2))
      · have chartSource (p : M × ℝ) (hp : p ∈ U ×ˢ Ioo (-ε) ε) :
            p.1 ∈ (extChartAt I x₀).source := hp.1.2
        exact ((continuousOn_extChartAt x₀).comp continuousOn_fst chartSource).prodMk
          continuousOn_snd
      · intro p hp
        exact (hgood p.1 hp.1 p.2 hp.2).2
    · intro p hp
      change α (e p.1) p.2 ∈ e.target
      exact interior_subset (hgood p.1 hp.1 p.2 hp.2).1.1
  refine ⟨ε, hε, U, hU, Φ, hΦC, ?_, ?_⟩
  · intro x hx
    have hxball := (hgood x hx 0 ⟨by linarith, hε⟩).2.1
    refine ⟨?_, ?_⟩
    · change e.symm (α (e x) 0) = x
      rw [(hα (e x) hxball).1, e.left_inv hx.2]
    · intro t ht
      let f : ℝ → E := α (e x)
      let xₜ : M := e.symm (f t)
      have hd : HasDerivAt f (F (f t)) t := by
        have hh := (hα (e x) hxball).2 t (hgood x hx t ht).2.2
        rw [(hgood x hx t ht).1.2] at hh
        exact hh
      have hf3 : f t ∈ e.target := interior_subset (hgood x hx t ht).1.1
      have hft1 : xₜ ∈ e.source := e.map_target hf3
      have hft2 := mem_extChartAt_source (I := I) xₜ
      apply HasMFDerivAt.hasMFDerivWithinAt
      refine ⟨(continuousAt_extChartAt_symm'' hf3).comp hd.continuousAt, ?_⟩
      apply HasDerivWithinAt.hasFDerivWithinAt
      simp only [mfld_simps]
      refine HasDerivAt.hasDerivWithinAt ?_
      change HasDerivAt ((extChartAt I xₜ ∘ e.symm) ∘ f) (X xₜ) t
      rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := X xₜ) hft2,
        ← tangentCoordChange_comp (I := I) (w := xₜ) (x := x₀) (y := xₜ)
          (z := xₜ) (v := (X xₜ : E)) ⟨⟨hft2, hft1⟩, hft2⟩]
      apply HasFDerivAt.comp_hasDerivAt _ _ hd
      apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
        (mem_nhds_iff.mpr ⟨interior e.target,
          subset_trans interior_subset (extChartAt_target_subset_range ..),
          isOpen_interior, (hgood x hx t ht).1.1⟩)
      change HasFDerivWithinAt (extChartAt I xₜ ∘ e.symm)
        (tangentCoordChange I x₀ xₜ xₜ) (range I) (f t)
      rw [← e.right_inv hf3]
      exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  · change ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ((m + 1 : ℕ) : WithTop ℕ∞)
      (e.symm ∘ (uncurry α ∘ (fun p : M × ℝ ↦ (e p.1, p.2)))) (U ×ˢ Ioo (-ε) ε)
    apply (contMDiffOn_extChartAt_symm x₀).comp
      (f := uncurry α ∘ (fun p : M × ℝ ↦ (e p.1, p.2)))
    · apply hαC1.contMDiffOn.comp (f := fun p : M × ℝ ↦ (e p.1, p.2))
      · apply ContMDiffOn.prodMk_space
        · apply (contMDiffOn_extChartAt (I := I) (n := ((m + 1 : ℕ) : WithTop ℕ∞)) (x := x₀)).comp
            (f := Prod.fst) contMDiffOn_fst
          intro p hp
          simp only [Set.mem_preimage]
          simpa only [e, extChartAt_source] using hp.1.2
        · exact contMDiffOn_snd
      · intro p hp
        exact (hgood p.1 hp.1 p.2 hp.2).2
    · intro p hp
      change α (e p.1) p.2 ∈ e.target
      exact interior_subset (hgood p.1 hp.1 p.2 hp.2).1.1


end CutoffRigidity.Riemann
