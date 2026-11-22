/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianCoordinateKilling
public import LeanPool.CutoffRigidity.RiemannianSplitting.DifferentiableCoordinateLocalFlow
public import LeanPool.CutoffRigidity.RiemannianSplitting.C1LocalExtension
public import LeanPool.CutoffRigidity.RiemannianSplitting.CoordinateFlowTangentEvolution

/-! # Actual local coordinate evolution of a parallel field preserves metric infinitesimally
All coordinate flows and their Fréchet derivatives are genuinely constructed.
The Killing identity is discharged by the actual Levi-Civita parallelism.
-/

@[expose] public section
open Bundle Set Filter Function Metric VectorField
open scoped Manifold ContDiff Topology NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The actual parallel field supplies an actual C¹ coordinate flow whose true
initial-point derivative has zero metric derivative at time zero. Every
nonlinear/linear ODE and Killing obligation is derived from the source data. -/
theorem exists_parallel_coordinate_localEvolution
    (x₀ : M) {X : (x : M) → TangentSpace I x}
    (hX : ContMDiffAt I I.tangent 1 (T% X) x₀)
    (hpX : CovariantDerivative.leviCivitaConnection I M X x₀ = 0) :
    ∃ G : E → E, ContDiff ℝ 1 G ∧
      G =ᶠ[𝓝 (extChartAt I x₀ x₀)] chartCoordinateField (I := I) x₀ X ∧
      ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, ∃ L : ℝ≥0,
        ContinuousOn (uncurry α) (ball (extChartAt I x₀ x₀) r ×ˢ Ioo (-ε) ε) ∧
        (∀ y ∈ ball (extChartAt I x₀ x₀) r, α y 0 = y ∧
          ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α y) (G (α y t)) t) ∧
        (∀ t ∈ Ioo (-ε) ε, LipschitzOnWith L (fun y ↦ α y t) (ball (extChartAt I x₀ x₀) r)) ∧
        (∀ t ∈ Ioo (-ε) ε, ContDiffOn ℝ 1 (fun y ↦ α y t) (ball (extChartAt I x₀ x₀) r)) ∧
        (∀ y ∈ ball (extChartAt I x₀ x₀) r, ∀ t ∈ Ioo (-ε) ε,
          α y t ∈ interior (extChartAt I x₀).target ∧
            G (α y t) = chartCoordinateField (I := I) x₀ X (α y t)) ∧
        ∀ u v : E, HasDerivAt (fun t ↦
          chartMetric (I := I) x₀ (α (extChartAt I x₀ x₀) t)
            ((fderiv ℝ (fun y ↦ α y t) (extChartAt I x₀ x₀)) u)
            ((fderiv ℝ (fun y ↦ α y t) (extChartAt I x₀ x₀)) v)) 0 0 := by
  let e := extChartAt I x₀
  let z := e x₀
  let F := chartCoordinateField (I := I) x₀ X
  have hF : ContDiffAt ℝ 1 F z := by
    have hc := contMDiffWithinAt_mpullbackWithin_extChartAt_symm
      (n := 2) (m := 1) hX.contMDiffWithinAt uniqueMDiffOn_univ (mem_univ x₀) (by norm_num)
    have hdom : e.target ∩ e.symm ⁻¹' univ ∈ 𝓝 z := by
      simp only [preimage_univ, inter_univ]
      exact mem_of_superset (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
        (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))) interior_subset
    have hcAt := hc.contMDiffAt hdom
    have hcCoord := (contMDiffAt_section_iff z).mp hcAt
    convert! hcCoord.contDiffAt using 1
    funext y
    simp [mfld_simps]
    rfl
  obtain ⟨G, hG, hGF⟩ := exists_contDiff_one_eventuallyEq_of_contDiffAt hF
  obtain ⟨R, hR, θ, hθ, α, L, hαC, hα, hαC1, hαLip⟩ :=
    exists_contDiff_lipschitz_coordinate_localFlow hG z
  have hz : z ∈ ball z R := mem_ball_self hR
  let W := interior e.target ∩ {y | G y = F y}
  have hW : W ∈ 𝓝 z := inter_mem
    (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))) hGF
  have hαzero : α z 0 = z := (hα z hz).1
  have hDnhds : ball z R ×ˢ Ioo (-θ) θ ∈ 𝓝 (z, 0) :=
    (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hz, by constructor <;> linarith⟩
  have hnear : (uncurry α) ⁻¹' W ∩ (ball z R ×ˢ Ioo (-θ) θ) ∈ 𝓝 (z, 0) := by
    apply inter_mem _ hDnhds
    apply (hαC.continuousAt hDnhds).preimage_mem_nhds
    simpa only [uncurry_apply_pair, hαzero] using hW
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  have hgood (y : E) (hy : y ∈ ball z r) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      α y t ∈ W ∧ (y ∈ ball z R ∧ t ∈ Ioo (-θ) θ) := by
    have htV : t ∈ V := hεV (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨ht.1, ht.2⟩)
    exact hUV (show (y, t) ∈ U ×ˢ V from ⟨hrU hy, htV⟩)
  have hsub : ball z r ⊆ ball z R := fun y hy ↦ (hgood y hy 0 ⟨by linarith, hε⟩).2.1
  have htime {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : t ∈ Ioo (-θ) θ :=
    (hgood z (mem_ball_self hr) t ht).2.2
  refine ⟨G, hG, hGF, r, hr, ε, hε, α, L, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hαC.mono (Set.prod_mono hsub (fun t ht ↦ htime ht))
  · intro y hy
    exact ⟨(hα y (hsub hy)).1, fun t ht ↦ (hα y (hsub hy)).2 t (htime ht)⟩
  · exact fun t ht ↦ (hαLip t (htime ht)).mono hsub
  · exact fun t ht ↦ (hαC1 t (htime ht)).mono hsub
  · exact fun y hy t ht ↦ (hgood y hy t ht).1
  · intro u v
    have hclosed {t : ℝ} (ht : t ∈ Icc (-(ε / 2)) (ε / 2)) : t ∈ Ioo (-ε) ε := by
      constructor <;> linarith [ht.1, ht.2]
    apply hasDerivAt_coordinateFlow_metric_zero_of_killing hG z hr (half_pos hε)
      (fun y hy ↦ (hα y (hsub hy)).1)
      (fun y hy t ht ↦ (hα y (hsub hy)).2 t (htime (hclosed ht)))
      (fun t ht ↦ (hαLip t (htime (hclosed ht))).mono hsub)
      ((contDiffAt_chartMetric (I := I) x₀).differentiableAt one_ne_zero) ?_ u v
    intro a b
    rw [hGF.eq_of_nhds, hGF.fderiv_eq]
    exact coordinate_killing_of_parallel x₀ (hX.mdifferentiableAt one_ne_zero) hpX a b

end CutoffRigidity
