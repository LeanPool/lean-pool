/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPCoord
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPEuclid

/-! # Continuity of `Γ(u,v)` and of `𝓛v` for smooth `u, v, V` -/

@[expose] public section
open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_carre {u v : M → ℝ} (hu : MSmooth F u) (hv : MSmooth F v) :
    Continuous (carre F u v) := by
  exact CutoffRigidity.continuous_inner_manifoldGradient
    (hu.of_le (WithTop.coe_le_coe.mpr le_top))
    (hv.of_le (WithTop.coe_le_coe.mpr le_top))

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuousAt_mgenerator {V v : M → ℝ} (hV : MSmooth F V) (hv : MSmooth F v) (x : M) :
    ContinuousAt (mgenerator F V v) x := by
  have hV2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 V :=
    hV.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 v :=
    hv.of_le (WithTop.coe_le_coe.mpr le_top)
  set φ := chartAt F x with hφ
  set T := φ.target with hTdef
  have hTo : IsOpen T := φ.open_target
  have hTe : ∀ z ∈ T, z ∈ (extChartAt 𝓘(ℝ, F) x).target := fun z hz => by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  set ρ := CutoffRigidity.chartWeight (F := F) x V with hρdef
  have hρpos : ∀ z ∈ T, 0 < ρ z := fun z hz =>
    mul_pos (Real.exp_pos _) (CutoffRigidity.chartRiemannianVolumeDensity_pos x (hTe z hz))
  have hρCD : ContDiffOn ℝ 1 ρ T := fun z hz =>
    (CutoffRigidity.chartWeight_hasFDerivAt x (hTe z hz) hV2).contDiffWithinAt
  set Yc := CutoffRigidity.chartCoordinateField (I := 𝓘(ℝ, F)) x
    (CutoffRigidity.manifoldGradient 𝓘(ℝ, F) v) with hYc
  have hYCD : ContDiffOn ℝ 1 Yc T := fun z hz =>
    (CutoffRigidity.contDiffAt_chartCoordinateField_grad x (hTe z hz) hv2).contDiffWithinAt
  have hdρ : ContinuousOn (fun z => fderiv ℝ ρ z) T :=
    hρCD.continuousOn_fderiv_of_isOpen hTo le_rfl
  have hdY : ContinuousOn (fun z => fderiv ℝ Yc z) T :=
    hYCD.continuousOn_fderiv_of_isOpen hTo le_rfl
  have hNc : ContinuousOn (fun z => fderiv ℝ ρ z (Yc z) +
      ρ z * LinearMap.trace ℝ F (fderiv ℝ Yc z).toLinearMap) T :=
    (hdρ.clm_apply hYCD.continuousOn).add
      (hρCD.continuousOn.mul (CutoffRigidity.traceCLM.continuous.comp_continuousOn hdY))
  have hN : ∀ z ∈ T, ρ z * mgenerator F V v (φ.symm z) =
      fderiv ℝ ρ z (Yc z) + ρ z * LinearMap.trace ℝ F (fderiv ℝ Yc z).toLinearMap := fun z hz =>
    CutoffRigidity.chartWeight_mul_generator x (hTe z hz) hV2 hv2
  have hgc : ContinuousOn (mgenerator F V v ∘ φ.symm) T := by
    have := hNc.div hρCD.continuousOn (fun z hz => (hρpos z hz).ne')
    refine this.congr (fun z hz => ?_)
    simp only [Function.comp, Pi.div_apply]
    rw [← hN z hz]
    have := (hρpos z hz).ne'
    field_simp
  have hx : x ∈ φ.source := mem_chart_source F x
  have hat : ContinuousAt (mgenerator F V v ∘ φ.symm) (φ x) :=
    hgc.continuousAt (hTo.mem_nhds (φ.map_source hx))
  have hφc : ContinuousAt φ x := φ.continuousAt hx
  have := hat.comp hφc
  refine this.congr ?_
  filter_upwards [φ.open_source.mem_nhds hx] with y hy
  simp [φ.left_inv hy]

end CutCur
