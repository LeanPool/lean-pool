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
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPTransfer
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPDensity

/-! # Integration by parts for functions supported in one chart -/

@[expose] public section
open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff Topology

namespace CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

theorem weightedIBP_of_chart {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} (x₀ : M)
    (hμ : (μ.restrict (chartAt F x₀).source).map (chartAt F x₀) =
      (volume.restrict (chartAt F x₀).target).withDensity fun z =>
        ENNReal.ofReal (Real.exp (-V ((chartAt F x₀).symm z)) * chartVolumeDensity F x₀ z))
    {u v : M → ℝ} (hu : MSmooth F u) (hv : MSmooth F v) (hK : HasCompactSupport u)
    (hS : tsupport u ⊆ (chartAt F x₀).source) :
    ∫ x, carre F u v x ∂μ = -∫ x, u x * mgenerator F V v x ∂μ := by
  classical
  set φ := chartAt F x₀ with hφ
  set T := φ.target with hTdef
  have hTo : IsOpen T := φ.open_target
  have hTm : MeasurableSet T := hTo.measurableSet
  have hTe : ∀ z ∈ T, z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := fun z hz => by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  have hsymm : ∀ z, (extChartAt 𝓘(ℝ, F) x₀).symm z = φ.symm z := fun _ => rfl
  have hV2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 V := hV.of_le
    (WithTop.coe_le_coe.mpr le_top)
  have hu2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 u := hu.of_le
    (WithTop.coe_le_coe.mpr le_top)
  have hv2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 v := hv.of_le
    (WithTop.coe_le_coe.mpr le_top)
  -- weight
  set ρ := CutoffRigidity.chartWeight (F := F) x₀ V with hρdef
  have hρpos : ∀ z ∈ T, 0 < ρ z := fun z hz =>
    mul_pos (Real.exp_pos _) (CutoffRigidity.chartRiemannianVolumeDensity_pos x₀ (hTe z hz))
  have hρeq : ∀ z ∈ T, ρ z = Real.exp (-V (φ.symm z)) * chartVolumeDensity F x₀ z := by
    intro z hz
    rw [chartVolumeDensity_eq_riemannian F x₀ hz]
    rfl
  have hμ' : (μ.restrict φ.source).map φ =
      (volume.restrict T).withDensity fun z => ENNReal.ofReal (ρ z) := by
    rw [hμ]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hTm] with z hz
    rw [hρeq z hz]
  -- compact support in the chart
  set K' := φ '' tsupport u with hK'def
  have hK' : IsCompact K' := hK.image_of_continuousOn (φ.continuousOn.mono hS)
  have hK'T : K' ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact φ.map_source (hS hx)
  set ut : F → ℝ := u ∘ φ.symm with hut
  have hvan : ∀ z ∈ T, z ∉ K' → ut =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz hzK
    filter_upwards [hK'.isClosed.isOpen_compl.mem_nhds hzK, hTo.mem_nhds hz] with w hw hwT
    by_contra hne
    apply hw
    refine ⟨φ.symm w, subset_tsupport u hne, φ.right_inv hwT⟩
  have hutCD : ContDiffOn ℝ 1 ut T := fun z hz =>
    ((CutoffRigidity.contDiffAt_comp_symm x₀ (hTe z hz) hu2).of_le (by norm_num)).contDiffWithinAt
  have hρCD : ContDiffOn ℝ 1 ρ T := fun z hz =>
    (CutoffRigidity.chartWeight_hasFDerivAt x₀ (hTe z hz) hV2).contDiffWithinAt
  set Yc := CutoffRigidity.chartCoordinateField (I := 𝓘(ℝ, F)) x₀
    (CutoffRigidity.manifoldGradient 𝓘(ℝ, F) v) with hYc
  have hYCD : ContDiffOn ℝ 1 Yc T := fun z hz =>
    (CutoffRigidity.contDiffAt_chartCoordinateField_grad x₀ (hTe z hz) hv2).contDiffWithinAt
  obtain ⟨hAi, hBi, hsum⟩ := CutoffRigidity.chart_divergence_zero hTo hK' hK'T hutCD hρCD hYCD hvan
  have hρcont : ContinuousOn ρ T := hρCD.continuousOn
  have hρnn : ∀ z ∈ T, 0 ≤ ρ z := fun z hz => (hρpos z hz).le
  have hdu : ContinuousOn (fun z => fderiv ℝ ut z) T :=
    hutCD.continuousOn_fderiv_of_isOpen hTo le_rfl
  have hdρ : ContinuousOn (fun z => fderiv ℝ ρ z) T :=
    hρCD.continuousOn_fderiv_of_isOpen hTo le_rfl
  have hdY : ContinuousOn (fun z => fderiv ℝ Yc z) T :=
    hYCD.continuousOn_fderiv_of_isOpen hTo le_rfl
  have hsupp0 : ∀ x, x ∉ φ.source → u x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hS (subset_tsupport u hne))
  have hgrad0 : ∀ x, x ∉ φ.source → CutoffRigidity.manifoldGradient 𝓘(ℝ, F) u x = 0 := by
    intro x hx
    apply CutoffRigidity.manifoldGradient_eq_zero_of_eventuallyEq
    have : x ∉ tsupport u := fun h => hx (hS h)
    exact notMem_tsupport_iff_eventuallyEq.mp this
  -- carré du champ
  have hcar : ∀ z ∈ T, carre F u v (φ.symm z) = fderiv ℝ ut z (Yc z) := fun z hz =>
    CutoffRigidity.inner_manifoldGradient_chart (v := v) x₀ (hTe z hz)
      ((hu2 _).mdifferentiableAt (by norm_num))
  have hcarc : ContinuousOn (carre F u v ∘ φ.symm) T :=
    ((hdu.clm_apply hYCD.continuousOn).congr (fun z hz => hcar z hz))
  have hcar0 : ∀ x, x ∉ φ.source → carre F u v x = 0 := by
    intro x hx
    change inner ℝ (CutoffRigidity.manifoldGradient 𝓘(ℝ, F) u x) _ = 0
    rw [hgrad0 x hx, inner_zero_left]
  have hI1 : ∫ x, carre F u v x ∂μ = ∫ z in T, ρ z * fderiv ℝ ut z (Yc z) := by
    rw [CutoffRigidity.integral_eq_chart_integral x₀ hμ' hρcont hρnn hcarc hcar0]
    exact setIntegral_congr_fun hTm (fun z hz => by rw [hcar z hz])
  -- generator
  have hN : ∀ z ∈ T, ρ z * mgenerator F V v (φ.symm z) =
      fderiv ℝ ρ z (Yc z) + ρ z * LinearMap.trace ℝ F (fderiv ℝ Yc z).toLinearMap := fun z hz =>
    CutoffRigidity.chartWeight_mul_generator x₀ (hTe z hz) hV2 hv2
  have hNc : ContinuousOn (fun z => fderiv ℝ ρ z (Yc z) +
      ρ z * LinearMap.trace ℝ F (fderiv ℝ Yc z).toLinearMap) T :=
    (hdρ.clm_apply hYCD.continuousOn).add
      (hρcont.mul (CutoffRigidity.traceCLM.continuous.comp_continuousOn hdY))
  have hgc : ContinuousOn ((fun x => u x * mgenerator F V v x) ∘ φ.symm) T := by
    have : ContinuousOn (fun z => ut z * ((fderiv ℝ ρ z (Yc z) +
        ρ z * LinearMap.trace ℝ F (fderiv ℝ Yc z).toLinearMap) / ρ z)) T :=
      hutCD.continuousOn.mul (hNc.div hρcont (fun z hz => (hρpos z hz).ne'))
    refine this.congr (fun z hz => ?_)
    simp only [Function.comp]
    rw [← hN z hz]
    have := (hρpos z hz).ne'
    field_simp
    exact mul_comm _ _
  have hg0 : ∀ x, x ∉ φ.source → u x * mgenerator F V v x = 0 := fun x hx => by
    rw [hsupp0 x hx, zero_mul]
  have hI2 : ∫ x, u x * mgenerator F V v x ∂μ = ∫ z in T, ut z * (fderiv ℝ ρ z (Yc z) +
      ρ z * LinearMap.trace ℝ F (fderiv ℝ Yc z).toLinearMap) := by
    rw [CutoffRigidity.integral_eq_chart_integral x₀ hμ' hρcont hρnn hgc hg0]
    refine setIntegral_congr_fun hTm (fun z hz => ?_)
    simp only [hut, Function.comp]
    rw [← hN z hz]
    ring
  rw [hI1, hI2]
  linarith

end CutCur
