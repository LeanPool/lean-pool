/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Measurability.StreamCubeResolventMeasurable
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ParameterizedProcessSemigroup
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Measurability.StreamResolventMeasurable

/-!
# Measurability of canonical quenched expectations

The transition argument is adapted from the Apache-2.0 upstream
`SuperdiffusionAudit/Support/SuperdiffusivityTransition.lean` at commit
`7f20476385d4af418f110303085ad0740c9eba46`. Here it applies directly to the
production process, so no duplicate diffusion characterization is needed.
-/

public section

namespace Algsuperdiff.Section5.Measurability

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form HCPolySupport MarkovProcess MeasureTheory ProbabilityTheory
open MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The canonical displacement observable has the live transition law. -/
theorem integral_streamProcess_eq_transition
    (M : ABKModel d) (omega : FullSample d M.gamma) (x : Vec d) (t : NNReal)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {G : Vec d → E} (hG : Continuous G) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    (∫ path, G (onePointRetract (0 : Vec d) (path t))
      ∂streamProcess M omega (x : OnePoint (Vec d))) =
      ∫ y, G y ∂(streamWholeSpaceResolvent M omega).kernelSemigroup t x := by
  let hreg := (streamExhaustionTailInput M omega).toOnePointRegular
  letI := hreg.metricSpace
  letI := hreg.completeSpace
  let R := streamWholeSpaceResolvent M omega
  have hev : Measurable (fun path : ContinuousPath (OnePoint (Vec d)) => path t) :=
    ContinuousPath.measurable_coordinateProcess t
  have hret : StronglyMeasurable (fun y : OnePoint (Vec d) =>
      G (onePointRetract (0 : Vec d) y)) :=
    (hG.measurable.comp (measurable_onePointRetract (0 : Vec d))).stronglyMeasurable
  have hmap : Measure.map (fun path : ContinuousPath (OnePoint (Vec d)) => path t)
      (streamProcess M omega (x : OnePoint (Vec d))) = R.onePointKernelSemigroup t x := by
    have hk := R.isFellerKernelSemigroup_onePointKernelSemigroup.continuousProcess_map_eval_nnreal
      R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
      hreg.kolmogorovRegular t
    exact (Kernel.map_apply _ hev (x : OnePoint (Vec d))).symm.trans
      (DFunLike.congr_fun hk (x : OnePoint (Vec d)))
  rw [← integral_map hev.aemeasurable hret.aestronglyMeasurable, hmap,
    R.onePointKernelSemigroup_apply_coe]
  have hmass : R.kernelSemigroup t x Set.univ = 1 :=
    isConservative_streamKernelSemigroup M omega t x
  rw [hmass, tsub_self, zero_smul, add_zero,
    integral_map OnePoint.continuous_coe.measurable.aemeasurable hret.aestronglyMeasurable]
  rfl

private theorem measurable_fix_second {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
    {F : α × β → E} (hF : Measurable F) (x : β) :
    Measurable (fun a => F (a, x)) :=
  hF.comp (measurable_id.prodMk measurable_const)

/-- A fixed starting point gives a measurable family of live transition measures. -/
theorem measurable_streamTransition_point
    (M : ABKModel d) (x : Vec d) (t : NNReal) :
    Measurable fun omega : FullSample d M.gamma =>
      (streamWholeSpaceResolvent M omega).kernelSemigroup t x := by
  apply measurable_fix_second
    (F := fun p : FullSample d M.gamma × Vec d =>
      (streamWholeSpaceResolvent M p.1).kernelSemigroup t p.2) (x := x)
  apply measurable_streamTransition_of_cube M
  intro mu f hf D hfD m y
  exact measurable_analyticCubeResolvent_stream M mu f hf D hfD m y

/-- Continuous observables of the canonical process have measurable quenched expectations. -/
theorem measurable_integral_streamProcess
    (M : ABKModel d) (x : Vec d) (t : NNReal)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {G : Vec d → E} (hG : Continuous G) :
    Measurable fun omega : FullSample d M.gamma =>
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ∫ path, G (onePointRetract (0 : Vec d) (path t))
        ∂streamProcess M omega (x : OnePoint (Vec d)) := by
  let K : Kernel (FullSample d M.gamma) (Vec d) :=
    ⟨fun omega => (streamWholeSpaceResolvent M omega).kernelSemigroup t x,
      measurable_streamTransition_point M x t⟩
  have hK : Measurable fun omega => ∫ y, G y ∂K omega :=
    (hG.stronglyMeasurable.integral_kernel (κ := K)).measurable
  have heq : (fun omega : FullSample d M.gamma =>
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ∫ path, G (onePointRetract (0 : Vec d) (path t))
        ∂streamProcess M omega (x : OnePoint (Vec d))) =
      fun omega => ∫ y, G y ∂K omega := by
    funext omega
    exact integral_streamProcess_eq_transition M omega x t hG
  rw [heq]
  exact hK

/-- Both quenched displacement expectations in Theorem A are measurable. -/
theorem measurable_streamProcess_displacement_expectations
    (M : ABKModel d) (t : NNReal) :
    Measurable (fun omega : FullSample d M.gamma =>
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ∫ path, onePointRetract (0 : Vec d) (path t)
        ∂streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))) ∧
    Measurable (fun omega : FullSample d M.gamma =>
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t))
        ∂streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))) := by
  refine ⟨measurable_integral_streamProcess M 0 t continuous_id, ?_⟩
  apply measurable_integral_streamProcess M 0 t
  unfold vecNormSq vecDot
  fun_prop

end

end Algsuperdiff.Section5.Measurability
