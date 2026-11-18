/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.WeightedGradient.Core
public import LeanPool.KLS.FunctionalInequalities.Energy.WeightedGradient.Closable
public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous
public import LeanPool.KLS.FunctionalInequalities.Energy.Form.Core
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance

/-!
# Raw/sequential-core agreement of the smooth-gradient pre-energy under density hypotheses

Source: Blueprint `thm:smooth-gradient-raw-core-agreement-density`. Read `LocalDensity`, its
consequences `LocalDensity.absolutelyContinuous`, `LocalDensity.frontier_support_null` and
`LocalDensity.locallyDominatesOn`, then `Test.toL2_mem_closure_domain`,
`lipschitzRelaxation_le_relaxation`, `preEnergy_agreesOnTests`, `preEnergy_isSequentialCoreFor`
and the intrinsic forms `Intrinsic.preEnergy_agreesOnTests`,
`Intrinsic.preEnergy_isSequentialCoreFor`.

Let `ν` be a probability law on a finite-dimensional real inner-product space `V` and `m` a Haar
measure. A *local density* for `ν` is an open set `Ω` carrying `ν`, on which `ν` has an `m`-density
`ρ` that is positive almost everywhere and whose reciprocal is locally essentially bounded. Under
these hypotheses the weighted gradient operator with unit weight is closable, and every smooth
test `f` (globally `C∞`, in `L²(ν)`, with square-integrable gradient) lies in the domain of the
closure with closure value `∇f`: smooth cutoffs of `f` are globally Lipschitz compactly supported
tests converging to `f` in graph norm. Hence the Lipschitz-gradient relaxation is at most the
smooth-gradient relaxation, and the raw energy `∫ ‖∇f‖² dν` of a smooth test equals its
relaxed energy: `AgreesOnTests`, and therefore `IsSequentialCoreFor`, since the relaxation is
definitionally sequentially generated.

The Blueprint also assumes `ρ ∈ L^∞_loc(Ω)`; that upper bound is not used here. Nothing is
asserted about laws without a local density, and no Cheeger-energy identification is claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy.SmoothGradient

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- Density hypotheses of the Blueprint: an open set `Ω` carrying `ν` on which `ν` has the
`m`-density `ρ`, positive almost everywhere with locally essentially bounded reciprocal. -/
structure LocalDensity (ν : ProbabilityMeasure V) (m : Measure V) where
  /-- The open set carrying the law. -/
  Ω : Set V
  isOpen : IsOpen Ω
  /-- The density on `Ω`. -/
  ρ : V → ℝ
  measurable : Measurable ρ
  /-- The complement of `Ω` is `ν`-null. -/
  compl_null : (ν : Measure V) Ωᶜ = 0
  /-- On Borel subsets of `Ω`, `ν` integrates `ρ` against `m`. -/
  restrict_eq : (ν : Measure V).restrict Ω =
    (m.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (ρ x)
  /-- The density is positive almost everywhere on `Ω`. -/
  pos : ∀ᵐ x ∂m, x ∈ Ω → 0 < ρ x
  /-- The reciprocal of the density is essentially bounded on compact subsets of `Ω`. -/
  inv_locallyBounded : ∀ K : Set V, IsCompact K → K ⊆ Ω → ∃ C : ℝ, ∀ᵐ x ∂m, x ∈ K → (ρ x)⁻¹ ≤ C

namespace LocalDensity

variable {ν : ProbabilityMeasure V} {m : Measure V} (D : LocalDensity ν m)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
/-- The law of a measurable subset of `Ω` is the integral of the density. -/
theorem measure_eq {s : Set V} (hs : MeasurableSet s) (hsΩ : s ⊆ D.Ω) :
    (ν : Measure V) s = ∫⁻ x in s, ENNReal.ofReal (D.ρ x) ∂m := by
  have h1 : (ν : Measure V) s = ((ν : Measure V).restrict D.Ω) s := by
    rw [Measure.restrict_apply hs, Set.inter_eq_self_of_subset_left hsΩ]
  rw [h1, D.restrict_eq, withDensity_apply _ hs, Measure.restrict_restrict hs,
    Set.inter_eq_self_of_subset_left hsΩ]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
include D in
/-- The law is absolutely continuous with respect to `m`. -/
theorem absolutelyContinuous : (ν : Measure V) ≪ m := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  have hsplit := measure_inter_add_sdiff (μ := (ν : Measure V)) s D.isOpen.measurableSet
  have h1 : (ν : Measure V) (s ∩ D.Ω) = 0 := by
    rw [D.measure_eq (hs.inter D.isOpen.measurableSet) Set.inter_subset_right]
    exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left hs0)
  have h2 : (ν : Measure V) (s \ D.Ω) = 0 := measure_mono_null (fun x hx ↦ hx.2) D.compl_null
  rw [← hsplit, h1, h2, add_zero]

variable [m.IsAddHaarMeasure]

section TestSupport

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- Every point of `Ω` lies in the support of the law. -/
theorem subset_support : D.Ω ⊆ (ν : Measure V).support := by
  intro x hx
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.mp hU
  set W := U' ∩ D.Ω with hW
  have hWo : IsOpen W := hU'o.inter D.isOpen
  have hWne : W.Nonempty := ⟨x, hxU', hx⟩
  have hWΩ : W ⊆ D.Ω := Set.inter_subset_right
  have hmeasf : Measurable fun y ↦ ENNReal.ofReal (D.ρ y) := D.measurable.ennreal_ofReal
  have hpos : 0 < (ν : Measure V) W := by
    rw [D.measure_eq hWo.measurableSet hWΩ, setLIntegral_pos_iff hmeasf]
    refine lt_of_lt_of_le (hWo.measure_pos m hWne) (measure_mono_ae ?_)
    filter_upwards [D.pos] with y hy hyW
    refine ⟨?_, hyW⟩
    rw [Function.mem_support]
    exact (ENNReal.ofReal_pos.mpr (hy (hWΩ hyW))).ne'
  exact hpos.trans_le (measure_mono (Set.inter_subset_left.trans hU'U))

/-- `Ω` lies in the interior of the support. -/
theorem subset_interior_support : D.Ω ⊆ interior (ν : Measure V).support :=
  interior_maximal D.subset_support D.isOpen

end TestSupport

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
include D in
/-- The frontier of the support is `ν`-null. -/
theorem frontier_support_null : (ν : Measure V) (frontier (ν : Measure V).support) = 0 := by
  refine measure_mono_null ?_ D.compl_null
  intro x hx hxΩ
  rw [Measure.isClosed_support.frontier_eq] at hx
  exact hx.2 (D.subset_interior_support hxΩ)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] [m.IsAddHaarMeasure] in
/-- On compact subsets of `Ω`, `m` is dominated by a constant multiple of `ν`. -/
theorem locallyDominatesOn : Probability.LocallyDominatesOn ν m D.Ω := by
  intro K hK hKΩ
  obtain ⟨C, hC⟩ := D.inv_locallyBounded K hK hKΩ
  set C' : ℝ := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨C'.toNNReal, Measure.le_iff.mpr fun s hs ↦ ?_⟩
  have hsK : MeasurableSet (s ∩ K) := hs.inter hK.measurableSet
  rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs,
    D.measure_eq hsK (Set.inter_subset_right.trans hKΩ), smul_eq_mul, ←
    lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  have hbound :
    ∀ᵐ x ∂(m.restrict (s ∩ K)), (1 : ℝ≥0∞) ≤ (C'.toNNReal : ℝ≥0∞) * ENNReal.ofReal (D.ρ x) := by
    rw [ae_restrict_iff' hsK]
    filter_upwards [hC, D.pos] with x hx hxpos hxsK
    have hρ : 0 < D.ρ x := hxpos (hKΩ hxsK.2)
    have hinv : (D.ρ x)⁻¹ ≤ C' := (hx hxsK.2).trans (le_max_left _ _)
    have hmul : 1 ≤ C' * D.ρ x := by
      rw [inv_le_iff_one_le_mul₀' hρ] at hinv
      linarith
    have : (C'.toNNReal : ℝ≥0∞) * ENNReal.ofReal (D.ρ x) = ENNReal.ofReal (C' * D.ρ x) := by
      rw [ENNReal.ofReal_mul hC'pos.le]
      rfl
    rw [this]
    exact ENNReal.one_le_ofReal.mpr hmul
  calc
    m (s ∩ K) = ∫⁻ x in s ∩ K, (1 : ℝ≥0∞) ∂m := by simp
    _ ≤ ∫⁻ x in s ∩ K, (C'.toNNReal : ℝ≥0∞) * ENNReal.ofReal (D.ρ x) ∂m :=
      lintegral_mono_ae hbound

end LocalDensity

section Agreement

variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure] (D : LocalDensity ν m)

open Energy.WeightedGradient Energy.Euclidean

/-- The unit-weight gradient operator on globally Lipschitz tests, under the density
hypotheses. -/
def lipschitzOperator : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  operator ν (ContinuousLinearMap.id ℝ V) D.absolutelyContinuous

/-- The operator is closable. -/
theorem lipschitzOperator_isClosable : (lipschitzOperator ν m D).IsClosable :=
  operator_isClosable_of_isOpen ν (ContinuousLinearMap.id ℝ V) D.absolutelyContinuous
    D.frontier_support_null D.isOpen D.compl_null D.locallyDominatesOn

omit [FiniteDimensional ℝ V] in
/-- The gradient of a smooth test is square integrable. -/
theorem Test.memLp_gradient (f : Test ν) : MemLp (gradient f.toFun) 2 (ν : Measure V) :=
  (memLp_two_iff_integrable_sq_norm (LipschitzApproximation.aestronglyMeasurable_gradient _ _)).mpr
    f.gradient_sq_integrable

/-- Smooth cutoffs: every smooth test is the graph-norm limit of globally Lipschitz compactly
supported tests, as elements of the operator domain. -/
theorem Test.exists_domain_sequence_tendsto (f : Test ν) :
    ∃ p : ℕ → (lipschitzOperator ν m D).domain,
      Tendsto
        (fun j ↦
          (((p j : (lipschitzOperator ν m D).domain) : Lp ℝ 2 (ν : Measure V)),
            lipschitzOperator ν m D (p j)))
        atTop (𝓝 (f.toL2, (Test.memLp_gradient ν f).toLp (gradient f.toFun))) := by
  have hac := D.absolutelyContinuous
  have hfr := D.frontier_support_null
  have hlip : LocallyLipschitz f.toFun :=
    (f.contDiff.of_le (by exact_mod_cast le_top)).locallyLipschitz
  have hgrad :
    MemLp (fun x ↦ (ContinuousLinearMap.id ℝ V) (gradient f.toFun x)) 2 (ν : Measure V) := by
    simpa using Test.memLp_gradient ν f
  obtain ⟨g, hg, hconv1, hconv2⟩ :=
    LipschitzApproximation.exists_compactSupport_weighted_L2 ν m hac
      (ContinuousLinearMap.id ℝ V) f.toFun hlip f.memLp_two hgrad
  have hIsTest : ∀ j, IsTest ν (ContinuousLinearMap.id ℝ V) (g j) := fun j ↦
    ⟨(hg j).2.1, (hg j).2.2.1, (hg j).2.2.2⟩
  refine
    ⟨fun j ↦
      ⟨(hIsTest j).memLp.toLp (g j),
        toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V) hac (hIsTest j)⟩,
      ?_⟩
  have hT :
    ∀ j,
      lipschitzOperator ν m D
          ⟨(hIsTest j).memLp.toLp (g j),
            toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V) hac (hIsTest j)⟩ =
        (hIsTest j).memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) (g j)) :=
    fun j ↦ operator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr (hIsTest j) _ rfl
  refine Filter.Tendsto.prodMk_nhds ?_ ?_
  · rw [tendsto_iff_dist_tendsto_zero]
    have h :
      ∀ j,
        dist ((hIsTest j).memLp.toLp (g j)) f.toL2 =
          (eLpNorm (fun x ↦ g j x - f.toFun x) 2 (ν : Measure V)).toReal := by
      intro j
      rw [dist_edist, Test.toL2, Lp.edist_toLp_toLp]
      rfl
    simp_rw [h]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv1
    simpa [Function.comp_def] using this
  · simp_rw [hT]
    rw [tendsto_iff_dist_tendsto_zero]
    have h :
      ∀ j,
        dist ((hIsTest j).memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) (g j)))
            ((Test.memLp_gradient ν f).toLp (gradient f.toFun)) =
          (eLpNorm
              (fun x ↦
                (ContinuousLinearMap.id ℝ V) (gradient (g j) x) -
                  (ContinuousLinearMap.id ℝ V) (gradient f.toFun x))
              2 (ν : Measure V)).toReal := by
      intro j
      rw [dist_edist, Lp.edist_toLp_toLp]
      rfl
    simp_rw [h]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv2
    simpa [Function.comp_def] using this

/-- Every smooth test lies in the domain of the closure of the Lipschitz operator, with closure
value its gradient. -/
theorem Test.toL2_mem_closure_domain (f : Test ν) :
    ∃ h : f.toL2 ∈ (lipschitzOperator ν m D).closure.domain,
      (lipschitzOperator ν m D).closure ⟨f.toL2, h⟩ =
        (Test.memLp_gradient ν f).toLp (gradient f.toFun) := by
  obtain ⟨p, hp⟩ := Test.exists_domain_sequence_tendsto ν m D f
  have hmem : (f.toL2, (Test.memLp_gradient ν f).toLp (gradient f.toFun)) ∈
      (lipschitzOperator ν m D).graph.topologicalClosure :=
    (Energy.mem_graph_topologicalClosure_iff _ _).mpr ⟨p, hp⟩
  rw [(lipschitzOperator_isClosable ν m D).graph_closure_eq_closure_graph,
    LinearPMap.mem_graph_iff] at hmem
  obtain ⟨z, hz1, hz2⟩ := hmem
  have hz1' : (z : Lp ℝ 2 (ν : Measure V)) = f.toL2 := hz1
  have hz2' : (lipschitzOperator ν m D).closure z =
      (Test.memLp_gradient ν f).toLp (gradient f.toFun) := hz2
  have hdom : f.toL2 ∈ (lipschitzOperator ν m D).closure.domain := hz1' ▸ z.2
  refine ⟨hdom, ?_⟩
  have hz : z = ⟨f.toL2, hdom⟩ := Subtype.ext hz1'
  rw [← hz]
  exact hz2'

section TestEnergy

omit [FiniteDimensional ℝ V]
/-- The raw energy of a smooth test is the squared `L²` norm of its gradient class. -/
theorem Test.coe_energy_eq_norm_toLp_sq (f : Test ν) :
    (f.energy : ℝ) = ‖(Test.memLp_gradient ν f).toLp (gradient f.toFun)‖ ^ 2 := by
  rw [Test.coe_energy, L2.norm_toLp_sq]

/-- The raw energy of a smooth test, in `ENNReal`, is the squared `NNReal` norm of its gradient
class. -/
theorem Test.energy_eq_nnnorm_sq (f : Test ν) :
    (f.energy : ENNReal) =
      ((‖(Test.memLp_gradient ν f).toLp (gradient f.toFun)‖₊ ^ 2 : ℝ≥0) : ENNReal) := by
  apply ENNReal.coe_inj.mpr
  apply NNReal.eq
  push_cast
  exact Test.coe_energy_eq_norm_toLp_sq ν f

end TestEnergy

/-- The Lipschitz-gradient relaxation is at most the smooth-gradient relaxation: smooth cutoffs are
recovery sequences for smooth tests. -/
theorem lipschitzRelaxation_le_relaxation (x : Lp ℝ 2 (ν : Measure V)) :
    (PreEnergy.ofLinearPMap (lipschitzOperator ν m D)).sequentialRelaxation x ≤ relaxation ν x := by
  refine PreEnergy.sequentialRelaxation_le_of_recovery_sequences (preEnergy ν)
    (PreEnergy.ofLinearPMap (lipschitzOperator ν m D)) (fun f ↦ ?_) x
  obtain ⟨p, hp⟩ := Test.exists_domain_sequence_tendsto ν m D f
  have h1 : Tendsto (fun j ↦ ((p j : (lipschitzOperator ν m D).domain) : Lp ℝ 2 (ν : Measure V)))
      atTop (𝓝 f.toL2) := (continuous_fst.tendsto _).comp hp
  have h2 : Tendsto (fun j ↦ lipschitzOperator ν m D (p j)) atTop
      (𝓝 ((Test.memLp_gradient ν f).toLp (gradient f.toFun))) := (continuous_snd.tendsto _).comp hp
  refine ⟨⟨p, h1⟩, le_of_eq ?_⟩
  change liminf (fun j ↦ (((‖lipschitzOperator ν m D (p j)‖₊ ^ 2 : ℝ≥0)) : ENNReal)) atTop =
    (f.energy : ENNReal)
  have h3 : Tendsto (fun j ↦ (((‖lipschitzOperator ν m D (p j)‖₊ ^ 2 : ℝ≥0)) : ENNReal)) atTop
      (𝓝 (((‖(Test.memLp_gradient ν f).toLp (gradient f.toFun)‖₊ ^ 2 : ℝ≥0)) : ENNReal)) := by
    apply ENNReal.tendsto_coe.mpr
    exact ((continuous_nnnorm.tendsto _).comp h2).pow 2
  rw [h3.liminf_eq]
  exact (Test.energy_eq_nnnorm_sq ν f).symm

include D in
/--
Blueprint `thm:smooth-gradient-raw-core-agreement-density`, agreement part: under the density
hypotheses the smooth-gradient relaxation of the class of a smooth test is its raw energy. -/
theorem preEnergy_agreesOnTests : (preEnergy ν).AgreesOnTests (relaxation ν) := by
  intro f
  refine le_antisymm ((preEnergy ν).sequentialRelaxation_toAmbient_le f) ?_
  obtain ⟨hdom, hval⟩ := Test.toL2_mem_closure_domain ν m D f
  calc
    ((preEnergy ν).energy f : ENNReal) = (f.energy : ENNReal) := rfl
    _ = (PreEnergy.ofLinearPMap (lipschitzOperator ν m D)).sequentialRelaxation f.toL2 := by
      rw [PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem _
          (lipschitzOperator_isClosable ν m D) ⟨f.toL2, hdom⟩,
        hval]
      exact Test.energy_eq_nnnorm_sq ν f
    _ ≤ relaxation ν ((preEnergy ν).toAmbient f) := lipschitzRelaxation_le_relaxation ν m D _

include D in
/-- Blueprint `thm:smooth-gradient-raw-core-agreement-density`: the smooth-gradient pre-energy is a
sequential form core for its relaxation under the density hypotheses. -/
theorem preEnergy_isSequentialCoreFor : (preEnergy ν).IsSequentialCoreFor (relaxation ν) :=
  ⟨preEnergy_agreesOnTests ν m D, rfl⟩

end Agreement

namespace Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
  [m.IsAddHaarMeasure] (D : LocalDensity (Probability.intrinsicMeasure μ) m)

omit [CompleteSpace E] in
include D in
/-- The intrinsic form of the Blueprint statement: the intrinsic smooth-gradient pre-energy of `μ`
agrees on tests with its relaxation when the intrinsic law has a local density. -/
theorem preEnergy_agreesOnTests :
    (preEnergy (Probability.intrinsicMeasure μ)).AgreesOnTests
      (relaxation (Probability.intrinsicMeasure μ)) :=
  SmoothGradient.preEnergy_agreesOnTests _ m D

omit [CompleteSpace E] in
include D in
/-- The intrinsic pre-energy is a sequential form core for the intrinsic relaxation. -/
theorem preEnergy_isSequentialCoreFor :
    (preEnergy (Probability.intrinsicMeasure μ)).IsSequentialCoreFor
      (relaxation (Probability.intrinsicMeasure μ)) :=
  SmoothGradient.preEnergy_isSequentialCoreFor _ m D

end Intrinsic

end FunctionalInequalities.Energy.SmoothGradient
