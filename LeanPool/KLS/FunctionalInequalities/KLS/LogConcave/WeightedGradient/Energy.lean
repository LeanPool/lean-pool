/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Closure
public import LeanPool.KLS.FunctionalInequalities.Energy.Cheeger.Identification
public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Core

/-!
# The unit-weight log-concave gradient generates the canonical energy

For a full-dimensional log-concave probability law, the squared norm form of the closed
unit-weight gradient is the smooth-gradient relaxation, hence twice the selected Cheeger energy.
This is the normalization bridge used by the heat-semigroup route: it does not identify a
differential expression for the generator and proves no Bakry--Émery estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.Euclidean Probability

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section FullDimensional

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]

omit [CompleteSpace V] in
/-- A full-dimensional log-concave law admits the local-density package used by the smooth-core
comparison. -/
theorem exists_smoothGradient_localDensity (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Nonempty (Energy.SmoothGradient.LocalDensity ν m) := by
  obtain ⟨ρ, hρ⟩ := hν.exists_isBorellDensity_of_interior_support_nonempty m hi
    (hν.absolutelyContinuous_haar m hi)
  refine ⟨{
    Ω := interior (ν : Measure V).support
    isOpen := isOpen_interior
    ρ := ρ
    measurable := hρ.measurable
    compl_null := ?_
    restrict_eq := ?_
    pos := ?_
    inv_locallyBounded := ?_ }⟩
  · have hsub : (interior (ν : Measure V).support)ᶜ ⊆
        (ν : Measure V).supportᶜ ∪ frontier (ν : Measure V).support := by
      intro x hx
      by_cases hs : x ∈ (ν : Measure V).support
      · exact Or.inr ⟨subset_closure hs, hx⟩
      · exact Or.inl hs
    exact measure_mono_null hsub
      (measure_union_null Measure.measure_compl_support (hν.frontier_support_eq_zero hi))
  · rw [← hρ.withDensity_eq,
      MeasureTheory.restrict_withDensity isOpen_interior.measurableSet]
  · exact Filter.Eventually.of_forall fun x hx ↦ hρ.pos_of_mem_interior_support hx
  · intro K hK hKΩ
    obtain ⟨a, _b, ha, hab⟩ := hρ.exists_bounds_of_isCompact hK hKΩ
    refine ⟨a⁻¹, Filter.Eventually.of_forall fun x hx ↦ ?_⟩
    simpa only [one_div] using one_div_le_one_div_of_le ha (hab x hx).1

/-- The local-slope relaxation is bounded by the unit-weight operator relaxation.  This is the
easy inclusion of globally Lipschitz operator tests into the literature local-slope test class. -/
private theorem localSlope_relaxation_le_weightedRelaxation (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    (x : Lp ℝ 2 (ν : Measure V)) :
    Energy.LocalSlope.relaxation ν x ≤
      (PreEnergy.ofLinearPMap
        (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)).sequentialRelaxation x := by
  let hac : (ν : Measure V) ≪ m := hν.absolutelyContinuous_haar m hi
  refine (PreEnergy.ofLinearPMap
      (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)).sequentialRelaxation_comp_le
    (Energy.LocalSlope.preEnergy ν) id continuous_id ?_ x
  rintro ⟨f, hf⟩
  obtain ⟨g, hg, hfg⟩ :=
    (Energy.WeightedGradient.mem_domain_operator_iff ν
      (ContinuousLinearMap.id ℝ V) hac f).mp hf
  obtain ⟨K, hK⟩ := hg.1
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [Energy.WeightedGradient.apply_id] using hg.memLp_apply
  have hadm : Energy.LocalSlope.Admissible ν g :=
    (Energy.LocalSlope.admissible_iff_memLp_gradient ν m hac g).mpr
      ⟨hK.locallyLipschitz, hg.memLp, hgrad⟩
  have hT : hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨f, hf⟩ =
      hgrad.toLp (gradient g) := by
    rw [Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac
      (hν.frontier_support_eq_zero hi) hg hf hfg]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y ↦ by
      rw [Energy.WeightedGradient.apply_id])
  refine ⟨⟨g, hadm⟩, hfg.symm, ?_⟩
  apply ENNReal.coe_le_coe.mp
  change ((Energy.LocalSlope.energy ν g).toNNReal : ENNReal) ≤
    ((‖hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨f, hf⟩‖₊ ^ 2 : NNReal) : ENNReal)
  rw [ENNReal.coe_toNNReal hadm.finite_energy, hT,
    Energy.LocalSlope.energy_eq_integral_gradient ν m hac g hK.locallyLipschitz hgrad,
    ← L2.norm_toLp_sq hgrad]
  rw [← ENNReal.ofReal_coe_nnreal]
  exact le_rfl

/-- The sequential relaxation of the unit-weight Lipschitz gradient operator is the canonical
smooth-gradient energy. -/
theorem weightedRelaxation_id_eq_smoothGradient (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (PreEnergy.ofLinearPMap
      (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)).sequentialRelaxation =
        Energy.SmoothGradient.relaxation ν := by
  obtain ⟨D⟩ := hν.exists_smoothGradient_localDensity m hi
  apply Functional.ext
  intro x
  apply le_antisymm
  · simpa [Energy.SmoothGradient.lipschitzOperator, weightedOperator] using
      Energy.SmoothGradient.lipschitzRelaxation_le_relaxation ν m D x
  · rw [Energy.SmoothGradient.relaxation_eq_localSlope ν]
    exact localSlope_relaxation_le_weightedRelaxation m hν hi x

/-- The squared norm form of the closed unit-weight gradient is the canonical energy. -/
theorem closedWeightedOperator_id_energy_eq_smoothGradient (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    PreEnergy.normSqEnergy
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) =
        Energy.SmoothGradient.relaxation ν := by
  rw [← weightedRelaxation_id_eq_smoothGradient m hν hi]
  exact (PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy
    (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)
    (hν.weightedOperator_isClosable m (ContinuousLinearMap.id ℝ V) hi)).symm

/-- Pointwise normalization: the closed unit-weight gradient form is twice the selected Cheeger
energy. -/
theorem closedWeightedOperator_id_energy_eq_two_mul_cheeger (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    (f : Lp ℝ 2 (ν : Measure V)) :
    PreEnergy.normSqEnergy
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) f =
      2 * Energy.Cheeger.energy ν f := by
  rw [closedWeightedOperator_id_energy_eq_smoothGradient m hν hi,
    Energy.SmoothGradient.relaxation_eq_two_mul_cheeger]

end FullDimensional

end FunctionalInequalities.KLS.LogConcave
