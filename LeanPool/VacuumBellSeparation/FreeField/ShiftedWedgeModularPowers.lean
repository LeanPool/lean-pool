/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ShiftedWedgeModularGraph
public import LeanPool.VacuumBellSeparation.FreeField.SourceModularResolvent
public import LeanPool.VacuumBellSeparation.FreeField.UnitaryResolventPowers
public import LeanPool.VacuumBellSeparation.FreeField.SourcePowerRangeWitness
public import LeanPool.VacuumBellSeparation.FreeField.ModularWeightInclusion

/-!
# Full original source powers for every translated left wedge

The actual polar unitary and the proved shifted logistic resolvent identify
all fractional powers in [0,1] with the translated maximal exponential.
The whole original source satisfies the bounded Gram-weight graph formula
for exponents in [0,1/2]. No boundedness of the halfspace is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ContinuousLinearMap

variable {m : ℝ} (hm : 0 < m) (ℓ : ℝ)

theorem shiftedWedgeSourceMap_adjoint (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    (complexSourceMap hm (leftWedgeTimeZero ℓ)).adjoint ψ =
      CFC.sqrt (sourceGram hm (leftWedgeTimeZero ℓ))
        ((leftWedgeSourcePolarUnitary hm ℓ).symm ψ) := by
  apply ext_inner_right ℂ
  intro z
  rw [(complexSourceMap hm (leftWedgeTimeZero ℓ)).adjoint_inner_left]
  rw [← leftWedgeSourcePolarUnitary_factorization hm ℓ z]
  have hi := (leftWedgeSourcePolarUnitary hm ℓ).inner_map_map
    ((leftWedgeSourcePolarUnitary hm ℓ).symm ψ)
    (CFC.sqrt (sourceGram hm (leftWedgeTimeZero ℓ)) z)
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  rw [hi]
  exact ((CFC.sqrt_nonneg (sourceGram hm (leftWedgeTimeZero ℓ))).isSelfAdjoint.isSymmetric _ _).symm

theorem shiftedWedgeSourcePolar_resolvent :
    (leftWedgeSourcePolarUnitary hm ℓ).conjStarAlgEquiv
      (sourceModularResolvent hm (leftWedgeTimeZero ℓ)) =
        sourcePhysicalResolvent hm (leftWedgeTimeZero ℓ) := by
  apply ContinuousLinearMap.ext
  intro ψ
  change leftWedgeSourcePolarUnitary hm ℓ
    ((1 / 2 : ℝ) • sourceGram hm (leftWedgeTimeZero ℓ)
      ((leftWedgeSourcePolarUnitary hm ℓ).symm ψ)) =
      (1 / 2 : ℝ) • complexSourceMap hm (leftWedgeTimeZero ℓ)
        ((complexSourceMap hm (leftWedgeTimeZero ℓ)).adjoint ψ)
  have hsmul := (leftWedgeSourcePolarUnitary hm ℓ).toLinearEquiv.toLinearMap.map_smul_of_tower
    (1 / 2 : ℝ) (sourceGram hm (leftWedgeTimeZero ℓ)
      ((leftWedgeSourcePolarUnitary hm ℓ).symm ψ))
  change leftWedgeSourcePolarUnitary hm ℓ
    ((1 / 2 : ℝ) • sourceGram hm (leftWedgeTimeZero ℓ)
      ((leftWedgeSourcePolarUnitary hm ℓ).symm ψ)) =
        (1 / 2 : ℝ) • leftWedgeSourcePolarUnitary hm ℓ
          (sourceGram hm (leftWedgeTimeZero ℓ)
            ((leftWedgeSourcePolarUnitary hm ℓ).symm ψ)) at hsmul
  rw [hsmul, shiftedWedgeSourceMap_adjoint,
    ← leftWedgeSourcePolarUnitary_factorization]
  congr 2
  exact (congrArg (fun A : ComplexSourceHilbert hm (leftWedgeTimeZero ℓ) →L[ℂ]
      ComplexSourceHilbert hm (leftWedgeTimeZero ℓ) =>
      A ((leftWedgeSourcePolarUnitary hm ℓ).symm ψ))
    (CFC.sqrt_mul_sqrt_self (sourceGram hm (leftWedgeTimeZero ℓ))
      (nonneg_iff_isPositive.mpr (sourceGram_isPositive hm (leftWedgeTimeZero ℓ))))).symm

/-- Linear isometry equivalence for the shifted wedge source Fourier unitary, of type
`ComplexSourceHilbert hm (leftWedgeTimeZero ℓ) ≃ₗᵢ[ℂ] RapidityL2`. -/
noncomputable def shiftedWedgeSourceFourierUnitary :
    ComplexSourceHilbert hm (leftWedgeTimeZero ℓ) ≃ₗᵢ[ℂ] RapidityL2 :=
  (leftWedgeSourcePolarUnitary hm ℓ).trans (shiftedWedgeFourier hm ℓ)

theorem shiftedWedgeSourceFourier_resolvent :
    (shiftedWedgeSourceFourierUnitary hm ℓ).conjStarAlgEquiv
      (sourceModularResolvent hm (leftWedgeTimeZero ℓ)) =
        exponentialResolvent rapidityMeasure (rapidityFrequencyExponent 1)
          (measurable_rapidityFrequencyExponent 1) := by
  rw [shiftedWedgeSourceFourierUnitary, LinearIsometryEquiv.conjStarAlgEquiv_trans]
  change (shiftedWedgeFourier hm ℓ).conjStarAlgEquiv
    ((leftWedgeSourcePolarUnitary hm ℓ).conjStarAlgEquiv
      (sourceModularResolvent hm (leftWedgeTimeZero ℓ))) = _
  rw [shiftedWedgeSourcePolar_resolvent]
  apply ContinuousLinearMap.ext
  intro f
  change shiftedWedgeFourier hm ℓ (sourcePhysicalResolvent hm (leftWedgeTimeZero ℓ)
    ((shiftedWedgeFourier hm ℓ).symm f)) = _
  rw [shiftedWedgePhysicalResolvent_fourier, LinearIsometryEquiv.apply_symm_apply]

theorem shiftedWedgeSourceModularResolvent_injective :
    Function.Injective (sourceModularResolvent hm (leftWedgeTimeZero ℓ)) := by
  have hG : Function.Injective (sourceGram hm (leftWedgeTimeZero ℓ)) :=
    (complexSourceMap hm (leftWedgeTimeZero ℓ)).adjoint_comp_self_injective_iff.mpr
      (complexSourceMap_injective_leftWedgeTimeZero hm ℓ)
  intro x y hxy
  apply hG
  change (1 / 2 : ℝ) • sourceGram hm (leftWedgeTimeZero ℓ) x =
    (1 / 2 : ℝ) • sourceGram hm (leftWedgeTimeZero ℓ) y at hxy
  exact (smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0)) hxy


/-- Shifted wedge source power. -/
noncomputable def shiftedWedgeSourcePower (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    ComplexSourceHilbert hm (leftWedgeTimeZero ℓ) →ₗ.[ℂ]
      ComplexSourceHilbert hm (leftWedgeTimeZero ℓ) :=
  resolventPowerRatio (sourceModularResolvent hm (leftWedgeTimeZero ℓ))
    (sourceModularResolvent_nonneg hm (leftWedgeTimeZero ℓ))
    (shiftedWedgeSourceModularResolvent_injective hm ℓ) c hc hc1

theorem shiftedWedgeSourcePower_fourier {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitaryPartialTransport (shiftedWedgeSourceFourierUnitary hm ℓ)
      (shiftedWedgeSourcePower hm ℓ c hc hc1) = rapidityExponential c := by
  rw [shiftedWedgeSourcePower,
    unitaryPartialTransport_resolventPowerRatio (shiftedWedgeSourceFourierUnitary hm ℓ)
      _ (sourceModularResolvent_nonneg hm (leftWedgeTimeZero ℓ))
      (sourceModularResolvent_le_one hm (leftWedgeTimeZero ℓ))
      (shiftedWedgeSourceModularResolvent_injective hm ℓ)
      _ (exponentialResolvent_nonneg rapidityMeasure _ _)
      (exponentialResolvent_le_one rapidityMeasure _ _)
      (exponentialResolvent_injective rapidityMeasure _ _)
      (shiftedWedgeSourceFourier_resolvent hm ℓ) hc hc1,
    resolventPowerRatio_exponentialResolvent rapidityMeasure _ _ hc hc1]
  have he : (fun ξ => c * rapidityFrequencyExponent 1 ξ) = rapidityFrequencyExponent c := by
    ext ξ
    unfold rapidityFrequencyExponent
    ring
  simp only [he, rapidityExponential]

theorem shiftedWedgeSourcePower_graph_fourier {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (x y : ComplexSourceHilbert hm (leftWedgeTimeZero ℓ)) :
    (x, y) ∈ (shiftedWedgeSourcePower hm ℓ c hc hc1).graph ↔
      (shiftedWedgeSourceFourierUnitary hm ℓ x, shiftedWedgeSourceFourierUnitary hm ℓ y) ∈
        (rapidityExponential c).graph := by
  rw [← shiftedWedgeSourcePower_fourier hm ℓ hc hc1, unitaryPartialTransport_mem_graph,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]

theorem shiftedWedgeSourcePower_physical {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitaryPartialTransport (leftWedgeSourcePolarUnitary hm ℓ)
      (shiftedWedgeSourcePower hm ℓ c hc hc1) = shiftedWedgeExponential hm ℓ c := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rcases p with ⟨x, y⟩
  rw [unitaryPartialTransport_mem_graph, shiftedWedgeExponential_mem_graph,
    shiftedWedgeSourcePower_graph_fourier hm ℓ hc hc1]
  simp only [shiftedWedgeSourceFourierUnitary, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem shiftedWedgeSourcePower_sqrt_graph {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (z : ComplexSourceHilbert hm (leftWedgeTimeZero ℓ)) :
    (sourceGramRoot hm (leftWedgeTimeZero ℓ) z,
      sourceModularWeight hm (leftWedgeTimeZero ℓ) c z) ∈
        (shiftedWedgeSourcePower hm ℓ c hc (by linarith)).graph := by
  rw [shiftedWedgeSourcePower, resolventPowerRatio, boundedRatio_mem_graph]
  exact sourceModularWeight_range_witness hm (leftWedgeTimeZero ℓ) hc hc2 z

/-- Whole-source equality in the actual maximal physical power graph. -/
theorem shiftedWedgeExponential_source_graph {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (z : ComplexSourceHilbert hm (leftWedgeTimeZero ℓ)) :
    (complexSourceMap hm (leftWedgeTimeZero ℓ) z,
      leftWedgeSourcePolarUnitary hm ℓ (sourceModularWeight hm (leftWedgeTimeZero ℓ) c z)) ∈
        (shiftedWedgeExponential hm ℓ c).graph := by
  rw [← shiftedWedgeSourcePower_physical hm ℓ hc (by linarith), unitaryPartialTransport_mem_graph,
    ← leftWedgeSourcePolarUnitary_factorization hm ℓ z,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
  exact shiftedWedgeSourcePower_sqrt_graph hm ℓ hc hc2 z

/-- Literal containing-wedge estimate on every original completed source. -/
theorem shiftedWedgeExponential_containing_wedge
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ⊆ leftWedgeTimeZero ℓ)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) (z : ComplexSourceHilbert hm U) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (complexSourceMap hm U z, χ) ∈ (shiftedWedgeExponential hm ℓ c).graph ∧
        ‖χ‖ ≤ ‖sourceModularWeight hm U c z‖ := by
  refine ⟨leftWedgeSourcePolarUnitary hm ℓ
    (sourceModularWeight hm (leftWedgeTimeZero ℓ) c (complexSourceInclusion hm hU z)), ?_, ?_⟩
  · have h := shiftedWedgeExponential_source_graph hm ℓ hc.le hc2 (complexSourceInclusion hm hU z)
    have he : complexSourceMap hm (leftWedgeTimeZero ℓ) (complexSourceInclusion hm hU z) =
        complexSourceMap hm U z :=
      DFunLike.congr_fun (complexSourceMap_comp_inclusion hm hU) z
    simpa only [he] using h
  · rw [LinearIsometryEquiv.norm_map]
    exact sourceModularWeight_inclusion_norm hm hU hc hc2 z

end VacuumBellSeparation
