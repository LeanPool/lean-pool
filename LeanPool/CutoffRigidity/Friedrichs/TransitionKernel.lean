/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Adapted from CutoffRigidity/Riemann/DiffKer3.lean through DiffKer5.lean for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.ContinuousRepresentatives
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Kernel.Composition.Comp

/-! # A Markov kernel from a conservative L² operator with continuous representatives -/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CutoffRigidity.L2Kernel.HasContinuousRepresentatives

section Indicator

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The L² vector represented by a measurable set's indicator function. -/
noncomputable def indicatorVector {A : Set X} (hA : MeasurableSet A) : X →₂[μ] ℝ :=
  indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)

/-- An indicator vector is represented by the corresponding indicator almost everywhere. -/
theorem ae_indicatorVector {A : Set X} (hA : MeasurableSet A) :
    (indicatorVector (μ := μ) hA : X → ℝ) =ᵐ[μ] A.indicator (fun _ => 1) :=
  indicatorConstLp_coeFn

/-- A measurable set's indicator vector is nonnegative almost everywhere. -/
theorem indicatorVector_nonneg {A : Set X} (hA : MeasurableSet A) :
    0 ≤ᵐ[μ] (indicatorVector (μ := μ) hA : X → ℝ) := by
  filter_upwards [ae_indicatorVector (μ := μ) hA] with y hy
  rw [hy]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) y

end Indicator

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]
  {T : (X →₂[μ] ℝ) →L[ℝ] (X →₂[μ] ℝ)} (h : HasContinuousRepresentatives T)

private noncomputable def evalContinuous (x : X) : (X →₂[μ] ℝ) →L[ℝ] ℝ :=
  let evaluation : (X →₂[μ] ℝ) →ₗ[ℝ] ℝ := ((ContinuousMap.evalCLM ℝ x).toLinearMap).comp h.lift
  let bounds := h.locally_bounded (isCompact_singleton (x := x))
  evaluation.mkContinuous (Classical.choose bounds) fun u =>
    Classical.choose_spec bounds u x (mem_singleton x)

/-- The L² density obtained by Riesz representation of point evaluation. -/
noncomputable def density (x : X) : X →₂[μ] ℝ :=
  (InnerProductSpace.toDual ℝ (X →₂[μ] ℝ)).symm (evalContinuous h x)

/-- Pairing with the density gives the value of the continuous representative. -/
theorem inner_density (x : X) (u : X →₂[μ] ℝ) :
    inner ℝ (h.density x) u = h.representative u x :=
  InnerProductSpace.toDual_symm_apply

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
/-- If the operator preserves nonnegativity, its continuous representative is nonnegative. -/
theorem representative_nonneg
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ))
    (u : X →₂[μ] ℝ) (hu : 0 ≤ᵐ[μ] u) (x : X) :
    0 ≤ h.representative u x := by
  have hAE : ∀ᵐ y ∂μ, 0 ≤ h.representative u y := by
    filter_upwards [positive u hu, h.ae_representative u] with y hPos hRep
    exact hRep ▸ hPos
  have hClosed : IsClosed {y | 0 ≤ h.representative u y} :=
    isClosed_le continuous_const (h.representative u).continuous
  have hUniv : {y | 0 ≤ h.representative u y} = univ := by
    apply (hClosed.ae_eq_univ_iff_eq (μ := μ)).mp
    filter_upwards [hAE] with y hy
    simp [hy]
  change x ∈ {y | 0 ≤ h.representative u y}
  rw [hUniv]
  exact mem_univ x

/-- The Riesz density of a positive operator has nonnegative values almost everywhere. -/
theorem density_nonneg
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ)) (x : X) :
    0 ≤ᵐ[μ] (h.density x : X → ℝ) := by
  let p := h.density x
  let q := Lp.negPart p
  have hq : 0 ≤ᵐ[μ] (q : X → ℝ) := by
    filter_upwards [Lp.coeFn_negPart_eq_max p] with y hy
    exact hy.symm ▸ le_max_right _ _
  have hPair : inner ℝ p q = -∫ y, q y ^ 2 ∂μ := by
    rw [L2.inner_def, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_negPart_eq_max p] with y hy
    change q y = max (-p y) 0 at hy
    simp only [RCLike.inner_apply, conj_trivial, hy]
    rcases le_total (p y) 0 with hy' | hy'
    · rw [max_eq_left (neg_nonneg.mpr hy'), neg_mul, neg_sq, pow_two]
    · simp [max_eq_right (neg_nonpos.mpr hy')]
  have hPos : 0 ≤ inner ℝ p q := h.inner_density x q ▸ h.representative_nonneg positive q hq x
  have hIntegral : ∫ y, q y ^ 2 ∂μ = 0 :=
    le_antisymm (neg_nonneg.mp (hPair ▸ hPos)) (integral_nonneg fun _ => sq_nonneg _)
  have hZero : (fun y => q y ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (q y))
      (Lp.memLp q).integrable_sq).mp hIntegral
  filter_upwards [hZero, Lp.coeFn_negPart_eq_max p] with y hy hqy
  have hq0 : q y = 0 := by simpa using hy
  have hLe : -p y ≤ 0 := (le_max_left _ (0 : ℝ)).trans_eq (hqy.symm.trans hq0)
  exact neg_nonpos.mp hLe

variable [IsFiniteMeasure μ]

private noncomputable def measureAt (x : X) : Measure X :=
  μ.withDensity fun y => ENNReal.ofReal (h.density x y)

private theorem measureAt_apply
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ))
    (x : X) {A : Set X} (hA : MeasurableSet A) :
    h.measureAt x A = ENNReal.ofReal (h.representative (indicatorVector hA) x) := by
  rw [measureAt, withDensity_apply _ hA]
  have hi : Integrable (h.density x : X → ℝ) (μ.restrict A) :=
    ((Lp.memLp _).integrable one_le_two).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_restrict_of_ae (h.density_nonneg positive x))]
  congr 1
  rw [← h.inner_density, real_inner_comm, indicatorVector, L2.inner_indicatorConstLp_one]

/-- The kernel representing a positive operator whose outputs have continuous representatives. -/
noncomputable def kernel
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ)) :
    Kernel X X where
  toFun := h.measureAt
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [h.measureAt_apply positive _ hA]
    exact ENNReal.measurable_ofReal.comp
      (h.representative (indicatorVector hA)).continuous.measurable

/-- The kernel applied to a measurable set equals the continuous output of that set's indicator. -/
theorem kernel_apply
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ))
    (x : X) {A : Set X} (hA : MeasurableSet A) :
    h.kernel positive x A = ENNReal.ofReal (h.representative (indicatorVector hA) x) :=
  h.measureAt_apply positive x hA

/-- Every transition measure is absolutely continuous with respect to the reference measure. -/
theorem kernel_ac
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ)) (x : X) :
    h.kernel positive x ≪ μ :=
  withDensity_absolutelyContinuous _ _

/-- Integrating an L² vector against the kernel gives its continuous output. -/
theorem kernel_integral
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ))
    (x : X) (u : X →₂[μ] ℝ) :
    Integrable (u : X → ℝ) (h.kernel positive x) ∧
      (∫ y, u y ∂h.kernel positive x) = h.representative u x := by
  let p := h.density x
  have hMeas : Measurable fun y => (p y).toNNReal :=
    (Lp.stronglyMeasurable p).measurable.real_toNNReal
  change Integrable (u : X → ℝ) (μ.withDensity fun y => (p y).toNNReal) ∧
    (∫ y, u y ∂μ.withDensity (fun z => (p z).toNNReal)) = h.representative u x
  have hProd : Integrable (fun y => p y * u y) μ :=
    (Lp.memLp p).integrable_mul (Lp.memLp u)
  have hAE : (fun y => (p y).toNNReal • u y) =ᵐ[μ] fun y => p y * u y := by
    filter_upwards [h.density_nonneg positive x] with y hy
    change 0 ≤ p y at hy
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hy]
  refine ⟨?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul hMeas]
    exact hProd.congr hAE.symm
  · rw [integral_withDensity_eq_integral_smul hMeas, integral_congr_ae hAE, ← h.inner_density,
      L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm, p]

/-- Composition of positive operators with continuous representatives is represented by the
composition of their kernels, in transition order. -/
theorem kernel_comp_eq {S U : (X →₂[μ] ℝ) →L[ℝ] (X →₂[μ] ℝ)}
    (hS : HasContinuousRepresentatives S) (hU : HasContinuousRepresentatives U)
    (hEq : U = S * T)
    (posS : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (S u : X → ℝ))
    (posT : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ))
    (posU : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (U u : X → ℝ)) :
    hU.kernel posU = (h.kernel posT) ∘ₖ (hS.kernel posS) := by
  ext x A hA
  rw [Kernel.comp_apply' _ _ _ hA, hU.kernel_apply posU x hA]
  simp_rw [h.kernel_apply posT _ hA]
  let u := indicatorVector (μ := μ) hA
  have hRep := h.ae_representative u
  have hRep' := (hS.kernel_ac posS x) hRep
  have hIntegral := hS.kernel_integral posS x (T u)
  rw [← ofReal_integral_eq_lintegral_ofReal (hIntegral.1.congr hRep')
    (ae_of_all _ (h.representative_nonneg posT u (indicatorVector_nonneg hA)))]
  rw [← integral_congr_ae hRep', hIntegral.2]
  congr 1
  apply congrArg (fun f : C(X, ℝ) => f x)
  apply hU.representative_eq
  rw [hEq, mul_apply_eq_comp]
  exact hS.ae_representative (T u)

/-- If the positive operator fixes one, its kernel is Markov. -/
theorem kernel_markov
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ))
    (one : T (Lp.const 2 μ (1 : ℝ)) = Lp.const 2 μ (1 : ℝ)) :
    IsMarkovKernel (h.kernel positive) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [h.kernel_apply positive x MeasurableSet.univ]
  have hOne : h.representative (indicatorVector MeasurableSet.univ) = ContinuousMap.const X 1 := by
    apply h.representative_eq
    rw [indicatorVector, indicatorConstLp_univ, one]
    exact Lp.coeFn_const 2 μ 1
  simp [hOne]

/-- If the operator preserves the reference integral, the kernel preserves the reference measure. -/
theorem kernel_invariant
    (positive : ∀ u : X →₂[μ] ℝ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] (T u : X → ℝ))
    (invariant : ∀ u : X →₂[μ] ℝ, (∫ y, T u y ∂μ) = ∫ y, u y ∂μ) :
    μ.bind (h.kernel positive) = μ := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  simp_rw [h.kernel_apply positive _ hA]
  let u := indicatorVector (μ := μ) hA
  have hRep := h.ae_representative u
  have hi : Integrable (h.representative u) μ := ((Lp.memLp (T u)).integrable one_le_two).congr hRep
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (h.representative_nonneg positive u (indicatorVector_nonneg hA)))]
  rw [← integral_congr_ae hRep, invariant, integral_congr_ae (ae_indicatorVector hA)]
  rw [integral_indicator_const _ hA]
  simp [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ A)]

end CutoffRigidity.L2Kernel.HasContinuousRepresentatives
