/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Tactic

/-!
# Coupling transport cost and a deterministic initial condition

The squared transport cost is defined by an infimum over actual couplings
of the measures, with the extended nonnegative integral of squared distance.
The Dirac formula is the deterministic-initial-condition step in the upper
bound proof of `th:maineucl` in `cutcur-lean.tex`.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped ENNReal NNReal

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- A genuine coupling measure, specified by its two marginals. -/
@[expose] def Coupling (μ ν : Measure E) :=
  {π : Measure (E × E) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

/-- Squared quadratic transport cost, allowing infinite second moments. -/
@[expose] noncomputable def squaredWasserstein (μ ν : Measure E) : ℝ≥0∞ :=
  ⨅ π : Coupling μ ν, ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val

/-- The independent product is a coupling of two probability measures. -/
noncomputable def productCoupling (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : Coupling μ ν :=
  ⟨μ.prod ν, by simp⟩

omit [MetricSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Every coupling of a probability first marginal is itself a probability measure. -/
theorem Coupling.isProbabilityMeasure {μ ν : Measure E} [IsProbabilityMeasure μ]
    (π : Coupling μ ν) : IsProbabilityMeasure π.val := by
  apply (Measure.isProbabilityMeasure_map_iff
    (μ := π.val) measurable_fst.aemeasurable).mp
  rw [π.property.1]
  infer_instance

omit [BorelSpace E] [SecondCountableTopology E] in
/-- Any specific coupling bounds the infimum defining the squared transport cost. -/
theorem squaredWasserstein_le_cost {μ ν : Measure E} (π : Coupling μ ν) :
    squaredWasserstein μ ν ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
  exact iInf_le _ π

/-- A deterministic first marginal forces that coordinate to equal its atom. -/
theorem Coupling.fst_ae_eq {x : E} {ν : Measure E} (π : Coupling (Measure.dirac x) ν) :
    ∀ᵐ z ∂π.val, z.1 = x := by
  apply ae_of_ae_map (μ := π.val) (p := fun y : E => y = x) measurable_fst.aemeasurable
  rw [π.property.1]
  simp

/-- The only coupling with a Dirac first marginal is its product with the second. -/
theorem Coupling.eq_dirac_prod {x : E} {ν : Measure E} [IsProbabilityMeasure ν]
    (π : Coupling (Measure.dirac x) ν) : π.val = (Measure.dirac x).prod ν := by
  have hae : (fun z : E × E => z) =ᵐ[π.val] (fun z => (x, z.2)) := by
    filter_upwards [π.fst_ae_eq] with z hz
    exact Prod.ext hz rfl
  calc
    π.val = π.val.map (fun z => z) := by simp
    _ = π.val.map (fun z => (x, z.2)) := Measure.map_congr hae
    _ = (π.val.map Prod.snd).map (Prod.mk x) := by
      rw [Measure.map_map measurable_prodMk_left measurable_snd]
      rfl
    _ = ν.map (Prod.mk x) := by rw [π.property.2]
    _ = (Measure.dirac x).prod ν := (Measure.dirac_prod x).symm

/-- The squared transport cost from a deterministic initial point is its second
moment about that point. This is an equality of genuine coupling infima. -/
theorem squaredWasserstein_dirac (x : E) (ν : Measure E) [IsProbabilityMeasure ν] :
    squaredWasserstein (Measure.dirac x) ν = ∫⁻ y, edist x y ^ 2 ∂ν := by
  have hcost (π : Coupling (Measure.dirac x) ν) :
      (∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val) = ∫⁻ y, edist x y ^ 2 ∂ν := by
    rw [π.eq_dirac_prod, Measure.dirac_prod]
    exact lintegral_map (by fun_prop) measurable_prodMk_left
  have : Nonempty (Coupling (Measure.dirac x) ν) := ⟨productCoupling _ _⟩
  unfold squaredWasserstein
  simp_rw [hcost]
  simp

section Pushforward

variable {F : Type*} [MetricSpace F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- Applying the same measurable map to both coordinates transports both marginals. -/
noncomputable def Coupling.map {μ ν : Measure E} (π : Coupling μ ν)
    {T : E → F} (hT : Measurable T) : Coupling (μ.map T) (ν.map T) := by
  refine ⟨π.val.map (fun z => (T z.1, T z.2)), ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (by fun_prop)]
    change π.val.map (T ∘ Prod.fst) = μ.map T
    rw [← Measure.map_map hT measurable_fst, π.property.1]
  · rw [Measure.map_map measurable_snd (by fun_prop)]
    change π.val.map (T ∘ Prod.snd) = ν.map T
    rw [← Measure.map_map hT measurable_snd, π.property.2]

/-- A Lipschitz map increases any coupling's squared cost by at most `K²`. -/
theorem Coupling.map_cost_le {μ ν : Measure E} (π : Coupling μ ν)
    {T : E → F} {K : ℝ≥0} (hT : LipschitzWith K T) :
    (∫⁻ z, edist z.1 z.2 ^ 2 ∂(π.map hT.continuous.measurable).val) ≤
      (K : ℝ≥0∞) ^ 2 * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
  change (∫⁻ z, edist z.1 z.2 ^ 2
    ∂π.val.map (fun z => (T z.1, T z.2))) ≤ _
  have hmT : Measurable T := hT.continuous.measurable
  have hpair : Measurable (fun z : E × E => (T z.1, T z.2)) := by fun_prop
  rw [lintegral_map (by fun_prop) hpair]
  calc
    (∫⁻ z, edist (T z.1) (T z.2) ^ 2 ∂π.val) ≤
        ∫⁻ z, ((K : ℝ≥0∞) * edist z.1 z.2) ^ 2 ∂π.val := by
      apply lintegral_mono
      intro z
      exact pow_le_pow_left' (hT.edist_le_mul z.1 z.2) 2
    _ = (K : ℝ≥0∞) ^ 2 * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
      simp only [mul_pow]
      exact lintegral_const_mul _ (by fun_prop)

/-- The coupling definition gives the Lipschitz pushforward bound used for the
multi-eigenmap in the proof of the main Wasserstein estimate. -/
theorem squaredWasserstein_map_le (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : E → F} {K : ℝ≥0} (hT : LipschitzWith K T) :
    squaredWasserstein (μ.map T) (ν.map T) ≤
      (K : ℝ≥0∞) ^ 2 * squaredWasserstein μ ν := by
  have : Nonempty (Coupling μ ν) := ⟨productCoupling μ ν⟩
  change squaredWasserstein (μ.map T) (ν.map T) ≤
    (K : ℝ≥0∞) ^ 2 * ⨅ π : Coupling μ ν, ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro π
  exact (squaredWasserstein_le_cost (π.map hT.continuous.measurable)).trans
    (π.map_cost_le hT)

end Pushforward

end CutoffRigidity
