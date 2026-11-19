/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.Comparison
public import LeanPool.KLS.FunctionalInequalities.Poincare.Comparison
public import LeanPool.KLS.FunctionalInequalities.Poincare.L2.Energy

/-!
# Comparing Poincaré constants of `L²` energies

For the same probability measure, increasing an energy shrinks its finite domain and enlarges
the denominator on the remaining tests. Consequently its optimal Poincaré constant can only
decrease. The proof is an explicit Rayleigh map, so zero-energy tests and infinite optimal
constants require no separate assumptions.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.L2Energy

universe u

variable {α : Type u} [MeasurableSpace α]

/-- Pointwise energy comparison induces a Rayleigh map in the contravariant direction. -/
def rayleighMap (μ : ProbabilityMeasure α)
    {lower upper : Energy.Functional (Lp ℝ 2 (μ : Measure α))}
    (h : lower.PointwiseLE upper) :
    TestFamily.RayleighMap (TestFamily.ofL2Energy μ upper)
      (TestFamily.ofL2Energy μ lower) where
  toFun f := Energy.Functional.domainMap h f
  variance_le _ := le_rfl
  energy_le f := Energy.Functional.finiteValue_domainMap_le h f

/-- Increasing an extended `L²` energy can only decrease its optimal Poincaré constant. -/
theorem constant_antitone (μ : ProbabilityMeasure α)
    {lower upper : Energy.Functional (Lp ℝ 2 (μ : Measure α))}
    (h : lower.PointwiseLE upper) :
    optimalConstant μ upper ≤ optimalConstant μ lower :=
  (rayleighMap μ h).constant_le

/-- A finite comparison factor transfers a form-gap bound to another energy. The comparison
is required only on the target's finite domain and itself guarantees finite source energy.
This includes `κ = 0` and `C = 0`; no multiplication by an infinite target energy is used. -/
theorem Holds.of_energy_le_mul {μ : ProbabilityMeasure α}
    {source target : Energy.Functional (Lp ℝ 2 (μ : Measure α))} {C κ : NNReal}
    (hC : Holds μ source C)
    (henergy : ∀ f : target.domain,
      source f.1 ≤ (κ : ENNReal) * target f.1) :
    Holds μ target (κ * C) := by
  intro f
  have hfinite : source.FiniteAt f.1 :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top f.2) (henergy f)
  let g : source.domain := ⟨f.1, hfinite⟩
  have hbound : source.finiteValue g ≤ κ * target.finiteValue f := by
    apply (ENNReal.coe_le_coe (r := source.finiteValue g)
      (q := κ * target.finiteValue f)).mp
    rw [ENNReal.coe_mul, source.coe_finiteValue g, target.coe_finiteValue f]
    exact henergy f
  change L2.variance μ f.1 ≤ (κ * C) * target.finiteValue f
  calc
    L2.variance μ f.1 ≤ C * source.finiteValue g := hC g
    _ ≤ C * (κ * target.finiteValue f) := mul_le_mul_of_nonneg_left hbound C.2
    _ = (κ * C) * target.finiteValue f := by rw [← mul_assoc, mul_comm C κ]

/-- The same finite energy comparison bounds the target's extended optimal constant. -/
theorem constant_le_mul_of_energy_le_mul {μ : ProbabilityMeasure α}
    {source target : Energy.Functional (Lp ℝ 2 (μ : Measure α))} {C κ : NNReal}
    (hC : Holds μ source C)
    (henergy : ∀ f : target.domain,
      source f.1 ≤ (κ : ENNReal) * target f.1) :
    optimalConstant μ target ≤ ((κ * C : NNReal) : ENNReal) :=
  (holds_iff_constant_le μ target (κ * C)).mp (hC.of_energy_le_mul henergy)

end FunctionalInequalities.Poincare.L2Energy
