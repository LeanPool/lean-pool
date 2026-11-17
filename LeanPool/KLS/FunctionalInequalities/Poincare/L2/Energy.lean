/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.Functional
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Optimal

/-!
# Poincaré constants for extended energies on real `L²`

This module connects the analytic carrier to the order-theoretic Poincaré optimizer.
For an extended energy on real `L²(μ)`, the tests are exactly the elements where the
energy is finite. Variance and finite energy then form a `Poincare.TestFamily`.

No closedness, quadraticity, or Markov property is assumed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare

universe u

variable {α : Type u} [MeasurableSpace α]

namespace TestFamily

/-- The finite-energy domain of an extended functional on real `L²(μ)`, equipped with
intrinsic `L²` variance and the functional's finite value. -/
def ofL2Energy (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) : TestFamily where
  Test := energy.domain
  variance f := L2.variance μ f.1
  energy f := energy.finiteValue f

/-- Variance in the induced test family is intrinsic `L²` variance. -/
@[simp]
theorem ofL2Energy_variance (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (f : energy.domain) :
    (ofL2Energy μ energy).variance f = L2.variance μ f.1 :=
  rfl

/-- Energy in the induced test family is the finite value certified by the domain subtype. -/
@[simp]
theorem ofL2Energy_energy (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (f : energy.domain) :
    (ofL2Energy μ energy).energy f = energy.finiteValue f :=
  rfl

end TestFamily

namespace L2Energy

/-- The optimal extended Poincaré constant of an energy on real `L²(μ)`. -/
def optimalConstant (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) : ENNReal :=
  (TestFamily.ofL2Energy μ energy).optimalConstant

/-- A finite Poincaré constant is valid on every finite-energy `L²` test. -/
def Holds (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) : Prop :=
  (TestFamily.ofL2Energy μ energy).Holds C

/-- Unfolding validity gives the Poincaré inequality on the finite-energy domain. -/
theorem holds_iff (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔
      ∀ f : energy.domain, L2.variance μ f.1 ≤ C * energy.finiteValue f :=
  Iff.rfl

/-- A finite `L²` Poincaré constant is valid exactly when it bounds the optimal one. -/
theorem holds_iff_constant_le (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔ optimalConstant μ energy ≤ (C : ENNReal) := by
  simpa [Holds, optimalConstant] using
    TestFamily.holds_iff_constant_le (TestFamily.ofL2Energy μ energy) C

/-- On a subsingleton carrier every `L²` class has zero variance, so every energy, including
one with empty or infinite finite-energy domain, has optimal Poincaré constant zero. -/
theorem constant_eq_zero_of_subsingleton [Subsingleton α] (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) : optimalConstant μ energy = 0 := by
  apply TestFamily.constant_eq_zero_of_variance_zero
  intro f
  exact L2.variance_eq_zero_of_subsingleton μ f.1

/-- Optimal constants agree along a linear isometric equivalence of `L²` spaces that preserves
variance and intertwines the two energies. -/
theorem constant_eq_of_linearIsometryEquiv {β : Type*} [MeasurableSpace β]
    (μ : ProbabilityMeasure α) (μ' : ProbabilityMeasure β)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (energy' : Energy.Functional (Lp ℝ 2 (μ' : Measure β)))
    (e : Lp ℝ 2 (μ' : Measure β) ≃ₗᵢ[ℝ] Lp ℝ 2 (μ : Measure α))
    (hvar : ∀ f, L2.variance μ (e f) = L2.variance μ' f)
    (henergy : ∀ f, energy' f = energy (e f)) :
    optimalConstant μ' energy' = optimalConstant μ energy := by
  have hholds : ∀ C : NNReal, Holds μ' energy' C ↔ Holds μ energy C := by
    intro C
    rw [holds_iff, holds_iff]
    constructor
    · intro h f
      have hmem : e.symm f.1 ∈ energy'.domain := by
        change energy' (e.symm f.1) ≠ ⊤
        rw [henergy, e.apply_symm_apply]
        exact f.2
      have := h ⟨e.symm f.1, hmem⟩
      rw [← hvar, e.apply_symm_apply] at this
      refine this.trans (le_of_eq ?_)
      congr 1
      apply NNReal.eq
      simp only [Energy.Functional.finiteValue, henergy, e.apply_symm_apply]
    · intro h f
      have hmem : e f.1 ∈ energy.domain := by
        change energy (e f.1) ≠ ⊤
        rw [← henergy]
        exact f.2
      have := h ⟨e f.1, hmem⟩
      rw [hvar] at this
      refine this.trans (le_of_eq ?_)
      congr 1
      apply NNReal.eq
      simp only [Energy.Functional.finiteValue, henergy]
  refine le_antisymm ?_ ?_
  · by_cases htop : optimalConstant μ energy = ⊤
    · rw [htop]; exact le_top
    · have h1 : Holds μ energy (optimalConstant μ energy).toNNReal :=
        (holds_iff_constant_le _ _ _).mpr (by rw [ENNReal.coe_toNNReal htop])
      have h2 := (holds_iff_constant_le _ _ _).mp ((hholds _).mpr h1)
      rwa [ENNReal.coe_toNNReal htop] at h2
  · by_cases htop : optimalConstant μ' energy' = ⊤
    · rw [htop]; exact le_top
    · have h1 : Holds μ' energy' (optimalConstant μ' energy').toNNReal :=
        (holds_iff_constant_le _ _ _).mpr (by rw [ENNReal.coe_toNNReal htop])
      have h2 := (holds_iff_constant_le _ _ _).mp ((hholds _).mp h1)
      rwa [ENNReal.coe_toNNReal htop] at h2

end L2Energy

end FunctionalInequalities.Poincare
