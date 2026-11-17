/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Optimal

/-!
# Comparison of abstract Poincaré test families

The optimizer in `Poincare.SmoothTest.Optimal` is independent of analysis. This module records the
two
order principles needed when changing a test domain or an energy: adding tests can only increase
the optimal constant, while increasing the energy on a fixed family can only decrease it.

All comparisons are made directly in `ENNReal`, so zero energies require no side conditions.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Poincare.TestFamily

universe u v

/-- A map from `F`-tests to `G`-tests that can only increase their Rayleigh quotients. -/
structure RayleighMap (F : TestFamily.{u}) (G : TestFamily.{v}) where
  /-- The image test. -/
  toFun : F.Test → G.Test
  /-- Variance does not decrease under the map. -/
  variance_le : ∀ f, F.variance f ≤ G.variance (toFun f)
  /-- Energy does not increase under the map. -/
  energy_le : ∀ f, G.energy (toFun f) ≤ F.energy f

namespace RayleighMap

variable {F : TestFamily.{u}} {G : TestFamily.{v}}

instance : CoeFun (RayleighMap F G) fun _ ↦ F.Test → G.Test :=
  ⟨RayleighMap.toFun⟩

/-- A Rayleigh map gives the pointwise quotient comparison, including at zero energy. -/
theorem rayleigh_le (e : RayleighMap F G) (f : F.Test) :
    F.rayleigh f ≤ G.rayleigh (e f) := by
  exact ENNReal.div_le_div (ENNReal.coe_le_coe.mpr (e.variance_le f))
    (ENNReal.coe_le_coe.mpr (e.energy_le f))

/-- A Rayleigh map bounds the source optimal constant by the target one. -/
theorem constant_le (e : RayleighMap F G) : F.optimalConstant ≤ G.optimalConstant := by
  rw [optimalConstant]
  refine iSup_le fun f ↦ (e.rayleigh_le f).trans ?_
  exact le_iSup G.rayleigh (e f)

end RayleighMap

/-- Restrict a test family to a predicate without changing its numerical data. -/
def restrict (F : TestFamily.{u}) (p : F.Test → Prop) : TestFamily.{u} where
  Test := {f : F.Test // p f}
  variance f := F.variance f.1
  energy f := F.energy f.1

/-- Inclusion of a restricted test family into the original family. -/
def restrictMap (F : TestFamily.{u}) (p : F.Test → Prop) :
    RayleighMap (F.restrict p) F where
  toFun f := f.1
  variance_le _ := le_rfl
  energy_le _ := le_rfl

/-- Restricting the test domain cannot increase the optimal constant. -/
theorem restrict_constant_le (F : TestFamily.{u}) (p : F.Test → Prop) :
    (F.restrict p).optimalConstant ≤ F.optimalConstant :=
  (F.restrictMap p).constant_le

/-- Build a test family from two finite nonnegative numerical functions. -/
def ofValues (Test : Type u) (variance energy : Test → NNReal) : TestFamily.{u} where
  Test := Test
  variance := variance
  energy := energy

/-- On a fixed test type and with fixed variance, increasing energy decreases the optimal
Poincaré constant. -/
theorem constant_anti_mono_energy {Test : Type u} (variance : Test → NNReal)
    {energy energy' : Test → NNReal} (h : ∀ f, energy f ≤ energy' f) :
    (ofValues Test variance energy').optimalConstant ≤
      (ofValues Test variance energy).optimalConstant := by
  let e : RayleighMap (ofValues Test variance energy')
      (ofValues Test variance energy) :=
    { toFun := id
      variance_le := fun _ ↦ le_rfl
      energy_le := h }
  exact e.constant_le

end FunctionalInequalities.Poincare.TestFamily
