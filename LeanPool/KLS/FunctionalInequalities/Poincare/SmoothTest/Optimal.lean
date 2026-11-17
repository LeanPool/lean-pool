/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv

/-!
# Optimal Poincaré constants for finite-valued test data

This module isolates the order-theoretic part of a Poincaré inequality. A `TestFamily`
records only a type of tests and finite nonnegative variance and energy values. It does not
choose a measure, a gradient, or a closed energy domain.

The optimal constant is the supremum of the extended Rayleigh quotients. Thus zero variance
over zero energy is zero, while positive variance over zero energy is infinity.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Poincare

universe u

/-- A family of tests whose variance and energy are both finite and nonnegative. -/
structure TestFamily where
  /-- The chosen test domain; it need not contain every ambient function. -/
  Test : Type u
  /-- Finite nonnegative variance assigned to each test. -/
  variance : Test → NNReal
  /-- Finite nonnegative energy assigned to each test; zero is allowed. -/
  energy : Test → NNReal

namespace TestFamily

/-- The extended Rayleigh quotient of a test. -/
def rayleigh (F : TestFamily) (f : F.Test) : ENNReal :=
  (F.variance f : ENNReal) / (F.energy f : ENNReal)

/-- The optimal constant, including infinity when the Rayleigh quotients are unbounded. -/
def optimalConstant (F : TestFamily) : ENNReal :=
  ⨆ f, rayleigh F f

/-- A finite constant is valid when it bounds variance by that constant times energy. -/
def Holds (F : TestFamily) (C : NNReal) : Prop :=
  ∀ f, F.variance f ≤ C * F.energy f

/-- The extended Rayleigh quotient is bounded by a finite `C` exactly when the defining
inequality holds. This includes zero-energy tests, whose quotient may be infinite. -/
theorem rayleigh_le_iff (F : TestFamily) (f : F.Test) (C : NNReal) :
    rayleigh F f ≤ (C : ENNReal) ↔ F.variance f ≤ C * F.energy f := by
  rw [rayleigh, ENNReal.div_le_iff_le_mul
    (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]

/-- A finite constant is valid exactly when it bounds the optimal extended constant. -/
theorem holds_iff_constant_le (F : TestFamily) (C : NNReal) :
    Holds F C ↔ optimalConstant F ≤ (C : ENNReal) := by
  rw [optimalConstant, iSup_le_iff]
  exact forall_congr' fun f ↦ (rayleigh_le_iff F f C).symm

/-- Every valid finite constant bounds the optimal constant from above. -/
theorem constant_le {F : TestFamily} {C : NNReal} (h : Holds F C) :
    optimalConstant F ≤ (C : ENNReal) :=
  (holds_iff_constant_le F C).mp h

/-- A finite upper bound for the optimal constant is a valid constant. -/
theorem holds_of_constant_le {F : TestFamily} {C : NNReal}
    (h : optimalConstant F ≤ (C : ENNReal)) : Holds F C :=
  (holds_iff_constant_le F C).mpr h

/-- The optimal constant is finite exactly when some finite constant is valid. -/
theorem constant_ne_top_iff_exists_holds (F : TestFamily) :
    F.optimalConstant ≠ ⊤ ↔ ∃ C : NNReal, F.Holds C := by
  constructor
  · intro hfinite
    refine ⟨F.optimalConstant.toNNReal, holds_of_constant_le ?_⟩
    rw [ENNReal.coe_toNNReal hfinite]
  · rintro ⟨C, hC⟩
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (constant_le hC)

/-- Infinity means that no finite Poincaré constant is valid. -/
theorem constant_eq_top_iff (F : TestFamily) :
    F.optimalConstant = ⊤ ↔ ∀ C : NNReal, ¬F.Holds C := by
  constructor
  · intro htop C hC
    exact (F.constant_ne_top_iff_exists_holds.mpr ⟨C, hC⟩) htop
  · intro h
    by_contra hfinite
    obtain ⟨C, hC⟩ := F.constant_ne_top_iff_exists_holds.mp hfinite
    exact h C hC

/-- Increasing a valid finite constant preserves validity. -/
theorem Holds.mono {F : TestFamily} {C C' : NNReal} (h : Holds F C) (hCC' : C ≤ C') :
    Holds F C' := by
  intro f
  exact (h f).trans (mul_le_mul_of_nonneg_right hCC' (F.energy f).2)

/-- Zero variance over zero energy has Rayleigh quotient zero. -/
theorem rayleigh_zero_zero {F : TestFamily} {f : F.Test}
    (hv : F.variance f = 0) (he : F.energy f = 0) : rayleigh F f = 0 := by
  simp [rayleigh, hv, he]

/-- Positive variance over zero energy has infinite Rayleigh quotient. -/
theorem rayleigh_eq_top_of_energy_zero {F : TestFamily} {f : F.Test}
    (hv : 0 < F.variance f) (he : F.energy f = 0) : rayleigh F f = ⊤ := by
  rw [rayleigh, he, ENNReal.coe_zero]
  exact ENNReal.div_zero (ENNReal.coe_ne_zero.mpr hv.ne')

/-- If every test has zero variance, the optimal constant is zero. -/
theorem constant_eq_zero_of_variance_zero (F : TestFamily)
    (h : ∀ f, F.variance f = 0) : optimalConstant F = 0 := by
  apply le_antisymm
  · rw [optimalConstant]
    exact iSup_le fun f ↦ by simp [rayleigh, h f]
  · exact bot_le

/-- An empty test family has optimal constant zero. -/
theorem constant_eq_zero_of_isEmpty (F : TestFamily) [IsEmpty F.Test] : F.optimalConstant = 0 :=
  F.constant_eq_zero_of_variance_zero fun f ↦ isEmptyElim f

/-- A positive-variance zero-energy test forces the optimal constant to be infinity. -/
theorem constant_eq_top_of_positive_variance_energy_zero (F : TestFamily) (f : F.Test)
    (hv : 0 < F.variance f) (he : F.energy f = 0) : F.optimalConstant = ⊤ := by
  apply top_unique
  calc
    ⊤ = F.rayleigh f := (rayleigh_eq_top_of_energy_zero hv he).symm
    _ ≤ F.optimalConstant := le_iSup F.rayleigh f

end TestFamily

end FunctionalInequalities.Poincare
