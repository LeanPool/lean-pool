/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Basic.ENNReal.Basic

/-!
# Extended nonnegative energy functionals

This module separates tests from the subtype on which an extended nonnegative energy is finite.
-/

@[expose] public section

namespace FunctionalInequalities.Energy


/-- An extended nonnegative energy on tests of type `X`. -/
structure Functional (X : Type*) where
  /-- The energy of a test, possibly `⊤`. -/
  toFun : X → ENNReal

namespace Functional

variable {X : Type*}

/-- An energy functional can be applied to a test. -/
instance : CoeFun (Functional X) fun _ ↦ X → ENNReal where
  coe energy := energy.toFun

/-- Applying a functional built from a function returns that function's value. -/
@[simp]
theorem mk_apply (energy : X → ENNReal) (x : X) : mk energy x = energy x := rfl

/-- Extended energy functionals are equal when all of their values are equal. -/
@[ext]
theorem ext {left right : Functional X} (h : ∀ x, left x = right x) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      congr
      funext x
      exact h x

/-- Pull an extended energy back along a map of test spaces. -/
def comap {Y : Type*} (energy : Functional Y) (f : X → Y) : Functional X where
  toFun x := energy (f x)

/-- A pulled-back functional evaluates by first applying the test-space map. -/
@[simp]
theorem comap_apply {Y : Type*} (energy : Functional Y) (f : X → Y) (x : X) :
    energy.comap f x = energy (f x) :=
  rfl

/-- The energy is finite at `x`. -/
def FiniteAt (energy : Functional X) (x : X) : Prop :=
  energy x ≠ ⊤

/-- Finiteness is equivalent to lying strictly below `⊤`. -/
theorem finiteAt_iff_lt_top (energy : Functional X) (x : X) :
    energy.FiniteAt x ↔ energy x < ⊤ := by
  rw [FiniteAt, lt_top_iff_ne_top]

/-- The set of tests with finite energy. It can be used as a subtype. -/
def domain (energy : Functional X) : Set X :=
  {x | energy.FiniteAt x}

/-- Membership in the domain is the finiteness predicate. -/
@[simp]
theorem mem_domain (energy : Functional X) (x : X) :
    x ∈ energy.domain ↔ energy.FiniteAt x :=
  Iff.rfl

/-- The finite energy as an `NNReal`.

The domain witness excludes `⊤`, so this does not use the fallback-to-zero behavior of
`ENNReal.toNNReal` on an infinite value.
-/
def finiteValue (energy : Functional X) (x : energy.domain) : NNReal :=
  (energy x.1).toNNReal

/-- Coercing a finite energy back to `ENNReal` recovers the original value. -/
@[simp]
theorem coe_finiteValue (energy : Functional X) (x : energy.domain) :
    (energy.finiteValue x : ENNReal) = energy x.1 :=
  ENNReal.coe_toNNReal x.2

/-- The zero functional assigns zero energy to every test. -/
instance : Zero (Functional X) where
  zero := ⟨fun _ ↦ 0⟩

/-- The zero functional evaluates to zero. -/
@[simp]
theorem zero_apply (x : X) : (0 : Functional X) x = 0 := rfl

/-- The zero functional is finite at every test. -/
@[simp]
theorem zero_finiteAt (x : X) : (0 : Functional X).FiniteAt x := by
  simp [FiniteAt]

/-- Every test belongs to the domain of the zero functional. -/
@[simp]
theorem domain_zero : (0 : Functional X).domain = Set.univ := by
  ext x
  simp

/-- The finite value of the zero functional is zero. -/
@[simp]
theorem finiteValue_zero (x : (0 : Functional X).domain) :
    (0 : Functional X).finiteValue x = 0 :=
  rfl

end Functional

/-- An energy functional vanishes at the zero test. -/
def ZeroEnergy {X : Type*} [Zero X] (energy : Functional X) : Prop :=
  energy 0 = 0

namespace ZeroEnergy

variable {X : Type*} [Zero X] {energy : Functional X}

/-- A zero-preserving energy is finite at the zero test. -/
theorem finiteAt_zero (h : ZeroEnergy energy) : energy.FiniteAt 0 := by
  change energy.toFun 0 ≠ ⊤
  change energy.toFun 0 = 0 at h
  rw [h]
  exact ENNReal.zero_ne_top

/-- The zero test belongs to the domain of a zero-preserving energy. -/
theorem zero_mem_domain (h : ZeroEnergy energy) : (0 : X) ∈ energy.domain :=
  h.finiteAt_zero

/-- The zero functional vanishes at the zero test. -/
@[simp]
theorem zero : ZeroEnergy (0 : Functional X) :=
  rfl

end ZeroEnergy

end FunctionalInequalities.Energy
