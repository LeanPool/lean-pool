/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Stochastic Domination

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open MeasureTheory

namespace ECRuntime

/-- The strict upper-tail event of an extended nonnegative random variable. -/
def runtimeTailEvent {Ω : Type*} (X : Ω → ENNReal) (t : ENNReal) : Set Ω :=
  {ω | t < X ω}

/-- The mass of the strict upper-tail event `t < X`. -/
def runtimeTailMass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ENNReal) (t : ENNReal) : ENNReal :=
  μ (runtimeTailEvent X t)

/-- Tail events are monotone under pointwise domination of the random variables. -/
theorem runtimeTailEvent_mono_of_pointwise_le
    {Ω : Type*} {X Y : Ω → ENNReal}
    (hXY : ∀ ω, X ω ≤ Y ω) (t : ENNReal) :
    runtimeTailEvent X t ⊆ runtimeTailEvent Y t := by
  intro ω hω
  exact lt_of_lt_of_le hω (hXY ω)

/-- A measurable extended nonnegative random variable has measurable strict upper tails. -/
theorem measurableSet_runtimeTailEvent
    {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ENNReal} (hX : Measurable X) (t : ENNReal) :
    MeasurableSet (runtimeTailEvent X t) := by
  change MeasurableSet (X ⁻¹' Set.Ioi t)
  exact measurableSet_Ioi.preimage hX

/--
First-order stochastic domination for extended nonnegative random variables, expressed
through all strict upper-tail probabilities.  `StochasticallyDominated μ X ν Y` means
that `X` under `μ` is no larger in distribution than `Y` under `ν`.
-/
def StochasticallyDominated
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : Measure Ω₁) (X : Ω₁ → ENNReal)
    (ν : Measure Ω₂) (Y : Ω₂ → ENNReal) : Prop :=
  ∀ t, runtimeTailMass μ X t ≤ runtimeTailMass ν Y t

/-- Stochastic domination is reflexive. -/
theorem stochasticallyDominated_refl
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ENNReal) :
    StochasticallyDominated μ X μ X := by
  intro t
  exact le_rfl

/-- Stochastic domination is transitive. -/
theorem stochasticallyDominated_trans
    {Ω₁ Ω₂ Ω₃ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃}
    {X₁ : Ω₁ → ENNReal} {X₂ : Ω₂ → ENNReal} {X₃ : Ω₃ → ENNReal}
    (h12 : StochasticallyDominated μ₁ X₁ μ₂ X₂)
    (h23 : StochasticallyDominated μ₂ X₂ μ₃ X₃) :
    StochasticallyDominated μ₁ X₁ μ₃ X₃ := by
  intro t
  exact (h12 t).trans (h23 t)

/-- Pointwise domination on a common probability space implies stochastic domination. -/
theorem stochasticallyDominated_of_pointwise_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hXY : ∀ ω, X ω ≤ Y ω) :
    StochasticallyDominated μ X μ Y := by
  intro t
  unfold runtimeTailMass
  exact measure_mono (runtimeTailEvent_mono_of_pointwise_le hXY t)

/--
For integer-valued runtime variables it is often convenient to compare only the tails
above natural thresholds.  This is the form used by geometric waiting-time arguments.
-/
def NatTailDominated
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : Measure Ω₁) (X : Ω₁ → ENNReal)
    (ν : Measure Ω₂) (Y : Ω₂ → ENNReal) : Prop :=
  ∀ k : ℕ,
    runtimeTailMass μ X (k : ENNReal) ≤
      runtimeTailMass ν Y (k : ENNReal)

/-- Full stochastic domination implies domination at every natural threshold. -/
theorem natTailDominated_of_stochasticallyDominated
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ : Measure Ω₁} {ν : Measure Ω₂}
    {X : Ω₁ → ENNReal} {Y : Ω₂ → ENNReal}
    (h : StochasticallyDominated μ X ν Y) :
    NatTailDominated μ X ν Y := by
  intro k
  exact h (k : ENNReal)

/-- Natural-threshold domination is reflexive. -/
theorem natTailDominated_refl
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ENNReal) :
    NatTailDominated μ X μ X := by
  intro k
  exact le_rfl

/-- Natural-threshold domination is transitive. -/
theorem natTailDominated_trans
    {Ω₁ Ω₂ Ω₃ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃}
    {X₁ : Ω₁ → ENNReal} {X₂ : Ω₂ → ENNReal} {X₃ : Ω₃ → ENNReal}
    (h12 : NatTailDominated μ₁ X₁ μ₂ X₂)
    (h23 : NatTailDominated μ₂ X₂ μ₃ X₃) :
    NatTailDominated μ₁ X₁ μ₃ X₃ := by
  intro k
  exact (h12 k).trans (h23 k)

/-- Pointwise domination also implies natural-threshold tail domination. -/
theorem natTailDominated_of_pointwise_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hXY : ∀ ω, X ω ≤ Y ω) :
    NatTailDominated μ X μ Y :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_of_pointwise_le μ hXY)

end ECRuntime
