/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.Functional
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Sequential relaxation of a finite pre-energy

A `PreEnergy` records a concrete test class, its realization in a topological space, and a
finite nonnegative energy on those tests. Its sequential relaxation at `x` is the infimum of
the energy `liminf` over all test sequences converging to `x`.

The definition is intentionally sequential. The intended applications use real `L²`, hence a
metrizable topology; identifying it with an abstract lower-semicontinuous envelope is a later
theorem, not part of this definition.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy

universe u v

/-- A finite pre-energy carried by concrete tests and realized in an ambient space. -/
structure PreEnergy (X : Type u) where
  /-- The concrete tests on which the pre-energy is evaluated. -/
  Test : Type v
  /-- The realization of a concrete test in the ambient space. -/
  toAmbient : Test → X
  /-- The finite nonnegative energy of a concrete test. -/
  energy : Test → NNReal

namespace PreEnergy

variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)

/-- The concrete realization is dense in the ambient topology.

This is a property of the chosen presentation, not a consequence of finite test energies or of
the relaxation construction.
-/
def DenseRealization : Prop :=
  Dense (Set.range P.toAmbient)

/-- A sequence of concrete tests whose realizations converge to `x`. -/
def ApproximatingSequence (x : X) : Type max u v :=
  {f : ℕ → P.Test // Tendsto (fun n ↦ P.toAmbient (f n)) atTop (𝓝 x)}

/-- The energy `liminf` of an approximating sequence. -/
def sequenceEnergy {x : X} (f : P.ApproximatingSequence x) : ENNReal :=
  liminf (fun n ↦ (P.energy (f.1 n) : ENNReal)) atTop

/-- The sequential relaxation functional associated with the pre-energy.

Lower semicontinuity of this functional is not asserted for an arbitrary topological space.
-/
def sequentialRelaxation : Functional X where
  toFun x := ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f

/-- The relaxed energy is the infimum of the `liminf` energies of all approximating sequences. -/
theorem sequentialRelaxation_apply (x : X) :
    P.sequentialRelaxation x = ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f :=
  rfl

/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f

/-- The constant sequence realizes a concrete test at its ambient image. -/
def constantSequence (f : P.Test) : P.ApproximatingSequence (P.toAmbient f) :=
  ⟨fun _ ↦ f, tendsto_const_nhds⟩

/-- Relaxation never increases the energy of a concrete test. -/
theorem sequentialRelaxation_toAmbient_le (f : P.Test) :
    P.sequentialRelaxation (P.toAmbient f) ≤ (P.energy f : ENNReal) := by
  refine (P.sequentialRelaxation_le_sequenceEnergy (P.constantSequence f)).trans_eq ?_
  exact liminf_const (P.energy f : ENNReal)

/-- Every realized concrete test has finite relaxed energy. -/
theorem sequentialRelaxation_finiteAt_toAmbient (f : P.Test) :
    P.sequentialRelaxation.FiniteAt (P.toAmbient f) :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (P.sequentialRelaxation_toAmbient_le f)

/-- A continuous map with energy-nonincreasing lifts on concrete tests has the same bound
after relaxation. Neither test class needs to be nonempty or densely realized.

Each source test must have one target test realizing its image exactly. For comparison by
approximating sequences in a common pseudometric space, see
`PreEnergy.sequentialRelaxation_le_of_recovery_sequences` in
`FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous`. The present result only needs
topological ambient spaces and also allows a map between different spaces.
-/
theorem sequentialRelaxation_comp_le {Y : Type*} [TopologicalSpace Y]
    (Q : PreEnergy Y) (T : X → Y) (hT : Continuous T)
    (h : ∀ f : P.Test, ∃ g : Q.Test,
      Q.toAmbient g = T (P.toAmbient f) ∧ Q.energy g ≤ P.energy f) (x : X) :
    Q.sequentialRelaxation (T x) ≤ P.sequentialRelaxation x := by
  rw [P.sequentialRelaxation_apply]
  refine le_iInf fun s ↦ ?_
  choose g hreal henergy using fun n ↦ h (s.1 n)
  have hconv : Tendsto (fun n ↦ Q.toAmbient (g n)) atTop (𝓝 (T x)) := by
    simpa only [hreal, Function.comp_def] using (hT.tendsto x).comp s.2
  exact (Q.sequentialRelaxation_le_sequenceEnergy ⟨g, hconv⟩).trans
    (liminf_le_liminf (Eventually.of_forall fun n ↦ ENNReal.coe_le_coe.mpr (henergy n)))

/-- Scaled comparison of relaxations along a continuous map: if every concrete test of `P` is
matched by a test of `Q` with the mapped realization and energy at most `κ` times as large, the
relaxations compare with the same finite factor at every point of finite `P`-relaxation. The
finiteness premise excludes `κ = 0` against an empty approximating class. -/
theorem sequentialRelaxation_comp_le_mul {Y : Type*} [TopologicalSpace Y]
    (Q : PreEnergy Y) (T : X → Y) (hT : Continuous T) (κ : NNReal)
    (h : ∀ f : P.Test, ∃ g : Q.Test,
      Q.toAmbient g = T (P.toAmbient f) ∧ (Q.energy g : ENNReal) ≤ κ * P.energy f) (x : X)
    (hx : P.sequentialRelaxation x ≠ ⊤) :
    Q.sequentialRelaxation (T x) ≤ κ * P.sequentialRelaxation x := by
  have hne : Nonempty (P.ApproximatingSequence x) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have := hempty
    apply hx
    rw [P.sequentialRelaxation_apply]
    exact iInf_of_empty (fun s : P.ApproximatingSequence x ↦ P.sequenceEnergy s)
  rw [P.sequentialRelaxation_apply,
    ENNReal.mul_iInf' (fun htop ↦ absurd htop ENNReal.coe_ne_top) (fun _ ↦ hne)]
  refine le_iInf fun s ↦ ?_
  choose g hreal henergy using fun n ↦ h (s.1 n)
  have hconv : Tendsto (fun n ↦ Q.toAmbient (g n)) atTop (𝓝 (T x)) := by
    simpa only [hreal, Function.comp_def] using (hT.tendsto x).comp s.2
  refine (Q.sequentialRelaxation_le_sequenceEnergy ⟨g, hconv⟩).trans ?_
  refine (liminf_le_liminf (Eventually.of_forall fun n ↦ henergy n)).trans_eq ?_
  have hmono : Monotone fun a : ENNReal ↦ (κ : ENNReal) * a := fun _ _ hab ↦ mul_le_mul' le_rfl hab
  exact (hmono.map_liminf_of_continuousAt (fun n ↦ (P.energy (s.1 n) : ENNReal))
    ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousAt)).symm

/-- The concrete realization is contained in the finite domain of its relaxation. -/
theorem range_toAmbient_subset_relaxation_domain :
    Set.range P.toAmbient ⊆ P.sequentialRelaxation.domain := by
  rintro _ ⟨f, rfl⟩
  exact P.sequentialRelaxation_finiteAt_toAmbient f

/-- A dense concrete realization gives a densely defined relaxed functional.

No quadratic or lower-semicontinuity conclusion is used here: this is only the domain-density
part of a future `ClosedQuadratic` witness.
-/
theorem DenseRealization.dense_relaxation_domain (h : P.DenseRealization) :
    Dense P.sequentialRelaxation.domain :=
  h.mono P.range_toAmbient_subset_relaxation_domain

end PreEnergy

end FunctionalInequalities.Energy
