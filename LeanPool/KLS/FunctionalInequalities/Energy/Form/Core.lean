/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Sequential cores and recovery sequences

This module states exactly how a concrete finite pre-energy may generate an extended ambient
energy. The definitions deliberately separate four claims that are often conflated:

* constancy of the concrete energy on fibers of the ambient realization;
* agreement on the concrete tests;
* equality with the sequential relaxation;
* existence of a recovery sequence whose energies converge.

No density or Sobolev-core theorem is inferred merely from smoothness of the tests.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy.PreEnergy


universe u v

variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)

/-- A recovery sequence at `x` converges to `x` in the ambient topology and has energies
converging to the prescribed extended value. -/
def HasRecoverySequenceAt (energy : Functional X) (x : X) : Prop :=
  ∃ f : P.ApproximatingSequence x,
    Tendsto (fun n ↦ (P.energy (f.1 n) : ENNReal)) atTop (𝓝 (energy x))

/-- The concrete energy is constant on fibers of the realization map.

This is necessary before a pre-energy on concrete functions can be the literal restriction of an
energy on an `L²` quotient. It can fail for ambient gradients under a singular measure.
-/
def RespectsAmbientFibers : Prop :=
  ∀ f g : P.Test, P.toAmbient f = P.toAmbient g → P.energy f = P.energy g

/-- A concrete test has the same energy before and after realization in the ambient space. -/
def AgreesOnTests (energy : Functional X) : Prop :=
  ∀ f : P.Test, energy (P.toAmbient f) = (P.energy f : ENNReal)

/-- The pre-energy sequentially generates an extended ambient energy. -/
def SequentiallyGenerates (energy : Functional X) : Prop :=
  P.sequentialRelaxation = energy

/-- A sequential form core both restricts the ambient energy correctly and generates it by
relaxation.

This project-specific name records the two exact equalities above. Identifying it with another
literature notion of graph-norm core is a theorem to be proved in the relevant analytic setting.
-/
structure IsSequentialCoreFor (energy : Functional X) : Prop where
  /-- The finite test energy is the restriction of the ambient energy. -/
  agreesOnTests : P.AgreesOnTests energy
  /-- Relaxing the test energy recovers the entire extended functional. -/
  sequentiallyGenerates : P.SequentiallyGenerates energy

namespace AgreesOnTests

omit [TopologicalSpace X] in
/-- Agreement with an ambient functional forces the concrete energy to respect realization
fibers. -/
theorem respectsAmbientFibers {energy : Functional X}
    (h : P.AgreesOnTests energy) : P.RespectsAmbientFibers := by
  intro f g hfg
  apply ENNReal.coe_injective
  rw [← h f, ← h g, hfg]

end AgreesOnTests

namespace IsSequentialCoreFor

/-- A sequential core necessarily has an energy that is well defined on realization fibers. -/
theorem respectsAmbientFibers {energy : Functional X}
    (h : P.IsSequentialCoreFor energy) : P.RespectsAmbientFibers :=
  h.agreesOnTests.respectsAmbientFibers

end IsSequentialCoreFor

/-- A recovery sequence gives the expected upper bound for the relaxed energy at its limit. -/
theorem sequentialRelaxation_le_of_hasRecoverySequenceAt {energy : Functional X} {x : X}
    (h : P.HasRecoverySequenceAt energy x) : P.sequentialRelaxation x ≤ energy x := by
  obtain ⟨f, hf⟩ := h
  calc
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
      P.sequentialRelaxation_le_sequenceEnergy f
    _ = energy x := hf.liminf_eq

namespace IsSequentialCoreFor

/-- On a sequential core, evaluating the relaxation is the same as evaluating the ambient
energy. -/
theorem sequentialRelaxation_apply {energy : Functional X}
    (h : P.IsSequentialCoreFor energy) (x : X) :
    P.sequentialRelaxation x = energy x := by
  rw [h.sequentiallyGenerates]

/-- On a sequential core, every concrete test retains its original finite energy. -/
theorem toAmbient_apply {energy : Functional X}
    (h : P.IsSequentialCoreFor energy) (f : P.Test) :
    energy (P.toAmbient f) = (P.energy f : ENNReal) :=
  h.agreesOnTests f

end IsSequentialCoreFor

end FunctionalInequalities.Energy.PreEnergy
