/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModel
public import LeanPool.TuringConeRigidity.Constructibility.UniformHierarchyStage

/-!
# Relative Model Syntax
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

def ordinalFormula (i : ℕ) : Formula :=
  .conj (.transitive i) (Formula.allMem i (.transitive 0))

theorem eval_ordinalFormula (i : ℕ) (e : ℕ → ZFSet.{u}) :
    (ordinalFormula i).Eval e ↔ (e i).IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  simp only [ordinalFormula,Formula.Eval,Formula.eval_transitive,
    Formula.eval_allMem,cons_zero]
  rfl

theorem ordinal_definable {M : ZFSet.{u}} (C : Context M) (i : ℕ) :
    Definable M (fun e => (e i).IsOrdinal) :=
  ⟨ordinalFormula (2*i),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by rw [eval_ordinalFormula,mix_even]⟩

theorem relativeLevel_sigmaDefinable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    SigmaDefinable M (fun e => (e 0).IsOrdinal ∧ e 1 ∈ stage R (e 0)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  have h := (stage_sigmaDefinable M R hM hT hR).and
    (((ordinal_definable C 1).toSigma hM).and ((member_definable C 2 0).toSigma hM))
  apply h.existsSet.congr
  intro e he
  change (∃ A ∈ M, A = stage R (e 0) ∧ (e 0).IsOrdinal ∧ e 1 ∈ A) ↔ _
  constructor
  · rintro ⟨A,_,rfl,ho,hx⟩; exact ⟨ho,hx⟩
  · rintro ⟨ho,hx⟩
    exact ⟨_,stage_mem M R (e 0) hM hT hR (he 0),rfl,ho,hx⟩

theorem relativeModel_sigmaDefinable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    SigmaDefinable M (fun e => InRelativeModel M R (e 0)) := by
  apply (relativeLevel_sigmaDefinable M R hM hT hR).existsSet.congr
  intro e _
  change (∃ o ∈ M, o.IsOrdinal ∧ e 0 ∈ stage R o) ↔ _
  constructor
  · rintro ⟨o,ho,hord,hx⟩
    refine ⟨o.rank,?_,?_⟩
    · rwa [hord.toZFSet_rank_eq]
    · change e 0 ∈ stage R o.rank.toZFSet
      rwa [hord.toZFSet_rank_eq]
  · rintro ⟨o,ho,hx⟩
    exact ⟨o.toZFSet,ho,ZFSet.isOrdinal_toZFSet o,hx⟩

theorem relativeModel_mem_sigmaDefinable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    SigmaDefinable M (fun e => e 0 ∈ relativeModel M R) :=
  (relativeModel_sigmaDefinable M R hM hT hR).congr
    (fun e _ => (mem_relativeModel M R (e 0) hM hT hR).symm)

end TuringRigidity.RelativeConstructible

end OAI
