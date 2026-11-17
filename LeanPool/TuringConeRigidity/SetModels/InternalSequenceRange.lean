/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalSequenceRange.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalFunctionOrbit

/-!
# Internal Sequence Range
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalSequenceRange
open TransitiveNameModel BoundedSetTheory

/-- The range of the natural-number-indexed graph `B`, restricted to `X`. -/
noncomputable def rangeSet (X B : ZFSet.{0}) : ZFSet.{0} :=
  X.sep (fun x => ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ B)

theorem rangeSet_mem (M X B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hX : X ∈ M) (hB : B ∈ M) : rangeSet X B ∈ M := by
  let e := cons ZFSet.omega (fun _ => B)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact sourceT_omega_mem M hM hT
    · exact hB
  simpa only [rangeSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 1 3)) e he hX

theorem mem_rangeSet (X : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ X)
    (x : ZFSet.{0}) : x ∈ rangeSet X (orbitGraph E) ↔ ∃ n, x = E n := by
  rw [rangeSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,n,hn,hpair⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,(orbitGraph_pair E n x).mp hpair⟩
  · rintro ⟨n,rfl⟩
    exact ⟨hE n,natSet n,(mem_omega _).mpr ⟨n,rfl⟩,(orbitGraph_pair E n _).mpr rfl⟩

/-- The union of the family `S`, restricted to the ambient set `U`. -/
noncomputable def unionSet (U S : ZFSet.{0}) : ZFSet.{0} :=
  U.sep (fun x => ∃ E ∈ S, x ∈ E)

theorem unionSet_mem (M U S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hS : S ∈ M) : unionSet U S ∈ M := by
  simpa only [unionSet,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.member 1 0))
      (fun _ => S) (fun _ => hS) hU

theorem mem_unionSet (U S x : ZFSet.{0}) (hS : ∀ E ∈ S, E ⊆ U) :
    x ∈ unionSet U S ↔ ∃ E ∈ S, x ∈ E := by
  rw [unionSet,ZFSet.mem_sep]
  exact ⟨And.right,fun ⟨E,hE,hx⟩ => ⟨hS E hE hx,E,hE,hx⟩⟩

end TuringRigidity.InternalSequenceRange

end OAI
