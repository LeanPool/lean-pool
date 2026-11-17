/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalProjectionFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalDefinitions

/-!
# Natural Projection Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u
namespace Formula

/-- Bounded formula computing either projection of a natural-number pair. -/
def naturalProjection (right : Bool) : Formula := .existsMem 2 (.existsMem 3
  (.conj (naturalPair 4 5 1 0 3) (.equal 2 (if right then 0 else 1))))

theorem naturalProjection_spec (right : Bool) : DefinesNatural.{u} (naturalProjection right)
    (fun n => if right then (Nat.unpair n).2 else (Nat.unpair n).1) := by
  intro e ho hQ n hn
  have select (a b : ZFSet.{u}) : cons b (cons a e) (if right then 0 else 1) =
      if right then b else a := by cases right <;> rfl
  have hmem (k : ℕ) : natSet.{u} k ∈ e 2 := by rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
  simp only [naturalProjection,Formula.Eval,cons_succ,select]
  constructor
  · rintro ⟨a,ha,b,hb,hpair,hy⟩
    rw [ho] at ha hb
    obtain ⟨a,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨b,rfl⟩ := (mem_omega b).mp hb
    have hp := (naturalPair_spec 4 5 1 0 3 (cons (natSet b) (cons (natSet a) e))
      ho hQ a b rfl rfl).mp hpair
    have he : n = Nat.pair a b := natSet_injective (hn.symm.trans hp)
    subst n
    cases right <;> simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.unpair_pair] using hy
  · intro hy
    refine ⟨natSet (Nat.unpair n).1,hmem _,natSet (Nat.unpair n).2,hmem _,?_,?_⟩
    · apply (naturalPair_spec 4 5 1 0 3
        (cons (natSet (Nat.unpair n).2) (cons (natSet (Nat.unpair n).1) e))
        ho hQ _ _ rfl rfl).mpr
      simpa only [cons_succ,Nat.pair_unpair] using hn
    · cases right <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using hy

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
