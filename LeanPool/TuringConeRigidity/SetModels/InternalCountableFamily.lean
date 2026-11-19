/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCountableFamily.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableUnion

/-!
# Internal Countable Family
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCountableFamily
open TransitiveNameModel BoundedSetTheory

theorem sequence_of_graph (S B : ZFSet.{0}) (hB : FunctionGraph ZFSet.omega S B) :
    ∃ E : ℕ → ZFSet.{0}, (∀ n, E n ∈ S) ∧ orbitGraph E = B := by
  classical
  have h (n : ℕ) := hB.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
  choose E hE hpair huniq using h
  refine ⟨E,hE,?_⟩
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_orbitGraph E z).mp hz
    exact hpair n
  · intro hz
    obtain ⟨n,hn,x,hx,rfl⟩ := hB.1 z hz
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact (orbitGraph_pair E n x).mpr (huniq n x hx hz)

theorem countable_sUnion (M S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hS : S ∈ M) (hcount : S = ∅ ∨ InternallyCountable M S)
    (hsets : ∀ A ∈ S, A = ∅ ∨ InternallyCountable M A) :
    ZFSet.sUnion S = ∅ ∨ InternallyCountable M (ZFSet.sUnion S) := by
  classical
  by_cases hne : ∃ x, x ∈ ZFSet.sUnion S
  · right
    rcases hcount with rfl|⟨B,hBM,hB,honto⟩
    · simp at hne
    obtain ⟨E,hE,hEB⟩ := sequence_of_graph S B hB
    apply InternalCountableUnion.internally_countable_union M (ZFSet.sUnion S) S hM hT
      (union_mem M hM hT.union hS) hS
      (fun A hA x hx => ZFSet.mem_sUnion.mpr ⟨A,hA,hx⟩) hsets E hE (hEB.symm ▸ hBM) _ hne
    intro x hx
    obtain ⟨A,hA,hxA⟩ := ZFSet.mem_sUnion.mp hx
    obtain ⟨n,hn,hnA⟩ := honto A hA
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    have he : A = E n := (orbitGraph_pair E n A).mp (hEB.symm ▸ hnA)
    exact ⟨n,he ▸ hxA⟩
  · left
    apply ZFSet.ext; intro x
    exact ⟨fun hx => False.elim (hne ⟨x,hx⟩),fun hx => False.elim (ZFSet.notMem_empty x hx)⟩

end TuringRigidity.InternalCountableFamily

end OAI
