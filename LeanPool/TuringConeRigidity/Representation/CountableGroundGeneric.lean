/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CountableGroundGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalAtomicTruth

/-!
# Countable Ground Generic
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory CountableForcing
universe u

theorem countable_ground_generic (M : ZFSet.{u}) [Countable (Conditions M)]
    (hne : ∃ x, x ∈ M) {c : ZFSet.{u}} [Preorder (Conditions c)] (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ GroundGeneric M G := by
  classical
  obtain ⟨x,hx⟩ := hne
  obtain ⟨m,_⟩ := label_surjective M hx
  let _ : Nonempty (Conditions M) := ⟨m⟩
  obtain ⟨e,he⟩ := exists_surjective_nat (Conditions M)
  let D : ℕ → Set (Conditions c) := fun n =>
    if Dense {q : Conditions c | label c q ∈ label M (e n)} then
      {q | label c q ∈ label M (e n)} else Set.univ
  have hD : ∀ n, Dense (D n) := by
    intro n
    dsimp only [D]
    split
    · assumption
    · exact fun q => ⟨q,le_rfl,Set.mem_univ _⟩
  obtain ⟨G,hp,hG⟩ := exists_generic D hD p
  refine ⟨G,hp,?_⟩
  intro E hEM hE
  obtain ⟨m,hm⟩ := label_surjective M hEM
  obtain ⟨n,rfl⟩ := he m
  have hd : Dense {q : Conditions c | label c q ∈ label M (e n)} := by
    rw [hm]; exact hE
  obtain ⟨q,hq,hqn⟩ := hG n
  refine ⟨q,hq,?_⟩
  simpa only [D,ite_eq_left hd,Set.mem_ofPred_eq,hm] using hqn

end TuringRigidity.AtomicForcing

end OAI
