/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GroundGenericRequirements.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CountableGroundGeneric

/-!
# Ground Generic Requirements
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.AtomicForcing
open TransitiveNameModel CountableForcing
universe u

theorem ground_generic_with_requirements (N : ZFSet.{u}) [Countable (Conditions N)]
    (hne : ∃ x, x ∈ N) {c : ZFSet.{u}} [Preorder (Conditions c)]
    (E : ℕ → Set (Conditions c)) (hE : ∀ n, Dense (E n)) (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ GroundGeneric N G ∧ GenericFor E G := by
  classical
  obtain ⟨x,hx⟩ := hne
  obtain ⟨m,_⟩ := label_surjective N hx
  let _ : Nonempty (Conditions N) := ⟨m⟩
  obtain ⟨e,he⟩ := exists_surjective_nat (Conditions N)
  let D : ℕ → Set (Conditions c) := fun n =>
    if Dense {q : Conditions c | label c q ∈ label N (e n)} then
      {q | label c q ∈ label N (e n)} else Set.univ
  have hD : ∀ n, Dense (D n) := by
    intro n
    dsimp only [D]
    split
    · assumption
    · exact fun q => ⟨q,le_rfl,Set.mem_univ _⟩
  let F : ℕ → Set (Conditions c) := fun n => if n % 2 = 0 then D (n/2) else E (n/2)
  have hF : ∀ n, Dense (F n) := by
    intro n
    dsimp only [F]
    split
    · exact hD _
    · exact hE _
  obtain ⟨G,hp,hG⟩ := exists_generic F hF p
  have hGD : GenericFor D G := by
    intro n; simpa [F] using hG (2*n)
  have hGE : GenericFor E G := by
    intro n; simpa [F,Nat.add_div] using hG (2*n+1)
  refine ⟨G,hp,?_,hGE⟩
  intro A hA hd
  obtain ⟨m,hm⟩ := label_surjective N hA
  obtain ⟨n,rfl⟩ := he m
  have hd' : Dense {q : Conditions c | label c q ∈ label N (e n)} := by rw [hm]; exact hd
  obtain ⟨q,hq,hqn⟩ := hGD n
  exact ⟨q,hq,by simpa only [D,ite_eq_left hd',Set.mem_ofPred_eq,hm] using hqn⟩

end TuringRigidity.AtomicForcing

end OAI
