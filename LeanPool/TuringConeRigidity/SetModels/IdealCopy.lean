/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/IdealCopy.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.IdealLift

/-!
# Ideal Copy
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IdealInterpretation
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding
noncomputable section

theorem transport_copy {U : ℕ → Prop} {I J : DegreeIdeal} (ρ : I ≃o J)
    (c : Copy U) (b : I) (hS : RelationBelow c.successor b.val) (hP : RelationBelow c.predicate
      b.val) :
    ∃ d : Copy U, RelationBelow d.successor (ρ b).val ∧ RelationBelow d.predicate (ρ b).val := by
  let S := RCode.ofBelow c.successor b hS
  let P := RCode.ofBelow c.predicate b hP
  have hn (n : ℕ) : c.node n ∈ I.carrier := by
    have hh : S.external.Holds (two (c.node n) (c.node (n+1))) := by
      simpa only [S,RCode.external_ofBelow] using (c.successor_spec _ _).mpr ⟨n,rfl,rfl⟩
    exact S.coordinates_mem hh 0
  let node : ℕ → I := fun n => ⟨c.node n,hn n⟩
  have hi : Function.Injective (fun n => (ρ (node n)).val) := by
    intro i j he
    have hh : ρ (node i) = ρ (node j) := Element.ext _ _ he
    exact c.injective (congrArg Element.val (ρ.injective hh))
  have hsuccessor (a d : J) : (S.map ρ).external.Holds (two a.val d.val) ↔
      ∃ k, a = ρ (node k) ∧ d = ρ (node (k+1)) := by
    have hh := S.transport_two ρ (ρ.symm a) (ρ.symm d)
    simp only [ρ.apply_symm_apply,S,RCode.external_ofBelow] at hh
    rw [hh,c.successor_spec]
    constructor
    · rintro ⟨k,hk,hl⟩
      have he : ρ.symm a = node k := Element.ext _ _ hk
      have hf : ρ.symm d = node (k+1) := Element.ext _ _ hl
      exact ⟨k,by rw [← he,ρ.apply_symm_apply],by rw [← hf,ρ.apply_symm_apply]⟩
    · rintro ⟨k,rfl,rfl⟩
      exact ⟨k,by simp only [ρ.symm_apply_apply,node],by simp only [ρ.symm_apply_apply,node]⟩
  have hpredicate (a : J) : (P.map ρ).external.Holds (one a.val) ↔
      ∃ k, U k ∧ a = ρ (node k) := by
    have hh := P.transport_one ρ (ρ.symm a)
    simp only [ρ.apply_symm_apply,P,RCode.external_ofBelow] at hh
    rw [hh,c.predicate_spec]
    constructor
    · rintro ⟨k,hk,he⟩
      have hf : ρ.symm a = node k := Element.ext _ _ he
      exact ⟨k,hk,by rw [← hf,ρ.apply_symm_apply]⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨k,hk,by simp only [ρ.symm_apply_apply,node]⟩
  have hsglobal (a d : Degree) : (S.map ρ).external.Holds (two a d) ↔
      ∃ k, a = (ρ (node k)).val ∧ d = (ρ (node (k+1))).val := by
    constructor
    · intro h
      have ha : a ∈ J.carrier := (S.map ρ).coordinates_mem h 0
      have hd : d ∈ J.carrier := (S.map ρ).coordinates_mem h 1
      obtain ⟨k,hk,hl⟩ := (hsuccessor ⟨a,ha⟩ ⟨d,hd⟩).mp h
      exact ⟨k,congrArg Element.val hk,congrArg Element.val hl⟩
    · rintro ⟨k,rfl,rfl⟩
      exact (hsuccessor _ _).mpr ⟨k,rfl,rfl⟩
  have hpglobal (a : Degree) : (P.map ρ).external.Holds (one a) ↔
      ∃ k, U k ∧ a = (ρ (node k)).val := by
    constructor
    · intro h
      have ha : a ∈ J.carrier := (P.map ρ).coordinates_mem h 0
      obtain ⟨k,hk,he⟩ := (hpredicate ⟨a,ha⟩).mp h
      exact ⟨k,hk,congrArg Element.val he⟩
    · rintro ⟨k,hk,rfl⟩
      exact (hpredicate _).mpr ⟨k,hk,rfl⟩
  let d : Copy U := ⟨fun k => (ρ (node k)).val,hi,(S.map ρ).external,(P.map
    ρ).external,hsglobal,hpglobal⟩
  refine ⟨d,S.map_below ρ b ?_,P.map_below ρ b ?_⟩
  · simpa only [S,RCode.external_ofBelow] using hS
  · simpa only [P,RCode.external_ofBelow] using hP

end
end TuringRigidity.IdealInterpretation

end OAI
