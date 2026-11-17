/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GlobalJumpRestriction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentLocality

/-!
# Global Jump Restriction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.PersistentLocality
open IdealInterpretation IdealLocality PersistentRestrictions OracleJump

def fullIdeal : DegreeIdeal :=
  ⟨Set.univ,⟨⊥,Set.mem_univ _⟩,fun _ _ => Set.mem_univ _,fun _ _ => Set.mem_univ _⟩

def fullEquiv : Degree ≃o fullIdeal where
  toFun a := ⟨a,Set.mem_univ _⟩
  invFun a := a.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem global_jump_restriction (π : Degree ≃o Degree) (J : CountableIdeal)
    (hjump : JumpClosed (ideal J))
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ J.carrier) :
    ∃ ρ : J ≃o J, RestrictsTo π J ρ ∧ Persistent J ρ := by
  let τ : fullIdeal ≃o fullIdeal := fullEquiv.symm.trans (π.trans fullEquiv)
  let z : fullIdeal := fullEquiv (degree (jump FixedArithmetic.zero))
  obtain ⟨σ,hσ⟩ := source_4_1_4 τ z rfl
    (J := ideal J) (fun _ _ => Set.mem_univ _) hjump himages
  let ρ := unlift σ
  have hρ : RestrictsTo π J ρ := by
    intro x
    exact (hσ ⟨x.val,x.property⟩).symm
  exact ⟨ρ,hρ,persistent_of_global_restriction π J ρ hρ⟩

end TuringRigidity.PersistentLocality

end OAI
