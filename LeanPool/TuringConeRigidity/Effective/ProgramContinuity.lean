/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/ProgramContinuity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericIdentity
public import LeanPool.TuringConeRigidity.Representation.GenericRepresentation

/-!
# Program Continuity
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericIdentity
open Set

theorem value_continuousOn (p : OracleCode) (P : Oracle) (S : Set Oracle)
    (hS : ∀ A ∈ S, Total p P A) : ContinuousOn (value p P) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_pi
  intro n
  have hO : Continuous (fun A : S => join A.val P) := by
    apply continuous_pi
    intro i
    dsimp only [join]
    split
    · exact continuous_const
    · exact (continuous_apply _).comp continuous_subtype_val
  have hf (b : Bool) : IsOpen {A : S | value p P A.val n = b} := by
    have he : {A : S | value p P A.val n = b} =
        (fun A : S => join A.val P) ⁻¹'
          {B | (if b then 1 else 0) ∈ OracleCode.eval (oracleFunction B) p n} := by
      ext A
      simp only [mem_ofPred_eq,mem_preimage]
      rw [(total_iff p P A.val).mp (hS A.val A.property)]
      simp only [oracleFunction,Part.mem_some_iff]
      cases b <;> cases value p P A.val n <;> simp
    rw [he]
    exact (OracleCode.halting_set_open p n _).preimage hO
  apply continuous_def.mpr
  intro U _
  have he : (fun A : S => value p P A.val n) ⁻¹' U =
      ⋃ b : Bool, ⋃ (_ : b ∈ U), {A : S | value p P A.val n = b} := by
    ext A; simp
  change IsOpen ((fun A : S => value p P A.val n) ⁻¹' U)
  rw [he]
  exact isOpen_iUnion (fun b => isOpen_iUnion (fun _ => hf b))

end GenericIdentity

theorem generic_continuous_of_program (π : Degree ≃o Degree)
    (h : GenericProgramRepresentation π) : GenericContinuousRepresentation π := by
  obtain ⟨D,hD,P,p,hp⟩ := h
  have ht (A : Oracle) (hA : ShuffleRequirements.GenericFor D A) : GenericIdentity.Total p P A := by
    obtain ⟨B,hB,_⟩ := hp A hA
    exact ⟨B,hB⟩
  refine ⟨D,hD,GenericIdentity.value p P,GenericIdentity.value_continuousOn p P _ ht,?_⟩
  intro A hA
  obtain ⟨B,hB,hπ⟩ := hp A hA
  change degree (programOutput p (join A P)) = _
  rw [programOutput_eq p _ B hB]
  exact hπ

theorem generic_program_iff_continuous (π : Degree ≃o Degree) :
    GenericProgramRepresentation π ↔ GenericContinuousRepresentation π :=
  ⟨generic_continuous_of_program π,generic_program_of_continuous π⟩

end TuringRigidity

end OAI
