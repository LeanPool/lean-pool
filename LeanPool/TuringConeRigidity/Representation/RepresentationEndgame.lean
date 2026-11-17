/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RepresentationEndgame.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericAssembly
public import LeanPool.TuringConeRigidity.Representation.GenericCodingBorel
public import LeanPool.TuringConeRigidity.Representation.BorelGeneric

/-!
# Representation Endgame
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

theorem representative_from_selected_generics (π : Degree ≃o Degree)
    (F : Oracle → Oracle) (hF : Measurable F)
    (G : Bool → Oracle → Oracle) (hG : ∀ b, Measurable (G b))
    (hinfinite : ∀ A b, GenericCoding.InfiniteOdd (G b A))
    (hgen : ∀ A b, degree (F (G b A)) = π (degree (G b A)))
    (hcoded : ∀ A b, degree (F (GenericCoding.code A (G b A))) =
      π (degree (GenericCoding.code A (G b A))))
    (hideal : ∀ A a, a ≤ degree A ↔
      a ≤ degree (join A (G false A)) ∧ a ≤ degree (join A (G true A))) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) := by
  apply representative_from_generic_coding π F hF GenericCoding.code GenericCoding.code_measurable
    G hG hgen hcoded
  intro A a
  rw [GenericCoding.join_degree_eq A (G false A) (hinfinite A false),
    GenericCoding.join_degree_eq A (G true A) (hinfinite A true)]
  exact hideal A a

theorem representative_from_generic_program (π : Degree ≃o Degree) (p : OracleCode) (P : Oracle)
    (G : Bool → Oracle → Oracle) (hG : ∀ b, Measurable (G b))
    (hinfinite : ∀ A b, GenericCoding.InfiniteOdd (G b A))
    (hgen : ∀ A b, ∃ B, OracleCode.eval (oracleFunction (join (G b A) P)) p = oracleFunction B ∧
      degree B = π (degree (G b A)))
    (hcoded : ∀ A b, ∃ B, OracleCode.eval (oracleFunction (join (GenericCoding.code A (G b A)) P))
      p =
      oracleFunction B ∧ degree B = π (degree (GenericCoding.code A (G b A))))
    (hideal : ∀ A a, a ≤ degree A ↔
      a ≤ degree (join A (G false A)) ∧ a ≤ degree (join A (G true A))) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) := by
  let F : Oracle → Oracle := fun Y => programOutput p (join Y P)
  have hF : Measurable F := (programOutput_measurable p).comp
    (join_measurable _ _ measurable_id measurable_const)
  apply representative_from_selected_generics π F hF G hG hinfinite
  · intro A b
    obtain ⟨B,hp,hB⟩ := hgen A b
    change degree (programOutput p (join (G b A) P)) = _
    rw [programOutput_eq p _ B hp]
    exact hB
  · intro A b
    obtain ⟨B,hp,hB⟩ := hcoded A b
    change degree (programOutput p (join (GenericCoding.code A (G b A)) P)) = _
    rw [programOutput_eq p _ B hp]
    exact hB
  · exact hideal

end TuringRigidity

end OAI
