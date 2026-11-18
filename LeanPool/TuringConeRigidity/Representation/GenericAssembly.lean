/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericAssembly.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.IdealSelection

/-!
# Generic Assembly
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

theorem representative_from_generic_coding (π : Degree ≃o Degree)
    (F : Oracle → Oracle) (hF : Measurable F)
    (C : Oracle → Oracle → Oracle) (hC : Measurable (Function.uncurry C))
    (G : Bool → Oracle → Oracle) (hG : ∀ b, Measurable (G b))
    (hgen : ∀ A b, degree (F (G b A)) = π (degree (G b A)))
    (hcoded : ∀ A b, degree (F (C A (G b A))) = π (degree (C A (G b A))))
    (hideal : ∀ A a, a ≤ degree A ↔
      a ≤ degree (join (C A (G false A)) (G false A)) ∧
      a ≤ degree (join (C A (G true A)) (G true A))) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) := by
  let L : Bool → Oracle → Oracle := fun b A => join (F (C A (G b A))) (F (G b A))
  have hL (b : Bool) : Measurable (L b) :=
    join_measurable _ _ (hF.comp (hC.comp (measurable_id.prodMk (hG b)))) (hF.comp (hG b))
  have hdegree (A : Oracle) (b : Bool) :
      degree (L b A) = π (degree (join (C A (G b A)) (G b A))) := by
    dsimp only [L]
    change degree (F (C A (G b A))) ⊔ degree (F (G b A)) =
      π (degree (C A (G b A)) ⊔ degree (G b A))
    rw [hcoded A b, hgen A b, π.map_sup]
  apply borel_of_ideal_intersection (L false) (L true) (hL false) (hL true)
    (fun A => π (degree A))
  intro A a
  rw [hdegree A false,hdegree A true]
  exact common_lower_transport π _ _ _ (hideal A) a

end TuringRigidity

end OAI
