/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/PartialComputability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Computability.PartrecCode

/-!
# Partial Computability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
open Computable

theorem partrec_code {α : Type*} [Primcodable α] {f : α →. ℕ} (hf : Partrec f) :
    ∃ c : Nat.Partrec.Code, ∀ a, c.eval (Encodable.encode a) = f a := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨c, fun a => ?_⟩
  simp [hc, Encodable.encodek, Part.map_id']

theorem partrec_cond {α : Type*} [Primcodable α] {b : α → Bool} {f g : α →. ℕ}
    (hb : Computable b) (hf : Partrec f) (hg : Partrec g) :
    Partrec (fun a => if b a then f a else g a) := by
  obtain ⟨cf,hcf⟩ := partrec_code hf
  obtain ⟨cg,hcg⟩ := partrec_code hg
  have hs : Computable (fun a => cond (b a) cf cg) :=
    Computable.cond hb (Computable.const cf) (Computable.const cg)
  exact (Nat.Partrec.Code.eval_part.comp hs Computable.encode).of_eq (fun a => by
    cases he : b a <;> simp [hcf,hcg])

theorem partrec_fixed_point {α : Type*} [Primcodable α]
    {f : Nat.Partrec.Code → α →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Nat.Partrec.Code, ∀ a, c.eval (Encodable.encode a) = f c a := by
  have hh : Partrec₂ (fun c n => (Encodable.decode (α := α) n : Part α).bind (f c)) :=
    (Computable.ofOption (Computable.decode.comp snd)).bind
      (hf.comp (fst.comp fst) snd)
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hh
  refine ⟨c,fun a => ?_⟩
  simp only [hc, Encodable.encodek]
  exact Part.bind_some a (f c)

end TuringRigidity

end OAI
