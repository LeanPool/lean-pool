/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformDefSuccessor.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ContextDefinablePower
public import LeanPool.TuringConeRigidity.Syntax.SigmaParameterized
public import LeanPool.TuringConeRigidity.SetModels.InternalDefinablePower

/-!
# Uniform Def Successor
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem definablePower_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    SigmaDefinable M (fun e => e 0 = definablePower (e 1)) := by
  exact definablePower_sigmaDefinable_of_context M
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩

theorem uniform_definable_successor (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ p : SigmaFormula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
      ∀ A ∈ M, ∀ D ∈ M, p.Realize M (cons D (cons A d)) ↔ D = definablePower A :=
  (definablePower_sigmaDefinable M hM hT).binary definablePower

theorem definablePower_image_mem (M a : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (ha : a ∈ M) :
    ∃ b ∈ M, ∀ y, y ∈ b ↔ ∃ x ∈ a, definablePower x = y := by
  obtain ⟨p,d,hd,hp⟩ := uniform_definable_successor M hM hT
  exact replacement_image M hM hT.replacement.finitePrefix p d hd ha definablePower
    (fun x hx => definablePower_mem M x hM hT (hM a ha x hx))
    (fun x hx y hy => hp x (hM a ha x hx) y hy)

end TuringRigidity.RelativeConstructible

end OAI
