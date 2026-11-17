/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaRecursionSchemas.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerGraph

/-!
# Omega Recursion Schemas
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem productSigma_context (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSigma.Realize M e ↔ e 0 = (a*b).toZFSet := by
  exact productSigma_of_context M C hRep e he a b ha hb

theorem omegaGraph_of_mem_iff_context (M d f : ZFSet.{u}) (C : Context M)
    (hdM : d ∈ M) (hfM : f ∈ M) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x)) :
    OmegaGraph M d (iterUnion 2 f) f := by
  exact omegaGraph_of_mem_iff_of_context M d f C hdM hfM hd hf

theorem mulOmega_sigmaDefinable_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
  M) :
    SigmaDefinable M (fun e => (e 1).IsOrdinal ∧ e 0 = ((e 1).rank*Ordinal.omega0).toZFSet) := by
  exact mulOmega_sigmaDefinable_of_context M C hRep

theorem omegaGraph_sigmaDefinable_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
  M) (hColl : SigmaCollection M)
    (d r f : ℕ) : SigmaDefinable M (fun e => OmegaGraph M (e d) (e r) (e f)) := by
  exact omegaGraph_sigmaDefinable_of_schemas M C hRep hColl d r f

theorem uniform_omega_certificate_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
  M) (hColl : SigmaCollection M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ f ∈ M, p.Realize M (cons f (cons x e)) ↔
        ∃ r ∈ M, OmegaGraph M (insert x x) r f := by
  exact uniform_omega_certificate_of_schemas M C hRep hColl

end TuringRigidity.OrdinalArithmetic

end OAI
