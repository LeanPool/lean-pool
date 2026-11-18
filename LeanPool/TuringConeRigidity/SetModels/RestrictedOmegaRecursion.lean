/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RestrictedOmegaRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.InternalOmegaPower

/-!
# Restricted Omega Recursion
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem internal_omegaGraph_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
  (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hxM : x ∈ M) (hxo : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M (insert x x) (iterUnion 2 f) f := by
  exact internal_omegaGraph_of_schemas M C hRep hColl x hxM hxo

theorem ordinal_omega_opow_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
  (hColl : SigmaCollection M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (Ordinal.omega0 ^ a).toZFSet ∈ M := by
  exact ordinal_omega_opow_of_schemas M C hRep hColl a ha

end TuringRigidity.OrdinalArithmetic

end OAI
