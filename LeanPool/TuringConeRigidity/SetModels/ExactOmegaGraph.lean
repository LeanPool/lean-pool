/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ExactOmegaGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerDefinability

/-!
# Exact Omega Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omegaGraph_of_exact_pairs (M d f : ZFSet.{u}) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x))
    (hval : ∀ x ∈ d, (Ordinal.omega0 ^ x.rank).toZFSet ∈ M) :
    OmegaGraph M d (iterUnion 2 f) f := by
  exact omegaGraph_of_exact_pairs_of_value_mem M d f hd hf hval

theorem OmegaGraph.union_value_mem {M d r f : ZFSet.{u}} (hg : OmegaGraph M d r f)
    {x : ZFSet.{u}} (hx : x ∈ d) : (Ordinal.omega0 ^ x.rank).toZFSet ∈ M := by
  obtain ⟨v,hv,hfv,_⟩ := hg.2.1.2 x hx
  obtain ⟨A,hA,hs,_,_⟩ := hg.2.2 x hx v hv hfv
  exact (omegaStageStep_exact hg hx hs) ▸ hA

end TuringRigidity.OrdinalArithmetic

end OAI
