/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ContextHierarchyGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ContextDefinablePower
public import LeanPool.TuringConeRigidity.Constructibility.HierarchyGraph
public import LeanPool.TuringConeRigidity.Syntax.SigmaParameterized

/-!
# Context Hierarchy Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
theorem definablePower_sigmaDefinable_context (M : ZFSet.{u}) (C : Context M) :
    SigmaDefinable M (fun e => e 0 = definablePower (e 1)) := by
  exact definablePower_sigmaDefinable_of_context M C

theorem uniform_definable_successor_context (M : ZFSet.{u}) (C : Context M) :
    ∃ p : SigmaFormula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
      ∀ A ∈ M, ∀ D ∈ M, p.Realize M (cons D (cons A d)) ↔ D = definablePower A :=
  (definablePower_sigmaDefinable_context M C).binary definablePower

theorem stageImage_mem_context (M : ZFSet.{u}) (C : Context M)
    {s x f : ZFSet.{u}} (hs : s ∈ M) (hx : x ∈ M) (hf : f ∈ M) : stageImage s x f ∈ M := by
  exact stageImage_mem_of_context M C hs hx hf

theorem hierarchyGraph_of_mem_iff_context (M R d f : ZFSet.{u}) (C : Context M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hfM : f ∈ M) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x))) :
    HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  exact hierarchyGraph_of_mem_iff_of_context M R d f C hs hdM hfM hd hf

end TuringRigidity.RelativeConstructible

end OAI
