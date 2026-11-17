/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalQuotientRequirement.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalQuotientLifting
public import LeanPool.TuringConeRigidity.CohenForcing.CheckedForcingRelation

/-!
# Internal Quotient Requirement
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalQuotientRequirement
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
attribute [local instance] InternalCollapse.order

noncomputable def requirement (c a R : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => ∃ r ∈ c, r ⊆ p ∧ ∃ V ∈ a, p ∈ V ∧ ZFSet.pair r V ∈ R)

theorem requirement_mem (M c a R : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (ha : a ∈ M) (hR : R ∈ M) : requirement c a R ∈ M := by
  let e := cons c (cons a (fun _ => R))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | _ | i
    · exact hc
    · exact ha
    · exact hR
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.conj (.subset 0 1) (.existsMem 3
      (.conj (.member 2 0) (.pairMem 1 0 5))))) e he hc
  simpa only [requirement,Formula.Eval,Formula.eval_subset,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using hs

theorem requirement_subset (c a R : ZFSet.{0}) : requirement c a R ⊆ c :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem requirement_lower (c a R : ZFSet.{0}) (ha : ∀ V ∈ a, IsCode c V) :
    Lower c (requirement c a R) := by
  intro p hp s hs hps
  obtain ⟨_,r,hr,hrp,V,hV,hpV,hrV⟩ := ZFSet.mem_sep.mp hp
  exact ZFSet.mem_sep.mpr ⟨hs,r,hr,fun _ h => hps (hrp h),V,hV,
    code_lower c V (ha V hV) p hpV s hs hps,hrV⟩

end TuringRigidity.InternalQuotientRequirement

end OAI
