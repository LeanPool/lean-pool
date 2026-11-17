/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenFactorRequirement.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFactor

/-!
# Cohen Factor Requirement
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenFactorRequirement
open TransitiveNameModel BoundedSetTheory CohenGroundPoset
open InternalCohenFactor InternalCohenRestriction InternalCohenPartition
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Conditions whose two coordinate restrictions extend a pair in the supplied relation `R`. -/
noncomputable def requirement (A B R : ZFSet.{0}) : ZFSet.{0} :=
  (conditions A).sep (fun p =>
    ∃ b ∈ conditions B, ZFSet.pair p b ∈ restrictionGraph A B ∧
    ∃ d ∈ conditions (A \ B), ZFSet.pair p d ∈ restrictionGraph A (A \ B) ∧
    ∃ r ∈ conditions (A \ B), r ⊆ d ∧
    ∃ a ∈ conditions B, a ⊆ b ∧ ZFSet.pair r a ∈ R)

theorem requirement_mem (M A B R : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hR : R ∈ M) : requirement A B R ∈ M := by
  have hD := complement_mem M A B hM hT hA hB
  let e := cons (conditions B) (cons (conditions (A \ B))
    (cons (restrictionGraph A B) (cons (restrictionGraph A (A \ B)) (fun _ => R))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact conditions_mem M B hM hT hB
    · exact conditions_mem M _ hM hT hD
    · exact restrictionGraph_mem M A B hM hT hA hB
    · exact restrictionGraph_mem M A _ hM hT hA hD
    · exact hR
  simpa only [requirement,Formula.Eval,Formula.eval_pairMem,Formula.eval_subset,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 1 0 4)
        (.existsMem 3 (.conj (.pairMem 2 0 6)
          (.existsMem 4 (.conj (.subset 0 1)
            (.existsMem 4 (.conj (.subset 0 3) (.pairMem 1 0 9))))))))) e he
      (conditions_mem M A hM hT hA)

theorem label_requirement (A B R : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A)) :
    label _ p ∈ requirement A B R ↔
      ∃ r : Conditions (conditions (A \ B)), ∃ a : Conditions (conditions B),
        project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p ≤ r ∧
        project A B hBA p ≤ a ∧ ZFSet.pair (label _ r) (label _ a) ∈ R := by
  rw [requirement,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,b,_,hb,d,_,hd,r,hr,hrd,a,ha,hab,hra⟩
    obtain ⟨r,rfl⟩ := label_surjective _ hr
    obtain ⟨a,rfl⟩ := label_surjective _ ha
    have hb' := ((pair_restrictionGraph A B _ b).mp hb).2.2
    have hd' := ((pair_restrictionGraph A (A \ B) _ d).mp hd).2.2
    refine ⟨r,a,?_,?_,hra⟩
    · change label _ r ⊆ label _ (project A (A \ B) _ p)
      rw [label_project,←hd']; exact hrd
    · change label _ a ⊆ label _ (project A B _ p)
      rw [label_project,←hb']; exact hab
  · rintro ⟨r,a,hr,ha,hra⟩
    refine ⟨label_mem _ p,label _ (project A B hBA p),label_mem _ _,
      (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩,
      label _ (project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p),label_mem _ _,
      (pair_restrictionGraph A (A \ B) _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A _ _ p⟩,
      label _ r,label_mem _ r,hr,label _ a,label_mem _ a,ha,hra⟩

end TuringRigidity.CohenFactorRequirement

end OAI
