/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenProjectionSymmetry.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenTailHomogeneity
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenProjectedGeneric

/-!
# Internal Cohen Projection Symmetry
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenProjectionSymmetry
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AutomorphismName
open CohenGroundPoset InternalCohenRestriction InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem project_fixed (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (a : Conditions (conditions A) ≃o Conditions (conditions A))
    (hfix : ∀ s, restrict B (label _ (a s)) = restrict B (label _ s))
    (s : Conditions (conditions A)) : project A B hBA (a s) = project A B hBA s := by
  apply label_injective
  simpa only [label_project] using hfix s

theorem projected_carrier_fixed (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (a : Conditions (conditions A) ≃o Conditions (conditions A))
    (hfix : ∀ s, restrict B (label _ (a s)) = restrict B (label _ s))
    (G : GenericFilter (Conditions (conditions A))) :
    (projected A B hBA (mapFilter a G)).carrier = (projected A B hBA G).carrier := by
  apply Set.ext; intro q
  rw [mem_projected,mem_projected]
  constructor
  · rintro ⟨p,hp,hpq⟩
    refine ⟨a.symm p,hp,?_⟩
    have hh := project_fixed A B hBA a hfix (a.symm p)
    rw [a.apply_symm_apply] at hh
    exact hh.symm.trans hpq
  · rintro ⟨p,hp,hpq⟩
    exact ⟨a p,by simpa only [mapFilter,Set.mem_ofPred_eq,a.symm_apply_apply] using hp,
      (project_fixed A B hBA a hfix p).trans hpq⟩

theorem projected_name_value_fixed (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (a : Conditions (conditions A) ≃o Conditions (conditions A))
    (hfix : ∀ s, restrict B (label _ (a s)) = restrict B (label _ s))
    (τ : Name (Conditions (conditions B))) (G : GenericFilter (Conditions (conditions A))) :
    τ.val (projected A B hBA (mapFilter a G)).carrier =
      τ.val (projected A B hBA G).carrier := by
  rw [projected_carrier_fixed A B hBA a hfix G]

theorem projected_cone_iff (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (p : Conditions (conditions A)) :
    project A B hBA p ∈ (projected A B hBA G).carrier ↔
      ∃ q ∈ G.carrier, restrict B (label _ p) ⊆ restrict B (label _ q) := by
  constructor
  · intro hp
    obtain ⟨q,hq,he⟩ := (mem_projected A B hBA G _).mp hp
    refine ⟨q,hq,?_⟩
    have hh := congrArg (label (conditions B)) he
    rw [label_project,label_project] at hh
    rw [hh]
  · rintro ⟨q,hq,hpq⟩
    apply (projected A B hBA G).upper (p := project A B hBA q)
    · change label _ (project A B hBA p) ⊆ label _ (project A B hBA q)
      simpa only [label_project] using hpq
    · exact projected_contains A B hBA G hq

end TuringRigidity.InternalCohenProjectionSymmetry

end OAI
