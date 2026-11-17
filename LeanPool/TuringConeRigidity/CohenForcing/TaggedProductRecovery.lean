/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/TaggedProductRecovery.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.TaggedProductGeneric

/-!
# Tagged Product Recovery
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TaggedProductRecovery
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting TaggedProductGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def jointSet (c g h : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun z => ∃ p ∈ g, ∃ s ∈ h, z = code p s)

theorem jointSet_mem (N c g h : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hg : g ∈ N) (hh : h ∈ N) : jointSet c g h ∈ N := by
  let e := cons g (cons h (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ N := by
    intro i
    rcases i with _ | _ | _ | i
    · exact hg
    · exact hh
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hsepCode (left right value : ZFSet.{0}) :
      (codeFormula 1 0 2 5 6).Eval (cons right (cons left (cons value e))) ↔
        value = code left right :=
    codeFormula_spec 1 0 2 5 6 _ rfl rfl
  simpa only [jointSet,Formula.Eval,hsepCode,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (codeFormula 1 0 2 5 6))) e he hc

variable (a b c : ZFSet.{0})
variable (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
variable (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b))

theorem code_mem_joint (p : Conditions a) (s : Conditions b) :
    code (label a p) (label b s) ∈ genericFilterSet c (joint a b c hcs G H).carrier ↔
      p ∈ G.carrier ∧ s ∈ H.carrier := by
  rw [mem_genericFilterSet]
  constructor
  · rintro ⟨r,hr,he⟩
    have hrps : r = productMap a b c hcs (p,s) := label_injective c
      (he.trans (label_productMap a b c hcs (p,s)).symm)
    exact (joint_mem a b c hcs G H p s).mp (hrps ▸ hr)
  · intro h
    exact ⟨productMap a b c hcs (p,s),(joint_mem a b c hcs G H p s).mpr h,
      label_productMap a b c hcs (p,s)⟩

theorem jointFilterSet_eq :
    genericFilterSet c (joint a b c hcs G H).carrier =
      jointSet c (genericFilterSet a G.carrier) (genericFilterSet b H.carrier) := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨r,_,hrz⟩ := (mem_genericFilterSet c _ z).mp hz
    have hzc := hrz ▸ label_mem c r
    obtain ⟨p,hp,s,hs,he⟩ := (hcs z).mp hzc
    obtain ⟨p,rfl⟩ := label_surjective a hp
    obtain ⟨s,rfl⟩ := label_surjective b hs
    obtain ⟨hpG,hsH⟩ := (code_mem_joint a b c hcs G H p s).mp (he ▸ hz)
    exact ZFSet.mem_sep.mpr ⟨hzc,label a p,(mem_genericFilterSet a _ _).mpr ⟨p,hpG,rfl⟩,
      label b s,(mem_genericFilterSet b _ _).mpr ⟨s,hsH,rfl⟩,he⟩
  · intro hz
    obtain ⟨_,p,hp,s,hs,he⟩ := ZFSet.mem_sep.mp hz
    obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a G.carrier p).mp hp
    obtain ⟨s,hsH,rfl⟩ := (mem_genericFilterSet b H.carrier s).mp hs
    exact he.symm ▸ (code_mem_joint a b c hcs G H p s).mpr ⟨hpG,hsH⟩

theorem leftFilterSet_eq : genericFilterSet a G.carrier =
    sectionSet a b (genericFilterSet c (joint a b c hcs G H).carrier) ∅ := by
  apply ZFSet.ext; intro p
  constructor
  · intro hp
    obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a _ p).mp hp
    obtain ⟨s,hs⟩ := H.nonempty
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,label b s,label_mem b s,
      code (label a p) (label b s),(code_mem_joint a b c hcs G H p s).mpr ⟨hpG,hs⟩,rfl,
      fun x hx => False.elim (ZFSet.notMem_empty x hx)⟩
  · intro hp
    obtain ⟨hpa,s,hs,z,hz,he,_⟩ := ZFSet.mem_sep.mp hp
    obtain ⟨p,rfl⟩ := label_surjective a hpa
    obtain ⟨s,rfl⟩ := label_surjective b hs
    have hpG := ((code_mem_joint a b c hcs G H p s).mp (he ▸ hz)).1
    exact (mem_genericFilterSet a _ _).mpr ⟨p,hpG,rfl⟩

theorem rightFilterSet_eq : genericFilterSet b H.carrier =
    fiberSet b (genericFilterSet c (joint a b c hcs G H).carrier) a := by
  apply ZFSet.ext; intro s
  constructor
  · intro hs
    obtain ⟨s,hsH,rfl⟩ := (mem_genericFilterSet b _ s).mp hs
    obtain ⟨p,hp⟩ := G.nonempty
    exact ZFSet.mem_sep.mpr ⟨label_mem b s,label a p,label_mem a p,
      code (label a p) (label b s),(code_mem_joint a b c hcs G H p s).mpr ⟨hp,hsH⟩,rfl⟩
  · intro hs
    obtain ⟨hsb,p,hp,z,hz,he⟩ := ZFSet.mem_sep.mp hs
    obtain ⟨p,rfl⟩ := label_surjective a hp
    obtain ⟨s,rfl⟩ := label_surjective b hsb
    have hsH := ((code_mem_joint a b c hcs G H p s).mp (he ▸ hz)).2
    exact (mem_genericFilterSet b _ _).mpr ⟨s,hsH,rfl⟩

end TuringRigidity.TaggedProductRecovery

end OAI
