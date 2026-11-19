/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryCollapse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CountableElementaryHull
public import LeanPool.TuringConeRigidity.SetModels.InternalStructureCollapse

/-!
# Elementary Collapse
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

/-- The elementary hull represented as a set using its countable smallness witness. -/
noncomputable def hullSet (a : ℕ → ZFSet.{u}) : ZFSet.{u} := by
  letI : Countable (hull a) := (hull_countable a).to_subtype
  letI : Small.{u} (hull a) := Countable.toSmall _
  exact ZFSet.range (fun x : hull a => x.val)

theorem mem_hullSet (a : ℕ → ZFSet.{u}) (x : ZFSet.{u}) : x ∈ hullSet a ↔ x ∈ hull a := by
  classical
  simp only [hullSet,ZFSet.mem_range]
  exact ⟨fun ⟨y,hy⟩ => hy ▸ y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩

instance hullSet_countable (a : ℕ → ZFSet.{u}) : Countable (Conditions (hullSet a)) := by
  let : Countable (hull a) := (hull_countable a).to_subtype
  exact Function.Injective.countable (f := fun x : Conditions (hullSet a) =>
    (⟨label _ x,(mem_hullSet a _).mp (label_mem _ x)⟩ : hull a))
    (fun x y h => label_injective (hullSet a) (congrArg (fun z : hull a => z.val) h))

theorem hullSet_extensional (a : ℕ → ZFSet.{u}) : StructureExtensional (hullSet a) := by
  intro x hx y hy he
  let e := cons x (fun _ => y)
  have hen : ∀ i, e i ∈ hull a := by
    intro i; cases i <;> simp only [e,cons_zero,cons_succ]
    · exact (mem_hullSet a x).mp hx
    · exact (mem_hullSet a y).mp hy
  let p := SentenceForm.all (SentenceForm.iff (.member 0 1) (.member 0 2))
  have hs : p.Sat (hull a) e := by
    simp only [p,SentenceForm.sat_all,SentenceForm.sat_iff,SentenceForm.Sat,
      cons_zero,cons_succ,e]
    exact fun z hz => he z ((mem_hullSet a z).mpr hz)
  have ht := (hull_elementary a p e hen).mp hs
  simp only [p,SentenceForm.sat_all,SentenceForm.sat_iff,SentenceForm.Sat,
    cons_zero,cons_succ,e,Set.mem_univ,forall_const] at ht
  exact ZFSet.ext ht

/-- The set of collapse values of all elements of the coded domain. -/
noncomputable def collapsed (d : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun x : Conditions d => structureMap d (label d x))

theorem mem_collapsed (d z : ZFSet.{u}) :
    z ∈ collapsed d ↔ ∃ x ∈ d, z = structureMap d x := by
  rw [collapsed,ZFSet.mem_range]
  constructor
  · rintro ⟨x,rfl⟩; exact ⟨_,label_mem _ x,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨i,rfl⟩ := label_surjective d hx
    exact ⟨i,rfl⟩

theorem collapsed_transitive (d : ZFSet.{u}) : Transitive (collapsed d) := by
  intro x hx y hy
  obtain ⟨z,_,rfl⟩ := (mem_collapsed d x).mp hx
  obtain ⟨w,hw,_,rfl⟩ := (mem_value d (membershipRelation d) _ z y).mp hy
  exact (mem_collapsed d _).mpr ⟨w,hw,rfl⟩

instance collapsed_countable (d : ZFSet.{u}) [Countable (Conditions d)] :
    Countable (Conditions (collapsed d)) := by
  let f : Conditions (collapsed d) → Conditions d := fun z => Classical.choose
    (ZFSet.mem_range.mp (show label (collapsed d) z ∈ collapsed d from label_mem _ z))
  have hf (z : Conditions (collapsed d)) : structureMap d (label d (f z)) = label _ z :=
    Classical.choose_spec (ZFSet.mem_range.mp (label_mem _ z))
  exact Function.Injective.countable (f := f) (fun x y h =>
    label_injective _ ((hf x).symm.trans ((congrArg (fun z => structureMap d (label d z)) h).trans
      (hf y))))

theorem collapse_injective (d : ZFSet.{u}) (he : StructureExtensional d)
    (x : ZFSet.{u}) (hx : x ∈ d) (y : ZFSet.{u}) (hy : y ∈ d)
    (h : structureMap d x = structureMap d y) : x = y :=
  value_injective (membershipRelation_wellFounded d) (membershipRelation_extensional he) x hx y hy h

theorem collapse_membership (d : ZFSet.{u}) (he : StructureExtensional d)
    (x : ZFSet.{u}) (hx : x ∈ d) (y : ZFSet.{u}) (hy : y ∈ d) :
    structureMap d x ∈ structureMap d y ↔ x ∈ y := by
  rw [structureMap,value_mem_iff (membershipRelation_wellFounded d)
    (membershipRelation_extensional he) hx,membershipRelation_pair]
  simp only [hx,hy,true_and]

theorem collapse_fixed (d x : ZFSet.{u}) (hx : x ∈ d)
    (h : ∀ y ∈ x, y ∈ d ∧ structureMap d y = y) : structureMap d x = x := by
  apply ZFSet.ext; intro y
  rw [structureMap,mem_value]
  constructor
  · rintro ⟨z,_,hz,hy⟩
    have hzx := ((membershipRelation_pair d z x).mp hz).2.2
    change y = structureMap d z at hy
    rw [(h z hzx).2] at hy
    exact hy ▸ hzx
  · intro hy
    refine ⟨y,(h y hy).1,(membershipRelation_pair d y x).mpr ⟨(h y hy).1,hx,hy⟩,?_⟩
    exact (h y hy).2.symm

end TuringRigidity.ElementaryModel

end OAI
