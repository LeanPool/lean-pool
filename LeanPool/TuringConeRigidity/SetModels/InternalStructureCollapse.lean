/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalStructureCollapse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.MostowskiCollapse
public import LeanPool.TuringConeRigidity.Syntax.FormulaIsomorphism

/-!
# Internal Structure Collapse
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

noncomputable def membershipRelation (d : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ d, ∃ y ∈ d, z = ZFSet.pair x y ∧ x ∈ y) (ZFSet.prod d d)

theorem membershipRelation_pair (d x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ membershipRelation d ↔ x ∈ d ∧ y ∈ d ∧ x ∈ y := by
  rw [membershipRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,a,ha,b,hb,he,hab⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨ha,hb,hab⟩
  · rintro ⟨hx,hy,hxy⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,hxy⟩

theorem membershipRelation_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d : ZFSet.{u}} (hd : d ∈ M) : membershipRelation d ∈ M := by
  simpa only [membershipRelation,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.member 1 0))))
      (fun _ => d) (fun _ => hd) (product_mem M hM hP hU hPow hS hd hd)

theorem membershipRelation_wellFounded (d : ZFSet.{u}) :
    WellFounded (Rel d (membershipRelation d)) := by
  apply ZFSet.mem_wf.mono
  intro x y h
  exact ((membershipRelation_pair d x y).mp h.2).2.2

def StructureExtensional (d : ZFSet.{u}) : Prop :=
  ∀ x ∈ d, ∀ y ∈ d, (∀ z ∈ d, z ∈ x ↔ z ∈ y) → x = y

theorem membershipRelation_extensional {d : ZFSet.{u}} (he : StructureExtensional d) :
    Extensional d (membershipRelation d) := by
  intro x hx y hy hxy
  apply he x hx y hy
  intro z hz
  simpa only [membershipRelation_pair,and_iff_right hz,and_iff_right hx,and_iff_right hy] using
    hxy z hz

noncomputable def structureMap (d : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  value d (membershipRelation d) (membershipRelation_wellFounded d)

theorem structureMap_fixed {d t : ZFSet.{u}} (ht : Transitive t) (htd : t ⊆ d)
    (x : ZFSet.{u}) (hx : x ∈ t) : structureMap d x = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [structureMap,mem_value]
    constructor
    · rintro ⟨y,_,hyx,hz⟩
      have hyx' := ((membershipRelation_pair d y x).mp hyx).2.2
      have hyv := ih y hyx' (ht x hx y hyx')
      change structureMap d y = y at hyv
      change z = structureMap d y at hz
      rw [hyv] at hz
      exact hz ▸ hyx'
    · intro hz
      have hzt := ht x hx z hz
      refine ⟨z,htd hzt,(membershipRelation_pair d z x).mpr ⟨htd hzt,htd hx,hz⟩,?_⟩
      exact (ih z hz hzt).symm

theorem internal_structure_collapse (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (he : StructureExtensional d) :
    ∃ b ∈ M, ∃ f ∈ M, Presents d f (structureMap d) ∧ Transitive b ∧
      (∀ y, y ∈ b ↔ ∃ x ∈ d, y = structureMap d x) ∧
      (∀ φ : SigmaFormula, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ d) →
        (φ.Realize d e ↔ φ.Realize b (fun i => structureMap d (e i)))) := by
  obtain ⟨b,hb,f,hf,hfg,hbt,hbdef,hi,hm⟩ := internal_mostowski M d (membershipRelation d)
    hM hP hU hPow hS hR hd (membershipRelation_mem M hM hP hU hPow hS hd)
    (membershipRelation_wellFounded d) (membershipRelation_extensional he)
  refine ⟨b,hb,f,hf,hfg,hbt,hbdef,?_⟩
  intro φ e henv
  apply φ.realize_isomorphism d b (structureMap d)
  · intro x hx
    exact (hbdef _).mpr ⟨x,hx,rfl⟩
  · intro y hy
    obtain ⟨x,hx,hyx⟩ := (hbdef y).mp hy
    exact ⟨x,hx,hyx.symm⟩
  · exact hi
  · intro x hx y hy
    exact (hm x hx y hy).trans
      ((membershipRelation_pair d x y).trans (and_iff_right hx |>.trans (and_iff_right hy)))
  · exact henv

end TuringRigidity.RelationCollapse

end OAI
