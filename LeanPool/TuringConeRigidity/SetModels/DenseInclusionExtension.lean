/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/DenseInclusionExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalDenseInclusion
public import LeanPool.TuringConeRigidity.SetModels.RegularTreeExtension

/-!
# Dense Inclusion Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.DenseInclusionExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalDenseInclusion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- The conditions in `b` weaker than some condition in `g`, using reverse inclusion as the
forcing order. -/
noncomputable def upperSet (b g : ZFSet.{0}) : ZFSet.{0} :=
  b.sep (fun q => ∃ p ∈ g, q ⊆ p)

/-- Restrict the set of conditions `k` to members of `a`. -/
noncomputable def restrictSet (a k : ZFSet.{0}) : ZFSet.{0} := a.sep (fun p => p ∈ k)

theorem upperSet_mem (N b g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hb : b ∈ N) (hg : g ∈ N) : upperSet b g ∈ N := by
  let e := fun _ : ℕ => g
  simpa only [upperSet,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.subset 1 0)) e (fun _ => hg) hb

theorem restrictSet_mem (N a k : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (ha : a ∈ N) (hk : k ∈ N) : restrictSet a k ∈ N := by
  let e := fun _ : ℕ => k
  simpa only [restrictSet,Formula.Eval,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded (.member 0 1) e (fun _ => hk) ha

theorem pushFilterSet_eq (a b : ZFSet.{0}) (hab : a ⊆ b) (G : GenericFilter (Conditions a)) :
    genericFilterSet b (push a b hab G).carrier = upperSet b (genericFilterSet a G.carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨q,⟨p,hp,hpq⟩,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    refine ZFSet.mem_sep.mpr ⟨label_mem b q,label a p,
      (mem_genericFilterSet _ _ _).mpr ⟨p,hp,rfl⟩,?_⟩
    change label b q ⊆ label b (embed a b hab p) at hpq
    rwa [label_embed] at hpq
  · intro hx
    obtain ⟨hxb,p,hpg,hxp⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨q,rfl⟩ := label_surjective b hxb
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ p).mp hpg
    exact (mem_genericFilterSet _ _ _).mpr ⟨q,⟨p,hp,by
      change label b q ⊆ label b (embed a b hab p); rwa [label_embed]⟩,rfl⟩

theorem originalFilterSet_eq (a b : ZFSet.{0}) (hab : a ⊆ b) (G : GenericFilter (Conditions a)) :
    genericFilterSet a G.carrier = restrictSet a (genericFilterSet b (push a b hab G).carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,(mem_genericFilterSet _ _ _).mpr
      ⟨embed a b hab p,(embed_mem_push a b hab G p).mpr hp,label_embed a b hab p⟩⟩
  · intro hx
    obtain ⟨hxa,hxk⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨p,rfl⟩ := label_surjective a hxa
    obtain ⟨q,hq,hqe⟩ := (mem_genericFilterSet _ _ _).mp hxk
    have he : q = embed a b hab p := label_injective b (hqe.trans (label_embed a b hab p).symm)
    exact (mem_genericFilterSet _ _ _).mpr ⟨p,(embed_mem_push a b hab G p).mp (he ▸ hq),rfl⟩

theorem extension_eq (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hab : a ⊆ b)
    (hd : ∀ q ∈ b, ∃ p ∈ a, q ⊆ p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M b (push a b hab G).carrier = genericExtensionSet M a G.carrier := by
  let K := push a b hab G
  have hK := push_ground_generic M a b hM hT ha hb hab hd G hG
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hMV,hkV⟩ := RegularTreeExtension.extension_properties M b hM hT hb K hK
  have hkN : genericFilterSet b K.carrier ∈ genericExtensionSet M a G.carrier := by
    rw [pushFilterSet_eq]
    exact upperSet_mem _ b _ hN hTN (hMN hb) hgN
  have hgV : genericFilterSet a G.carrier ∈ genericExtensionSet M b K.carrier := by
    rw [originalFilterSet_eq a b hab G]
    exact restrictSet_mem _ a _ hV hTV (hMV ha) hkV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN K.carrier hkN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.DenseInclusionExtension

end OAI
