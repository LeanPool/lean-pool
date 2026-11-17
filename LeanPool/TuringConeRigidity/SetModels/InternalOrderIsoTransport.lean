/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalOrderIsoTransport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.DenseInclusionExtension

/-!
# Internal Order Iso Transport
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalOrderIsoTransport
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- The image of the set `g` under the set-coded relation `f`, restricted to `b`. -/
noncomputable def imageSet (b f g : ZFSet.{0}) : ZFSet.{0} :=
  b.sep (fun y => ∃ x ∈ g, ZFSet.pair x y ∈ f)

/-- The preimage of the set `k` under the set-coded relation `f`, restricted to `a`. -/
noncomputable def preimageSet (a f k : ZFSet.{0}) : ZFSet.{0} :=
  a.sep (fun x => ∃ y ∈ k, ZFSet.pair x y ∈ f)

theorem imageSet_mem (M b f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hb : b ∈ M) (hf : f ∈ M) (hg : g ∈ M) : imageSet b f g ∈ M := by
  let e := cons g (fun _ => f)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hg
    · exact hf
  simpa only [imageSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 1 3)) e he hb

theorem preimageSet_mem (M a f k : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hf : f ∈ M) (hk : k ∈ M) : preimageSet a f k ∈ M := by
  let e := cons k (fun _ => f)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hk
    · exact hf
  simpa only [preimageSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 1 0 3)) e he ha

theorem map_ground_generic (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (AutomorphismName.mapFilter e G) := by
  intro D hD hd
  let E := DenseInclusionExtension.restrictSet b D
  have hE := DenseInclusionExtension.restrictSet_mem M b D hM hT hb hD
  have hden : Dense {p : Conditions a | label a p ∈ preimageSet a f E} := by
    intro p
    obtain ⟨q,hqp,hqD⟩ := hd (e p)
    refine ⟨e.symm q,by simpa using e.symm.monotone hqp,?_⟩
    exact ZFSet.mem_sep.mpr ⟨label_mem a _,label b q,ZFSet.mem_sep.mpr ⟨label_mem b q,hqD⟩,(he _
      _).mpr (e.apply_symm_apply q).symm⟩
  obtain ⟨p,hp,hpD⟩ := hG (preimageSet a f E) (preimageSet_mem M a f E hM hT ha hf hE) hden
  obtain ⟨_,y,hyD,hpy⟩ := ZFSet.mem_sep.mp hpD
  obtain ⟨hyb,hyD⟩ := ZFSet.mem_sep.mp hyD
  obtain ⟨q,rfl⟩ := label_surjective b hyb
  obtain rfl := (he p q).mp hpy
  exact ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,hyD⟩

theorem mapFilterSet_eq (a b f : ZFSet.{0}) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) :
    genericFilterSet b (AutomorphismName.mapFilter e G).carrier =
      imageSet b f (genericFilterSet a G.carrier) := by
  apply ZFSet.ext; intro y
  constructor
  · intro hy
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet _ _ y).mp hy
    exact ZFSet.mem_sep.mpr ⟨label_mem b q,label a (e.symm q),
      (mem_genericFilterSet _ _ _).mpr ⟨e.symm q,hq,rfl⟩,(he _ _).mpr (e.apply_symm_apply q).symm⟩
  · intro hy
    obtain ⟨hyb,x,hx,hxy⟩ := ZFSet.mem_sep.mp hy
    obtain ⟨q,rfl⟩ := label_surjective b hyb
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    obtain rfl := (he p q).mp hxy
    exact (mem_genericFilterSet _ _ _).mpr ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,rfl⟩

theorem originalFilterSet_eq (a b f : ZFSet.{0}) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) :
    genericFilterSet a G.carrier =
      preimageSet a f (genericFilterSet b (AutomorphismName.mapFilter e G).carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,label b (e p),
      (mem_genericFilterSet _ _ _).mpr ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,rfl⟩,
      (he p (e p)).mpr rfl⟩
  · intro hx
    obtain ⟨hxa,y,hy,hxy⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨p,rfl⟩ := label_surjective a hxa
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet _ _ y).mp hy
    obtain rfl := (he p q).mp hxy
    exact (mem_genericFilterSet _ _ _).mpr ⟨p,by simpa [AutomorphismName.mapFilter] using hq,rfl⟩

theorem extension_eq (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M b (AutomorphismName.mapFilter e G).carrier = genericExtensionSet M a
      G.carrier := by
  let K := AutomorphismName.mapFilter e G
  have hK := map_ground_generic M a b f hM hT ha hb hf e he G hG
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hMV,hkV⟩ := RegularTreeExtension.extension_properties M b hM hT hb K hK
  have hkN : genericFilterSet b K.carrier ∈ genericExtensionSet M a G.carrier := by
    rw [mapFilterSet_eq a b f e he G]
    exact imageSet_mem _ b f _ hN hTN (hMN hb) (hMN hf) hgN
  have hgV : genericFilterSet a G.carrier ∈ genericExtensionSet M b K.carrier := by
    rw [originalFilterSet_eq a b f e he G]
    exact preimageSet_mem _ a f _ hV hTV (hMV ha) (hMV hf) hkV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN K.carrier hkN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.InternalOrderIsoTransport

end OAI
