/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelActionDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelIdealDecoding

/-!
# Set Model Action Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section

theorem decode_action {M : ZFSet.{u}} (C : Context M) {L f : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hIM : idealSet I ∈ M) (ha : IsAction f (idealSet I) L) :
    ∃ ρ : I ≃o I, automorphismSet ρ = f := by
  have hi (a : I) : degreeSet.{u} a.val ∈ idealSet I :=
    (mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩
  have hm (a : I) : degreeSet.{u} a.val ∈ M := C.transitive _ hIM _ (hi a)
  have hex (a : I) : ∃ b : I, ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ f := by
    obtain ⟨y,hy,hxy,_⟩ := ha.1.1.2 _ (hi a)
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I y).mp hy
    exact ⟨⟨b,hb⟩,hxy⟩
  choose F hF using hex
  have hle (a b : I) : F a ≤ F b ↔ a ≤ b := by
    have hh := ha.2 _ (hi a) _ (hi b) _ (hi (F a)) _ (hi (F b)) ⟨hF a,hF b⟩
    rw [order_code C hL (hm a) (hm b),order_code C hL (hm (F a)) (hm (F b))] at hh
    exact hh.symm
  have hinj : Function.Injective F := by
    intro a b he
    exact le_antisymm ((hle a b).mp (le_of_eq he)) ((hle b a).mp (le_of_eq he.symm))
  have hsurj : Function.Surjective F := by
    intro b
    obtain ⟨x,hx,hxb⟩ := ha.1.2 _ (hi b)
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I x).mp hx
    refine ⟨⟨a,hac⟩,Subtype.ext (degreeSet_injective ?_)⟩
    exact ha.1.1.unique (hi ⟨a,hac⟩) (hi (F ⟨a,hac⟩)) (hi b) (hF ⟨a,hac⟩) hxb
  let ρ : I ≃o I :=
    { toEquiv := Equiv.ofBijective F ⟨hinj, hsurj⟩
      map_rel_iff' := by
        intro a b
        exact hle a b }
  have hpair (a b : I) : ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ f ↔ ρ a = b := by
    constructor
    · intro hab
      apply Subtype.ext
      apply degreeSet_injective
      exact ha.1.1.unique (hi a) (hi (F a)) (hi b) (hF a) hab
    · intro he
      have he' : F a = b := he
      simpa only [he'] using hF a
  refine ⟨ρ,ZFSet.ext (fun z => ?_)⟩
  constructor
  · intro hz
    obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
    exact (hpair a (ρ a)).mpr rfl
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ha.1.1.1 z hz
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨b,hbc,rfl⟩ := (mem_idealSet I y).mp hy
    exact (action_code ρ ⟨a,hac⟩ ⟨b,hbc⟩).mpr ((hpair ⟨a,hac⟩ ⟨b,hbc⟩).mp hz)

theorem ideal_subset_iff {I J : CountableIdeal} :
    idealSet.{u} I ⊆ idealSet J ↔ I.carrier ⊆ J.carrier := by
  constructor
  · intro h a ha
    obtain ⟨b,hb,he⟩ := (mem_idealSet J _).mp (h ((mem_idealSet I _).mpr ⟨a,ha,rfl⟩))
    exact (degreeSet_injective he).symm ▸ hb
  · exact ideal_subset

theorem extends_sets_iff {I J : CountableIdeal} (hIJ : I.carrier ⊆ J.carrier)
    (ρ : I ≃o I) (σ : J ≃o J) :
    automorphismSet.{u} ρ ⊆ automorphismSet σ ↔ Extends hIJ ρ σ := by
  constructor
  · intro h a
    have hh := h ((mem_automorphismSet ρ _).mpr ⟨a,rfl⟩)
    have he := (action_code σ ⟨a.val,hIJ a.property⟩ ⟨(ρ a).val,hIJ (ρ a).property⟩).mp hh
    exact congrArg Subtype.val he
  · exact extends_sets

end
end TuringRigidity.SetModelSatisfaction

end OAI
