/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeForcingExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeConstructibleExtension
public import LeanPool.TuringConeRigidity.Representation.CommonGenericModels

/-!
# Two-cone graphs in forcing extensions

A persistent partial map extends to both cones of the degree ideal of a coded
set-forcing extension. The whole graph lies in the extension's relative L(R)
and has a name encoded in the ground model. The name may depend on the generic
filter; this theorem does not supply a uniform generic oracle program.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeForcingExtension

open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open RecursiveNames CountableForcing AtomicForcing RelativeConstructible
open PersistentRestrictions TwoConeSetGraphs OracleJump
open ConePersistence (Cone)

universe u

/-- Extend persistently to both cones of all extension degrees. The graph's
internality and its ground-model name are conclusions, not hypotheses. -/
theorem persistent_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    (I : CountableIdeal) {a b : Degree} (ρ : Cone I a ≃o Cone I b)
    (hρ : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : I.carrier ⊆ J.carrier, ∃ σ : Cone J a ≃o Cone J b,
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Persistent J σ ∧
      coneGraph σ ∈ relativeModel E (groundReals E) ∧
      ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ := by
  intro E hE hTE J
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier htop
  have hIJ : I.carrier ⊆ J.carrier := by
    intro d hd
    obtain ⟨A, hA, rfl⟩ := hIM hd
    refine ⟨A, ?_, rfl⟩
    change realCode A ∈ E
    exact hME hA
  obtain ⟨σ, he, hσ, hσL⟩ := TwoConeConstructibleExtension.persistent_extension_in_relativeModel
    E hE hTE I ρ hρ hza hzb hIJ
  have hσE : coneGraph σ ∈ E := relativeModel_subset E _ hσL
  obtain ⟨t, ht, hval⟩ := (mem_extensionSet M c G.carrier _).mp hσE
  exact ⟨hIJ, σ, he, hσ, hσL, t, ht, hval⟩

/-- Specialize to cones in the full ground-model degree ideal. -/
theorem ground_cone_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    {a b : Degree}
    (ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b)
    (hρ : TwoConePersistence.Persistent (modelIdeal M hM hT) ρ)
    (ha : a ∈ (modelIdeal M hM hT).carrier) (hb : b ∈ (modelIdeal M hM hT).carrier) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : (modelIdeal M hM hT).carrier ⊆ J.carrier, ∃ σ : Cone J a ≃o Cone J b,
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Persistent J σ ∧
      coneGraph σ ∈ relativeModel E (groundReals E) ∧
      ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ :=
  persistent_extension_name M hM hT hc hoM ho G hG htop (modelIdeal M hM hT) ρ hρ
    (modelIdeal_jump M hM hT a ha) (modelIdeal_jump M hM hT b hb) (fun _ hx => hx)

/-- Global restrictions need no separate regularity or definability assumption. -/
theorem global_restriction_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b)
    (he : TwoConePersistence.RestrictsTo e (modelIdeal M hM hT) ρ)
    (ha : a ∈ (modelIdeal M hM hT).carrier) (hb : b ∈ (modelIdeal M hM hT).carrier) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : (modelIdeal M hM hT).carrier ⊆ J.carrier, ∃ σ : Cone J a ≃o Cone J b,
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Persistent J σ ∧
      coneGraph σ ∈ relativeModel E (groundReals E) ∧
      ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ :=
  ground_cone_extension_name M hM hT hc hoM ho G hG htop ρ
    (TwoConePersistence.persistent_of_global_restriction e (modelIdeal M hM hT) ρ he) ha hb

/-- A representative of a forward value has a ground-model name. -/
theorem model_cone_output_name (M c : ZFSet.{u}) [Countable (Conditions M)]
    (G : Set (Conditions c))
    (hE : Transitive (genericExtensionSet M c G)) (hTE : SourceT (genericExtensionSet M c G))
    {a b : Degree} (σ : Cone (modelIdeal (genericExtensionSet M c G) hE hTE) a ≃o
      Cone (modelIdeal (genericExtensionSet M c G) hE hTE) b)
    (A : Oracle) (hA : A ∈ modelReals (genericExtensionSet M c G)) (ha : a ≤ degree A) :
    ∃ B : Oracle, ∃ t : Name (Conditions c),
      t.encode (label c) ∈ M ∧ t.val G = realCode B ∧
      degree B = (σ ⟨degree A, ⟨A, hA, rfl⟩, ha⟩).val := by
  obtain ⟨B, hB, hdegree⟩ := (σ ⟨degree A, ⟨A, hA, rfl⟩, ha⟩).property.1
  obtain ⟨t, ht, hval⟩ := (mem_extensionSet M c G (realCode B)).mp hB
  exact ⟨B, t, ht, hval, hdegree⟩

/-- A representative of an inverse value has a name, with the target test. -/
theorem model_cone_inverse_output_name (M c : ZFSet.{u}) [Countable (Conditions M)]
    (G : Set (Conditions c))
    (hE : Transitive (genericExtensionSet M c G)) (hTE : SourceT (genericExtensionSet M c G))
    {a b : Degree} (σ : Cone (modelIdeal (genericExtensionSet M c G) hE hTE) a ≃o
      Cone (modelIdeal (genericExtensionSet M c G) hE hTE) b)
    (A : Oracle) (hA : A ∈ modelReals (genericExtensionSet M c G)) (hb : b ≤ degree A) :
    ∃ B : Oracle, ∃ t : Name (Conditions c),
      t.encode (label c) ∈ M ∧ t.val G = realCode B ∧
      degree B = (σ.symm ⟨degree A, ⟨A, hA, rfl⟩, hb⟩).val :=
  model_cone_output_name M c G hE hTE σ.symm A hA hb

end OAI.TuringRigidity.TwoConeForcingExtension
