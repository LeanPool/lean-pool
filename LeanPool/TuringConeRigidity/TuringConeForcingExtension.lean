/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeForcingExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeConstructibleExtension
public import LeanPool.TuringConeRigidity.Representation.CommonGenericModels

/-!
# Cone maps in forcing extensions

For a countable transitive SourceT model and an arbitrary coded set forcing,
a persistent partial cone map on old degrees extends persistently to all
degrees of the generic extension. The full graph belongs to relative L(R) of
the extension, hence to the extension, and has a ground-model forcing name.

The name supplied here may depend on the generic filter. This is not yet a
uniform name, a uniform program on generic inputs, or unconditional cone
rigidity. No cone extension is assumed as a field or an axiom.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeForcingExtension

open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open RecursiveNames CountableForcing AtomicForcing RelativeConstructible
open PersistentRestrictions ConePersistence ConeSetGraphs OracleJump

universe u

/-- A persistent partial cone map extends to all degrees of the forcing
extension; its graph is constructible over the extension reals and named
in the ground model. -/
theorem persistent_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    (I : CountableIdeal) {a : Degree} (ρ : I ≃o Cone I a)
    (hρ : ConePersistence.Persistent I ρ) (hza : degreeJump a ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : I.carrier ⊆ J.carrier, ∃ σ : J ≃o Cone J a,
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Persistent J σ ∧
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
  obtain ⟨σ, he, hσ, hσL⟩ := ConeConstructibleExtension.persistent_extension_in_relativeModel
    E hE hTE I ρ hρ hza hIJ
  have hσE : coneGraph σ ∈ E := relativeModel_subset E _ hσL
  obtain ⟨t, ht, hval⟩ := (mem_extensionSet M c G.carrier _).mp hσE
  exact ⟨hIJ, σ, he, hσ, hσL, t, ht, hval⟩

/-- Specialize to a persistent cone map on the entire ground-model ideal.
Jump membership is automatic for this domain. -/
theorem ground_cone_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    {a : Degree} (ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a)
    (hρ : ConePersistence.Persistent (modelIdeal M hM hT) ρ) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : (modelIdeal M hM hT).carrier ⊆ J.carrier, ∃ σ : J ≃o Cone J a,
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Persistent J σ ∧
      coneGraph σ ∈ relativeModel E (groundReals E) ∧
      ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ :=
  persistent_extension_name M hM hT hc hoM ho G hG htop (modelIdeal M hM hT) ρ hρ
    (modelIdeal_jump M hM hT a (ConePresentation.base_mem ρ)) (fun _ hx => hx)

/-- A restriction of an arbitrary global cone isomorphism satisfies the
persistence hypothesis without a definability or regularity assumption. -/
theorem global_restriction_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    {a : Degree} (e : Degree ≃o Set.Ici a)
    (ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a)
    (he : ConePersistence.RestrictsTo e (modelIdeal M hM hT) ρ) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : (modelIdeal M hM hT).carrier ⊆ J.carrier, ∃ σ : J ≃o Cone J a,
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Persistent J σ ∧
      coneGraph σ ∈ relativeModel E (groundReals E) ∧
      ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ :=
  ground_cone_extension_name M hM hT hc hoM ho G hG htop ρ
    (ConePersistence.persistent_of_global_restriction e (modelIdeal M hM hT) ρ he)

/-- Representatives of forward values have ground-model names. -/
theorem model_cone_output_name (M c : ZFSet.{u}) [Countable (Conditions M)]
    (G : Set (Conditions c))
    (hE : Transitive (genericExtensionSet M c G)) (hTE : SourceT (genericExtensionSet M c G))
    {a : Degree} (σ : modelIdeal (genericExtensionSet M c G) hE hTE ≃o
      Cone (modelIdeal (genericExtensionSet M c G) hE hTE) a)
    (A : Oracle) (hA : A ∈ modelReals (genericExtensionSet M c G)) :
    ∃ B : Oracle, ∃ t : Name (Conditions c),
      t.encode (label c) ∈ M ∧ t.val G = realCode B ∧
      degree B = (σ ⟨degree A, ⟨A, hA, rfl⟩⟩).val := by
  obtain ⟨B, hB, hdegree⟩ := (σ ⟨degree A, ⟨A, hA, rfl⟩⟩).property.1
  obtain ⟨t, ht, hval⟩ := (mem_extensionSet M c G (realCode B)).mp hB
  exact ⟨B, t, ht, hval, hdegree⟩

/-- Representatives of inverse values above the base also have names. -/
theorem model_cone_inverse_output_name (M c : ZFSet.{u}) [Countable (Conditions M)]
    (G : Set (Conditions c))
    (hE : Transitive (genericExtensionSet M c G)) (hTE : SourceT (genericExtensionSet M c G))
    {a : Degree} (σ : modelIdeal (genericExtensionSet M c G) hE hTE ≃o
      Cone (modelIdeal (genericExtensionSet M c G) hE hTE) a)
    (A : Oracle) (hA : A ∈ modelReals (genericExtensionSet M c G)) (ha : a ≤ degree A) :
    ∃ B : Oracle, ∃ t : Name (Conditions c),
      t.encode (label c) ∈ M ∧ t.val G = realCode B ∧
      degree B = (σ.symm ⟨degree A, ⟨A, hA, rfl⟩, ha⟩).val := by
  obtain ⟨B, hB, hdegree⟩ := (σ.symm ⟨degree A, ⟨A, hA, rfl⟩, ha⟩).property
  obtain ⟨t, ht, hval⟩ := (mem_extensionSet M c G (realCode B)).mp hB
  exact ⟨B, t, ht, hval, hdegree⟩

end OAI.TuringRigidity.ConeForcingExtension
