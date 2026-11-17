/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeForcingDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeExtensionBounds
public import LeanPool.TuringConeRigidity.Constructibility.OneRealConstructionDefinition

/-!
# One-real definitions of the cone graphs obtained by forcing

The finite-construction theorem gives a definition from one real and an
ordinal level of L(R). This is a definability statement inside the model, not
a claim that the parameter is a ground-model real or that the associated map
on arbitrary reals is already Borel.

The final theorem starts from the model's own real-coded extension property;
ambient persistence is derived using the previously proved absoluteness
result, rather than imposed as an extra hypothesis.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeForcingDefinition

open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
open PersistentRestrictions ConePersistence ConeSetGraphs OrdinalCoding
open RecursiveNames CountableForcing AtomicForcing

universe u

/-- The persistent cone graph is defined over a level of L(R) using one real. -/
theorem persistent_graph_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {a : Degree} (ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a)
    (hρ : ConePersistence.Persistent (modelIdeal M hM hT) ρ) :
    ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
      δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ p.bound ≤ 2 ∧
      realCode P ∈ level (groundReals M) δ ∧
      coneGraph ρ = definedSubset (level (groundReals M) δ) p
        (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨t, P, hP, hi, ht, hval⟩ :=
    ConeConstructibleExtension.persistent_graph_construction M hM hT ρ hρ
  obtain ⟨p, hbound, hdef⟩ := t.cofinal_one_real_definition
  obtain ⟨β, _, _, _, hidx, hreal, hset⟩ :=
    hdef M hM hT P hP ht hi 0 (internal_ordinal_zero M hM hT)
  exact ⟨heightDomainIndex (paddedCode t.ordinalVector β), P, p,
    hidx, hP, hbound, hreal, hval ▸ hset⟩

theorem persistent_extension_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) {a : Degree} (ρ : I ≃o Cone I a)
    (hρ : ConePersistence.Persistent I ρ) (hza : OracleJump.degreeJump a ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a,
      ConePersistence.Extends hIM ρ σ ∧
      ConePersistence.Persistent (modelIdeal M hM hT) σ ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals M) δ ∧
        coneGraph σ = definedSubset (level (groundReals M) δ) p
          (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨σ, he, hσ, _⟩ :=
    ConeConstructibleExtension.persistent_extension_in_model M hM hT I ρ hρ hza hIM
  exact ⟨σ, he, hσ, persistent_graph_one_real_definition M hM hT σ hσ⟩

/-- Combine forcing extension, a ground-model name, and a one-real definition
of the same extended graph. The real parameter is allowed to be in E. -/
theorem forcing_extension_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    (I : CountableIdeal) {a : Degree} (ρ : I ≃o Cone I a)
    (hρ : ConePersistence.Persistent I ρ) (hza : OracleJump.degreeJump a ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : I.carrier ⊆ J.carrier, ∃ σ : J ≃o Cone J a,
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Persistent J σ ∧
      (∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ) ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ E ∧ P ∈ modelReals E ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals E) δ ∧
        coneGraph σ = definedSubset (level (groundReals E) δ) p
          (fun _ : Fin p.bound => realCode P) := by
  intro E hE hTE J
  obtain ⟨hIJ, σ, he, hσ, _, hname⟩ :=
    ConeForcingExtension.persistent_extension_name M hM hT hc hoM ho G hG htop I ρ hρ hza hIM
  exact ⟨hIJ, σ, he, hσ, hname, persistent_graph_one_real_definition E hE hTE σ hσ⟩

/-- Start with internal real-coded persistence. Absoluteness supplies ambient
persistence, and the forcing construction then yields a named graph on all
extension degrees. -/
theorem coded_forcing_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    {I : CountableIdeal} {A R : Oracle} (hA : ConePresentation.Presented I A)
    (hAM : A ∈ SetModelReals.reals M) (hRM : R ∈ SetModelReals.reals M) (k : ℕ)
    (ρ : I ≃o Cone I (degree (EncodedForcing.columns A k)))
    (hza : OracleJump.degreeJump (degree (EncodedForcing.columns A k)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ ConePresentation.Graph ρ hA v)
    (hp : ConeInternalPersistence.HasExtensions (SetModelReals.reals M) A R k) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : I.carrier ⊆ J.carrier, ∃ σ : J ≃o Cone J (degree (EncodedForcing.columns A k)),
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Persistent J σ ∧
      coneGraph σ ∈ relativeModel E (groundReals E) ∧
      ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ := by
  have hρ := (ConeInternalPersistence.internal_extensions_iff_persistent
    M hM hT hA hAM hRM k ρ hza hR).mp hp
  have hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier := by
    intro d hd
    obtain ⟨n, hn⟩ := (hA d).mp hd
    exact ⟨EncodedForcing.columns A n,
      sourceT_real_lower M hM hT hAM (CodingExtraction.column_projection_reduces A n), hn⟩
  exact ConeForcingExtension.persistent_extension_name M hM hT hc hoM ho G hG htop
    I ρ hρ hza hIM

end OAI.TuringRigidity.ConeForcingDefinition
