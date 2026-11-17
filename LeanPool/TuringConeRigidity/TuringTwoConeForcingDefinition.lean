/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeForcingDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeForcingExtension
public import LeanPool.TuringConeRigidity.Constructibility.OneRealConstructionDefinition

/-!
# One-real definitions of the native two-cone graphs

The full graph is defined over an ordinal level of relative L(R) from one
real. The real may belong to the extension, not the ground model. This is not
a Borel lift or a uniform oracle program. The coded entry point derives
ambient persistence from the already proved internal-witness absoluteness.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeForcingDefinition

open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
open PersistentRestrictions TwoConeSetGraphs OrdinalCoding OracleJump
open RecursiveNames CountableForcing AtomicForcing
open ConePersistence (Cone)

universe u

/-- A persistent two-cone graph has a definition from one real and a level. -/
theorem persistent_graph_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {a b : Degree}
    (ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b)
    (hρ : TwoConePersistence.Persistent (modelIdeal M hM hT) ρ)
    (ha : a ∈ (modelIdeal M hM hT).carrier) (hb : b ∈ (modelIdeal M hM hT).carrier) :
    ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
      δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ p.bound ≤ 2 ∧
      realCode P ∈ level (groundReals M) δ ∧
      coneGraph ρ = definedSubset (level (groundReals M) δ) p
        (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨t, P, hP, hi, ht, hval⟩ :=
    TwoConeConstructibleExtension.persistent_graph_construction M hM hT ρ hρ ha hb
  obtain ⟨p, hbound, hdef⟩ := t.cofinal_one_real_definition
  obtain ⟨β, _, _, _, hidx, hreal, hset⟩ :=
    hdef M hM hT P hP ht hi 0 (internal_ordinal_zero M hM hT)
  exact ⟨heightDomainIndex (paddedCode t.ordinalVector β), P, p,
    hidx, hP, hbound, hreal, hval ▸ hset⟩

theorem persistent_extension_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) {a b : Degree} (ρ : Cone I a ≃o Cone I b)
    (hρ : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b,
      TwoConePersistence.Extends hIM ρ σ ∧
      TwoConePersistence.Persistent (modelIdeal M hM hT) σ ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals M) δ ∧
        coneGraph σ = definedSubset (level (groundReals M) δ) p
          (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨σ, he, hσ, _⟩ :=
    TwoConeConstructibleExtension.persistent_extension_in_model M hM hT I ρ hρ hza hzb hIM
  exact ⟨σ, he, hσ, persistent_graph_one_real_definition M hM hT σ hσ
    (hIM (I.lower (degree_le_jump a) hza)) (hIM (I.lower (degree_le_jump b) hzb))⟩

/-- The ground-model name and the one-real definition describe the SAME graph. -/
theorem forcing_extension_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
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
      (∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ) ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ E ∧ P ∈ modelReals E ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals E) δ ∧
        coneGraph σ = definedSubset (level (groundReals E) δ) p
          (fun _ : Fin p.bound => realCode P) := by
  intro E hE hTE J
  obtain ⟨hIJ, σ, he, hσ, _, hname⟩ :=
    TwoConeForcingExtension.persistent_extension_name M hM hT hc hoM ho G hG htop
      I ρ hρ hza hzb hIM
  exact ⟨hIJ, σ, he, hσ, hname, persistent_graph_one_real_definition E hE hTE σ hσ
    (hIJ (I.lower (degree_le_jump a) hza)) (hIJ (I.lower (degree_le_jump b) hzb))⟩

/-- Internal real-coded persistence supplies the ambient persistence hypothesis. -/
theorem coded_forcing_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    {I : CountableIdeal} {A R : Oracle} (hA : ConePresentation.Presented I A)
    (hAM : A ∈ SetModelReals.reals M) (hRM : R ∈ SetModelReals.reals M) (k : ℕ)
    (ρ : Cone I (degree (EncodedForcing.columns A (Nat.unpair k).1)) ≃o
      Cone I (degree (EncodedForcing.columns A (Nat.unpair k).2)))
    (hza : degreeJump (degree (EncodedForcing.columns A (Nat.unpair k).1)) ∈ I.carrier)
    (hzb : degreeJump (degree (EncodedForcing.columns A (Nat.unpair k).2)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ TwoConePresentation.RawGraph ρ A v)
    (hp : TwoConeInternalPersistence.HasExtensions (SetModelReals.reals M) A R k) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : I.carrier ⊆ J.carrier,
      ∃ σ : Cone J (degree (EncodedForcing.columns A (Nat.unpair k).1)) ≃o
          Cone J (degree (EncodedForcing.columns A (Nat.unpair k).2)),
        TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Persistent J σ ∧
        coneGraph σ ∈ relativeModel E (groundReals E) ∧
        ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = coneGraph σ := by
  have hρ := (TwoConeInternalPersistence.internal_extensions_iff_persistent
    M hM hT hA hAM hRM k ρ hza hzb hR).mp hp
  have hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier := by
    intro d hd
    obtain ⟨n, hn⟩ := (hA d).mp hd
    exact ⟨EncodedForcing.columns A n,
      sourceT_real_lower M hM hT hAM (CodingExtraction.column_projection_reduces A n), hn⟩
  exact TwoConeForcingExtension.persistent_extension_name M hM hT hc hoM ho G hG htop
    I ρ hρ hza hzb hIM

end OAI.TuringRigidity.TwoConeForcingDefinition
