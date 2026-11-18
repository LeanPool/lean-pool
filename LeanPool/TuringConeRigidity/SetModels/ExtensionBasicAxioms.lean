/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ExtensionBasicAxioms.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameUnionCode

/-!
# Extension Basic Axioms
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open Set RecursiveNames BoundedSetTheory CountableForcing
universe u

namespace BasicAxioms

/-- Extensionality with element comparisons restricted to members of the model. -/
def Extensionality (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, (∀ x ∈ M, x ∈ a ↔ x ∈ b) → a = b

/-- The model contains an element with no members inside the model. -/
def EmptySet (M : ZFSet.{u}) : Prop := ∃ a ∈ M, ∀ x ∈ M, x ∉ a

/-- Every internally nonempty model element has an internally membership-minimal element. -/
def Foundation (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, (∃ x ∈ M, x ∈ a) →
    ∃ y ∈ M, y ∈ a ∧ ∀ z ∈ M, ¬ (z ∈ y ∧ z ∈ a)

theorem extensionality (M : ZFSet.{u}) (hM : Transitive M) : Extensionality M := by
  intro a ha b hb h
  apply ZFSet.ext
  intro x
  exact ⟨fun hx => (h x (hM a ha x hx)).mp hx,
    fun hx => (h x (hM b hb x hx)).mpr hx⟩

theorem foundation (M : ZFSet.{u}) (hM : Transitive M) : Foundation M := by
  rintro a ha ⟨x,_,hxa⟩
  have hne : a ≠ ∅ := by intro h; exact ZFSet.notMem_empty x (h ▸ hxa)
  obtain ⟨y,hya,hy⟩ := ZFSet.regularity a hne
  refine ⟨y,hM a ha y hya,hya,fun z _ hz => ?_⟩
  have hz' : z ∈ a ∩ y := ZFSet.mem_inter.mpr ⟨hz.2,hz.1⟩
  exact ZFSet.notMem_empty z (hy ▸ hz')

end BasicAxioms

theorem empty_mem_ground (M : ZFSet.{u}) (hM : Transitive M) (hne : M ≠ ∅) :
    (∅ : ZFSet.{u}) ∈ M := by
  obtain ⟨a,ha,hmin⟩ := ZFSet.regularity M hne
  have he : a = ∅ := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      have hi : x ∈ M ∩ a := ZFSet.mem_inter.mpr ⟨hM a ha x hx,hx⟩
      exact hmin ▸ hi
    · exact fun hx => False.elim (ZFSet.notMem_empty x hx)
  exact he ▸ ha

/-- The forcing name with no children, representing the empty set. -/
def emptyName (P : Type u) : Name P :=
  .mk (ULift Empty) (fun i => i.down.elim) (fun i => i.down.elim)

theorem encode_emptyName {P : Type u} (l : P → ZFSet.{u}) :
    (emptyName P).encode l = ∅ := by
  apply ZFSet.ext
  intro x
  simp [emptyName,Name.encode]

theorem val_emptyName {P : Type u} (G : Set P) : Name.val G (emptyName P) = ∅ := by
  apply ZFSet.ext
  intro x
  simp [emptyName,Name.mem_val]

theorem mem_extensionSet (M p : ZFSet.{u}) (G : Set (Conditions p)) (x : ZFSet.{u}) :
    x ∈ genericExtensionSet M p G ↔
      ∃ τ : Name (Conditions p), τ.encode (label p) ∈ M ∧ τ.val G = x := by
  change x ∈ (genericExtensionSet M p G : Set ZFSet.{u}) ↔ _
  rw [genericExtensionSet_coe]
  rfl

theorem extension_empty_mem (M p : ZFSet.{u}) (hM : Transitive M) (hne : M ≠ ∅)
    (G : Set (Conditions p)) : (∅ : ZFSet.{u}) ∈ genericExtensionSet M p G := by
  apply (mem_extensionSet M p G _).mpr
  refine ⟨emptyName _,?_,val_emptyName G⟩
  rw [encode_emptyName]
  exact empty_mem_ground M hM hne

theorem encode_pair {P : Type u} [Top P] (l : P → ZFSet.{u}) (σ τ : Name P) :
    (Name.pair σ τ).encode l =
      ({ZFSet.pair (σ.encode l) (l ⊤),ZFSet.pair (τ.encode l) (l ⊤)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro x
  change x ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,ZFSet.mem_pair]
  constructor
  · rintro ⟨⟨b⟩,hb⟩
    cases b
    · exact Or.inr hb.symm
    · exact Or.inl hb.symm
  · rintro (hx|hx)
    · exact ⟨⟨true⟩,hx.symm⟩
    · exact ⟨⟨false⟩,hx.symm⟩

theorem names_pair_closed (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hp : p ∈ M)
    {σ τ : Name (Conditions p)} (hσ : σ ∈ names M p) (hτ : τ ∈ names M p) :
    Name.pair σ τ ∈ names M p := by
  have ht := hM p hp (label p ⊤) (label_mem p ⊤)
  change (Name.pair σ τ).encode (label p) ∈ M
  rw [encode_pair]
  exact pair_mem M hM hP (orderedPair_mem M hM hP hσ ht) (orderedPair_mem M hM hP hτ ht)

theorem extension_pairing (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hp : p ∈ M)
    (G : Set (Conditions p)) (hG : ⊤ ∈ G) : Pairing (genericExtensionSet M p G) := by
  intro a ha b hb
  obtain ⟨σ,hσ,rfl⟩ := (mem_extensionSet M p G a).mp ha
  obtain ⟨τ,hτ,rfl⟩ := (mem_extensionSet M p G b).mp hb
  refine ⟨({σ.val G,τ.val G} : ZFSet.{u}),?_,fun x _ => ZFSet.mem_pair⟩
  exact (mem_extensionSet M p G _).mpr
    ⟨Name.pair σ τ,names_pair_closed M p hM hP hp hσ hτ,Name.val_pair G hG σ τ⟩

theorem names_union_closed (M p r : ZFSet.{u}) [Preorder (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hp : p ∈ M) (hrM : r ∈ M)
    (hr : ∀ q s : Conditions p, ZFSet.pair (label p q) (label p s) ∈ r ↔ q ≤ s)
    {τ : Name (Conditions p)} (hτ : τ ∈ names M p) :
    Name.union τ ∈ names M p := by
  change (Name.union τ).encode (label p) ∈ M
  rw [encode_union p r hr]
  exact unionCode_mem M hM hP hU hPow hS hτ hp hrM

theorem extension_union (M p r : ZFSet.{u}) [Preorder (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hp : p ∈ M) (hrM : r ∈ M)
    (hr : ∀ q s : Conditions p, ZFSet.pair (label p q) (label p s) ∈ r ↔ q ≤ s)
    (G : GenericFilter (Conditions p)) : BoundedSetTheory.Union (genericExtensionSet M p
      G.carrier) := by
  intro a ha
  obtain ⟨τ,hτ,rfl⟩ := (mem_extensionSet M p G.carrier a).mp ha
  refine ⟨ZFSet.sUnion (τ.val G.carrier),?_,?_⟩
  · exact (mem_extensionSet M p G.carrier _).mpr
      ⟨Name.union τ,names_union_closed M p r hM hP hU hPow hS hp hrM hr hτ,Name.val_union G τ⟩
  · intro x _
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,genericExtensionSet_transitive M p hM G.carrier _ ha y hy,hy,hxy⟩
    · rintro ⟨y,_,hy,hxy⟩
      exact ⟨y,hy,hxy⟩

theorem extension_five_axioms (M p r : ZFSet.{u})
    [Preorder (Conditions p)] [Top (Conditions p)]
    (hM : Transitive M) (hne : M ≠ ∅) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hp : p ∈ M) (hrM : r ∈ M)
    (hr : ∀ q s : Conditions p, ZFSet.pair (label p q) (label p s) ∈ r ↔ q ≤ s)
    (G : GenericFilter (Conditions p)) (hG : ⊤ ∈ G.carrier) :
    let E := genericExtensionSet M p G.carrier
    BasicAxioms.Extensionality E ∧ BasicAxioms.EmptySet E ∧
      Pairing E ∧ BoundedSetTheory.Union E ∧ BasicAxioms.Foundation E := by
  dsimp
  have hE := genericExtensionSet_transitive M p hM G.carrier
  exact ⟨BasicAxioms.extensionality _ hE,
    ⟨∅,extension_empty_mem M p hM hne G.carrier,fun x _ => ZFSet.notMem_empty x⟩,
    extension_pairing M p hM hP hp G.carrier hG,
    extension_union M p r hM hP hU hPow hS hp hrM hr G,
    BasicAxioms.foundation _ hE⟩

end TuringRigidity.TransitiveNameModel

end OAI
