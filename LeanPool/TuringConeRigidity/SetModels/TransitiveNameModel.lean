/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/TransitiveNameModel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameEncoding
public import LeanPool.TuringConeRigidity.SetModels.NameExtension

/-!
# Transitive Name Model
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open Set RecursiveNames
universe u

/-- The small type of elements of the set-coded condition poset `p`. -/
abbrev Conditions (p : ZFSet.{u}) : Type u := Shrink p

/-- The ground-model set label corresponding to a condition-type element. -/
noncomputable def label (p : ZFSet.{u}) (q : Conditions p) : ZFSet.{u} :=
  ((equivShrink p).symm q).val

theorem label_injective (p : ZFSet.{u}) : Function.Injective (label p) :=
  fun _ _ h => (equivShrink p).symm.injective (Subtype.ext h)

theorem label_mem (p : ZFSet.{u}) (q : Conditions p) : label p q ∈ p :=
  ((equivShrink p).symm q).property

/-- The forcing names whose set codes belong to `M`. -/
def names (M p : ZFSet.{u}) : Set (Name (Conditions p)) :=
  {τ | Name.encode (label p) τ ∈ M}

/-- Every member of every element of `M` also belongs to `M`. -/
def Transitive (M : ZFSet.{u}) : Prop := ∀ x ∈ M, ∀ y ∈ x, y ∈ M

/-- The values of names coded in `M`, interpreted using `G`. -/
def genericExtension (M p : ZFSet.{u}) (G : Set (Conditions p)) : Set ZFSet.{u} :=
  extension (names M p) G

theorem names_childClosed (M p : ZFSet.{u}) (hM : Transitive M) :
    ChildClosed (names M p) := by
  intro τ hτ σ hσ
  cases τ with
  | mk ι child tag =>
    obtain ⟨i,rfl⟩ := hσ
    change Name.encode (label p) (.mk ι child tag) ∈ M at hτ
    have hp : ZFSet.pair (Name.encode (label p) (child i)) (label p (tag i)) ∈ M :=
      hM (Name.encode (label p) (.mk ι child tag)) hτ _ (ZFSet.mem_range_self i)
    have hs : ({Name.encode (label p) (child i)} : ZFSet.{u}) ∈ M :=
      hM _ hp _ (ZFSet.mem_pair.mpr (Or.inl rfl))
    exact hM _ hs _ (ZFSet.mem_singleton.mpr rfl)

theorem genericExtension_transitive (M p : ZFSet.{u}) (hM : Transitive M)
    (G : Set (Conditions p)) :
    ∀ x ∈ genericExtension M p G, ∀ y ∈ x, y ∈ genericExtension M p G :=
  extension_transitive _ (names_childClosed M p hM) G

/-- Interpret a set-coded forcing name, using the empty set for codes that represent no name. -/
noncomputable def valueOnCode (p : ZFSet.{u}) (G : Set (Conditions p))
    (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ τ : Name (Conditions p), Name.encode (label p) τ = x
    then Name.val G h.choose else ∅

theorem valueOnCode_encode (p : ZFSet.{u}) (G : Set (Conditions p))
    (τ : Name (Conditions p)) :
    valueOnCode p G (Name.encode (label p) τ) = Name.val G τ := by
  classical
  have h : ∃ σ : Name (Conditions p), Name.encode (label p) σ = Name.encode (label p) τ :=
    ⟨τ,rfl⟩
  rw [valueOnCode,dite_eq_left h]
  exact Name.val_eq_of_encode_eq _ (label_injective p) G _ τ h.choose_spec

theorem genericExtension_countable (M p : ZFSet.{u})
    (hM : (M : Set ZFSet.{u}).Countable) (G : Set (Conditions p)) :
    (genericExtension M p G).Countable := by
  apply (hM.image (valueOnCode p G)).mono
  rintro x ⟨τ,hτ,rfl⟩
  exact ⟨Name.encode (label p) τ,hτ,valueOnCode_encode p G τ⟩

/-- The generic-extension value family represented as a set through its ground-model name
codes. -/
noncomputable def genericExtensionSet (M p : ZFSet.{u}) (G : Set (Conditions p)) :
    ZFSet.{u} := ZFSet.range
      (fun x : {x : M // ∃ τ : Name (Conditions p), Name.encode (label p) τ = x.val} =>
        valueOnCode p G x.val.val)

theorem genericExtensionSet_coe (M p : ZFSet.{u}) (G : Set (Conditions p)) :
    (genericExtensionSet M p G : Set ZFSet.{u}) = genericExtension M p G := by
  ext x
  change x ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨c,hc⟩,τ,hτ⟩,hx⟩
    refine ⟨τ,?_,?_⟩
    · change Name.encode (label p) τ ∈ M
      simpa only [hτ] using hc
    · have hv := valueOnCode_encode p G τ
      rw [hτ] at hv
      exact hv.symm.trans hx
  · rintro ⟨τ,hτ,rfl⟩
    exact ⟨⟨⟨Name.encode (label p) τ,hτ⟩,τ,rfl⟩,valueOnCode_encode p G τ⟩

theorem genericExtensionSet_transitive (M p : ZFSet.{u}) (hM : Transitive M)
    (G : Set (Conditions p)) : Transitive (genericExtensionSet M p G) := by
  intro x hx y hy
  have hx' : x ∈ genericExtension M p G := by
    rw [←genericExtensionSet_coe]; exact hx
  have hy' := genericExtension_transitive M p hM G x hx' y hy
  rw [←genericExtensionSet_coe] at hy'
  exact hy'

theorem ground_subset (M p : ZFSet.{u}) [Top (Conditions p)]
    (hcheck : ∀ x ∈ M, Name.encode (label p) (Name.check x) ∈ M)
    (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    (M : Set ZFSet.{u}) ⊆ genericExtension M p G :=
  ground_subset_extension _ _ hcheck G hG

end TuringRigidity.TransitiveNameModel

end OAI
