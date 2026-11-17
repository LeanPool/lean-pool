/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/DefinedPrefixRemoval.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenPrefixOverwrite
public import LeanPool.TuringConeRigidity.Effective.UniformTableSimulation
public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleGroundReals

/-!
# Defined Prefix Removal
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
open CohenGroundPoset CohenColumnRealName CohenFiniteFlip FiniteOverwrite
open TableIndices IndexMatrix
open ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem equidegree_mem_ownDegree (E u : ZFSet.{0}) (hE : Transitive E) (hT : SourceT E)
    (hu : u ∈ degreeUniverse (groundReals E)) (A B : Oracle)
    (hB : realCode B ∈ u) (he : degree A = degree B) : realCode A ∈ u := by
  obtain ⟨C,hC,rfl⟩ := (mem_degreeUniverse _ _).mp hu
  have hmem := actual_degreeCode_membership E hE hT (groundReals E)
    (realCode_mem_groundReals E) ((realCode_mem_groundReals E C).mp hC)
  exact (hmem A).mpr (he.trans ((hmem B).mp hB))

theorem defined_value_extension_eq (M c : ZFSet.{0}) (δ : Ordinal.{0})
    (Z : ZFSet.{0}) (φ : SentenceForm) (f : Name (Conditions c))
    (hfv : ∀ H : GenericFilter (Conditions c), GroundGeneric M H →
      f.val H.carrier = definedSubset (level (groundReals (genericExtensionSet M c H.carrier)) δ)
        φ (fun _ : Fin φ.bound => Z))
    (G H : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (hH : GroundGeneric M H)
    (he : genericExtensionSet M c G.carrier = genericExtensionSet M c H.carrier) :
    f.val G.carrier = f.val H.carrier := by
  rw [hfv G hG,hfv H hH,he]

theorem remove_defined_program_prefix (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : SentenceForm)
    (f : Name (Conditions (poset K)))
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (R A₀ : Oracle) (d ℓ : ℕ)
    (hprog : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
        (∀ n < ℓ, A n = A₀ n) → ∃ X : Oracle,
          Represents (join A R) (machine d) X ∧
          ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
          ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
            realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f.val H.carrier) :
    ∃ e : ℕ, ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → ∃ X : Oracle,
        Represents (join A R) (machine e) X ∧
        ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
        ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
          realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f.val H.carrier := by
  let s := FiniteShuffle.initial A₀ ℓ
  obtain ⟨e,he⟩ := (overwrite_join_program s R).table_simulation d
  refine ⟨e,fun H hH A hv => ?_⟩
  let Hs := prefixFilter K a s A H
  obtain ⟨hHs,hExt,hval⟩ := prefixFilter_properties M K a hM hT hK ha s A H hH hv
  have hprefix : ∀ n < ℓ, overwrite s A n = A₀ n := by
    intro n hn
    rw [overwrite_below _ _ _ (by simpa [s] using hn),FiniteShuffle.prefix_getD _ _ _ hn]
  obtain ⟨X,hX,u,hu,v,hv',hAu,hXv,hpair⟩ := hprog Hs hHs (overwrite s A) hval hprefix
  have hfEq := defined_value_extension_eq M (poset K) δ Z φ f hfv Hs H hHs hH hExt
  rw [hExt] at hu hv'
  rw [hfEq] at hpair
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (manyColumn_internal M K hM hT hK).1 H hH
  exact ⟨X,he A X hX,u,hu,v,hv',
    equidegree_mem_ownDegree _ u hE hTE hu A (overwrite s A) hAu
      (degree_overwrite s A).symm,hXv,hpair⟩

end TuringRigidity.RelativeConstructible

end OAI
