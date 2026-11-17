/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenValue.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenName

/-!
# Internal Cohen Value
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing
  RecursiveNames
open FiniteShuffle ShuffleRequirements
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem bit_in_filter (A : Oracle) (n : ℕ) :
    (∃ q ∈ (pushFilter (realFilter A)).carrier,
      ZFSet.pair (natSet n) (bitSet true) ∈ label conditions q) ↔ A n = true := by
  constructor
  · rintro ⟨q,hq,hbit⟩
    let p := conditionEquiv.symm q
    have hp : Realizes p.word A := hq
    have hl : label conditions q = wordCode p.word := by
      rw [←label_encodeCondition p]; congr 1; exact (conditionEquiv.apply_symm_apply q).symm
    rw [hl,pair_mem_wordCode] at hbit
    obtain ⟨hn,hbit⟩ := hbit
    have he := hp n hn
    simpa only [List.getD,List.getElem?_eq_getElem hn,Option.getD_some,←hbit] using he.symm
  · intro hn
    let p : Condition := ⟨initial A (n+1)⟩
    have hp : Realizes p.word A := (realizes_initial A A (n+1)).mpr (fun _ _ => rfl)
    have hl : n < p.word.length := by simp [p,initial]
    refine ⟨conditionEquiv p,by simpa [pushFilter,realFilter] using hp,?_⟩
    rw [show label conditions (conditionEquiv p) = wordCode p.word from label_encodeCondition p]
    apply (pair_mem_wordCode _ _ _).mpr
    refine ⟨hl,?_⟩
    have he := (hp n hl).trans hn
    simpa only [List.getD,List.getElem?_eq_getElem hl,Option.getD_some] using he.symm

theorem val_realName (A : Oracle) :
    realName.val (pushFilter (realFilter A)).carrier = realCode A := by
  have ht : (⊤ : Conditions conditions) ∈ (pushFilter (realFilter A)).carrier := by
    obtain ⟨p,hp⟩ := (pushFilter (realFilter A)).nonempty
    exact (pushFilter (realFilter A)).upper le_top hp
  apply ZFSet.ext; intro z
  rw [realName,Name.mem_val]
  simp only [Name.val_check _ ht]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hq,rfl⟩
    exact (natSet_mem_realCode _ _).mpr ((bit_in_filter A n).mp ⟨q,hq,hbit⟩)
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    obtain ⟨q,hq,hbit⟩ := (bit_in_filter A n).mpr ((natSet_mem_realCode A n).mp hz)
    exact ⟨⟨(q,n),hbit⟩,hq,rfl⟩

theorem generic_real_value (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions conditions)) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, G = pushFilter (realFilter A) ∧
      realName.val G.carrier = realCode A ∧
      A ∈ modelReals (genericExtensionSet M conditions G.carrier) := by
  obtain ⟨A,rfl⟩ := groundGeneric_real M hM hT G hG
  refine ⟨A,rfl,val_realName A,?_⟩
  exact (mem_extensionSet M conditions _ _).mpr ⟨realName,realName_internal M hM hT,val_realName A⟩

theorem external_genericReal_value (A : Oracle) :
    CohenRecursiveName.genericReal.val (realFilter A).carrier =
      realName.val (pushFilter (realFilter A)).carrier := by
  rw [CohenRecursiveName.val_genericReal,val_realName]
  apply ZFSet.ext; intro z
  rw [CohenRecursiveName.realSet,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨n,hn⟩,rfl⟩
    simpa only [natSet_eq_mk,CohenRecursiveName.numeral] using (natSet_mem_realCode A n).mpr hn
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    exact ⟨⟨n,(natSet_mem_realCode A n).mp hz⟩,(natSet_eq_mk n).symm⟩

theorem val_output_transport (y : Name (Conditions conditions)) (G : GenericFilter Condition) :
    (y.rename conditionEquiv.symm).val G.carrier = y.val (pushFilter G).carrier :=
  Name.val_rename conditionEquiv.symm _ _ (fun _ => Iff.rfl) y

end TuringRigidity.InternalCohen

end OAI
