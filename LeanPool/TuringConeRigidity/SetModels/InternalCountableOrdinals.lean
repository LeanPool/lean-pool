/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCountableOrdinals.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableClosure
public import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Internal Countable Ordinals
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCountableOrdinals
open TransitiveNameModel BoundedSetTheory InternalCountableClosure

def FirstUncountable (M K : ZFSet.{0}) : Prop :=
  K.IsOrdinal ∧ K ∈ M ∧ ¬ (K = ∅ ∨ InternallyCountable M K) ∧
    ∀ a ∈ K, a = ∅ ∨ InternallyCountable M a

theorem successor_mem (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) : insert a a ∈ M := by
  have he : insert a a = ({a} : ZFSet.{0}) ∪ a := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  rw [he]
  exact binary_union_mem M hM hT.pairing hT.union (singleton_mem M hM hT.pairing ha) ha

theorem nonempty (M K : ZFSet.{0}) (hK : FirstUncountable M K) : ∃ x, x ∈ K := by
  classical
  by_contra h
  apply hK.2.2.1; left
  apply ZFSet.ext; intro x
  exact ⟨fun hx => False.elim (h ⟨x,hx⟩),fun hx => False.elim (ZFSet.notMem_empty x hx)⟩

theorem countable_ordinal_lt (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (haM : a ∈ M) (ha : a.IsOrdinal)
    (hct : a = ∅ ∨ InternallyCountable M a) : a ∈ K := by
  rcases ha.mem_or_subset hK.1 with h|h
  · exact h
  · exfalso
    rcases hct with rfl|hct
    · obtain ⟨x,hx⟩ := nonempty M K hK
      exact ZFSet.notMem_empty x (h hx)
    · exact hK.2.2.1 (Or.inr (countable_subset M a K hM hT haM hK.2.1 h hct (nonempty M K hK)))

theorem unique (M K L : ZFSet.{0})
    (hK : FirstUncountable M K) (hL : FirstUncountable M L) : K = L := by
  rcases hK.1.mem_trichotomous hL.1 with h|h|h
  · exact False.elim (hK.2.2.1 (hL.2.2.2 K h))
  · exact h
  · exact False.elim (hL.2.2.1 (hK.2.2.2 L h))

theorem sUnion_isOrdinal (S : ZFSet.{0}) (hS : ∀ a ∈ S, a.IsOrdinal) :
    (ZFSet.sUnion S).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  refine ⟨ZFSet.IsTransitive.sUnion' (fun a ha => (hS a ha).isTransitive),?_⟩
  intro x hx
  obtain ⟨a,ha,hx⟩ := ZFSet.mem_sUnion.mp hx
  exact (hS a ha).mem hx

theorem countable_ordinal_union (M S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hSM : S ∈ M) (hct : S = ∅ ∨ InternallyCountable M S)
    (hord : ∀ a ∈ S, a.IsOrdinal)
    (hsets : ∀ a ∈ S, a = ∅ ∨ InternallyCountable M a) :
    ZFSet.sUnion S ∈ M ∧ (ZFSet.sUnion S).IsOrdinal ∧
      (ZFSet.sUnion S = ∅ ∨ InternallyCountable M (ZFSet.sUnion S)) :=
  ⟨union_mem M hM hT.union hSM,sUnion_isOrdinal S hord,
    InternalCountableFamily.countable_sUnion M S hM hT hSM hct hsets⟩

theorem countable_subset_bounded (M K S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hSM : S ∈ M) (hSK : S ⊆ K)
    (hct : S = ∅ ∨ InternallyCountable M S) :
    ∃ b ∈ K, b ∈ M ∧ b.IsOrdinal ∧ InternallyCountable M b ∧ ∀ a ∈ S, a ∈ b := by
  obtain ⟨hUM,hU,hctU⟩ := countable_ordinal_union M S hM hT hSM hct
    (fun a ha => hK.1.mem (hSK ha)) (fun a ha => hK.2.2.2 a (hSK ha))
  let b := insert (ZFSet.sUnion S) (ZFSet.sUnion S)
  have hbM : b ∈ M := successor_mem M _ hM hT hUM
  have hb : b.IsOrdinal := ZFSet.isOrdinal_succ hU
  have hcb : InternallyCountable M b := countable_insert M _ _ hM hT hUM hUM hctU
  refine ⟨b,countable_ordinal_lt M K b hM hT hK hbM hb (Or.inr hcb),hbM,hb,hcb,?_⟩
  intro a ha
  have hsub : a ⊆ ZFSet.sUnion S := fun x hx => ZFSet.mem_sUnion.mpr ⟨a,ha,hx⟩
  exact ZFSet.mem_insert_iff.mpr (((hK.1.mem (hSK ha)).subset_iff_eq_or_mem hU).mp hsub)

theorem no_countable_cofinal_subset (M K S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hSM : S ∈ M) (hSK : S ⊆ K)
    (hct : S = ∅ ∨ InternallyCountable M S) :
    ¬ (∀ b ∈ K, ∃ a ∈ S, b ⊆ a) := by
  obtain ⟨b,hb,_,_,_,hbound⟩ := countable_subset_bounded M K S hM hT hK hSM hSK hct
  intro h
  obtain ⟨a,ha,hba⟩ := h b hb
  exact ZFSet.mem_irrefl a (hba (hbound a ha))

theorem firstUncountable_below (M L : ZFSet.{0}) (hM : Transitive M)
    (hL : L ∈ M) (hord : L.IsOrdinal)
    (hunc : ¬ (L = ∅ ∨ InternallyCountable M L)) :
    ∃ K, FirstUncountable M K ∧ K ⊆ L := by
  classical
  have h : ∀ L : ZFSet.{0}, L ∈ M → L.IsOrdinal →
      ¬ (L = ∅ ∨ InternallyCountable M L) → ∃ K, FirstUncountable M K ∧ K ⊆ L := by
    intro L
    induction L using ZFSet.mem_wf.induction with
    | h L ih =>
      intro hLM ho hu
      by_cases hs : ∀ a ∈ L, a = ∅ ∨ InternallyCountable M a
      · exact ⟨L,⟨ho,hLM,hu,hs⟩,fun _ h => h⟩
      · push Not at hs
        obtain ⟨a,ha,hac⟩ := hs
        obtain ⟨K,hK,hKa⟩ := ih a ha (hM L hLM a ha) (ho.mem ha) (not_or.mpr hac)
        exact ⟨K,hK,fun x hx => ho.subset_of_mem ha (hKa hx)⟩
  exact h L hL hord hunc

end TuringRigidity.InternalCountableOrdinals

end OAI
