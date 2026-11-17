/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenConditions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CollapsePrefixAbsolute

/-!
# Internal Cohen Conditions
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing

/-- Represent a Boolean as the corresponding von Neumann numeral zero or one. -/
noncomputable def bitSet (b : Bool) : ZFSet.{0} := natSet (if b then 1 else 0)

/-- The two-element set used as the Boolean alphabet. -/
noncomputable def alphabet : ZFSet.{0} := {bitSet false, bitSet true}

theorem bitSet_injective : Function.Injective bitSet := by
  intro a b h
  have h' := natSet_injective h
  cases a <;> cases b <;> simp_all [bitSet]

theorem mem_alphabet (x : ZFSet.{0}) : x ∈ alphabet ↔ ∃ b : Bool, x = bitSet b := by
  simp only [alphabet,ZFSet.mem_insert_iff,ZFSet.mem_singleton]
  constructor
  · rintro (h|h)
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · rintro ⟨b,rfl⟩; cases b <;> simp

/-- Set-coded graph of the finite binary word. -/
noncomputable def wordCode (s : List Bool) : ZFSet.{0} :=
  ZFSet.range (fun i : Fin s.length => ZFSet.pair (natSet i.val) (bitSet s[i.val]))

theorem mem_wordCode (s : List Bool) (z : ZFSet.{0}) :
    z ∈ wordCode s ↔ ∃ i : Fin s.length, z = ZFSet.pair (natSet i.val) (bitSet s[i.val]) := by
  simp only [wordCode,ZFSet.mem_range,eq_comm]

theorem pair_mem_wordCode (s : List Bool) (n : ℕ) (b : Bool) :
    ZFSet.pair (natSet n) (bitSet b) ∈ wordCode s ↔
      ∃ h : n < s.length, b = s[n] := by
  rw [mem_wordCode]
  constructor
  · rintro ⟨i,he⟩
    obtain ⟨hn,hb⟩ := ZFSet.pair_inj.mp he
    have hn' := natSet_injective hn
    exact ⟨hn' ▸ i.isLt,by simpa only [←hn'] using bitSet_injective hb⟩
  · rintro ⟨hn,rfl⟩; exact ⟨⟨n,hn⟩,rfl⟩

theorem wordCode_function (s : List Bool) :
    TransitiveNameModel.FunctionGraph (natSet s.length) alphabet (wordCode s) := by
  constructor
  · intro z hz
    obtain ⟨i,rfl⟩ := (mem_wordCode s z).mp hz
    exact ⟨natSet i.val,(natSet_mem_natSet _ _).mpr i.isLt,
      bitSet s[i.val],(mem_alphabet _).mpr ⟨_,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨n,hn,rfl⟩ := (mem_natSet _ _).mp hx
    refine ⟨bitSet s[n],(mem_alphabet _).mpr ⟨_,rfl⟩,
      (pair_mem_wordCode _ _ _).mpr ⟨hn,rfl⟩,?_⟩
    intro y _ hy
    obtain ⟨i,he⟩ := (mem_wordCode _ _).mp hy
    obtain ⟨hi,hy⟩ := ZFSet.pair_inj.mp he
    have hi' := natSet_injective hi
    simpa only [←hi'] using hy

theorem wordCode_subset_iff (s t : List Bool) : wordCode s ⊆ wordCode t ↔ s <+: t := by
  constructor
  · intro h
    apply List.prefix_iff_getElem.mpr
    have hl : s.length ≤ t.length := by
      by_contra hn
      have hi : t.length < s.length := Nat.lt_of_not_ge hn
      have hh := (pair_mem_wordCode t t.length s[t.length]).mp
        (h ((pair_mem_wordCode s t.length s[t.length]).mpr ⟨hi,rfl⟩))
      exact (Nat.lt_irrefl _) hh.1
    exact ⟨hl,fun i hi => ((pair_mem_wordCode t i s[i]).mp
      (h ((pair_mem_wordCode s i s[i]).mpr ⟨hi,rfl⟩))).2⟩
  · intro h z hz
    obtain ⟨i,rfl⟩ := (mem_wordCode s z).mp hz
    exact (pair_mem_wordCode t _ _).mpr ⟨lt_of_lt_of_le i.isLt h.length_le,
      (List.prefix_iff_getElem.mp h).2 _ i.isLt⟩

theorem wordCode_injective : Function.Injective wordCode := by
  intro s t h
  exact List.Sublist.antisymm
    ((wordCode_subset_iff s t).mp (by rw [h])).sublist
    ((wordCode_subset_iff t s).mp (by rw [h])).sublist

theorem prefix_iff_wordCode (p : ZFSet.{0}) : Prefix alphabet p ↔ ∃ s, wordCode s = p := by
  classical
  constructor
  · rintro ⟨n,hp⟩
    have hv (i : Fin n) : ∃ b : Bool, ZFSet.pair (natSet i.val) (bitSet b) ∈ p := by
      obtain ⟨y,hy,hyf,_⟩ := hp.2 _ ((natSet_mem_natSet _ _).mpr i.isLt)
      obtain ⟨b,rfl⟩ := (mem_alphabet y).mp hy
      exact ⟨b,hyf⟩
    let s := List.ofFn (fun i : Fin n => (hv i).choose)
    have hs : s.length = n := List.length_ofFn
    refine ⟨s,ZFSet.ext (fun z => ?_)⟩
    constructor
    · intro hz
      obtain ⟨i,rfl⟩ := (mem_wordCode _ _).mp hz
      simpa only [s,List.getElem_ofFn] using (hv ⟨i.val,hs ▸ i.isLt⟩).choose_spec
    · intro hz
      obtain ⟨x,hx,y,_,rfl⟩ := hp.1 z hz
      obtain ⟨i,hi,rfl⟩ := (mem_natSet n x).mp hx
      have hv' := (hv ⟨i,hi⟩).choose_spec
      have he := hp.functional ((natSet_mem_natSet _ _).mpr hi) hz hv'
      rw [he]
      exact (mem_wordCode _ _).mpr ⟨⟨i,hs.symm ▸ hi⟩,by simp [s]⟩
  · rintro ⟨s,rfl⟩; exact ⟨s.length,wordCode_function s⟩

/-- The set of finite initial-segment functions into the Boolean alphabet. -/
noncomputable def conditions : ZFSet.{0} :=
  ZFSet.sep (Prefix alphabet) (ZFSet.powerset (ZFSet.prod ZFSet.omega alphabet))

theorem mem_conditions (p : ZFSet.{0}) : p ∈ conditions ↔ Prefix alphabet p := by
  rw [conditions,ZFSet.mem_sep]
  exact ⟨And.right,fun h => ⟨ZFSet.mem_powerset.mpr (prefix_subset h),h⟩⟩

theorem alphabet_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) : alphabet ∈ M := by
  have hn (n : ℕ) : natSet n ∈ M :=
    hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact pair_mem M hM hT.pairing (hn 0) (hn 1)

theorem conditions_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) : conditions ∈ M := by
  obtain ⟨c,hc,hdef⟩ := conditions_exist_absolute_without_choice M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT)
    (alphabet_mem M hM hT)
  have he : c = conditions := ZFSet.ext (fun p => (hdef p).trans (mem_conditions p).symm)
  exact he ▸ hc

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Encode a word condition as an element of the set-coded condition poset. -/
noncomputable def encodeCondition (p : Condition) : Conditions conditions :=
  equivShrink conditions ⟨wordCode p.word,(mem_conditions _).mpr ⟨_,wordCode_function _⟩⟩

theorem label_encodeCondition (p : Condition) : label conditions (encodeCondition p) = wordCode
  p.word := by
  simp [encodeCondition,label]

/-- Order isomorphism between word conditions and their set-coded initial-segment graphs. -/
noncomputable def conditionEquiv : Condition ≃o Conditions conditions := by
  have bijective : Function.Bijective encodeCondition := by
    constructor
    · intro p q h
      apply Condition.ext
      apply wordCode_injective
      simpa only [label_encodeCondition] using congrArg (label conditions) h
    · intro q
      obtain ⟨s,hs⟩ := (prefix_iff_wordCode _).mp ((mem_conditions _).mp (label_mem conditions q))
      exact ⟨⟨s⟩,label_injective conditions (by rw [label_encodeCondition]; exact hs)⟩
  refine { Equiv.ofBijective encodeCondition bijective with map_rel_iff' := ?_ }
  intro p q
  change label conditions (encodeCondition q) ⊆ label conditions (encodeCondition p) ↔ _
  rw [label_encodeCondition,label_encodeCondition,wordCode_subset_iff]
  rfl

end TuringRigidity.InternalCohen

end OAI
