/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenConditionCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalFiniteSubsets
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenConditions
public import LeanPool.TuringConeRigidity.CohenForcing.CohenCoordinates

/-!
# Cohen Condition Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenConditionCode
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenSymmetry CohenCoordinates
open InternalCohen (bitSet alphabet bitSet_injective mem_alphabet)

/-- Set-coded graph of the finitely supported Boolean condition `p`. -/
noncomputable def graph (A : ZFSet.{0}) (p : Condition (Conditions A)) : ZFSet.{0} :=
  ZFSet.range (fun i : ↥(support p) =>
    ZFSet.pair (label A i.val) (bitSet ((p.val i.val).getD false)))

theorem pair_mem_graph (A : ZFSet.{0}) (p : Condition (Conditions A))
    (i : Conditions A) (b : Bool) :
    ZFSet.pair (label A i) (bitSet b) ∈ graph A p ↔ p.val i = some b := by
  classical
  rw [graph,ZFSet.mem_range]
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨he,hb⟩ := ZFSet.pair_inj.mp hj
    have hji := label_injective A he
    have hn := (mem_support p j.val).mp j.property
    have hv : p.val j.val = some ((p.val j.val).getD false) := by
      cases h : p.val j.val with
      | none => exact False.elim (hn h)
      | some c => rfl
    rw [bitSet_injective hb,hji] at hv
    exact hv
  · intro hi
    refine ⟨⟨i,(mem_support p i).mpr (by simp [hi])⟩,?_⟩
    simp [hi]

theorem mem_graph (A : ZFSet.{0}) (p : Condition (Conditions A)) (z : ZFSet.{0}) :
    z ∈ graph A p ↔ ∃ i b, p.val i = some b ∧ z = ZFSet.pair (label A i) (bitSet b) := by
  constructor
  · intro hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨i.val,_,(pair_mem_graph A p _ _).mp (ZFSet.mem_range_self i),rfl⟩
  · rintro ⟨i,b,hi,rfl⟩; exact (pair_mem_graph A p i b).mpr hi

theorem graph_subset_iff (A : ZFSet.{0}) (p q : Condition (Conditions A)) :
    graph A q ⊆ graph A p ↔ p ≤ q := by
  constructor
  · intro h i b hb; exact (pair_mem_graph A p i b).mp (h ((pair_mem_graph A q i b).mpr hb))
  · intro h z hz
    obtain ⟨i,b,hi,rfl⟩ := (mem_graph A q z).mp hz
    exact (pair_mem_graph A p i b).mpr (h i b hi)

theorem graph_injective (A : ZFSet.{0}) : Function.Injective (graph A) := by
  intro p q h
  apply le_antisymm
  · exact (graph_subset_iff A p q).mp (by rw [h])
  · exact (graph_subset_iff A q p).mp (by rw [h])

/-- The relation `p` assigns at most one alphabet value to each coordinate in `A`. -/
def SingleValued (A p : ZFSet.{0}) : Prop :=
  ∀ x ∈ A, ∀ b ∈ alphabet, ∀ c ∈ alphabet,
    ZFSet.pair x b ∈ p → ZFSet.pair x c ∈ p → b = c

/-- A finite, single-valued relation from coordinates in `A` to the Boolean alphabet. -/
def IsCondition (A p : ZFSet.{0}) : Prop :=
  p ∈ finiteSubsets (ZFSet.prod A alphabet) ∧ SingleValued A p

theorem graph_isCondition (A : ZFSet.{0}) (p : Condition (Conditions A)) :
    IsCondition A (graph A p) := by
  constructor
  · apply (mem_finiteSubsets_iff _ _).mpr
    constructor
    · intro z hz
      obtain ⟨i,b,_,rfl⟩ := (mem_graph A p z).mp hz
      exact ZFSet.mem_prod.mpr ⟨_,label_mem A i,_,(mem_alphabet _).mpr ⟨b,rfl⟩,rfl⟩
    · rw [graph,ZFSet.coe_range]; exact Set.finite_range _
  · intro x hx b hb c hc hpb hpc
    obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
    obtain ⟨c,rfl⟩ := (mem_alphabet _).mp hc
    let i : Conditions A := equivShrink A ⟨x,hx⟩
    have hi : label A i = x := by simp [i,label]
    rw [←hi,pair_mem_graph] at hpb hpc
    exact congrArg bitSet (Option.some.inj (hpb.symm.trans hpc))

theorem isCondition_iff_graph (A x : ZFSet.{0}) :
    IsCondition A x ↔ ∃ p : Condition (Conditions A), graph A p = x := by
  classical
  constructor
  · intro hx
    have hsub := ((mem_finiteSubsets_iff _ _).mp hx.1).1
    have hfin := ((mem_finiteSubsets_iff _ _).mp hx.1).2
    let v (i : Conditions A) : Option Bool :=
      if h : ∃ b, ZFSet.pair (label A i) (bitSet b) ∈ x then some h.choose else none
    have hv (i : Conditions A) (b : Bool) :
        v i = some b ↔ ZFSet.pair (label A i) (bitSet b) ∈ x := by
      dsimp only [v]
      split_ifs with h
      · constructor
        · intro he; exact Option.some.inj he ▸ h.choose_spec
        · intro hb
          have he := hx.2 _ (label_mem A i) _ ((mem_alphabet _).mpr ⟨h.choose,rfl⟩)
            _ ((mem_alphabet _).mpr ⟨b,rfl⟩) h.choose_spec hb
          exact congrArg some (bitSet_injective he)
      · constructor
        · intro he; cases he
        · intro hb; exact False.elim (h ⟨b,hb⟩)
    have hfinite : {i | v i ≠ none}.Finite := by
      let f (i : Conditions A) := ZFSet.pair (label A i) (bitSet ((v i).getD false))
      have hf : Function.Injective f := by
        intro i j he; exact label_injective A (ZFSet.pair_inj.mp he).1
      apply (hfin.preimage hf.injOn).subset
      intro i hi
      change f i ∈ x
      apply (hv i _).mp
      cases he : v i with
      | none => exact False.elim (hi he)
      | some b => rfl
    let p : Condition (Conditions A) := ⟨v,hfinite⟩
    refine ⟨p,ZFSet.ext (fun z => ?_)⟩
    constructor
    · intro hz
      obtain ⟨i,b,hi,rfl⟩ := (mem_graph A p z).mp hz
      exact (hv i b).mp hi
    · intro hz
      obtain ⟨i,hi,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
      obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
      let j : Conditions A := equivShrink A ⟨i,hi⟩
      have hj : label A j = i := by simp [j,label]
      rw [←hj]
      exact (pair_mem_graph A p j b).mpr ((hv j b).mpr (hj ▸ hz))
  · rintro ⟨p,rfl⟩; exact graph_isCondition A p

end TuringRigidity.CohenConditionCode

end OAI
