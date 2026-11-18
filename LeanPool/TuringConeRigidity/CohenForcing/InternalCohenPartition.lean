/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenPartition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenRestriction

/-!
# Internal Cohen Partition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenPartition
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohenRestriction
open InternalCohen (alphabet)

theorem complement_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : A \ B ∈ M := by
  simpa only [ZFSet.sep_notMem,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.neg (.member 0 1))
      (fun _ => B) (fun _ => hB) hA

theorem condition_subset (A p : ZFSet.{0}) (hp : p ∈ conditions A) :
    p ⊆ ZFSet.prod A alphabet :=
  ((mem_finiteSubsets_iff _ _).mp ((mem_conditions A p).mp hp).1).1

theorem condition_mono (A B p : ZFSet.{0}) (hBA : B ⊆ A) (hp : p ∈ conditions B) :
    p ∈ conditions A := by
  obtain ⟨hf,hs⟩ := (mem_conditions B p).mp hp
  obtain ⟨hsub,hfin⟩ := (mem_finiteSubsets_iff _ _).mp hf
  apply (mem_conditions A p).mpr
  constructor
  · apply (mem_finiteSubsets_iff _ _).mpr
    exact ⟨fun z hz => by
      obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
      exact ZFSet.pair_mem_prod.mpr ⟨hBA hx,hb⟩,hfin⟩
  · intro x _ b hb c hc hxb hxc
    have hx := (ZFSet.pair_mem_prod.mp (hsub hxb)).1
    exact hs x hx b hb c hc hxb hxc

theorem union_condition (A B p q : ZFSet.{0}) (hBA : B ⊆ A)
    (hp : p ∈ conditions B) (hq : q ∈ conditions (A \ B)) :
    p ∪ q ∈ conditions A := by
  have hpA := condition_mono A B p hBA hp
  have hqA := condition_mono A (A \ B) q (fun _ h => (ZFSet.mem_sdiff.mp h).1) hq
  have hpf := ((mem_finiteSubsets_iff _ _).mp ((mem_conditions A p).mp hpA).1).2
  have hqf := ((mem_finiteSubsets_iff _ _).mp ((mem_conditions A q).mp hqA).1).2
  apply (mem_conditions A _).mpr
  constructor
  · apply (mem_finiteSubsets_iff _ _).mpr
    exact ⟨fun z hz => (ZFSet.mem_union.mp hz).elim (fun h => condition_subset A p hpA h) (fun h
      => condition_subset A q hqA h),
      by rw [ZFSet.coe_union]; exact hpf.union hqf⟩
  · intro x hx b hb c hc hxb hxc
    rcases ZFSet.mem_union.mp hxb with hxb|hxb <;>
      rcases ZFSet.mem_union.mp hxc with hxc|hxc
    · exact ((mem_conditions A p).mp hpA).2 x hx b hb c hc hxb hxc
    · exact False.elim ((ZFSet.mem_sdiff.mp (ZFSet.pair_mem_prod.mp (condition_subset (A \ B) q hq
      hxc)).1).2
        (ZFSet.pair_mem_prod.mp (condition_subset B p hp hxb)).1)
    · exact False.elim ((ZFSet.mem_sdiff.mp (ZFSet.pair_mem_prod.mp (condition_subset (A \ B) q hq
      hxb)).1).2
        (ZFSet.pair_mem_prod.mp (condition_subset B p hp hxc)).1)
    · exact ((mem_conditions A q).mp hqA).2 x hx b hb c hc hxb hxc

theorem union_restrict (A B p : ZFSet.{0}) (hp : p ∈ conditions A) :
    restrict B p ∪ restrict (A \ B) p = p := by
  classical
  apply ZFSet.ext; intro z
  rw [ZFSet.mem_union,mem_restrict,mem_restrict]
  constructor
  · exact fun h => h.elim And.left And.left
  · intro hz
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (condition_subset A p hp hz)
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hz,ZFSet.pair_mem_prod.mpr ⟨hxB,hb⟩⟩
    · exact Or.inr ⟨hz,ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_sdiff.mpr ⟨hx,hxB⟩,hb⟩⟩

theorem restrict_union_left (A B p q : ZFSet.{0})
    (hp : p ∈ conditions B) (hq : q ∈ conditions (A \ B)) : restrict B (p ∪ q) = p := by
  apply ZFSet.ext; intro z
  rw [mem_restrict,ZFSet.mem_union]
  constructor
  · rintro ⟨hz,hzB⟩
    rcases hz with hz|hz
    · exact hz
    · obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp hzB
      exact False.elim ((ZFSet.mem_sdiff.mp (ZFSet.pair_mem_prod.mp (condition_subset (A \ B) q hq
        hz)).1).2 hx)
  · intro hz; exact ⟨Or.inl hz,condition_subset B p hp hz⟩

theorem restrict_union_right (A B p q : ZFSet.{0})
    (hp : p ∈ conditions B) (hq : q ∈ conditions (A \ B)) : restrict (A \ B) (p ∪ q) = q := by
  apply ZFSet.ext; intro z
  rw [mem_restrict,ZFSet.mem_union]
  constructor
  · rintro ⟨hz,hzB⟩
    rcases hz with hz|hz
    · obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp hzB
      exact False.elim ((ZFSet.mem_sdiff.mp hx).2 (ZFSet.pair_mem_prod.mp (condition_subset B p hp
        hz)).1)
    · exact hz
  · intro hz; exact ⟨Or.inr hz,condition_subset (A \ B) q hq hz⟩

theorem subset_iff_restrict (A B p q : ZFSet.{0})
    (hp : p ∈ conditions A) (hq : q ∈ conditions A) :
    p ⊆ q ↔ restrict B p ⊆ restrict B q ∧ restrict (A \ B) p ⊆ restrict (A \ B) q := by
  constructor
  · intro h; exact ⟨restrict_mono B p q h,restrict_mono (A \ B) p q h⟩
  · intro h z hz
    rw [←union_restrict A B p hp,ZFSet.mem_union] at hz
    rw [←union_restrict A B q hq,ZFSet.mem_union]
    exact hz.elim (fun hz => Or.inl (h.1 hz)) (fun hz => Or.inr (h.2 hz))

end TuringRigidity.InternalCohenPartition

end OAI
