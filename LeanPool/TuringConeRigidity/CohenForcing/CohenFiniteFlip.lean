/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenFiniteFlip.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenBitFlip
public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseCounting

/-!
# Cohen Finite Flip
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.CohenFiniteFlip
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCollapse
open CohenGroundPoset InternalCohenBitFlip
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- The finite column mask changing the initial segment of `A` to the word `s`. -/
noncomputable def prefixMask (a : ZFSet.{0}) (s : List Bool) (A : Oracle) : ZFSet.{0} :=
  ZFSet.range (fun i : {n : Fin s.length // A n.val ≠ s[n.val]} =>
    ZFSet.pair a (natSet i.val.val))

theorem pair_mem_prefixMask (a : ZFSet.{0}) (s : List Bool) (A : Oracle) (n : ℕ) :
    ZFSet.pair a (natSet n) ∈ prefixMask a s A ↔
      n < s.length ∧ A n ≠ s.getD n false := by
  classical
  rw [prefixMask,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨i,hi⟩,he⟩
    have he' : i.val = n := natSet_injective (ZFSet.pair_inj.mp he).2
    subst n
    exact ⟨i.isLt,by simpa [List.getD,i.isLt] using hi⟩
  · rintro ⟨hn,hd⟩
    exact ⟨⟨⟨n,hn⟩,by simpa [List.getD,hn] using hd⟩,rfl⟩

theorem prefixMask_mem (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (s : List Bool) (A : Oracle) : prefixMask a s A ∈ M := by
  classical
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  apply InternalFiniteSubsets.finite_subset_mem M (ZFSet.prod K ZFSet.omega) _ hM hT hC
  apply (InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mpr
  constructor
  · intro x hx
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.pair_mem_prod.mpr ⟨ha,(mem_omega _).mpr ⟨i.val.val,rfl⟩⟩
  · rw [prefixMask,ZFSet.coe_range]
    exact Set.finite_range _

theorem pair_mem_flip_label (C B : ZFSet.{0}) (p : Conditions (conditions C))
    (x : ZFSet.{0}) (hx : x ∈ C) (b : Bool) :
    ZFSet.pair x (bitSet b) ∈ label _ (flipIso C B p) ↔
      (x ∈ B ∧ ZFSet.pair x (bitSet (!b)) ∈ label _ p) ∨
      (x ∉ B ∧ ZFSet.pair x (bitSet b) ∈ label _ p) := by
  have h := ((pair_flipGraph C B _ _).mp ((flipGraph_spec C B p _).mpr rfl)).2.2 x hx
  cases b
  · exact h.1
  · exact h.2

theorem pair_mem_flip_union (C B : ZFSet.{0}) (G : GenericFilter (Conditions (conditions C)))
    (x : ZFSet.{0}) (hx : x ∈ C) (b : Bool) :
    ZFSet.pair x (bitSet b) ∈ unionGraph (AutomorphismName.mapFilter (flipIso C B) G) ↔
      (x ∈ B ∧ ZFSet.pair x (bitSet (!b)) ∈ unionGraph G) ∨
      (x ∉ B ∧ ZFSet.pair x (bitSet b) ∈ unionGraph G) := by
  constructor
  · intro h
    obtain ⟨q,hq,hbit⟩ := (InternalCollapse.mem_unionGraph _ _).mp h
    let p := (flipIso C B).symm q
    have hq' : q = flipIso C B p := (flipIso C B).apply_symm_apply q |>.symm
    rw [hq',pair_mem_flip_label C B p x hx b] at hbit
    rcases hbit with ⟨hB,hbit⟩ | ⟨hB,hbit⟩
    · exact Or.inl ⟨hB,(InternalCollapse.mem_unionGraph _ _).mpr ⟨p,hq,hbit⟩⟩
    · exact Or.inr ⟨hB,(InternalCollapse.mem_unionGraph _ _).mpr ⟨p,hq,hbit⟩⟩
  · intro h
    rcases h with ⟨hB,hbit⟩ | ⟨hB,hbit⟩
    · obtain ⟨p,hp,hbit⟩ := (InternalCollapse.mem_unionGraph _ _).mp hbit
      exact (InternalCollapse.mem_unionGraph _ _).mpr ⟨flipIso C B p, by simpa
        [AutomorphismName.mapFilter] using hp,
        (pair_mem_flip_label C B p x hx b).mpr (Or.inl ⟨hB,hbit⟩)⟩
    · obtain ⟨p,hp,hbit⟩ := (InternalCollapse.mem_unionGraph _ _).mp hbit
      exact (InternalCollapse.mem_unionGraph _ _).mpr ⟨flipIso C B p, by simpa
        [AutomorphismName.mapFilter] using hp,
        (pair_mem_flip_label C B p x hx b).mpr (Or.inr ⟨hB,hbit⟩)⟩

end TuringRigidity.CohenFiniteFlip

end OAI
