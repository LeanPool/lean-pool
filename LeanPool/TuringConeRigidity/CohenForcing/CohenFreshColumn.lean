/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenFreshColumn.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalSingletonColumn
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenUnusedColumns

/-!
# Cohen Fresh Column
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenFreshColumn
open TransitiveNameModel BoundedSetTheory InternalCountableOrdinals InternalCountableClosure
open InternalUncountableComplement CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem product_difference (K C W : ZFSet.{0}) :
    ZFSet.prod K W \ ZFSet.prod C W = ZFSet.prod (K \ C) W := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨hzK,hzC⟩ := ZFSet.mem_sdiff.mp hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hzK
    exact ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_sdiff.mpr ⟨hx,fun h =>
      hzC (ZFSet.pair_mem_prod.mpr ⟨h,hn⟩)⟩,hn⟩
  · intro hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨hxK,hxC⟩ := ZFSet.mem_sdiff.mp hx
    exact ZFSet.mem_sdiff.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hxK,hn⟩,
      fun h => hxC (ZFSet.pair_mem_prod.mp h).1⟩

theorem difference_singleton (K C a : ZFSet.{0}) :
    (K \ C) \ {a} = K \ insert a C := by
  apply ZFSet.ext; intro z
  simp only [ZFSet.mem_sdiff,ZFSet.mem_singleton,ZFSet.mem_insert_iff]
  tauto

theorem fresh_column (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C) :
    ∃ a ∈ K \ C,
      ZFSet.prod {a} ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega ∧
      (ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega) \ ZFSet.prod {a} ZFSet.omega =
        ZFSet.prod (K \ insert a C) ZFSet.omega ∧
      ∃ e : Conditions (conditions (ZFSet.prod {a} ZFSet.omega)) ≃o Conditions (conditions
        ZFSet.omega),
      ∃ f ∈ M, (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ f ↔ q = e p) ∧
      ∃ eR : Conditions (conditions (ZFSet.prod (K \ insert a C) ZFSet.omega)) ≃o
          Conditions (conditions (ZFSet.prod K ZFSet.omega)),
      ∃ g ∈ M, ∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ g ↔ q = eR p := by
  classical
  have hunc := difference_uncountable M K C hM hT hK.2.1 hK.2.2.1 hC hCK hct
  have hne : ∃ a, a ∈ K \ C := by
    by_contra hn
    apply hunc; left
    apply ZFSet.ext; intro a
    exact ⟨fun ha => False.elim (hn ⟨a,ha⟩),fun ha => False.elim (ZFSet.notMem_empty a ha)⟩
  obtain ⟨a,ha⟩ := hne
  have haK := (ZFSet.mem_sdiff.mp ha).1
  have haM := hM K hK.2.1 a haK
  have hCi : insert a C ∈ M := by
    have hi : insert a C = ({a} : ZFSet.{0}) ∪ C := by
      apply ZFSet.ext; intro z
      simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
    rw [hi]
    exact binary_union_mem M hM hT.pairing hT.union (singleton_mem M hM hT.pairing haM) hC
  have hiK : insert a C ⊆ K := by
    intro x hx
    exact (ZFSet.mem_insert_iff.mp hx).elim (fun he => he ▸ haK) (fun hx => hCK hx)
  obtain ⟨e,f,hf,hfe⟩ := InternalSingletonColumn.internal_column_iso M a hM hT haM
  obtain ⟨_,_,_,_,_,_,eR,g,hg,hge,_⟩ := InternalCohenUnusedColumns.unused_columns_forcing
    M K (insert a C) hM hT hK hCi hiK (Or.inr (countable_insert M C a hM hT hC haM hct))
  refine ⟨a,ha,?_,?_,e,f,hf,hfe,eR,g,hg,hge⟩
  · intro z hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
    have hx_eq : x = a := ZFSet.mem_singleton.mp hx
    subst x
    rw [product_difference]
    exact ZFSet.pair_mem_prod.mpr ⟨ha,hn⟩
  · rw [product_difference,product_difference,difference_singleton]

end TuringRigidity.CohenFreshColumn

end OAI
