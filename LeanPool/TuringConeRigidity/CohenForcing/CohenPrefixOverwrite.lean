/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenPrefixOverwrite.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenFiniteFlip
public import LeanPool.TuringConeRigidity.Effective.FiniteOverwrite

/-!
# Cohen Prefix Overwrite
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.CohenFiniteFlip
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCollapse
open CohenGroundPoset InternalCohenBitFlip CohenColumnRealName FiniteOverwrite
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

noncomputable def prefixFilter (K a : ZFSet.{0}) (s : List Bool) (A : Oracle)
    (G : GenericFilter (Conditions (poset K))) : GenericFilter (Conditions (poset K)) :=
  AutomorphismName.mapFilter (flipIso (ZFSet.prod K ZFSet.omega) (prefixMask a s A)) G

theorem prefixFilter_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (s : List Bool) (A : Oracle)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (hv : (realName K a).val G.carrier = realCode A) :
    (realName K a).val (prefixFilter K a s A G).carrier = realCode (overwrite s A) := by
  obtain ⟨B,hB,hbits,_⟩ := generic_real_value M K a hM hT hK ha G hG
  have hBA : B = A := realCode_injective (hB.symm.trans hv)
  subst B
  apply val_realName K a _ (overwrite s A)
  intro n b
  rw [prefixFilter,pair_mem_flip_union _ _ G _
    (ZFSet.pair_mem_prod.mpr ⟨ha,(mem_omega _).mpr ⟨n,rfl⟩⟩) b,
    pair_mem_prefixMask,hbits n (!b),hbits n b]
  by_cases hn : n < s.length <;> cases hA : A n <;>
    cases hs : s.getD n false <;> cases b <;> simp only [overwrite,hn,hA,hs] <;> decide

theorem prefixFilter_properties (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (s : List Bool) (A : Oracle)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (hv : (realName K a).val G.carrier = realCode A) :
    AtomicForcing.GroundGeneric M (prefixFilter K a s A G) ∧
      genericExtensionSet M (poset K) (prefixFilter K a s A G).carrier =
        genericExtensionSet M (poset K) G.carrier ∧
      (realName K a).val (prefixFilter K a s A G).carrier = realCode (overwrite s A) := by
  let C := ZFSet.prod K ZFSet.omega
  let B := prefixMask a s A
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hc := (manyColumn_internal M K hM hT hK).1
  have hf := flipGraph_mem M C B hM hT hC (prefixMask_mem M K a hM hT hK ha s A)
  exact ⟨InternalOrderIsoTransport.map_ground_generic M (poset K) (poset K) (flipGraph C B)
      hM hT hc hc hf (flipIso C B) (flipGraph_spec C B) G hG,
    InternalOrderIsoTransport.extension_eq M (poset K) (poset K) (flipGraph C B)
      hM hT hc hc hf (flipIso C B) (flipGraph_spec C B) G hG,
    prefixFilter_value M K a hM hT hK ha s A G hG hv⟩

end TuringRigidity.CohenFiniteFlip

end OAI
