/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenUnusedColumns.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalUncountableComplement
public import LeanPool.TuringConeRigidity.SetModels.InternalProductBijection
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenReindex
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenColumnReading

/-!
# Internal Cohen Unused Columns
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenUnusedColumns
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalCountableOrdinals InternalUncountableComplement InternalProductBijection
open CohenGroundPoset InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem unused_columns_forcing (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C) :
    ∃ f ∈ M, FunctionGraph (K \ C) K f ∧
      (∀ x ∈ K \ C, ∀ x' ∈ K \ C, ∀ y ∈ K,
        ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') ∧
      (∀ y ∈ K, ∃ x ∈ K \ C, ZFSet.pair x y ∈ f) ∧
      productGraph (K \ C) K ZFSet.omega f ∈ M ∧
      ∃ e : Conditions (conditions (ZFSet.prod (K \ C) ZFSet.omega)) ≃o
          Conditions (conditions (ZFSet.prod K ZFSet.omega)),
        ∃ g ∈ M, (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ g ↔ q = e p) ∧
          conditions (ZFSet.prod (K \ C) ZFSet.omega) ∈ M ∧
          InternalCollapse.orderSet (conditions (ZFSet.prod (K \ C) ZFSet.omega)) ∈ M ∧
          conditions (ZFSet.prod K ZFSet.omega) ∈ M ∧
          InternalCollapse.orderSet (conditions (ZFSet.prod K ZFSet.omega)) ∈ M := by
  obtain ⟨f,hfM,hf,hi,hs⟩ := complement_bijection M K C hM hT hK hC hCK hct
  have hD := difference_mem M K C hM hT hK.2.1 hC
  have hω := sourceT_omega_mem M hM hT
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hD hω
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hK.2.1 hω
  have hF := productGraph_mem M (K \ C) K ZFSet.omega f hM hT hD hK.2.1 hω hfM
  obtain ⟨e,hg,hge,horders⟩ := InternalCohenReindex.internal_reindex M _ _ _ hM hT hA hB hF
    (productGraph_function _ _ _ _ hf) (productGraph_injective _ _ _ _ hi) (productGraph_onto _ _
      _ _ hs)
  exact ⟨f,hfM,hf,hi,hs,hF,e,_,hg,hge,horders⟩

theorem column_reading_with_unused_forcing (M K : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
    ∃ C ∈ M, ∃ _hCK : C ⊆ K, (C = ∅ ∨ InternallyCountable M C) ∧
      ∃ e : Conditions (conditions (ZFSet.prod (K \ C) ZFSet.omega)) ≃o
          Conditions (conditions (ZFSet.prod K ZFSet.omega)),
        ∃ g ∈ M, (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ g ↔ q = e p) ∧
        ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
          (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
          (InternalNiceName.nice E : Name (Conditions (conditions (ZFSet.prod C
            ZFSet.omega)))).encode
            (label (conditions (ZFSet.prod C ZFSet.omega))) ∈ M ∧
          ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
          ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
            AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
            AtomicForcing.GroundGeneric M (projected _ _ hBA G) ∧
            (InternalNiceName.nice E : Name (Conditions (conditions (ZFSet.prod C
              ZFSet.omega)))).val
              (projected _ _ hBA G).carrier = τ.val G.carrier ∧
            τ.val G.carrier ∈ genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega))
              (projected _ _ hBA G).carrier ∧
            ∀ p ∈ G.carrier, project _ _ hBA p ∈ (projected _ _ hBA G).carrier := by
  obtain ⟨C,hC,hCK,hct,E,hE,hEn,hname,hBA,hval⟩ :=
    InternalCohenColumnReading.internal_column_reading M K hM hT hK.2.1 τ hτ
  obtain ⟨_,_,_,_,_,_,e,g,hg,hge,_⟩ := unused_columns_forcing M K C hM hT hK hC hCK hct
  exact ⟨C,hC,hCK,hct,e,g,hg,hge,E,hE,hEn,hname,hBA,hval⟩

end TuringRigidity.InternalCohenUnusedColumns

end OAI
