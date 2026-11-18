/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenBooleanReading.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanIntermediate
public import LeanPool.TuringConeRigidity.SetModels.InternalColumnExtension
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenColumnReading

/-!
# Internal Cohen Boolean Reading
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenBooleanReading
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
attribute [local instance] codeOrder codePreorder

/-- Boolean reading retaining the projected generic filter and canonical name value. -/
theorem original_name_boolean_intermediate_with_reading (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M)
    (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
    ∃ C ∈ M, ∃ _hCK : C ⊆ K, (C = ∅ ∨ InternallyCountable M C) ∧
      ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
        (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
        ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
          (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode (conditions (ZFSet.prod C ZFSet.omega)) U) ∧
          (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
          A = InternalGeneratedAlgebra.generated (conditions (ZFSet.prod C ZFSet.omega)) B Q
            (InternalBooleanBits.seeds (conditions (ZFSet.prod C ZFSet.omega)) B E) ∧
          Closed (conditions (ZFSet.prod C ZFSet.omega)) B Q A ∧
          positive A ∈ M ∧ InternalBooleanGraph.inclusionOrder (positive A) ∈ M ∧
          ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
            ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
            ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
              AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
              AtomicForcing.GroundGeneric M
                (InternalCohenProjectedGeneric.projected _ _ hBA G) ∧
              (InternalNiceName.nice E : Name (Conditions
                (conditions (ZFSet.prod C ZFSet.omega)))).val
                (InternalCohenProjectedGeneric.projected _ _ hBA G).carrier = τ.val G.carrier ∧
              ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
                (∀ q, q ∈ H.carrier ↔ InternalBooleanGeneric.Hit
                  (InternalCohenProjectedGeneric.projected _ _ hBA G) (label (positive A) q)) ∧
                σ.val H.carrier = τ.val G.carrier ∧
                Transitive (genericExtensionSet M (positive A) H.carrier) ∧
                SourceT (genericExtensionSet M (positive A) H.carrier) ∧
                M ⊆ genericExtensionSet M (positive A) H.carrier ∧
                τ.val G.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
                genericFilterSet (positive A) H.carrier ∈ genericExtensionSet M (positive A)
                  H.carrier ∧
                genericExtensionSet M (positive A) H.carrier ⊆
                  genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
                ∀ p ∈ G.carrier, ∃ q ∈ H.carrier,
                  label (positive A) q = InternalBooleanProjection.project
                    (conditions (ZFSet.prod C ZFSet.omega)) A
                    (InternalBooleanDense.basicCode (conditions (ZFSet.prod C ZFSet.omega))
                      (label _ (InternalCohenFactor.project _ _ hBA p))) := by
  obtain ⟨C,hCM,hCK,hcount,E,hgraph,hE,_,hBA,hread⟩ :=
    InternalCohenColumnReading.internal_column_reading M K hM hT hK τ hτ
  have hω := sourceT_omega_mem M hM hT
  have hKM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  have hDM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hCM hω
  have hcM := conditions_mem M _ hM hT hDM
  obtain ⟨B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,σ,hσ,hall⟩ :=
    InternalBooleanIntermediate.internal_boolean_intermediate M _ hM hT hcM E hE hgraph
  refine ⟨C,hCM,hCK,hcount,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,
    positive_mem M A hM hT hAM,(projected_order_code M A hM hT hAM).1,σ,hσ,hBA,?_⟩
  intro G hG hreal
  obtain ⟨hJG,hJval,_,_⟩ := hread G hG hreal
  refine ⟨hJG,hJval,?_⟩
  let J := InternalCohenProjectedGeneric.projected _ _ hBA G
  obtain ⟨p,hp⟩ := J.nonempty
  have hJtop : ⊤ ∈ J.carrier := J.upper le_top hp
  obtain ⟨H,hHG,hhit,hval,hN,hTN,hMN,hXN,hHN,hNJ⟩ := hall J hJG hJtop
  have hv : σ.val H.carrier = τ.val G.carrier := hval.trans hJval
  refine ⟨H,hHG,hhit,hv,hN,hTN,hMN,hv ▸ hXN,hHN,?_,?_⟩
  · intro x hx
    exact InternalColumnExtension.column_extension_subset M _ _ hM hT hKM hDM hBA G hG (hNJ hx)
  · intro p hp
    have hpJ := InternalCohenProjectedGeneric.projected_contains _ _ hBA G hp
    obtain ⟨q,hq,he⟩ := InternalSameNameGeneric.projected_condition M _ B Q A
      hM hT hcM hBM hAM hB hQ hA J _ hpJ
    exact ⟨q,(hhit q).mpr hq,he⟩

theorem original_name_boolean_intermediate (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M)
    (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
    ∃ C ∈ M, ∃ _hCK : C ⊆ K, (C = ∅ ∨ InternallyCountable M C) ∧
      ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
        (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
        ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
          (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode (conditions (ZFSet.prod C ZFSet.omega)) U) ∧
          (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
          A = InternalGeneratedAlgebra.generated (conditions (ZFSet.prod C ZFSet.omega)) B Q
            (InternalBooleanBits.seeds (conditions (ZFSet.prod C ZFSet.omega)) B E) ∧
          Closed (conditions (ZFSet.prod C ZFSet.omega)) B Q A ∧
          positive A ∈ M ∧ InternalBooleanGraph.inclusionOrder (positive A) ∈ M ∧
          ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
            ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
            ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
              AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
              ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
                (∀ q, q ∈ H.carrier ↔ InternalBooleanGeneric.Hit
                  (InternalCohenProjectedGeneric.projected _ _ hBA G) (label (positive A) q)) ∧
                σ.val H.carrier = τ.val G.carrier ∧
                Transitive (genericExtensionSet M (positive A) H.carrier) ∧
                SourceT (genericExtensionSet M (positive A) H.carrier) ∧
                M ⊆ genericExtensionSet M (positive A) H.carrier ∧
                τ.val G.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
                genericFilterSet (positive A) H.carrier ∈ genericExtensionSet M (positive A)
                  H.carrier ∧
                genericExtensionSet M (positive A) H.carrier ⊆
                  genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
                ∀ p ∈ G.carrier, ∃ q ∈ H.carrier,
                  label (positive A) q = InternalBooleanProjection.project
                    (conditions (ZFSet.prod C ZFSet.omega)) A
                    (InternalBooleanDense.basicCode (conditions (ZFSet.prod C ZFSet.omega))
                      (label _ (InternalCohenFactor.project _ _ hBA p))) := by
  obtain ⟨C,hCM,hCK,hcount,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,
    hB,hQ,heq,hA,hpos,horder,σ,hσ,hBA,hall⟩ :=
    original_name_boolean_intermediate_with_reading M K hM hT hK τ hτ
  exact ⟨C,hCM,hCK,hcount,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,
    hB,hQ,heq,hA,hpos,horder,σ,hσ,hBA,
    fun G hG hreal => (hall G hG hreal).2.2⟩

end TuringRigidity.InternalCohenBooleanReading

end OAI
