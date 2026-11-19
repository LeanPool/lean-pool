/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CountedOriginalRealQuotient.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OriginalRealQuotientModel
public import LeanPool.TuringConeRigidity.CohenForcing.CountedCohenConditions
public import LeanPool.TuringConeRigidity.SetModels.InternalQuotientCountability

/-!
# Counted Original Real Quotient
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CountedOriginalRealQuotient
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
attribute [local instance] codeOrder codePreorder

theorem original_name_counted_quotient (M K : ZFSet.{0})
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
          ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
            ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
            ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
              AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
              let J := InternalCohenProjectedGeneric.projected _ _ hBA G
              let X := τ.val G.carrier
              ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
                σ.val H.carrier = X ∧
                genericExtensionSet M (positive A) H.carrier = RealGeneratedModel.hull M X ∧
                RealGeneratedModel.Contains M X (RealGeneratedModel.hull M X) ∧
                let q := InternalQuotientConditions.conditions (conditions (ZFSet.prod C
                  ZFSet.omega)) A
                  (genericFilterSet (positive A) H.carrier)
                q ∈ RealGeneratedModel.hull M X ∧ InternalCollapse.orderSet q ∈
                  RealGeneratedModel.hull M X ∧
                InternallyCountable (RealGeneratedModel.hull M X) q ∧
                ∃ Gq : GenericFilter (Conditions q), AtomicForcing.GroundGeneric
                  (RealGeneratedModel.hull M X) Gq ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier =
                    genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericFilterSet q Gq.carrier =
                    genericFilterSet (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier ⊆
                    genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
                  ∀ p ∈ G.carrier, ∃ r ∈ Gq.carrier,
                    label q r = label _ (InternalCohenFactor.project _ _ hBA p) := by
  obtain ⟨C,hC,hCK,hct,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,hAe,hA,σ,hσ,hBA,hall⟩ :=
    OriginalRealQuotientModel.original_name_quotient M K hM hT hK τ hτ
  have hcM := (manyColumn_internal M C hM hT hC).1
  have hcount := CountedCohenConditions.many_column_conditions_countable M C hM hT hC hct
  refine ⟨C,hC,hCK,hct,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,hAe,hA,σ,hσ,hBA,?_⟩
  intro G hG hreal
  obtain ⟨H,hHG,hval,hHull,hprop,hq,ho,Gq,hGq,hext,hcode,hsub,hcond⟩ := hall G hG hreal
  refine ⟨H,hHG,hval,hHull,hprop,hq,ho,?_,Gq,hGq,hext,hcode,hsub,hcond⟩
  apply InternalCountableClosure.countable_subset _ _ _ hprop.1 hprop.2.1
    (hprop.2.2.1 hcM) hq (InternalQuotientConditions.conditions_subset _ A _)
    (InternalQuotientCountability.countability_upward M _ _ hprop.2.2.1 hcount)
  obtain ⟨p,_⟩ := Gq.nonempty
  exact ⟨label _ p,label_mem _ p⟩

end TuringRigidity.CountedOriginalRealQuotient

end OAI
