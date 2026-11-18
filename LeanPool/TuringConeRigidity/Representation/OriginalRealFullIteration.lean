/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OriginalRealFullIteration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CountedOriginalRealQuotient
public import LeanPool.TuringConeRigidity.CohenForcing.CohenFactorIteration

/-!
# Original Real Full Iteration
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OriginalRealFullIteration
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
attribute [local instance] codeOrder codePreorder

theorem original_name_full_iteration (M K : ZFSet.{0})
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
              let D := ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega
              let L := InternalCohenProjectedGeneric.projected _ D
                (fun _ h => (ZFSet.mem_sdiff.mp h).1) G
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
                  AtomicForcing.GroundGeneric
                    (genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier) L ∧
                  genericExtensionSet (genericExtensionSet (RealGeneratedModel.hull M X) q
                    Gq.carrier)
                    (conditions D) L.carrier =
                    genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
                  modelReals (genericExtensionSet
                    (genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier)
                    (conditions D) L.carrier) =
                    modelReals (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega))
                      G.carrier) ∧
                  ∀ p ∈ G.carrier, ∃ r ∈ Gq.carrier,
                    label q r = label _ (InternalCohenFactor.project _ _ hBA p) := by
  obtain ⟨C,hC,hCK,hct,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,hAe,hA,σ,hσ,hBA,hall⟩ :=
    CountedOriginalRealQuotient.original_name_counted_quotient M K hM hT hK τ hτ
  have hω := sourceT_omega_mem M hM hT
  have hKM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  have hCM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hC hω
  refine ⟨C,hC,hCK,hct,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,hAe,hA,σ,hσ,hBA,?_⟩
  intro G hG hreal
  obtain ⟨H,hHG,hval,hHull,hprop,hq,ho,hcount,Gq,hGq,hext,hcode,_,hcond⟩ := hall G hG hreal
  refine ⟨H,hHG,hval,hHull,hprop,hq,ho,hcount,Gq,hGq,hext,hcode,?_,?_,?_,hcond⟩
  · rw [hext]
    exact CohenUntouchedGeneric.untouched_ground_generic M _ _ hM hT hKM hCM hBA G hG
  · rw [hext]
    exact CohenFactorIteration.extension_eq M _ _ hM hT hKM hCM hBA G hG
  · rw [hext]
    exact congrArg modelReals (CohenFactorIteration.extension_eq M _ _ hM hT hKM hCM hBA G hG)

end TuringRigidity.OriginalRealFullIteration

end OAI
