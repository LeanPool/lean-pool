/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OriginalRealQuotientModel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.RealHullQuotient
public import LeanPool.TuringConeRigidity.Representation.OriginalRealGeneratedModel

/-!
# Original Real Quotient Model
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OriginalRealQuotientModel
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
attribute [local instance] codeOrder codePreorder

theorem original_name_quotient (M K : ZFSet.{0})
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
  obtain ⟨C,hCM,hCK,hcount,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,
    hB,hQ,heq,hA,hpos,horder,σ,hσ,hBA,hall⟩ :=
    OriginalRealGeneratedModel.original_name_hull_with_reading M K hM hT hK τ hτ
  have hω := sourceT_omega_mem M hM hT
  have hKM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  have hDM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hCM hω
  have hcM := conditions_mem M _ hM hT hDM
  refine ⟨C,hCM,hCK,hcount,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,σ,hσ,hBA,?_⟩
  intro G hG hreal
  obtain ⟨hJG,hJval,H,hHG,hhit,hv,hHull,hprop,_,_,_⟩ := hall G hG hreal
  let J := InternalCohenProjectedGeneric.projected _ _ hBA G
  obtain ⟨p,hp⟩ := J.nonempty
  have hJtop : ⊤ ∈ J.carrier := J.upper le_top hp
  have hcar : H.carrier = (projected M _ B Q A hM hT hcM hBM hAM hB hQ hA J).carrier :=
    Set.ext (fun q => hhit q)
  refine ⟨H,hHG,hv,hHull,hprop,?_⟩
  dsimp only
  rw [hcar]
  have hfactor := RealHullQuotient.quotient_over_hull M _ B Q A hM hT hcM hBM hQM hAM hB hQ hA
    E hE hgraph heq J hJG hJtop
  dsimp only at hfactor
  rw [hJval] at hfactor
  obtain ⟨hq,ho,hGq,hext,hcode,hcond⟩ := hfactor
  refine ⟨hq,ho,InternalQuotientGeneric.quotient M _ B Q A hM hT hcM hBM hAM hB hQ hA J,
    hGq,hext,hcode,?_,?_⟩
  · rw [hext]
    exact InternalColumnExtension.column_extension_subset M _ _ hM hT hKM hDM hBA G hG
  · intro p hp
    exact hcond _ (InternalCohenProjectedGeneric.projected_contains _ _ hBA G hp)

end TuringRigidity.OriginalRealQuotientModel

end OAI
