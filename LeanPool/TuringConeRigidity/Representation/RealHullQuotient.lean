/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RealHullQuotient.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.RealGeneratedModel
public import LeanPool.TuringConeRigidity.SetModels.InternalQuotientExtension

/-!
# Real Hull Quotient
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RealHullQuotient
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalGeneratedAlgebra InternalProjectedGeneric InternalQuotientGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem quotient_over_hull (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈
      G.carrier) :
    let X := (InternalNiceName.nice E : Name (Conditions c)).val G.carrier
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
    let K := quotient M c B Q A hM hT hc hBM hAM hB hQ hA G
    q ∈ RealGeneratedModel.hull M X ∧ InternalCollapse.orderSet q ∈ RealGeneratedModel.hull M X ∧
      AtomicForcing.GroundGeneric (RealGeneratedModel.hull M X) K ∧
      genericExtensionSet (RealGeneratedModel.hull M X) q K.carrier = genericExtensionSet M c
        G.carrier ∧
      genericFilterSet q K.carrier = genericFilterSet c G.carrier ∧
      ∀ p ∈ G.carrier, ∃ r ∈ K.carrier, label q r = label c p := by
  have he := RealGeneratedModel.projected_extension_eq_hull M c B Q A
    hM hT hc hBM hQM hAM hB hQ hA E hE hgraph hAe G hG hGt
  obtain ⟨_,_,_,_,hq,ho⟩ := InternalQuotientExtension.intermediate_properties M c B Q A
    hM hT hc hBM hAM hB hQ hA G hG
  dsimp only
  rw [←he]
  exact ⟨hq,ho,quotient_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG,
    InternalQuotientExtension.extension_eq M c B Q A hM hT hc hBM hAM hB hQ hA G hG hGt,
    RestrictedForcingFilter.filterSet_eq c _ (InternalQuotientConditions.conditions_subset c A _) G
      (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G),
    RestrictedForcingFilter.original_condition c _ (InternalQuotientConditions.conditions_subset c
      A _) G
      (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G)⟩

theorem own_reals_eq (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈
      G.carrier) :
    let X := (InternalNiceName.nice E : Name (Conditions c)).val G.carrier
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
    let K := quotient M c B Q A hM hT hc hBM hAM hB hQ hA G
    modelReals (genericExtensionSet (RealGeneratedModel.hull M X) q K.carrier) =
      modelReals (genericExtensionSet M c G.carrier) := by
  have he := (quotient_over_hull M c B Q A hM hT hc hBM hQM hAM hB hQ hA E hE hgraph hAe G hG
    hGt).2.2.2.1
  exact congrArg modelReals he

end TuringRigidity.RealHullQuotient

end OAI
