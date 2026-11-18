/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SameRealBooleanFilter.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanExpressionCoverage
public import LeanPool.TuringConeRigidity.Representation.GenericFilterName
public import LeanPool.TuringConeRigidity.SetModels.InternalProjectedGeneric

/-!
# Same Real Boolean Filter
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SameRealBooleanFilter
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanBits InternalBooleanGeneric
open InternalProjectedGeneric BooleanExpressionCertificate
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder codeOrder
  codePreorder

theorem generated_agreement (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hSB : S ⊆ B)
    (G H : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) (hH : AtomicForcing.GroundGeneric M H)
    (hseed : ∀ U ∈ S, Hit G U ↔ Hit H U) :
    ∀ U ∈ generated c B Q S, Hit G U ↔ Hit H U := by
  intro U hU
  obtain ⟨K,_,_,g,_,hg,t,_,hp⟩ :=
    generated_certificate M c B Q S U hM hT hc hBM hQM hSM hB hQ hSB hU
  exact hg.generic_agreement M c B Q S K g hM hT hc hB hQ G H hG hH hseed t U hp

theorem same_real_hits (M c B Q : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (G H : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) (hH : AtomicForcing.GroundGeneric M H)
    (hGt : ⊤ ∈ G.carrier) (hHt : ⊤ ∈ H.carrier)
    (heq : (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier =
      (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val H.carrier) :
    ∀ U ∈ generated c B Q (seeds c B E), Hit G U ↔ Hit H U := by
  apply generated_agreement M c B Q (seeds c B E) hM hT hc hBM hQM
    (seeds_mem M c B hM hT hc hBM E hE hgraph) hB hQ
    (fun _ h => (ZFSet.mem_sep.mp h).1) G H hG hH
  intro U hU
  obtain ⟨_,n,rfl⟩ := ZFSet.mem_sep.mp hU
  rw [hit_bit_iff M c hM hT hc E hE G hG hGt n,
    hit_bit_iff M c hM hT hc E hE H hH hHt n,heq]

theorem same_real_projected_filter (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G H : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) (hH : AtomicForcing.GroundGeneric M H)
    (hGt : ⊤ ∈ G.carrier) (hHt : ⊤ ∈ H.carrier)
    (heq : (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier =
      (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val H.carrier) :
    genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA H).carrier := by
  have hhit := same_real_hits M c B Q hM hT hc hBM hQM hB hQ E hE hgraph G H hG hH hGt hHt heq
  have hfilters : (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA H).carrier := by
    apply Set.ext; intro q
    change Hit G (label (positive A) q) ↔ Hit H (label (positive A) q)
    apply hhit
    rw [←hAe]
    exact (ZFSet.mem_sep.mp (label_mem (positive A) q)).1
  rw [hfilters]

end TuringRigidity.SameRealBooleanFilter

end OAI
