/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalSameNameGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalProjectedGeneric

/-!
# Internal Same Name Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalSameNameGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense
open InternalBooleanBits InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem projected_bit_iff (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (hbits : ∀ n, bitCode c (E n) ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hTop : ⊤ ∈ G.carrier) (n : ℕ) :
    (∃ q ∈ (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier,
      label (positive A) q = bitCode c (E n)) ↔
        natSet n ∈ (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier :=
          by
  rw [← hit_bit_iff M c hM hT hc E hE G hG hTop n]
  constructor
  · rintro ⟨q,hq,he⟩
    change Hit G (label (positive A) q) at hq
    rwa [he] at hq
  · intro h
    obtain ⟨p,hp,hpb⟩ := h
    have hn : bitCode c (E n) ≠ ∅ := fun h0 => ZFSet.notMem_empty _ (h0 ▸ hpb)
    obtain ⟨q,hq⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hbits n,hn⟩)
    refine ⟨q,?_,hq⟩
    change Hit G (label (positive A) q)
    rw [hq]
    exact ⟨p,hp,hpb⟩

theorem projected_condition (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (p : Conditions c) (hp : p ∈ G.carrier) :
    ∃ q ∈ (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier,
      label (positive A) q = project c A (basicCode c (label c p)) := by
  let b := basicCode c (label c p)
  have hbM := basicCode_mem M c _ hM hT hc (label_mem c p)
  have hbc : IsCode c b := regular_isCode c _
  have hpb := subset_project c A b hbc.1 (mem_basicCode c _ (label_mem c p))
  have hPA := project_mem_part M c B Q A b hM hT hc hBM hAM hbM hB hQ hA
  have hn : project c A b ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ hpb)
  obtain ⟨q,hq⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hPA,hn⟩)
  refine ⟨q,?_,hq⟩
  change Hit G (label (positive A) q)
  rw [hq]
  exact ⟨p,hp,hpb⟩

theorem internal_same_name_generic (M c : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) :
    ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
      (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
      A = generated c B Q (seeds c B E) ∧ Closed c B Q A ∧
      positive A ∈ M ∧ InternalBooleanGraph.inclusionOrder (positive A) ∈ M ∧
      InternalBooleanGraph.graph c B A ∈ M ∧
      ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G → ⊤ ∈ G.carrier →
        ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
          (∀ n, (∃ q ∈ H.carrier, label (positive A) q = bitCode c (E n)) ↔
            natSet n ∈ (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val
              G.carrier) ∧
          ∀ p ∈ G.carrier, ∃ q ∈ H.carrier,
            label (positive A) q = project c A (basicCode c (label c p)) := by
  obtain ⟨B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,hbits,_⟩ :=
    internal_bit_generated_part M c hM hT hc E hE hgraph
  refine ⟨B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,positive_mem M A hM hT hAM,
    (projected_order_code M A hM hT hAM).1,InternalBooleanGraph.graph_mem M c B A hM hT hc hBM
      hAM,?_⟩
  intro G hG hTop
  refine ⟨projected M c B Q A hM hT hc hBM hAM hB hQ hA G,
    projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG,?_,?_⟩
  · exact fun n => projected_bit_iff M c B Q A hM hT hc hBM hAM hB hQ hA E hE hbits G hG hTop n
  · exact fun p hp => projected_condition M c B Q A hM hT hc hBM hAM hB hQ hA G p hp

end TuringRigidity.InternalSameNameGeneric

end OAI
