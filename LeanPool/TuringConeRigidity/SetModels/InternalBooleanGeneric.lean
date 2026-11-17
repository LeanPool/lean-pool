/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanBits

/-!
# Internal Boolean Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def Hit {c : ZFSet.{0}} (G : GenericFilter (Conditions c)) (U : ZFSet.{0}) : Prop :=
  ∃ p ∈ G.carrier, label c p ∈ U

noncomputable def decision (c U : ZFSet.{0}) : ZFSet.{0} := U ∪ neg c U

theorem decision_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : decision c U ∈ M :=
  binary_union_mem M hM hT.pairing hT.union hU (neg_mem M c U hM hT hc hU)

theorem decision_dense (c U : ZFSet.{0}) (hUc : U ⊆ c) :
    Dense {p : Conditions c | label c p ∈ decision c U} := by
  classical
  intro p
  by_cases h : ∃ q ∈ U, label c p ⊆ q
  · obtain ⟨q,hq,hpq⟩ := h
    obtain ⟨q,rfl⟩ := label_surjective c (hUc hq)
    exact ⟨q,hpq,ZFSet.mem_union.mpr (Or.inl hq)⟩
  · refine ⟨p,le_rfl,ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sep.mpr ⟨label_mem c p,?_⟩))⟩
    intro q hq hpq
    exact h ⟨q,hq,hpq⟩

theorem generic_decision (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (hUc : U ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G U ∨ Hit G (neg c U) := by
  obtain ⟨p,hp,hpd⟩ := hG (decision c U) (decision_mem M c U hM hT hc hU) (decision_dense c U hUc)
  rcases ZFSet.mem_union.mp hpd with h | h
  · exact Or.inl ⟨p,hp,h⟩
  · exact Or.inr ⟨p,hp,h⟩

theorem hit_neg_excludes (c U : ZFSet.{0}) (hU : Lower c U)
    (G : GenericFilter (Conditions c)) (hn : Hit G (neg c U)) : ¬ Hit G U := by
  rintro ⟨q,hq,hqU⟩
  obtain ⟨p,hp,hpN⟩ := hn
  obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
  have hrU := hU _ hqU _ (label_mem c r) hrq
  exact (ZFSet.mem_sep.mp hpN).2 (label c r) hrU hrp

theorem hit_complement_iff (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hUM : U ∈ M) (hU : IsCode c U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G (neg c U) ↔ ¬ Hit G U := by
  constructor
  · exact hit_neg_excludes c U (code_lower c U hU) G
  · intro hn
    exact (generic_decision M c U hM hT hc hUM hU.1 G hG).resolve_left hn

theorem hit_regular_iff (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hUM : U ∈ M) (hUc : U ⊆ c) (hU : Lower c U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G (regular c U) ↔ Hit G U := by
  constructor
  · intro hr
    rcases generic_decision M c U hM hT hc hUM hUc G hG with hp | hn
    · exact hp
    · exact False.elim (hit_neg_excludes c (neg c U) (neg_lower c U) G hr hn)
  · rintro ⟨p,hp,hpU⟩
    exact ⟨p,hp,subset_regular c U hUc hU hpU⟩

theorem hit_supCode_iff (M c F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hFM : F ∈ M) (hF : ∀ U ∈ F, IsCode c U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G (supCode c F) ↔ ∃ U ∈ F, Hit G U := by
  rw [supCode,hit_regular_iff M c _ hM hT hc (union_mem M hM hT.union hFM)
    (union_subset c F hF) (union_lower c F (fun U hU => code_lower c U (hF U hU))) G hG]
  constructor
  · rintro ⟨p,hp,hpF⟩
    obtain ⟨U,hU,hpU⟩ := ZFSet.mem_sUnion.mp hpF
    exact ⟨U,hU,p,hp,hpU⟩
  · rintro ⟨U,hU,p,hp,hpU⟩
    exact ⟨p,hp,ZFSet.mem_sUnion.mpr ⟨U,hU,hpU⟩⟩

theorem hit_bit_iff (M c : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hTop : ⊤ ∈ G.carrier) (n : ℕ) :
    Hit G (bitCode c (E n)) ↔
      natSet n ∈ (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier := by
  have he := InternalBooleanBits.interpret_bit c E (fun n => (hE n).2) n
  have hv : Hit G (bitCode c (E n)) ↔
      ∃ p ∈ G.carrier, p ∈ (RealGeneratedPart.bit (InternalRealQuotient.tags c E) n : LowerSet
        (Conditions c)) := by
    change (∃ p ∈ G.carrier, p ∈ (interpret c (bitCode c (E n)) (regular_isCode c _) : LowerSet
      (Conditions c))) ↔ _
    rw [he]
  rw [hv,RealGeneratedPart.bit_hit_iff _ G
    (InternalRealQuotient.ground_generic_decisions M c hM hT hc E hE G hG)]
  exact (InternalRealQuotient.nice_value_iff E G hTop n).symm

end TuringRigidity.InternalBooleanGeneric

end OAI
