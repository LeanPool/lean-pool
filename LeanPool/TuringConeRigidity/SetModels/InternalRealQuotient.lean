/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalRealQuotient.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.RealGeneratedPart
public import LeanPool.TuringConeRigidity.CohenForcing.QuotientNames
public import LeanPool.TuringConeRigidity.CohenForcing.CohenInternalDecision
public import LeanPool.TuringConeRigidity.SetModels.InternalNiceName

/-!
# Internal Real Quotient
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalRealQuotient
open Set CountableForcing TransitiveNameModel BoundedSetTheory RecursiveNames
open ForcingProjection RegularCompletion BooleanProjection
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Read the set-coded tag families as sets of condition-label elements. -/
def tags (c : ZFSet.{0}) (E : ℕ → ZFSet.{0}) : ℕ → Set (Conditions c) :=
  fun n => {p | label c p ∈ E n}

theorem label_below (c U : ZFSet.{0}) (hUc : U ⊆ c) (p : Conditions c) :
    label c p ∈ CohenInternalDecision.below c U ↔
      p ∈ RealGeneratedPart.tagLower {q | label c q ∈ U} := by
  rw [CohenInternalDecision.below,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,hqp⟩
    obtain ⟨q,rfl⟩ := label_surjective c (hUc hq)
    exact ⟨q,hq,hqp⟩
  · rintro ⟨q,hq,hpq⟩
    exact ⟨label_mem c p,label c q,hq,hpq⟩

theorem label_decision (c : ZFSet.{0}) (E : ℕ → ZFSet.{0})
    (hEc : ∀ n, E n ⊆ c) (n : ℕ) (p : Conditions c) :
    label c p ∈ CohenInternalDecision.decision c (CohenInternalDecision.below c (E n)) (E n) ↔
      p ∈ RealGeneratedPart.decision (tags c E) n := by
  rw [CohenInternalDecision.decision,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,hp | hp⟩
    · obtain ⟨q,hq,hqp⟩ := hp
      obtain ⟨q,rfl⟩ := label_surjective c (hEc n hq)
      exact Or.inl ⟨q,hq,hqp⟩
    · apply Or.inr
      apply (mem_compl _ p).mpr
      intro q hqp hq
      exact hp (label c q) ((label_below c (E n) (hEc n) q).mpr hq) hqp
  · intro hp
    refine ⟨label_mem c p,?_⟩
    rcases hp with ⟨q,hq,hpq⟩ | hp
    · exact Or.inl ⟨label c q,hq,hpq⟩
    · apply Or.inr
      intro q hq hpq
      obtain ⟨q,rfl⟩ := label_surjective c (ZFSet.mem_sep.mp hq).1
      exact (mem_compl _ p).mp hp q hpq ((label_below c (E n) (hEc n) q).mp hq)

theorem ground_generic_decisions (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    GenericFor (RealGeneratedPart.decision (tags c E)) G := by
  intro n
  let D := CohenInternalDecision.decision c (CohenInternalDecision.below c (E n)) (E n)
  have hDM : D ∈ M := CohenInternalDecision.decision_mem M c _ _ hM hT hc
    (CohenInternalDecision.below_mem M c _ hM hT hc (hE n).1) (hE n).1
  have hd : Dense {p : Conditions c | label c p ∈ D} := by
    intro p
    obtain ⟨q,hqp,hq⟩ := RealGeneratedPart.decision_dense (tags c E) n p
    exact ⟨q,hqp,(label_decision c E (fun n => (hE n).2) n q).mpr hq⟩
  obtain ⟨p,hp,hpD⟩ := hG D hDM hd
  exact ⟨p,hp,(label_decision c E (fun n => (hE n).2) n p).mp hpD⟩

theorem nice_value_iff {c : ZFSet.{0}} [Top (Conditions c)]
    (E : ℕ → ZFSet.{0}) (G : GenericFilter (Conditions c)) (hTop : ⊤ ∈ G.carrier) (n : ℕ) :
    natSet n ∈ (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ↔
      n ∈ RealGeneratedPart.value (tags c E) G := by
  rw [InternalNiceName.mem_val_nice E G.carrier hTop]
  constructor
  · rintro ⟨m,p,hp,hpE,hmn⟩
    have he := natSet_injective hmn
    subst m
    exact ⟨p,hp,hpE⟩
  · rintro ⟨p,hp,hpE⟩
    exact ⟨n,p,hp,hpE,rfl⟩

theorem projected_nice_bit (M c : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hTop : ⊤ ∈ G.carrier) (n : ℕ) :
    (∃ hn : RealGeneratedPart.bit (tags c E) n ≠ ⊥,
      (⟨RealGeneratedPart.bit (tags c E) n,RealGeneratedPart.bit_mem_part (tags c E) n,hn⟩ :
        PartPositive (RealGeneratedPart.part (tags c E))) ∈
        (imageFilter (RealGeneratedPart.projection (tags c E)) G).carrier) ↔
      natSet n ∈ (InternalNiceName.nice E : Name (Conditions c)).val G.carrier := by
  rw [RealGeneratedPart.projected_bit_iff _ G
    (ground_generic_decisions M c hM hT hc E hE G hG),nice_value_iff E G hTop]

theorem original_name_value (c : ZFSet.{0}) (E : ℕ → ZFSet.{0})
    (G : GenericFilter (Conditions c)) (τ : Name (Conditions c)) :
    (QuotientNames.restrict (RealGeneratedPart.projection (tags c E))
      (imageFilter (RealGeneratedPart.projection (tags c E)) G) τ).val
      (quotientFilter (RealGeneratedPart.projection (tags c E)) G).carrier = τ.val G.carrier :=
  QuotientNames.original_val_restrict _ G τ

end TuringRigidity.InternalRealQuotient

end OAI
