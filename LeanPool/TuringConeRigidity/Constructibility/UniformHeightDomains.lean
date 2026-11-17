/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformHeightDomains.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GroundSeedOrdinalHeight
public import LeanPool.TuringConeRigidity.Constructibility.ConstructionHeightDomains

/-!
# Uniform Height Domains
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

noncomputable def realSeedOffset : Ordinal.{u} :=
  (insert ZFSet.omega ZFSet.omega : ZFSet.{u}).rank

noncomputable def heightDomainIndex (a : Ordinal.{u}) : Ordinal.{u} := a - realSeedOffset + 1

theorem ground_seed_offset (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalHeight (seed (groundReals M)) = realSeedOffset := ordinalHeight_ground_seed M hM hT

theorem heightDomainIndex_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (heightDomainIndex a).toZFSet ∈ M :=
  internal_difference_successor M hM hT a realSeedOffset ha

theorem largestOrdinal_ground_domain (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : realSeedOffset ≤ a) :
    a.toZFSet ∈ level (groundReals M) (heightDomainIndex a) ∧
      ∀ e : ℕ → ZFSet.{u}, e 0 ∈ level (groundReals M) (heightDomainIndex a) →
        (largestOrdinalSentence.Sat (level (groundReals M) (heightDomainIndex a) : Set ZFSet) e ↔
          e 0 = a.toZFSet) := by
  have hoff := ground_seed_offset M hM hT
  have hm := largest_ordinal_at_difference (groundReals M) a (hoff ▸ ha)
  rw [hoff] at hm
  refine ⟨hm.1,?_⟩
  intro e he
  exact largestOrdinalSentence_unique _ (level_transitive _ _) a hm.1
    (fun b hb => (hm.2 b).mp hb) e he

theorem bindLargestOrdinal_ground_domain (p : SentenceForm) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (a : Ordinal.{u}) (ha : realSeedOffset ≤ a)
    (e : ℕ → ZFSet.{u}) :
    (bindLargestOrdinal p).Sat (level (groundReals M) (heightDomainIndex a) : Set ZFSet) e ↔
      p.Sat (level (groundReals M) (heightDomainIndex a) : Set ZFSet) (cons a.toZFSet e) := by
  have h := bindLargestOrdinal_level p (groundReals M) (a-realSeedOffset) e
  rw [ground_seed_offset M hM hT,Ordinal.add_sub_cancel_of_le ha] at h
  exact h

theorem Construction.height_domain_subset (t : Construction.{u}) :
    ∃ q : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
        ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ realSeedOffset ≤ β ∧
          ∀ a : Ordinal.{u}, a.toZFSet ∈ M → β ≤ a →
            (heightDomainIndex a).toZFSet ∈ M ∧
            (∀ i, t.ordinalInputs P i ∈ level (groundReals M) (heightDomainIndex a)) ∧
            (∀ e : ℕ → ZFSet.{u}, e 0 ∈ level (groundReals M) (heightDomainIndex a) →
              (largestOrdinalSentence.Sat (level (groundReals M) (heightDomainIndex a) : Set
                ZFSet) e ↔
                e 0 = a.toZFSet)) ∧
            t.value (groundReals M) P = definedSubset
              (level (groundReals M) (heightDomainIndex a)) q
              (fun i : Fin q.bound => t.ordinalInputs P i) := by
  obtain ⟨q,hq⟩ := t.largest_domain_definition
  refine ⟨q,?_⟩
  intro M hM hT P hP ht hi
  obtain ⟨β,hβ,hβspec⟩ := hq M hM hT P hP ht hi
  have hoff : realSeedOffset.toZFSet ∈ M := by
    rw [← ground_seed_offset M hM hT]
    exact ordinalHeight_mem_model M _ hM hT.separation.finitePrefix.bounded
      (seed_mem M _ hM hT (groundReals_mem M hM hT)) (seed_transitive _)
  refine ⟨max β realSeedOffset,internal_ordinal_max M hβ hoff,le_max_right _ _,?_⟩
  intro a ha hle
  obtain ⟨hδ,hv,he,hm,hdef⟩ := hβspec a ha ((le_max_left _ _).trans hle)
  rw [ground_seed_offset M hM hT] at hδ hv he hm hdef
  exact ⟨hδ,he,hm,definedSubset_of_membership _ _ (level_transitive _ _) hv q
    (t.ordinalInputs P) hdef⟩

end TuringRigidity.RelativeConstructible

end OAI
