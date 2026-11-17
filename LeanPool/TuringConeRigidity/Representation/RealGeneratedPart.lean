/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RealGeneratedPart.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularProjection
public import LeanPool.TuringConeRigidity.SetModels.GeneratedBooleanPart

/-!
# Real Generated Part
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RealGeneratedPart
open Set CountableForcing ForcingProjection RegularCompletion BooleanProjection
open GeneratedBooleanPart RegularProjection
universe u
variable {P : Type u} [Preorder P]

def tagLower (U : Set P) : LowerSet P where
  carrier := {p | ∃ q ∈ U, p ≤ q}
  lower' := by rintro p q hpq ⟨r,hr,hqr⟩; exact ⟨r,hr,hpq.trans hqr⟩

def bit (N : ℕ → Set P) (n : ℕ) : Algebra P :=
  Heyting.Regular.toRegular (tagLower (N n))

noncomputable def part (N : ℕ → Set P) : CompleteSublattice (Algebra P) :=
  generated (Set.range (bit N))

theorem bit_mem_part (N : ℕ → Set P) (n : ℕ) : bit N n ∈ part N :=
  subset_generated _ ⟨n,rfl⟩

theorem part_compl (N : ℕ → Set P) (a : Algebra P) (ha : a ∈ part N) : aᶜ ∈ part N :=
  generated_compl _ a ha

noncomputable def projection (N : ℕ → Set P) : Projection P (PartPositive (part N)) :=
  originalProjection (part N) (part_compl N)

def decision (N : ℕ → Set P) (n : ℕ) : Set P :=
  {p | p ∈ tagLower (N n) ∨ p ∈ (tagLower (N n))ᶜ}

theorem decision_dense (N : ℕ → Set P) (n : ℕ) : Dense (decision N n) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ q ∈ tagLower (N n)
  · obtain ⟨q,hqp,hq⟩ := h
    exact ⟨q,hqp,Or.inl hq⟩
  · exact ⟨p,le_rfl,Or.inr ((mem_compl _ p).mpr (fun q hqp hq => h ⟨q,hqp,hq⟩))⟩

def value (N : ℕ → Set P) (G : GenericFilter P) : Set ℕ :=
  {n | ∃ p ∈ G.carrier, p ∈ N n}

theorem bit_hit_iff (N : ℕ → Set P) (G : GenericFilter P)
    (hG : GenericFor (decision N) G) (n : ℕ) :
    (∃ p ∈ G.carrier, p ∈ (bit N n : LowerSet P)) ↔ n ∈ value N G := by
  constructor
  · rintro ⟨p,hp,hpbit⟩
    obtain ⟨q,hq,hqdec⟩ := hG n
    rcases hqdec with ⟨r,hr,hqr⟩ | hqneg
    · exact ⟨r,G.upper hqr hq,hr⟩
    · obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
      have hrbit : r ∈ (bit N n : LowerSet P) := (bit N n : LowerSet P).lower hrp hpbit
      have hrneg := ((tagLower (N n))ᶜ).lower hrq hqneg
      exact False.elim ((mem_compl ((tagLower (N n))ᶜ) r).mp hrbit r le_rfl hrneg)
  · rintro ⟨p,hp,hpN⟩
    exact ⟨p,hp,(show tagLower (N n) ≤ ((bit N n : LowerSet P)) from le_compl_compl)
      ⟨p,hpN,le_rfl⟩⟩

theorem projected_bit_iff (N : ℕ → Set P) (G : GenericFilter P)
    (hG : GenericFor (decision N) G) (n : ℕ) :
    (∃ hn : bit N n ≠ ⊥,
      (⟨bit N n,bit_mem_part N n,hn⟩ : PartPositive (part N)) ∈
        (imageFilter (projection N) G).carrier) ↔ n ∈ value N G := by
  constructor
  · rintro ⟨hn,hmem⟩
    exact (bit_hit_iff N G hG n).mp
      ((image_mem_iff (part N) (part_compl N) G ⟨bit N n,bit_mem_part N n,hn⟩).mp hmem)
  · intro hv
    obtain ⟨p,hp,hpb⟩ := (bit_hit_iff N G hG n).mpr hv
    have hn : bit N n ≠ ⊥ := by
      intro h
      rw [h] at hpb
      exact hpb
    exact ⟨hn,(image_mem_iff (part N) (part_compl N) G
      ⟨bit N n,bit_mem_part N n,hn⟩).mpr ⟨p,hp,hpb⟩⟩

theorem same_real_generators (N : ℕ → Set P) (G H : GenericFilter P)
    (hG : GenericFor (decision N) G) (hH : GenericFor (decision N) H)
    (heq : value N G = value N H) (n : ℕ) :
    (∃ hn : bit N n ≠ ⊥,
      (⟨bit N n,bit_mem_part N n,hn⟩ : PartPositive (part N)) ∈
        (imageFilter (projection N) G).carrier) ↔
    (∃ hn : bit N n ≠ ⊥,
      (⟨bit N n,bit_mem_part N n,hn⟩ : PartPositive (part N)) ∈
        (imageFilter (projection N) H).carrier) := by
  rw [projected_bit_iff N G hG,projected_bit_iff N H hH,heq]

theorem projected_countable_presentation [Countable P] (N : ℕ → Set P) :
    (Set.range (projection N).map).Countable ∧ Dense (Set.range (projection N).map) :=
  originalProjection_countable_dense (part N) (part_compl N)

end TuringRigidity.RealGeneratedPart

end OAI
