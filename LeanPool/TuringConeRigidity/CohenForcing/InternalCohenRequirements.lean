/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenRequirements.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters

/-!
# Internal Cohen Requirements
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
open FiniteShuffle ShuffleRequirements
attribute [local instance] BoundedSetTheory.InternalCollapse.order
  BoundedSetTheory.InternalCollapse.collapsePreorder

def openRequirement (E : ZFSet.{0}) (s : List Bool) : Prop :=
  ∃ t : Condition, t.word <+: s ∧ wordCode t.word ∈ E

theorem openRequirement_dense (E : ZFSet.{0})
    (hE : CountableForcing.Dense {p : Condition | wordCode p.word ∈ E}) :
    DenseOpen (openRequirement E) := by
  constructor
  · intro s
    obtain ⟨t,ht,htE⟩ := hE ⟨s⟩
    exact ⟨t.word,ht,t,List.prefix_rfl,htE⟩
  · rintro s t hst ⟨q,hqs,hq⟩
    exact ⟨q,hqs.trans hst,hq⟩

theorem ground_family (M : ZFSet.{0}) [Countable (Conditions M)] (hne : ∃ x, x ∈ M) :
    ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
      ∀ A : Oracle, ShuffleRequirements.GenericFor D A ↔
        AtomicForcing.GroundGeneric M (pushFilter (realFilter A)) := by
  classical
  obtain ⟨x,hx⟩ := hne
  obtain ⟨m,_⟩ := label_surjective M hx
  let _ : Nonempty (Conditions M) := ⟨m⟩
  obtain ⟨e,he⟩ := exists_surjective_nat (Conditions M)
  let good (n : ℕ) := CountableForcing.Dense {p : Condition | wordCode p.word ∈ label M (e n)}
  let D (n : ℕ) (s : List Bool) := if good n then openRequirement (label M (e n)) s else True
  have hD : ∀ n, DenseOpen (D n) := by
    intro n; dsimp only [D]; split
    · exact openRequirement_dense _ ‹good n›
    · exact ⟨fun s => ⟨s,List.prefix_rfl,True.intro⟩,fun _ _ _ _ => True.intro⟩
  refine ⟨D,hD,fun A => ?_⟩
  rw [groundGeneric_iff,pull_push]
  constructor
  · intro h E hEM hE
    obtain ⟨q,hq⟩ := label_surjective M hEM
    obtain ⟨n,rfl⟩ := he q
    have hg : good n := by dsimp only [good]; rw [hq]; exact hE
    obtain ⟨s,hs,hAs⟩ := h n
    dsimp only [D] at hs
    rw [ite_eq_left hg] at hs
    obtain ⟨t,ht,htE⟩ := hs
    exact ⟨t,realizes_mono ht hAs,by simpa only [hq] using htE⟩
  · intro h n
    by_cases hg : good n
    · obtain ⟨t,ht,htE⟩ := h (label M (e n)) (label_mem M (e n)) hg
      exact ⟨t.word,by dsimp only [D]; rw [ite_eq_left hg]; exact ⟨t,List.prefix_rfl,htE⟩,ht⟩
    · exact ⟨[],by dsimp only [D]; rw [ite_eq_right hg]; trivial,by intro i hi; simp at hi⟩

theorem generic_below (D : ℕ → List Bool → Prop) (hD : ∀ n, DenseOpen (D n))
    (s : List Bool) : ∃ A : Oracle, ShuffleRequirements.GenericFor D A ∧ Realizes s A := by
  let E : ℕ → Set Condition := fun n => {p | D n p.word}
  have hE : ∀ n, CountableForcing.Dense (E n) := by
    intro n p
    obtain ⟨t,ht,htD⟩ := (hD n).1 p.word
    exact ⟨⟨t⟩,ht,htD⟩
  obtain ⟨G,A,hp,hG,heq,_⟩ := CohenRecursiveName.exists_generic_real E hE ⟨s⟩
  subst G
  refine ⟨A,?_,hp⟩
  intro n
  obtain ⟨p,hp,hpD⟩ := hG n
  exact ⟨p.word,hpD,hp⟩

end TuringRigidity.InternalCohen

end OAI
