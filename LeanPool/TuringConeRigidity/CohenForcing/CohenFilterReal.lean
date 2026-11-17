/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenFilterReal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenBorelForcing
public import LeanPool.TuringConeRigidity.CohenForcing.ForcingRequirements

/-!
# Cohen Filter Real
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenFilterReal
open Set FiniteShuffle ShuffleRequirements CountableForcing CohenBorelForcing

/-- Word conditions of length at least `n`. -/
def Long (n : ℕ) : Set Condition := {p | n ≤ p.word.length}

theorem long_dense (n : ℕ) : CountableForcing.Dense (Long n) := by
  intro p
  refine ⟨⟨p.word ++ List.replicate n false⟩,List.prefix_append _ _,?_⟩
  simp [Long]

theorem exists_realFilter (G : GenericFilter Condition)
    (hG : CountableForcing.GenericFor Long G) : ∃ A : Oracle, G = realFilter A := by
  classical
  choose q hqG hq using fun n => hG (n+1)
  let A : Oracle := fun n => (q n).word.getD n false
  have hreal : ∀ p ∈ G.carrier, Realizes p.word A := by
    intro p hp n hn
    obtain ⟨r,_,hrp,hrq⟩ := G.directed hp (hqG n)
    have hqn : n < (q n).word.length := by have := hq n; dsimp [Long] at this; omega
    exact (getD_of_prefix hrp n hn).trans (getD_of_prefix hrq n hqn).symm
  have hmem : ∀ p, p ∈ G.carrier ↔ Realizes p.word A := by
    intro p
    refine ⟨hreal p,?_⟩
    intro hpA
    have hlen : p.word.length ≤ (q p.word.length).word.length := by
      have := hq p.word.length; dsimp [Long] at this; omega
    have hqA := hreal _ (hqG p.word.length)
    have hpre : p.word <+: (q p.word.length).word := by
      conv_lhs => rw [←prefix_default p.word]
      conv_rhs => rw [←prefix_default (q p.word.length).word]
      apply initial_prefix hlen
      intro n hn
      exact (hpA n hn).trans (hqA n (lt_of_lt_of_le hn hlen)).symm
    exact G.upper hpre (hqG p.word.length)
  refine ⟨A,?_⟩
  have hc : G.carrier = (realFilter A).carrier := Set.ext hmem
  have hext (F H : GenericFilter Condition) (h : F.carrier = H.carrier) : F = H := by
    cases F
    cases H
    cases h
    rfl
  exact hext G (realFilter A) hc

theorem realFilter_long (A : Oracle) : CountableForcing.GenericFor Long (realFilter A) := by
  intro n
  exact ⟨⟨initial A n⟩,(realizes_initial A A n).mpr (fun _ _ => rfl),by simp [Long]⟩

theorem weak_iff_reals (p : Condition) (a : Sentence Condition)
    (E : ℕ → Set Condition) (hE : ∀ n, CountableForcing.Dense (E n)) :
    Sentence.WeakForces p a ↔ ∀ A : Oracle,
      CountableForcing.GenericFor (Sentence.Requirements (.neg (.neg a))) (realFilter A) →
      CountableForcing.GenericFor E (realFilter A) → Realizes p.word A →
      Sentence.Truth (realFilter A) a := by
  constructor
  · intro h A hA _ hp
    exact (Sentence.weak_iff_all_generic p a).mp h (realFilter A) hA hp
  · intro h
    apply (Sentence.weak_iff_with_extra p a (mergeRequirements Long E)
      (mergeRequirements_dense Long E long_dense hE)).mpr
    intro G hGa hGE hp
    obtain ⟨hGL,hGE⟩ := (generic_merge_iff Long E G).mp hGE
    obtain ⟨A,rfl⟩ := exists_realFilter G hGL
    exact h A hGa hGE hp

theorem sourceEquation_weak_iff_reals (c : OracleCode) (R : Oracle) :
    ∃ a : Sentence Condition, ∀ (E : ℕ → Set Condition),
      (∀ n, CountableForcing.Dense (E n)) → ∀ p : Condition,
      (Sentence.WeakForces p a ↔ ∀ A : Oracle,
        CountableForcing.GenericFor (Sentence.Requirements (.neg (.neg a))) (realFilter A) →
        CountableForcing.GenericFor E (realFilter A) → Realizes p.word A →
        GenericIdentity.SourceEquation c R (GenericTruth.triple A)) := by
  obtain ⟨a,ha⟩ := borel_represented _
    ((GenericIdentity.sourceEquation_measurable c R).preimage GenericTruth.triple_measurable)
  refine ⟨a,?_⟩
  intro E hE p
  rw [weak_iff_reals p a E hE]
  apply forall_congr'
  intro A
  exact imp_congr_right (fun _ => imp_congr_right (fun _ => imp_congr_right (fun _ => ha A)))

end TuringRigidity.CohenFilterReal

end OAI
