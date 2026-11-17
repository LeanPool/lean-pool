/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenNiceNames.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenChainCondition
public import Mathlib.Order.Zorn

/-!
# Cohen Nice Names
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenNiceNames
open Set CountableForcing CohenSymmetry CohenCoordinates CohenChainCondition
universe u
variable {ι : Type u}

theorem compatible_symm {p q : Condition ι} (h : Compatible p q) : Compatible q p :=
  fun i a b ha hb => (h i b a hb ha).symm

theorem compatible_refl (p : Condition ι) : Compatible p p :=
  fun _ _ _ ha hb => Option.some.inj (ha.symm.trans hb)

theorem countable_predense_antichain (U : Set (Condition ι)) :
    ∃ A ⊆ U, Antichain A ∧ A.Countable ∧
      ∀ p ∈ U, ∃ a ∈ A, Compatible p a := by
  classical
  obtain ⟨A,hA⟩ := zorn_subset {A : Set (Condition ι) | A ⊆ U ∧ Antichain A} (by
    intro c hc hchain
    refine ⟨⋃₀ c,⟨?_,?_⟩,fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro p ⟨s,hs,hp⟩
      exact (hc hs).1 hp
    · intro p hp q hq hpq
      obtain ⟨s,hs,hps⟩ := hp
      obtain ⟨t,ht,hqt⟩ := hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 (hst hps) hqt hpq
      · exact (hc hs).2 hps (hts hqt) hpq)
  refine ⟨A,hA.1.1,hA.1.2,antichain_countable A hA.1.2,?_⟩
  intro p hp
  by_contra h
  have hnone : ∀ a ∈ A, ¬ Compatible p a := by
    intro a ha hpa
    exact h ⟨a,ha,hpa⟩
  have hins : insert p A ⊆ U ∧ Antichain (insert p A) := by
    constructor
    · exact Set.insert_subset hp hA.1.1
    · exact hA.1.2.insert (fun a ha _ =>
        ⟨hnone a ha,fun hap => hnone a ha (compatible_symm hap)⟩)
  have hpA : p ∈ A := hA.2 hins (Set.subset_insert _ _) (Set.mem_insert _ _)
  exact hnone p hpA (compatible_refl p)

def RealName (ι : Type u) := ℕ → Set (Condition ι)

def value (N : RealName ι) (G : GenericFilter (Condition ι)) : Set ℕ :=
  {n | ∃ p ∈ G.carrier, p ∈ N n}

def below (U : Set (Condition ι)) : Set (Condition ι) :=
  {q | ∃ p ∈ U, q ≤ p}

def decision (N A : RealName ι) (n : ℕ) : Set (Condition ι) :=
  {q | (∃ a ∈ A n, q ≤ a) ∨ ∀ p, p ≤ q → p ∉ below (N n)}

theorem decision_dense (N A : RealName ι)
    (hA : ∀ n p, p ∈ below (N n) → ∃ a ∈ A n, Compatible p a) (n : ℕ) :
    Dense (decision N A n) := by
  classical
  intro q
  by_cases h : ∃ p, p ≤ q ∧ p ∈ below (N n)
  · obtain ⟨p,hpq,hpN⟩ := h
    obtain ⟨a,ha,hpa⟩ := hA n p hpN
    exact ⟨merge p a,(merge_le_left p a).trans hpq,
      Or.inl ⟨a,ha,merge_le_right hpa⟩⟩
  · exact ⟨q,le_rfl,Or.inr (fun p hpq hpN => h ⟨p,hpq,hpN⟩)⟩

theorem value_eq_of_generic (N A : RealName ι) (hA : ∀ n, A n ⊆ below (N n))
    (G : GenericFilter (Condition ι)) (hG : GenericFor (decision N A) G) :
    value A G = value N G := by
  ext n
  constructor
  · rintro ⟨a,ha,haA⟩
    obtain ⟨p,hp,hap⟩ := hA n haA
    exact ⟨p,G.upper hap ha,hp⟩
  · rintro ⟨p,hp,hpN⟩
    obtain ⟨q,hq,hdec⟩ := hG n
    rcases hdec with ⟨a,ha,hqa⟩ | hneg
    · exact ⟨a,G.upper hqa hq,ha⟩
    · obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact False.elim (hneg r hrq ⟨p,hpN,hrp⟩)

theorem countably_supported_name (N : RealName ι) :
    ∃ A : RealName ι, ∃ S : Set ι,
      S.Countable ∧ (∀ n, Antichain (A n)) ∧
      (∀ n p, p ∈ A n → ∀ i, p.val i ≠ none → i ∈ S) ∧
      (∀ n, Dense (decision N A n)) ∧
      ∀ G : GenericFilter (Condition ι), GenericFor (decision N A) G →
        value A G = value N G := by
  classical
  choose A hsub hanti hcount hpred using
    fun n => countable_predense_antichain (below (N n))
  let S : Set ι := ⋃ n, ⋃ p ∈ A n, {i | p.val i ≠ none}
  refine ⟨A,S,antichain_support_countable A hanti,hanti,?_,
    decision_dense N A hpred,fun G hG => value_eq_of_generic N A hsub G hG⟩
  intro n p hp i hi
  exact Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr
    ⟨p,Set.mem_iUnion.mpr ⟨hp,hi⟩⟩⟩

end TuringRigidity.CohenNiceNames

end OAI
