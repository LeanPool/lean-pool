/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenChainCondition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Countable

public import LeanPool.TuringConeRigidity.CohenForcing.CohenCoordinates

/-!
# Cohen Chain Condition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenChainCondition
open Set CohenSymmetry CohenCoordinates
universe u
variable {ι : Type u}

/-- Pairwise incompatibility of distinct conditions in a family. -/
def Antichain (A : Set (Condition ι)) : Prop :=
  A.Pairwise (fun p q => ¬ Compatible p q)

theorem bounded_antichain_finite (n : ℕ) (A : Set (Condition ι))
    (hA : Antichain A) (hn : ∀ p ∈ A, (support p).card ≤ n) : A.Finite := by
  classical
  induction n generalizing A with
  | zero =>
    apply Set.finite_singleton (⊤ : Condition ι) |>.subset
    intro p hp
    have hzero : support p = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hn p hp))
    have he : p = ⊤ := by
      apply Condition.ext
      funext i
      have hi : p.val i = none := by
        by_contra hi
        have := (mem_support p i).mpr hi
        simp [hzero] at this
      exact hi
    exact he
  | succ n ih =>
    by_cases hempty : A = ∅
    · simp [hempty]
    obtain ⟨p,hp⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    let slice (i : ι) (b : Bool) : Set (Condition ι) := {q ∈ A | q.val i = some b}
    have hs (i : ι) (b : Bool) : (slice i b).Finite := by
      have he : (erase i '' slice i b).Finite := by
        apply ih
        · intro r hr s hs hrs
          obtain ⟨q,hq,rfl⟩ := hr
          obtain ⟨t,ht,rfl⟩ := hs
          intro hcomp
          exact hA hq.1 ht.1 (fun h => hrs (congrArg (erase i) h))
            (compatible_of_erase i b hq.2 ht.2 hcomp)
        · rintro r ⟨q,hq,rfl⟩
          rw [support_erase,Finset.card_erase_of_mem]
          · have := hn q hq.1
            have hpos : 0 < (support q).card := Finset.card_pos.mpr
              ⟨i,(mem_support q i).mpr (by simp [hq.2])⟩
            omega
          · exact (mem_support q i).mpr (by simp [hq.2])
      exact he.of_finite_image ((erase_injective_on i b).mono (fun _ h => h.2))
    apply (Set.finite_singleton p |>.union
      (p.finite.biUnion (fun i _ => Set.finite_univ.biUnion (fun b _ => hs i b)))).subset
    intro q hq
    by_cases he : q = p
    · exact Or.inl he
    · right
      have hc := hA hp hq (Ne.symm he)
      have hw : ∃ i a b, p.val i = some a ∧ q.val i = some b := by
        by_contra hw
        apply hc
        intro i a b ha hb
        exact False.elim (hw ⟨i,a,b,ha,hb⟩)
      obtain ⟨i,a,b,ha,hb⟩ := hw
      exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
        ⟨(by simp [ha]),Set.mem_iUnion.mpr
          ⟨b,Set.mem_iUnion.mpr ⟨Set.mem_univ b,⟨hq,hb⟩⟩⟩⟩⟩

theorem antichain_countable (A : Set (Condition ι)) (hA : Antichain A) :
    A.Countable := by
  have h (n : ℕ) : {p ∈ A | (support p).card ≤ n}.Countable := by
    have hsubset : {p ∈ A | (support p).card ≤ n} ⊆ A := fun _ hp => hp.1
    exact (bounded_antichain_finite n _ (hA.mono hsubset) (fun _ hp => hp.2)).countable
  apply (Set.countable_iUnion h).mono
  intro p hp
  exact Set.mem_iUnion.mpr ⟨(support p).card,hp,le_rfl⟩

theorem antichain_support_countable (A : ℕ → Set (Condition ι))
    (hA : ∀ n, Antichain (A n)) :
    (⋃ n, ⋃ p ∈ A n, {i | p.val i ≠ none}).Countable := by
  apply Set.countable_iUnion
  intro n
  exact (antichain_countable (A n) (hA n)).biUnion (fun p _ => p.finite.countable)

end TuringRigidity.CohenChainCondition

end OAI
