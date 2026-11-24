/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting the separators in a chain of radial circuits

In the proof of Graph Minors XII, (4.1), page 248, nonconsecutive circuits
have disjoint insides. A vertex therefore belongs to at most two circuits.
Counting vertex occurrences gives twice the size of the separator as an upper bound.
-/

public section

namespace GraphMinor.GM12

open Finset

/-- The counting step of Graph Minors XII, (4.1), page 248. If each separator
vertex occurs in at most two sets, their total size is at most twice the
size of the separator. -/
theorem sum_card_le_twice_separator {α ι : Type*} [DecidableEq α] [Fintype ι]
    (Z : Finset α) (C : ι → Finset α) (hsub : ∀ i, C i ⊆ Z)
    (hmult : ∀ x ∈ Z, (univ.filter fun i => x ∈ C i).card ≤ 2) :
    ∑ i, (C i).card ≤ 2 * Z.card := by
  classical
  have hcard : ∀ i, (C i).card = ∑ x ∈ Z, if x ∈ C i then 1 else 0 := by
    intro i
    rw [← Finset.sum_filter]
    have heq : Z.filter (fun x => x ∈ C i) = C i := by
      ext x
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub i h, h⟩⟩
    rw [heq]
    simp
  simp_rw [hcard]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x ∈ Z, (univ.filter fun i => x ∈ C i).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ _x ∈ Z, 2 := Finset.sum_le_sum hmult
    _ = 2 * Z.card := by simp [Nat.mul_comm]


/-- A vertex occurs at most twice in a chain whose nonconsecutive members are
disjoint. This supplies the multiplicity bound in XII (4.1), page 248. -/
theorem chain_membership_card_le_two {α : Type*} [DecidableEq α] {n : ℕ}
    (C : Fin n → Finset α)
    (hdisj : ∀ i j : Fin n, i.val + 1 < j.val → Disjoint (C i) (C j)) (x : α) :
    (univ.filter fun i => x ∈ C i).card ≤ 2 := by
  classical
  have hclose : ∀ i j : Fin n, x ∈ C i → x ∈ C j → j.val ≤ i.val + 1 := by
    intro i j hi hj
    by_contra h
    have hgap : i.val + 1 < j.val := Nat.lt_of_not_ge h
    exact Finset.disjoint_left.mp (hdisj i j hgap) hi hj
  apply Nat.le_of_not_gt
  intro h
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp h
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  have h₁ := hclose i j hi' hj'
  have h₂ := hclose j i hj' hi'
  have h₃ := hclose i k hi' hk'
  have h₄ := hclose k i hk' hi'
  have h₅ := hclose j k hj' hk'
  have h₆ := hclose k j hk' hj'
  have hne₁ : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hne₂ : i.val ≠ k.val := fun h => hik (Fin.ext h)
  have hne₃ : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  omega

/-- The bound on total separator occurrences for the circuit chain chosen in
Graph Minors XII, proof of (4.1), page 248. -/
theorem chain_sum_card_le_twice_separator {α : Type*} {n : ℕ}
    (Z : Finset α) (C : Fin n → Finset α) (hsub : ∀ i, C i ⊆ Z)
    (hdisj : ∀ i j : Fin n, i.val + 1 < j.val → Disjoint (C i) (C j)) :
    ∑ i, (C i).card ≤ 2 * Z.card := by
  classical
  exact sum_card_le_twice_separator Z C hsub
    (fun x _ => chain_membership_card_le_two C hdisj x)

end GraphMinor.GM12
