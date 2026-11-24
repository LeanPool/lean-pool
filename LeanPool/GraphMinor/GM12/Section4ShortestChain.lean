/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Relation
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Choosing a chain with no shortcuts

Graph Minors XII, proof of (4.1), page 248, chooses a chain of circuit
insides whose nonconsecutive members are disjoint. Take a shortest chain
in the intersection graph. An intersection between nonconsecutive members
would replace at least two steps by one, contradicting shortest length.
-/

public section

namespace GraphMinor.GM12

open Set SimpleGraph

/-- The shortest-chain choice in XII (4.1), page 248. The endpoints are
preserved, consecutive sets meet, and nonconsecutive sets are disjoint. -/
theorem exists_irredundant_intersection_chain {α ι : Type*} (C : ι → Set α)
    {a b : ι} (h : Relation.ReflTransGen (fun i j => (C i ∩ C j).Nonempty) a b) :
    ∃ (n : ℕ) (f : Fin (n + 1) → ι), f 0 = a ∧ f (Fin.last n) = b ∧
      (∀ i : Fin n, (C (f i.castSucc) ∩ C (f i.succ)).Nonempty) ∧
      ∀ i j, i.val + 1 < j.val → Disjoint (C (f i)) (C (f j)) := by
  classical
  let G : SimpleGraph ι := {
    Adj := fun i j => i ≠ j ∧ (C i ∩ C j).Nonempty
    symm := ⟨fun {_ _} h => ⟨h.1.symm, h.2.imp (fun _ hx => hx.symm)⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have hr : G.Reachable a b := by
    induction h with
    | refl => exact .refl _
    | @tail c d h hcd ih =>
      by_cases heq : c = d
      · subst d
        exact ih
      · exact ih.trans (SimpleGraph.Adj.reachable (G := G) ⟨heq, hcd⟩)
  obtain ⟨p, hpPath, hp⟩ := hr.exists_path_of_dist
  refine ⟨p.length, fun i => p.getVert i.val, ?_, ?_, ?_, ?_⟩
  · exact p.getVert_zero
  · exact p.getVert_length
  · intro i
    exact (p.adj_getVert_succ i.isLt).2
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi : i.val ≤ p.length := Nat.le_of_lt_succ i.isLt
    have hj : j.val ≤ p.length := Nat.le_of_lt_succ j.isLt
    have hne : p.getVert i.val ≠ p.getVert j.val := by
      intro heq
      have heq' := hpPath.getVert_injOn hi hj heq
      omega
    have hadj : G.Adj (p.getVert i.val) (p.getVert j.val) := ⟨hne, ⟨x, hxi, hxj⟩⟩
    have hshort := SimpleGraph.dist_le ((p.take i.val).append (hadj.toWalk.append (p.drop j.val)))
    simp only [Walk.length_append, SimpleGraph.Adj.length_toWalk, Walk.take_length,
      Walk.drop_length,
      Nat.min_eq_left hi] at hshort
    omega

end GraphMinor.GM12
