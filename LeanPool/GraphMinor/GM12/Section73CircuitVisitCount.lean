/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkSubstitution
import Mathlib.Data.List.Nodup

/-!
# Visit counts for circuit walks

The walk selection in XII (7.3), page 262, uses XI (9.2) and
the six shapes of a tie. A disc boundary contributes a circuit
walk, which visits each vertex at most once. For a closed walk,
counting departures is the same as counting its support with the
first vertex removed. A simple closed walk has this latter list
without repetitions. This proves the needed circuit visit bound.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

open Classical in
/-- The departure count, plus the final position, is the count in
the full support list. -/
theorem walkVertexCount_add_end_eq_count_support
    {α β : Type*} {G : Graph α β} (v : α) {a b : α} (W : GraphWalk G a b) :
    walkVertexCount v W + (if b = v then 1 else 0) = W.support.count v := by
  induction W with
  | @nil z h => by_cases hzv : z = v <;> simp [walkVertexCount, GraphWalk.support, hzv]
  | @cons x y z e h P ih =>
    rw [walkVertexCount, GraphWalk.support_cons, List.count_cons]
    by_cases hxv : x = v <;> simp [hxv] at * <;> omega

open Classical in
/-- On a closed walk, departure counts equal the counts in the
support list with its first position removed. -/
theorem walkVertexCount_eq_count_support_tail
    {α β : Type*} {G : Graph α β} (v : α) {a : α} (W : GraphWalk G a a) :
    walkVertexCount v W = W.support.tail.count v := by
  have hh := walkVertexCount_add_end_eq_count_support v W
  rw [W.support_eq_cons, List.count_cons] at hh
  by_cases hav : a = v <;> simp [hav] at hh <;> omega

/-- A simple closed walk visits any vertex at most once, with
visits counted before the repeated final position. This is the
disc-boundary case of the visit bounds used in XII (7.3). -/
theorem walkVertexCount_le_one_of_isSimpleClosed
    {α β : Type*} {G : Graph α β} {a : α} {W : GraphWalk G a a}
    (hW : W.IsSimpleClosed) (v : α) : walkVertexCount v W ≤ 1 := by
  classical
  rw [walkVertexCount_eq_count_support_tail]
  exact List.nodup_iff_count_le_one.mp hW.1 v

/-- Departure counts add when walks are concatenated. -/
theorem walkVertexCount_append
    {α β : Type*} {G : Graph α β} (v : α) {a b c : α}
    (P : GraphWalk G a b) (Q : GraphWalk G b c) :
    walkVertexCount v (P.append Q) = walkVertexCount v P + walkVertexCount v Q := by
  classical
  induction P with
  | nil h => simp only [GraphWalk.append, walkVertexCount, Nat.zero_add]
  | cons h R ih =>
    change (if _ = v then 1 else 0) + walkVertexCount v (R.append Q) = _
    rw [ih, walkVertexCount]
    exact (Nat.add_assoc _ _ _).symm

/-- Traversing a simple path and returning along it visits every
vertex at most twice, and an endpoint at most once. These are the
line contributions to the tie bounds used in XII (7.3), page 262. -/
theorem walkVertexCount_backtrack_bounds
    {α β : Type*} {G : Graph α β} {a b : α} (P : GraphWalk G a b) (hP : P.IsSimple)
    (v : α) : walkVertexCount v (P.append P.reverse) ≤ 2 ∧
      (v = a ∨ v = b → walkVertexCount v (P.append P.reverse) ≤ 1) := by
  classical
  have hcount : P.support.count v ≤ 1 := List.nodup_iff_count_le_one.mp hP v
  have h₁ := walkVertexCount_add_end_eq_count_support v P
  have h₂ := walkVertexCount_add_end_eq_count_support v P.reverse
  rw [GraphWalk.support_reverse, List.count_reverse] at h₂
  rw [walkVertexCount_append]
  constructor
  · omega
  · rintro (rfl | rfl) <;> simp only [ite_true] at h₁ h₂ <;> omega

/-- A circuit has a closed walk in its ambient drawing of exactly
its length, with the same underlying drawing and at most one
visit to every vertex. This supplies the circuit walks in the
tie argument used by XII (7.3), page 262. -/
theorem exists_circuit_walk_with_visit_bound
    {S : Type*} [TopologicalSpace S] [T1Space S] {K C : Drawing S}
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K) :
    ∃ (a : S) (W : GraphWalk K.toGraph a a), walkDrawing K W = C ∧
      W.length = C.length ∧ ∀ v, walkVertexCount v W ≤ 1 := by
  classical
  obtain ⟨a, P, hP, _, hV, hE⟩ := hC
  obtain ⟨W, hWS, hWE⟩ := hCK.exists_walk_up P
  have hW : W.IsSimpleClosed := by
    change W.support.tail.Nodup ∧ W.edges.Nodup
    rw [hWS, hWE]
    exact hP
  have hdraw : walkDrawing K W = C := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hWS, hV]
    · rw [walkDrawing_E, hWE, hE]
  have hlen : W.length = C.length := by
    change W.edges.length = C.E.ncard
    rw [hWE, hE]
    have hset : {e | e ∈ P.edges} = (P.edges.toFinset : Set (Set S)) := by ext e; simp
    rw [hset, ncard_coe_finset, List.toFinset_card_of_nodup hP.2]
  exact ⟨a, W, hdraw, hlen, walkVertexCount_le_one_of_isSimpleClosed hW⟩

end GraphMinor.GM12
