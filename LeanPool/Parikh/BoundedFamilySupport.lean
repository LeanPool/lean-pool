/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.GrammarTrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Counting bounded tree syntax

For counting, root compatibility may be discarded: every valid active open
tree is covered by choosing a production and a child tuple of its fixed arity.
Mathlib's finite function spaces count the tuples, and finite unions bound
each height layer. This is a classical overcount, not an executable enumerator.
The existing executable enumerator retains the root checks.

Source: `lem:count-trees`.
-/
namespace Parikh

/-- The number of positions in a full `b`-ary tree through depth `H`. -/
@[expose] def heightPositions (b H : ℕ) : ℕ := ∑ i ∈ Finset.range (H + 1), b ^ i

theorem heightPositions_zero (b : ℕ) : heightPositions b 0 = 1 := by
  simp [heightPositions]

theorem heightPositions_succ (b H : ℕ) :
    heightPositions b (H + 1) = 1 + b * heightPositions b H := by
  unfold heightPositions
  rw [Finset.sum_range_succ']
  simp only [pow_succ', pow_zero]
  rw [Finset.mul_sum]
  omega

theorem heightPositions_pos (b H : ℕ) : 1 ≤ heightPositions b H := by
  cases H with
  | zero => simp [heightPositions_zero]
  | succ H => rw [heightPositions_succ]; omega

namespace ParseTree
variable {T N : Type*}

/-- Every child's height is strictly smaller than its production node's height. -/
theorem height_child_lt (r : ContextFreeRule T N) (children : List (ParseTree T N))
    (c : ParseTree T N) (hc : c ∈ children) : c.height < (node r children).height := by
  have hm : c.height ∈ children.map height := List.mem_map_of_mem hc
  have hmax := List.le_max_of_mem hm
  rw [height.eq_3, List.foldl_max_eq_max (List.ne_nil_of_mem hm), Nat.zero_max]
  omega

/-- All ordered child tuples from a finite family, at a production's fixed arity. -/
@[expose] noncomputable def nodeFamily (r : ContextFreeRule T N) (family : Finset (ParseTree T N)) :
    Finset (ParseTree T N) := by
  classical
  exact Finset.univ.image fun f : Fin r.output.length → family =>
    node r (List.ofFn fun i => (f i).val)

theorem mem_nodeFamily (r : ContextFreeRule T N) (family : Finset (ParseTree T N))
    (children : List (ParseTree T N)) (hlen : children.length = r.output.length)
    (hchildren : ∀ c ∈ children, c ∈ family) : node r children ∈ nodeFamily r family := by
  classical
  let f : Fin r.output.length → family := fun i =>
    ⟨children[i.val]'(by omega), hchildren _ (List.getElem_mem (by omega))⟩
  apply Finset.mem_image.mpr
  refine ⟨f, Finset.mem_univ _, ?_⟩
  congr 1
  apply List.ext_getElem <;> simp [f, hlen]

theorem card_nodeFamily_le (r : ContextFreeRule T N) (family : Finset (ParseTree T N)) :
    (nodeFamily r family).card ≤ family.card ^ r.output.length := by
  classical
  exact (Finset.card_image_le).trans_eq (by simp)
end ParseTree

variable {T : Type*} [Fintype T]

/-- Terminal leaves and active holes; the ambient nonterminal type may be infinite. -/
@[expose] noncomputable def treeLeaves (g : ContextFreeGrammar T) : Finset (ParseTree T g.NT) := by
  classical
  exact Finset.univ.image ParseTree.terminal ∪ (activeNonterminals g).image ParseTree.hole

/-- A finite overcount of active open trees, without child-root compatibility checks. -/
@[expose] noncomputable def treeFamily (g : ContextFreeGrammar T) : ℕ → Finset (ParseTree T
  g.NT) := by
  classical
  exact Nat.rec (treeLeaves g) fun _ previous =>
    treeLeaves g ∪ g.rules.biUnion (fun r => ParseTree.nodeFamily r previous)

theorem card_treeLeaves_le (g : ContextFreeGrammar T) :
    (treeLeaves g).card ≤ Fintype.card T + (activeNonterminals g).card := by
  classical
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add (by simpa using Finset.card_image_le (s := (Finset.univ : Finset T)))
    Finset.card_image_le

/-- Every bounded active open tree belongs to the counting family. -/
theorem mem_treeFamily (g : ContextFreeGrammar T) (H : ℕ) (t : ParseTree T g.NT)
    (ht : ActiveOpen g t) (hh : t.height ≤ H) : t ∈ treeFamily g H := by
  classical
  induction H generalizing t with
  | zero =>
    cases ht.1 with
    | terminal a => simp [treeFamily, treeLeaves]
    | hole A =>
      have hA := ht.2 A (by simp only [ParseTree.holes.eq_2, List.mem_singleton])
      simp [treeFamily, treeLeaves, hA]
    | node r cs hr hv roots => rw [ParseTree.height.eq_3] at hh; omega
  | succ H ih =>
    cases ht.1 with
    | terminal a => simp [treeFamily, treeLeaves]
    | hole A =>
      have hA := ht.2 A (by simp only [ParseTree.holes.eq_2, List.mem_singleton])
      simp [treeFamily, treeLeaves, hA]
    | node r cs hr hv roots =>
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨r, hr, ParseTree.mem_nodeFamily r _ cs ?_ ?_⟩
      · simpa using congrArg List.length roots
      · intro c hc
        have hchild := ParseTree.height_child_lt r cs c hc
        apply ih c ⟨hv c hc, ?_⟩ (by omega)
        intro A hA
        apply ht.2 A
        simp only [ParseTree.holes.eq_3, ← List.flatMap_def, List.mem_flatMap]
        exact ⟨c, hc, hA⟩

/-- Count each layer using finite union and function-space cardinalities. -/
theorem card_treeFamily_le (g : ContextFreeGrammar T) (b q : ℕ)
    (hq : 1 + Fintype.card T + (activeNonterminals g).card + g.rules.card ≤ q)
    (hb : ∀ r ∈ g.rules, r.output.length ≤ b) (H : ℕ) :
    (treeFamily g H).card ≤ q ^ heightPositions b H := by
  classical
  have hq1 : 1 ≤ q := by omega
  induction H with
  | zero => simpa [treeFamily, heightPositions_zero] using (card_treeLeaves_le g).trans (by omega)
  | succ H ih =>
    let A := q ^ heightPositions b H
    have hA : 1 ≤ A ^ b := one_le_pow₀ (one_le_pow₀ hq1)
    have hnodes : ∀ r ∈ g.rules,
        (ParseTree.nodeFamily r (treeFamily g H)).card ≤ A ^ b := by
      intro r hr
      exact (ParseTree.card_nodeFamily_le r _).trans
        ((Nat.pow_le_pow_left ih _).trans (pow_le_pow_right₀ (one_le_pow₀ hq1) (hb r hr)))
    calc
      (treeFamily g (H + 1)).card
          ≤ (treeLeaves g).card + ∑ r ∈ g.rules,
              (ParseTree.nodeFamily r (treeFamily g H)).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
      _ ≤ (Fintype.card T + (activeNonterminals g).card) + g.rules.card * A ^ b := by
        exact Nat.add_le_add (card_treeLeaves_le g) (by
          simpa using Finset.sum_le_sum hnodes)
      _ ≤ q * A ^ b := by
        have hl := Nat.mul_le_mul_left (Fintype.card T + (activeNonterminals g).card) hA
        have hq' : Fintype.card T + (activeNonterminals g).card + g.rules.card ≤ q := by omega
        calc
          _ ≤ (Fintype.card T + (activeNonterminals g).card) * A ^ b +
              g.rules.card * A ^ b := Nat.add_le_add_right (by simpa using hl) _
          _ = (Fintype.card T + (activeNonterminals g).card + g.rules.card) * A ^ b :=
            (Nat.add_mul _ _ _).symm
          _ ≤ q * A ^ b := Nat.mul_le_mul_right _ hq'
      _ = q ^ heightPositions b (H + 1) := by
        dsimp [A]
        rw [heightPositions_succ, pow_add, pow_one, Nat.mul_comm b, ← pow_mul]

omit [Fintype T] in
/-- Valid trees have at most the full branching-tree budget of terminal leaves. -/
theorem yield_length_le_heightPositions (g : ContextFreeGrammar T) (b : ℕ)
    (hb : ∀ r ∈ g.rules, r.output.length ≤ b) (H : ℕ) (t : ParseTree T g.NT)
    (hv : Valid g t) (hh : t.height ≤ H) : t.yield.length ≤ heightPositions b H := by
  induction H generalizing t with
  | zero =>
    cases hv with
    | terminal a => simp [ParseTree.yield.eq_1, heightPositions_zero]
    | hole A => simp only [ParseTree.yield.eq_2, List.length_nil, Nat.zero_le]
    | node r cs hr hc roots => rw [ParseTree.height.eq_3] at hh; omega
  | succ H ih =>
    cases hv with
    | terminal a => simpa only [ParseTree.yield.eq_1, List.length_singleton] using
      heightPositions_pos b (H + 1)
    | hole A => simp only [ParseTree.yield.eq_2, List.length_nil, Nat.zero_le]
    | node r cs hr hc roots =>
      have hlen : cs.length ≤ b := by
        have := congrArg List.length roots
        simpa using this.le.trans (hb r hr)
      have hchildren : ∀ n ∈ cs.map (fun c => c.yield.length), n ≤ heightPositions b H := by
        intro n hn
        obtain ⟨c, hmem, rfl⟩ := List.mem_map.mp hn
        have hchild := ParseTree.height_child_lt r cs c hmem
        exact ih c (hc c hmem) (by omega)
      calc
        (ParseTree.node r cs).yield.length = (cs.map (fun c => c.yield.length)).sum := by
          simp only [ParseTree.yield.eq_3, List.length_flatten, List.map_map, Function.comp_def]
        _ ≤ cs.length * heightPositions b H := by
          simpa [List.length_map, nsmul_eq_mul] using List.sum_le_length_nsmul _ _ hchildren
        _ ≤ b * heightPositions b H := Nat.mul_le_mul_right _ hlen
        _ ≤ heightPositions b (H + 1) := by rw [heightPositions_succ]; omega

end Parikh
