/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Layout.Encode

/-!
# A common binary tree for each host position

At a core position edges for different neighbors share a prefix tree.
At a frozen position each neighbor has a separate path from the root.
Thus a frozen station of large arity need not send all its bits through
one core relay. All potential relay positions are fixed by the host.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout
open Finset

open Classical in
/-- The indexing data represented by `Fin d → Bool`. -/
abbrev Address (d : ℕ) := Fin d → Bool
open Classical in
/-- Indexes the relay by the coordinates of `V × Fin (d + 1) × Address d`. -/
abbrev Relay (V : Type) (d : ℕ) := V × Fin (d + 1) × Address d
open Classical in
/-- Indexes the node by the coordinates of `V ⊕ Relay V d`. -/
abbrev Node (V : Type) (d : ℕ) := V ⊕ Relay V d

open Classical in
theorem node_count (V : Type) [Fintype V] (d : ℕ) :
    Fintype.card (Node V d) = (1 + (d + 1) * 2 ^ d) * Fintype.card V := by
  simp [Node, Relay, Address]
  ring

open Classical in
/-- Each potential neighbor gets its own address. -/
structure Trie (V : Type) (d : ℕ) where
  /-- The `Trie` component of type `V → Prop`. -/
  frozen : V → Prop
  /-- The `Trie` component of type `V → Finset V`. -/
  near : V → Finset V
  symm : ∀ u v, u ∈ near v → v ∈ near u
  /-- The encoding map carried by `Trie`, with type `V → V → Address d`. -/
  code : V → V → Address d
  inject : ∀ v, Set.InjOn (code v) (near v)

namespace Trie
variable {V : Type} {d : ℕ}

open Classical in
/-- Builds `Trie V d where frozen` with the specified `frozen`, `near`, `symm`, `code`. -/
def make (frozen : V → Prop) (near : V → Finset V)
    (hs : ∀ u v, u ∈ near v → v ∈ near u) (hd : ∀ v, (near v).card ≤ 2 ^ d) : Trie V d where
  frozen := frozen
  near := near
  symm := hs
  code v u := if h : u ∈ near v then
    binaryCode ↥(near v) d (by simpa using hd v) ⟨u, h⟩ else fun _ => false
  inject v u hu w hw he := by
    change u ∈ near v at hu
    change w ∈ near v at hw
    simp only [dite_eq_left hu, dite_eq_left hw] at he
    exact congrArg Subtype.val ((binaryCode _ _ _).injective he)

variable (T : Trie V d)

open Classical in
/-- Chooses the operation for the left or right summand. -/
def fixed : Node V d → Prop := Sum.elim T.frozen (fun _ => False)

open Classical in
/-- Returns `h.choose` when `h : ∃ w ∈ T.near v, T.code v w = c` holds, and `v` otherwise. -/
def peer (v : V) (c : Address d) : V :=
  if h : ∃ w ∈ T.near v, T.code v w = c then h.choose else v

open Classical in
theorem peer_code {v w : V} (hw : w ∈ T.near v) : T.peer v (T.code v w) = w := by
  have h : ∃ u ∈ T.near v, T.code v u = T.code v w := ⟨w, hw, rfl⟩
  rw [peer, dite_eq_left h]
  exact T.inject v h.choose_spec.1 hw h.choose_spec.2

open Classical in
/-- Evaluates `if i.val < j then c i else false` at the input `i`. -/
def mask (c : Address d) (j : ℕ) : Address d :=
  fun i => if i.val < j then c i else false

open Classical in
/-- Returns `T.code v w` when `T.frozen v` holds, and `mask (T.code v w) j` otherwise. -/
def address (v w : V) (j : Fin (d + 1)) :=
  if T.frozen v then T.code v w else mask (T.code v w) j

open Classical in
/-- The value specified by `(v, j, T.address v w j)`. -/
def branch (v w : V) (j : Fin (d + 1)) : Relay V d := (v, j, T.address v w j)

open Classical in
theorem address_last (v w : V) : T.address v w (Fin.last d) = T.code v w := by
  have h : mask (T.code v w) d = T.code v w := funext fun i => ite_eq_left i.isLt
  simp [address, h]

open Classical in
/-- The value specified by `Fin.cases (.inl v) (fun i => .inr (v, i.castSucc, if T.frozen v then
c else mask c i)) j`. -/
def up (v : V) (j : Fin (d + 1)) (c : Address d) : Node V d :=
  Fin.cases (.inl v) (fun i => .inr (v, i.castSucc, if T.frozen v then c else mask c i)) j

open Classical in
/-- The down of type `Node V d` for the given inputs. -/
def down (v : V) (j : Fin (d + 1)) (c : Address d) (b : Bool) : Node V d :=
  Fin.lastCases (.inr (T.branch (T.peer v c) v (Fin.last d)))
    (fun i => .inr (v, i.succ, if T.frozen v then c else Function.update c i b)) j

open Classical in
private theorem up_branch (v w : V) (j : Fin d) :
    T.up v j.succ (T.address v w j.succ) = .inr (T.branch v w j.castSucc) := by
  simp only [up, Fin.cases_succ, branch, address]
  by_cases h : T.frozen v
  · simp [h]
  · simp only [ite_eq_right h]
    congr 3
    funext i
    simp only [mask, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> first | rfl | omega

open Classical in
private theorem down_branch (v w : V) (j : Fin d) :
    T.down v j.castSucc (T.address v w j.castSucc) (T.code v w j) = .inr (T.branch v w j.succ) := by
  simp only [down, Fin.lastCases_castSucc, branch, address]
  by_cases h : T.frozen v
  · simp [h]
  · simp only [ite_eq_right h]
    congr 3
    funext i
    by_cases he : i = j
    · subst i; simp [mask]
    · rw [Function.update_of_ne he]
      simp only [mask, Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> first | rfl | omega

open Classical in
/-- The possible used in the `Trie` construction. -/
def possible : Node V d → Finset (Node V d)
  | .inl v => if T.frozen v then univ.image (fun c : Address d => .inr (v, 0, c))
    else {.inr (v, 0, fun _ => false)}
  | .inr (v, j, c) => {T.up v j c, T.down v j c false, T.down v j c true}

open Classical in
/-- Selects the elements of `(T.possible x)` satisfying `(fun y => x ∈ T.possible y)`. -/
def adj (x : Node V d) := (T.possible x).filter (fun y => x ∈ T.possible y)

open Classical in
/-- Selects the elements of `(T.adj x)` satisfying `(fun y => ¬ T.fixed x ∧ ¬ T.fixed y)`. -/
def core (x : Node V d) := (T.adj x).filter (fun y => ¬ T.fixed x ∧ ¬ T.fixed y)

open Classical in
theorem adj_symm {x y : Node V d} : y ∈ T.adj x → x ∈ T.adj y := by
  simp [adj, and_comm]

open Classical in
theorem core_symm {x y : Node V d} (h : y ∈ T.core x) : x ∈ T.core y := by
  obtain ⟨h, hx, hy⟩ := mem_filter.mp h
  exact mem_filter.mpr ⟨T.adj_symm h, hy, hx⟩

open Classical in
theorem separate {v w : Node V d} (h : w ∈ T.adj v) : ¬ (T.fixed v ∧ T.fixed w) := by
  rintro ⟨hv, hw⟩
  cases v with
  | inr _ => exact hv
  | inl v =>
    cases w with
    | inr _ => exact hw
    | inl w =>
      change T.frozen v at hv
      have := (mem_filter.mp h).1
      simp [possible, hv] at this

open Classical in
theorem relay_degree (v : Relay V d) : (T.adj (.inr v)).card ≤ 3 := by
  obtain ⟨u, j, c⟩ := v
  refine (card_filter_le _ _).trans ?_
  unfold possible
  have hh := card_insert_le (T.down u j c false) {T.down u j c true}
  simp only [card_singleton] at hh
  exact (card_insert_le _ _).trans (by omega)

open Classical in
theorem degree (v : Node V d) : (T.adj v).card ≤ max 3 (2 ^ d) := by
  cases v with
  | inl v =>
    refine (card_filter_le _ _).trans ?_
    simp only [possible]
    split_ifs
    · apply le_trans card_image_le
      simp [Address]
    · simp
  | inr v => exact (T.relay_degree v).trans (le_max_left _ _)

open Classical in
theorem core_degree (v : Node V d) : (T.core v).card ≤ 3 := by
  cases v with
  | inl v =>
    by_cases h : T.frozen v
    · simp [core, fixed, h]
    · refine (card_filter_le _ _).trans ((card_filter_le _ _).trans ?_)
      simp [possible, h]
  | inr v => exact (card_filter_le _ _).trans (T.relay_degree v)

open Classical in
private theorem mem_up (v : V) (j : Fin (d + 1)) (c : Address d) :
    T.up v j c ∈ T.possible (.inr (v, j, c)) := mem_insert_self _ _

open Classical in
private theorem mem_down (v : V) (j : Fin (d + 1)) (c : Address d) (b : Bool) :
    T.down v j c b ∈ T.possible (.inr (v, j, c)) := by cases b <;> simp [possible]

open Classical in
theorem root (v w : V) : .inr (T.branch v w 0) ∈ T.adj (.inl v) := by
  apply mem_filter.mpr
  refine ⟨?_, T.mem_up v 0 (T.address v w 0)⟩
  by_cases h : T.frozen v
  · simp [possible, h, branch]
  · have he : mask (T.code v w) 0 = fun _ => false := by funext i; simp [mask]
    simp [possible, h, branch, address, he]

open Classical in
theorem edge (v w : V) (j : Fin d) :
    .inr (T.branch v w j.succ) ∈ T.adj (.inr (T.branch v w j.castSucc)) := by
  apply mem_filter.mpr
  constructor
  · rw [← T.down_branch]
    exact T.mem_down _ _ _ _
  · rw [← T.up_branch]
    exact T.mem_up _ _ _

open Classical in
private theorem end_mem {v w : V} (h : w ∈ T.near v) :
    .inr (T.branch w v (Fin.last d)) ∈ T.possible (.inr (T.branch v w (Fin.last d))) := by
  have he := T.mem_down v (Fin.last d) (T.address v w (Fin.last d)) false
  simpa only [down, Fin.lastCases_last, branch, address_last, T.peer_code h] using he

open Classical in
theorem join {v w : V} (h : w ∈ T.near v) :
    .inr (T.branch w v (Fin.last d)) ∈ T.adj (.inr (T.branch v w (Fin.last d))) :=
  mem_filter.mpr ⟨T.end_mem h, T.end_mem (T.symm w v h)⟩

end Trie
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout
