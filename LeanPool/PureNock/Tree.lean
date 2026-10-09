/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

/-!
# Nouns

Inductive proper binary trees with `Nat` atoms (`main.tex:318–349`).
-/

@[expose] public section

namespace Nock

-- main.tex:347–349  (Def:noun)
/-- **`Def:noun`** (`main.tex:347–349`).
    `n := (t, dt) ∈ L_dk^{2·(λ−1)} × DT(F)^λ := N^λ(F)` is a noun of size `λ` over field `F`.
    (paper: field F; Lean: Nat leaves.) -/
inductive Noun where
  | atom : Nat → Noun
  | cell : Noun → Noun → Noun
deriving Repr, DecidableEq, Inhabited

namespace Noun

/-- `?` in Nock terms: is this noun a cell? -/
def isCell : Noun → Bool
  | .cell _ _ => true
  | .atom _   => false

/-- Test whether a noun is an atomic value rather than a cell. -/
def isAtom (n : Noun) : Bool := !n.isCell

-- main.tex:329–331  (Def:tree_nodes)
/-- **`Def:tree_nodes`** (`main.tex:329–331`).
    Given `t ∈ L_full_BT`, a node with no children is a leaf; a non-leaf is an internal node. -/
def leaves : Noun → Nat
  | .atom _   => 1
  | .cell l r => l.leaves + r.leaves

/-- Total node count. -/
def size : Noun → Nat
  | .atom _   => 1
  | .cell l r => 1 + l.size + r.size

-- main.tex:329–331  (Def:tree_nodes)
/-- **`Def:tree_nodes`** (`main.tex:329–331`).
    Given `t ∈ L_full_BT`, a node with no children is a leaf; a non-leaf is an internal node. -/
def internal : Noun → Nat
  | .atom _   => 0
  | .cell l r => 1 + l.internal + r.internal

/-! ### `Lem:pbt_size` (main.tex:333–335) -/

-- main.tex:333–335  (Lem:pbt_size — additive form)
theorem size_add_one (n : Noun) : n.size + 1 = 2 * n.leaves := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [size, leaves]; omega

-- main.tex:333–335  (Lem:pbt_size)
/-- **`Lem:pbt_size`** (`main.tex:333–335`).
    A tree `t ∈ L_full_BT^{2λ−1}` has `λ−1` internal and `λ` leaf nodes. -/
theorem pbt_size (n : Noun) :
    n.size = 2 * n.leaves - 1 ∧ n.internal = n.leaves - 1 := by
  have hs : n.size + 1 = 2 * n.leaves := size_add_one n
  refine ⟨by omega, ?_⟩
  induction n with
  | atom k => rfl
  | cell l r ihl ihr =>
      have hl := size_add_one l
      have hr := size_add_one r
      simp only [internal, leaves]; omega

-- main.tex:333–335  (Lem:pbt_size)
/-- **`Lem:pbt_size`** (`main.tex:333–335`).
    A tree `t ∈ L_full_BT^{2λ−1}` has `λ−1` internal and `λ` leaf nodes. -/
theorem pbt_size_of_size {n : Noun} {lam : Nat} (hlam : 1 ≤ lam)
    (h : n.size = 2 * lam - 1) : n.leaves = lam ∧ n.internal = lam - 1 := by
  have hs : n.size + 1 = 2 * n.leaves := size_add_one n
  have hi : n.internal = n.leaves - 1 := (pbt_size n).2
  refine ⟨by omega, by omega⟩

/-- Every node of a proper binary tree is a leaf or an internal node:
    `size = leaves + internal`. -/
theorem size_eq_leaves_add_internal (n : Noun) : n.size = n.leaves + n.internal := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [size, leaves, internal]; omega

/-- Every noun has at least one leaf (atoms contribute 1; cells sum positive leaf counts). -/
theorem one_le_leaves (n : Noun) : 1 ≤ n.leaves := by
  induction n with
  | atom k => simp [leaves]
  | cell l r ihl ihr => simp only [leaves]; omega

end Noun

/-! The circular S-expression object at `main.tex:305–312` is out of scope:
the paper restricts subsequent use to proper binary trees. -/

/-! ### Proper n-ary trees (`main.tex:351–364`)

The paper includes this unused generalization for completeness. -/

-- main.tex:355–363  (Def: Proper n-ary Tree)
/-- **`Def` proper n-ary** (`main.tex:355–363`).
    `L_full_T,n = { t ∈ T^n | (size(t)=1) ∪ ((⋂_{1≤i≤n} child_i(t) ∈ L_full_T^n) ∩ (∅ =
    ⋂_{1≤i≤n} child_i(t))) }`;
    `L^λ_full_T,n = { t ∈ L_full_T^n | size(t)=λ }`.
    Unused in paper body. -/
inductive NAryTree (k : Nat) where
  | leaf : NAryTree k
  | node : (Fin k → NAryTree k) → NAryTree k

namespace NAryTree

-- main.tex:353  (`child_i : T^n → T^n`)
/-- Return the indexed child of an internal n-ary tree, or none at a leaf. -/
def childi {k : Nat} (i : Fin k) : NAryTree k → Option (NAryTree k)
  | .leaf   => none
  | .node f => some (f i)

end NAryTree

end Nock
