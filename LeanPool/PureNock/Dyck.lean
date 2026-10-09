/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree

/-!
# Dyck words and proper binary trees

Formalizes the grammar, tree encoding, graded correspondence, and Catalan
cardinality in `Lem:optimal_dyck` (`main.tex:337–342`).
-/

@[expose] public section

namespace Nock

/-! ### The Dyck language (main.tex:337) -/

-- main.tex:337  (prelude of Lem:optimal_dyck — L_dk)
/-- Prelude of **`Lem:optimal_dyck`** (`main.tex:337`).
    `L_dk = { w ∈ {0,1}^* | w=ε or ∃ w₁,w₂ ∈ L_dk s.t. w = 0 w₁ 1 w₂ }`. -/
inductive Dyck : List Bool → Prop
  | eps : Dyck []
  | cat {w₁ w₂ : List Bool} : Dyck w₁ → Dyck w₂ → Dyck (false :: w₁ ++ true :: w₂)

/-! ### Proper binary tree shapes = `L_full_BT` (main.tex:318–327) -/

-- main.tex:318–327  (Def:Proper_BT)
/-- **`Def:Proper_BT`** (`main.tex:318–327`).
    `L_full_BT = { t ∈ T | (size(t)=1) ∪ (left(t) ∈ L_full_BT ∩ right(t) ∈ L_full_BT ∩ (left(t)
    ∩ right(t)=∅)) }`;
    `L^λ_full_BT = { t ∈ L_full_BT | size(t)=λ }`. -/
inductive BTree where
  | leaf : BTree
  | node : BTree → BTree → BTree
deriving Repr, DecidableEq, Inhabited

namespace BTree

/-- Total node count of a shape (matches `Noun.size`). -/
def size : BTree → Nat
  | .leaf     => 1
  | .node l r => 1 + l.size + r.size

/-- The Dyck encoding of a proper binary tree (main.tex:337): `leaf ↦ ε`,
    `node l r ↦ 0 · encode l · 1 · encode r`. -/
def encode : BTree → List Bool
  | .leaf     => []
  | .node l r => false :: encode l ++ true :: encode r

/-- A Dyck word encoding a tree has length `size − 1` (each internal node contributes the
    pair `0…1`).  Stated additively to avoid truncated subtraction. -/
theorem encode_length_add_one (t : BTree) : (encode t).length + 1 = t.size := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      simp only [encode, size, List.length_cons, List.length_append]
      omega

/-! ### `encode` lands in the Dyck language, and is onto it (main.tex:340) -/

-- main.tex:340  (⇐ direction of `L_dk ≡ L_full_BT`: every tree's encoding is Dyck)
/-- Every tree encodes to a Dyck word. -/
theorem dyck_encode (t : BTree) : Dyck (encode t) := by
  induction t with
  | leaf => exact Dyck.eps
  | node l r ihl ihr => exact Dyck.cat ihl ihr

-- main.tex:340  (⇒ direction of `L_dk ≡ L_full_BT`: every Dyck word is some tree's encoding)
/-- Every Dyck word is the encoding of some tree (surjectivity of `encode` onto `L_dk`). -/
theorem exists_encode_of_dyck {w : List Bool} (h : Dyck w) : ∃ t : BTree, encode t = w := by
  induction h with
  | eps => exact ⟨.leaf, rfl⟩
  | @cat w₁ w₂ _ _ ih₁ ih₂ =>
      obtain ⟨t₁, ht₁⟩ := ih₁
      obtain ⟨t₂, ht₂⟩ := ih₂
      exact ⟨.node t₁ t₂, by simp only [encode, ht₁, ht₂]⟩

/-! ### A greedy parser, to pin down injectivity of `encode`

    `decode fuel w` parses exactly one tree off the front of `w`, returning the tree and the
    unconsumed suffix.  A leading `0` (`false`) starts a `node`; anything else (a leading `1`
    or the empty word) is a `leaf` consuming nothing.  This is the algorithmic inverse of
    `encode`; `decode_encode` proves the round-trip, which yields injectivity. -/
/-- Parse one binary tree from a Dyck prefix, returning the tree and unconsumed suffix. -/
def decode : Nat → List Bool → Option (BTree × List Bool)
  | 0,         _                => none
  | fuel + 1, (false :: rest) =>
      match decode fuel rest with
      | some (l, true :: rest₁) =>
          match decode fuel rest₁ with
          | some (r, rest₂) => some (.node l r, rest₂)
          | none            => none
      | _ => none
  | _ + 1,     rest            => some (.leaf, rest)   -- leading `1`, or `[]`

end BTree
end Nock

namespace Nock
namespace BTree

/-! ### Round-trip: `decode` inverts `encode`, hence `encode` is injective -/

/-- The greedy parser recovers the encoded tree and returns the untouched suffix, provided
    the fuel covers the tree's size and the suffix is not "open"-led (which is exactly the
    invariant maintained by the recursion: a left subtree is followed by its closing `1`, a
    right subtree by the parent's suffix). -/
theorem decode_encode :
    ∀ (t : BTree) (fuel : Nat) (rest : List Bool),
      t.size ≤ fuel → (rest = [] ∨ rest.head? = some true) →
      decode fuel (encode t ++ rest) = some (t, rest) := by
  intro t
  induction t with
  | leaf =>
      intro fuel rest _ hrest
      cases fuel with
      | zero => simp [size] at *
      | succ f =>
          simp only [encode, List.nil_append]
          rcases hrest with h | h
          · subst h; rfl
          · cases rest with
            | nil => rfl
            | cons b rs =>
                simp only [List.head?_cons, Option.some.injEq] at h
                subst h; rfl
  | node l r ihl ihr =>
      intro fuel rest hsize hrest
      cases fuel with
      | zero => simp [size] at hsize
      | succ f =>
          -- fuel = f+1, f ≥ size l + size r ≥ size l, size r
          simp only [size] at hsize
          have hfl : l.size ≤ f := by omega
          have hfr : r.size ≤ f := by omega
          -- left subtree: continuation starts with `true`
          have hL := ihl f (true :: (encode r ++ rest)) hfl (Or.inr rfl)
          -- right subtree: continuation is the (open-free) `rest`
          have hR := ihr f rest hfr hrest
          simp only [encode, List.cons_append, List.append_assoc, decode, hL, hR]

/-- `encode` is injective: distinct shapes have distinct Dyck words. -/
theorem encode_injective {t₁ t₂ : BTree} (h : encode t₁ = encode t₂) : t₁ = t₂ := by
  have hlen : t₁.size = t₂.size := by
    have e₁ := encode_length_add_one t₁
    have e₂ := encode_length_add_one t₂
    rw [h] at e₁; omega
  have d₁ : decode t₁.size (encode t₁ ++ []) = some (t₁, []) :=
    decode_encode t₁ t₁.size [] (Nat.le_refl _) (Or.inl rfl)
  have d₂ : decode t₁.size (encode t₂ ++ []) = some (t₂, []) :=
    decode_encode t₂ t₁.size [] (by omega) (Or.inl rfl)
  rw [h] at d₁
  have := d₁.symm.trans d₂
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this.1

/-! ### `Lem:optimal_dyck` (main.tex:340–342) -/

-- main.tex:340–342  (Lem:optimal_dyck)
/-- **`Lem:optimal_dyck`** (`main.tex:340–342`).
    `L_dk ≡ L_full_BT`. -/
theorem dyck_iff_encode {w : List Bool} : Dyck w ↔ ∃ t : BTree, encode t = w :=
  ⟨exists_encode_of_dyck, fun ⟨t, ht⟩ => ht ▸ dyck_encode t⟩

-- main.tex:340–342  (Lem:optimal_dyck)
/-- **`Lem:optimal_dyck`** (`main.tex:340–342`).
    `∀λ, L^{2λ}_dk ≡ L^{2λ+1}_full_BT`. -/
theorem dyck_length_graded {w : List Bool} (t : BTree) (ht : encode t = w) (lam : Nat) :
    w.length = 2 * lam ↔ t.size = 2 * lam + 1 := by
  have := encode_length_add_one t
  rw [ht] at this
  omega

end BTree

/-! ### Connection to `Noun`: a noun is a shape (`BTree`) plus leaf data (main.tex:347) -/

namespace Noun

-- main.tex:347,1164  (a noun `n = (t, dt)` = a Dyck word/tree shape `t` + leaf array `dt`)
/-- The **shape** of a noun: erase the leaf data, leaving a proper binary tree (`L_full_BT`).
    The paper's noun `(t, dt)` pairs this shape (encoded as the Dyck word `t`) with the leaf
    array `dt`; the Dyck bijection above governs the `t` component. -/
def shape : Noun → Nock.BTree
  | .atom _   => .leaf
  | .cell l r => .node l.shape r.shape

/-- The shape preserves leaf and node counts (`Noun.size = BTree.size ∘ shape`). -/
theorem shape_size (n : Noun) : n.shape.size = n.size := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [shape, Nock.BTree.size, size]; omega

/-- The Dyck word of a noun: the encoding of its shape.  By `Lem:pbt_size` (main.tex:333) a
    noun with `λ` leaves has size `2λ − 1`, so its Dyck word has length `2λ − 2 = 2(λ−1)`,
    matching the paper's `L^{2(λ−1)}_dk` component of a noun (main.tex:1164). -/
def dyckWord (n : Noun) : List Bool := n.shape.encode

/-- A noun's Dyck word has length `2·leaves − 2 = 2(λ−1)` (main.tex:1164). -/
theorem dyckWord_length (n : Noun) : n.dyckWord.length + 2 = 2 * n.leaves := by
  have h1 := Nock.BTree.encode_length_add_one n.shape
  have h2 := shape_size n
  have h3 := size_add_one n
  simp only [dyckWord]
  omega

/-! ### Leaf array + Def "noun" uniqueness (main.tex:347)

    A noun is `(t, dt)` = Dyck shape + DFS leaf array.  These live here (not in NPR) so the
    Pure Nock language closure can talk about uniqueness without importing Field/Goldilocks. -/

/-- The leaf values of a noun in left-to-right (DFS) order — the paper's leaf array `dt`
    (main.tex:1164), here over `Nat` (cast into the field at the NPR layer). -/
def leafList : Noun → List Nat
  | .atom k   => [k]
  | .cell l r => l.leafList ++ r.leafList

@[simp] theorem leafList_length (n : Noun) : n.leafList.length = n.leaves := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp [leafList, leaves, ihl, ihr]

-- main.tex:333,347  (a noun's shape fixes its leaf count `λ`)
/-- Equal shape ⇒ equal leaf count: the Dyck shape already determines `λ` (`Lem:pbt_size`,
    main.tex:333), so it constrains how the leaf array splits between the two subtrees. -/
theorem shape_leaves_eq {n₁ n₂ : Noun} (h : n₁.shape = n₂.shape) :
    n₁.leaves = n₂.leaves := by
  have hs : n₁.shape.size = n₂.shape.size := by rw [h]
  rw [shape_size, shape_size] at hs
  have e₁ := size_add_one n₁
  have e₂ := size_add_one n₂
  omega

-- main.tex:347  (shape + leaf array reconstruct the noun uniquely)
/-- **Reconstruction.**  If two nouns have the same shape (Dyck word) and the same leaf
    array, they are the *same* noun: the shape fixes the tree structure and the leaf list
    fills the leaves in DFS order, leaving no ambiguity. -/
theorem eq_of_shape_leafList :
    ∀ {n₁ n₂ : Noun}, n₁.shape = n₂.shape → n₁.leafList = n₂.leafList → n₁ = n₂ := by
  intro n₁
  induction n₁ with
  | atom k₁ =>
      intro n₂ hshape hleaf
      cases n₂ with
      | atom k₂ =>
          simp only [leafList, List.cons.injEq, and_true] at hleaf; rw [hleaf]
      | cell l r => simp [shape] at hshape
  | cell l₁ r₁ ihl ihr =>
      intro n₂ hshape hleaf
      cases n₂ with
      | atom k₂ => simp [shape] at hshape
      | cell l₂ r₂ =>
          simp only [shape, BTree.node.injEq] at hshape
          obtain ⟨hsl, hsr⟩ := hshape
          simp only [leafList] at hleaf
          have hlen : l₁.leafList.length = l₂.leafList.length := by
            rw [leafList_length, leafList_length, shape_leaves_eq hsl]
          obtain ⟨hll, hrl⟩ := List.append_inj hleaf hlen
          rw [ihl hsl hll, ihr hsr hrl]

-- main.tex:347  (Def "noun": the tuple `(t, dt)` corresponds to a UNIQUE noun)
/-- **Def "noun" uniqueness (main.tex:347).**  The map sending a noun to its Dyck word +
    leaf array, `n ↦ (n.dyckWord, n.leafList)`, is injective.  This is the paper's claim
    that the tuple `(t, dt)` "corresponds to a unique noun" (main.tex:345,347). -/
theorem noun_dyck_leaf_injective :
    Function.Injective (fun n : Noun => (n.dyckWord, n.leafList)) := by
  intro n₁ n₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hd, hl⟩ := h
  have hshape : n₁.shape = n₂.shape :=
    BTree.encode_injective (by simpa only [dyckWord] using hd)
  exact eq_of_shape_leafList hshape hl

end Noun

/-! ### Catalan cardinality `|L^{2λ}_dk| = C_λ` (`Lem:optimal_dyck`, main.tex:341) -/

namespace BTree

/-- The shape isomorphism to Mathlib's `BinaryTree`: a proper-binary-tree `leaf` is Mathlib's
    empty leaf `nil`; a `node` is a Mathlib `node` carrying the unit value. -/
def toBin : BTree → BinaryTree Unit
  | .leaf     => .nil
  | .node l r => .node () (toBin l) (toBin r)

/-- Inverse of `toBin`. -/
def ofBin : BinaryTree Unit → BTree
  | .nil        => .leaf
  | .node _ l r => .node (ofBin l) (ofBin r)

@[simp] theorem ofBin_toBin (t : BTree) : ofBin (toBin t) = t := by
  induction t <;> simp_all [toBin, ofBin]

@[simp] theorem toBin_ofBin (t : BinaryTree Unit) : toBin (ofBin t) = t := by
  induction t <;> simp_all [toBin, ofBin]

/-- Under the shape isomorphism, `BTree.size` is `2·numNodes + 1`: a proper binary tree with
    `λ` internal (Mathlib) nodes has `2λ+1` total nodes (`Lem:pbt_size`, main.tex:333). -/
theorem size_eq (t : BTree) : t.size = 2 * (toBin t).numNodes + 1 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      simp only [size, toBin, BinaryTree.numNodes, ihl, ihr]
      omega

/-- **`|L^{2λ}_dk|` as a finset (main.tex:337–341).**  The Dyck words of length `2λ`, obtained
    as the image of Mathlib's `treesOfNumNodesEq λ` under `encode ∘ ofBin`. -/
noncomputable def dyckWordsOfLen (lam : ℕ) : Finset (List Bool) :=
  (BinaryTree.treesOfNumNodesEq lam).map
    ⟨fun t => encode (ofBin t), by
      intro a b h
      have := encode_injective h
      have := congrArg toBin this
      simpa using this⟩

/-- A word lies in `dyckWordsOfLen λ` iff it is a Dyck word of length `2λ` — i.e. this finset is
    exactly the paper's `L^{2λ}_dk`. -/
theorem mem_dyckWordsOfLen {lam : ℕ} {w : List Bool} :
    w ∈ dyckWordsOfLen lam ↔ Dyck w ∧ w.length = 2 * lam := by
  simp only [dyckWordsOfLen, Finset.mem_map, Function.Embedding.coeFn_mk,
    BinaryTree.mem_treesOfNumNodesEq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨dyck_encode _, ?_⟩
    have hlen := encode_length_add_one (ofBin t)
    have hsz := size_eq (ofBin t)
    rw [toBin_ofBin, ht] at hsz
    omega
  · rintro ⟨hd, hlen⟩
    obtain ⟨s, hs⟩ := exists_encode_of_dyck hd
    refine ⟨toBin s, ?_, ?_⟩
    · have hlen' := encode_length_add_one s
      have hsz := size_eq s
      rw [hs, hlen] at hlen'
      omega
    · rw [ofBin_toBin, hs]

-- main.tex:340–342  (Lem:optimal_dyck)
/-- **`Lem:optimal_dyck`** (`main.tex:340–342`).
    `|L^{2λ}_dk| = C_λ`. -/
theorem dyckWordsOfLen_card (lam : ℕ) : (dyckWordsOfLen lam).card = catalan lam := by
  rw [dyckWordsOfLen, Finset.card_map, BinaryTree.treesOfNumNodesEq_card_eq_catalan]

end BTree
end Nock
