/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Models.Observations
public import LeanPool.DeciSigma1.Satisfiability.Decide
import Mathlib.Data.Set.Finite.List

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Trees over `{⊥, f}` as trees over `{⊥, f, ⊤}` without `⊤`

A tree over `{⊥, f}` is a set `P` of constructor positions. Labeling these positions `f` and
every other path of the domain `⊥` gives a tree `P.toTree` over `{⊥, f, ⊤}` in which `⊤` does
not occur, and every such tree arises from the set `t.positions` of its constructor positions.
The correspondence preserves `⊥`, the constructor, the covariant order, regularity and
finiteness.

The trees without `⊤` are those below the tree `PrefixSet.univ.toTree`, all of whose paths are
labeled `f`. They are also described by an inequality: when `u ≤ f(u, …, u)` in the covariant
order, no tree below `u` contains `⊤` (`Tree.isTopFree_of_le_of_le_node`), and the tree
`PrefixSet.univ.toTree` satisfies this inequality with equality.

## Main declarations

- `Tree.IsTopFree`, `Tree.positions`: trees in which `⊤` does not occur, and their constructor
  positions.
- `PrefixSet.toTree`, `PrefixSet.positions_toTree`, `Tree.toTree_positions`: the embedding and
  its inverse on trees without `⊤`.
- `PrefixSet.toTree_le_toTree`, `PrefixSet.toTree_bot`, `PrefixSet.toTree_node`: the embedding
  preserves and reflects the order and commutes with `⊥` and the constructor.
- `Tree.isTopFree_of_le_of_le_node`: trees below a tree `u ≤ f(u, …, u)` contain no `⊤`.
- `PrefixSet.univ`, `PrefixSet.node_univ`: the tree all of whose paths are labeled `f`.
- `PrefixSet.subtrees_toTree_finite_iff`, `PrefixSet.finiteTop_toTree_iff`: the embedding
  preserves and reflects regularity and finiteness.
-/

@[expose] public section


namespace DeciSigma1.Semantics

variable {n : ℕ}

namespace Tree

/-- The label `⊤` does not occur in the tree. -/
def IsTopFree (t : Tree n) : Prop := ∀ π, t.fn π ≠ some Sym.top

/-- The constructor positions of a tree: the paths labeled `f`. -/
def positions (t : Tree n) : PrefixSet n where
  carrier := {π | t.fn π = some Sym.f}
  prefix_closed := by
    intro u v h
    by_cases hv : v = []
    · simpa [hv] using h
    · exact t.label_eq_f_of_proper_prefix (List.prefix_append u v) (by simpa using hv)
        (by simp [show t.fn (u ++ v) = some Sym.f from h])

@[simp] theorem mem_positions (t : Tree n) (π : List (Fin n)) :
    π ∈ t.positions.carrier ↔ t.fn π = some Sym.f := Iff.rfl

private theorem eq_f_of_f_le {b : Sym} (h : Sym.f ≤ b) (hb : b ≠ Sym.top) : b = Sym.f := by
  cases b
  · exact absurd h (by decide)
  · rfl
  · exact absurd rfl hb

/-- If `⊤` does not occur in `u`, the covariant order `t ≤ u` gives the inclusion of
constructor positions. -/
theorem positions_le_of_le {t u : Tree n} (hu : u.IsTopFree) (h : t ≤ u) :
    t.positions ≤ u.positions := by
  intro π
  induction π using List.reverseRecOn with
  | nil =>
    intro ht
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp u.root_isSome
    exact hb.trans (congrArg some (eq_f_of_f_le (h [] _ b ht hb) fun he => hu [] (he ▸ hb)))
  | append_singleton π i ih =>
    intro ht
    have hπ : u.fn π = some Sym.f := ih (t.positions.prefix_closed π [i] ht)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((u.child_isSome_iff π i).mpr hπ)
    exact hb.trans (congrArg some (eq_f_of_f_le (h _ _ b ht hb) fun he => hu _ (he ▸ hb)))

/-- If `⊤` does not occur in `t`, the inclusion of constructor positions gives the covariant
order `t ≤ u`. -/
theorem le_of_positions_le {t u : Tree n} (ht : t.IsTopFree) (h : t.positions ≤ u.positions) :
    t ≤ u := by
  intro π a b ha hb
  cases a with
  | bot => exact Sym.bot_le b
  | f => exact (Option.some.inj ((h (show π ∈ t.positions.carrier from ha)).symm.trans hb)).le
  | top => exact absurd ha (ht π)

/-- On trees without `⊤`, the covariant order is the inclusion of constructor positions. -/
theorem le_iff_positions_le {t u : Tree n} (ht : t.IsTopFree) (hu : u.IsTopFree) :
    t ≤ u ↔ t.positions ≤ u.positions :=
  ⟨positions_le_of_le hu, le_of_positions_le ht⟩

/-- If `u ≤ f(u, …, u)` in the covariant order, then `⊤` does not occur in any tree below
`u`. -/
theorem isTopFree_of_le_of_le_node {t u : Tree n} (hu : u ≤ node fun _ => u) (ht : t ≤ u) :
    t.IsTopFree := by
  intro π
  induction π generalizing t with
  | nil =>
    intro h
    rw [(root_eq_top_iff t).mp h, top_le_iff] at ht
    rw [ht, top_le_iff] at hu
    exact node_ne_top _ hu
  | cons i π ih =>
    rcases (le_iff_root_cases t u).mp ht with rfl | rfl | ⟨a, b, rfl, rfl, hab⟩
    · simp
    · rw [top_le_iff] at hu
      exact absurd hu (node_ne_top _)
    · exact ih ((hab i).trans ((node_le_node_iff _ _).mp hu i))

/-- A subtree of a tree without `⊤` contains no `⊤`. -/
theorem IsTopFree.subtree {t u : Tree n} (ht : t.IsTopFree) {π : List (Fin n)}
    (h : t.subtree π = some u) : u.IsTopFree :=
  fun ρ => by rw [subtree_fn h]; exact ht (π ++ ρ)

/-- The constructor positions of the subtree at `π` are the residual at `π`. -/
theorem positions_subtree {t u : Tree n} {π : List (Fin n)} (h : t.subtree π = some u) :
    u.positions = t.positions.residual π :=
  PrefixSet.ext (Set.ext fun ρ => by simp [PrefixSet.residual, subtree_fn h])

end Tree

namespace PrefixSet

open Classical in
/-- The tree over `{⊥, f, ⊤}` whose constructor positions are `P`: the paths in `P` are labeled
`f`, and the root and the children of paths in `P` are labeled `⊥` when they are not in `P`. -/
noncomputable def toTree (P : PrefixSet n) : Tree n where
  fn π :=
    if π ∈ P.carrier then some Sym.f
    else if π = [] ∨ π.dropLast ∈ P.carrier then some Sym.bot
    else none
  wf := by
    refine ⟨by split_ifs <;> simp_all, fun π i => ?_⟩
    have h := P.prefix_closed π [i]
    by_cases h₁ : π ++ [i] ∈ P.carrier <;> by_cases h₂ : π ∈ P.carrier <;> simp_all

theorem toTree_fn_eq_f (P : PrefixSet n) (π : List (Fin n)) :
    P.toTree.fn π = some Sym.f ↔ π ∈ P.carrier := by
  simp only [toTree]
  split_ifs <;> simp_all

/-- The label `⊤` does not occur in an embedded tree. -/
theorem isTopFree_toTree (P : PrefixSet n) : P.toTree.IsTopFree := by
  intro π
  simp only [toTree]
  split_ifs <;> simp

/-- The constructor positions of the embedded tree are the given ones. -/
@[simp] theorem positions_toTree (P : PrefixSet n) : P.toTree.positions = P :=
  PrefixSet.ext (Set.ext fun π => toTree_fn_eq_f P π)

/-- The embedding preserves and reflects the order. -/
@[simp] theorem toTree_le_toTree (P Q : PrefixSet n) : P.toTree ≤ Q.toTree ↔ P ≤ Q := by
  rw [Tree.le_iff_positions_le (isTopFree_toTree P) (isTopFree_toTree Q), positions_toTree,
    positions_toTree]

theorem toTree_injective : Function.Injective (toTree (n := n)) :=
  Function.LeftInverse.injective positions_toTree

/-- A tree without `⊤` is the embedding of its constructor positions. -/
theorem _root_.DeciSigma1.Semantics.Tree.toTree_positions {t : Tree n} (ht : t.IsTopFree) :
    t.positions.toTree = t :=
  le_antisymm
    (Tree.le_of_positions_le (isTopFree_toTree _) (positions_toTree _).le)
    (Tree.le_of_positions_le ht (positions_toTree _).ge)

/-- The embedding maps `⊥` to `⊥`. -/
@[simp] theorem toTree_bot : (bot : PrefixSet n).toTree = Tree.bot := by
  rw [← Tree.toTree_positions (t := Tree.bot) (fun π => by cases π <;> simp)]
  exact congrArg toTree (PrefixSet.ext (Set.ext fun π => by cases π <;> simp))

/-- The embedding commutes with the constructor. -/
theorem toTree_node (a : Fin n → PrefixSet n) :
    (node a).toTree = Tree.node fun i => (a i).toTree := by
  have ht : (Tree.node fun i => (a i).toTree).IsTopFree := by
    intro π
    cases π with
    | nil => simp
    | cons i π => exact isTopFree_toTree (a i) π
  rw [← Tree.toTree_positions ht]
  refine congrArg toTree (PrefixSet.ext (Set.ext fun π => ?_))
  cases π with
  | nil => simp
  | cons i π => simp [toTree_fn_eq_f]

@[simp] theorem toTree_eq_bot_iff (P : PrefixSet n) : P.toTree = Tree.bot ↔ P = bot := by
  rw [← toTree_bot, toTree_injective.eq_iff]

end PrefixSet

/-- A tree without `⊤` has finitely many subtrees exactly when its set of constructor positions
has finitely many residuals. -/
theorem Tree.IsTopFree.subtrees_finite_iff {t : Tree n} (ht : t.IsTopFree) :
    (Characterization.subtrees t).Finite ↔ IsRegularTree t.positions := by
  constructor
  · intro h
    apply ((h.image fun u => u.positions.carrier).insert ∅).subset
    rintro _ ⟨w, rfl⟩
    by_cases hw : (t.fn w).isSome
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp ((t.subtree_isSome_iff w).mpr hw)
      exact Or.inr ⟨u, ⟨w, hu⟩, congrArg PrefixSet.carrier (Tree.positions_subtree hu)⟩
    · refine Or.inl (Set.eq_empty_of_forall_notMem fun v hv => hw ?_)
      exact t.domain_append_left w v (by simp [show t.fn (w ++ v) = some Sym.f from hv])
  · intro h
    have hc : Function.Injective (PrefixSet.carrier (n := n)) := fun _ _ => PrefixSet.ext
    apply ((h.preimage hc.injOn).image PrefixSet.toTree).subset
    rintro u ⟨π, hu⟩
    exact ⟨u.positions, ⟨π, congrArg PrefixSet.carrier (Tree.positions_subtree hu).symm⟩,
      Tree.toTree_positions (ht.subtree hu)⟩

/-- The embedding preserves and reflects regularity. -/
theorem PrefixSet.subtrees_toTree_finite_iff (P : PrefixSet n) :
    (Characterization.subtrees P.toTree).Finite ↔ IsRegularTree P := by
  rw [(PrefixSet.isTopFree_toTree P).subtrees_finite_iff, PrefixSet.positions_toTree]

/-- The embedding preserves and reflects finiteness: `P.toTree` is the tree of a finite term
exactly when `P` has finitely many constructor positions. -/
theorem PrefixSet.finiteTop_toTree_iff (P : PrefixSet n) :
    Full.Models.FiniteTop P.toTree ↔ IsFiniteTree P := by
  constructor
  · rintro ⟨g, hg⟩
    refine (List.finite_length_le (Fin n) g.height).subset fun π hπ => g.length_le_height ?_
    rw [hg, (PrefixSet.toTree_fn_eq_f P π).mpr hπ]
    rfl
  · intro h
    obtain ⟨d, hd⟩ := (h.image List.length).bddAbove
    refine ⟨FTree.truncate (d + 1) P.toTree, FTree.toTree_truncate fun π hπ => ?_⟩
    simp only [PrefixSet.toTree] at hπ
    split_ifs at hπ with h₁ h₂
    · exact (hd ⟨π, h₁, rfl⟩).trans (Nat.le_succ d)
    · rcases h₂ with rfl | h₂
      · simp
      · have := hd ⟨_, h₂, rfl⟩
        simp only [List.length_dropLast] at this
        omega
    · simp at hπ

end DeciSigma1.Semantics
