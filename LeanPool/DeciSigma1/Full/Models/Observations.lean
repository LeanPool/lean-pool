/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Semantics.PrefixSet
public import LeanPool.DeciSigma1.Constraints.Basic
public import LeanPool.DeciSigma1.Semantics.Classes

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Observations of trees and ground bounds

An observation of a tree at a path records whether the tree reaches `⊤` along the path, or whether
it reaches `⊥`. A tree is determined by the set of paths along which it does not reach `⊥` and the
set along which it does not reach `⊤` (`PrefixPair.realize`), and each observation, or its negation,
is equivalent to a bound by a finite tree (`observation_bound`). This module also defines the
regular trees (`RegularTop`) and finite trees (`FiniteTop`) over `{⊥, f, ⊤}`, satisfiability in a
class of trees, and the property that finitely many compatible finite bounds can be realized by a
finite solution (`FiniteBoundPinning`).

## Main declarations

- `Models.HasTopPrefix`, `Models.nonBottomPrefixes`: the two observations of a tree.
- `Models.PrefixPair`, `Models.PrefixPair.realize`: trees from their observations.
- `Models.Observation`, `Models.GroundBound`, `Models.observation_bound`: observations as bounds by
  finite trees.
- `Models.RegularTop`, `Models.FiniteTop`, `Models.SatisfiableIn`: tree classes and satisfiability
  in a class.
- `Models.FiniteBoundPinning`: realization of finite bounds by finite solutions.
-/

@[expose] public section


namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics

variable {n : ℕ}

/-- The tree `t` reaches `⊤` along the path `w`. -/
def HasTopPrefix (t : Semantics.Tree n) (w : List (Fin n)) : Prop :=
  Semantics.Tree.HasLabel t w Sym.top

/-- The paths along which `t` does not reach `⊥`, a prefix-closed set. -/
def nonBottomPrefixes (t : Semantics.Tree n) : PrefixSet n where
  carrier := {w | ¬ Semantics.Tree.HasLabel t w Sym.bot}
  prefix_closed := by
    rintro u v h ⟨p, ⟨s, hs⟩, hp⟩
    apply h
    exact ⟨p, ⟨s ++ v, by simpa only [List.append_assoc] using congrArg (fun q => q ++ v) hs⟩, hp⟩

@[simp] theorem mem_nonBottomPrefixes (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ (nonBottomPrefixes t).carrier ↔ ¬ Semantics.Tree.HasLabel t w Sym.bot := Iff.rfl

@[simp] theorem not_hasTopPrefix_bot (w : List (Fin n)) :
    ¬ HasTopPrefix Tree.bot w := by simp [HasTopPrefix]
@[simp] theorem hasTopPrefix_top (w : List (Fin n)) :
    HasTopPrefix Tree.top w := by simp [HasTopPrefix]
@[simp] theorem nonBottomPrefixes_bot :
    nonBottomPrefixes (Tree.bot : Semantics.Tree n) = PrefixSet.bot := by ext w; simp

/-- The prefix-closed set of all paths. -/
@[simp] theorem nonBottomPrefixes_top :
    nonBottomPrefixes (Tree.top : Semantics.Tree n) = PrefixSet.univ := by ext w; simp

@[simp] theorem nonBottomPrefixes_node (a : Fin n → Semantics.Tree n) :
    nonBottomPrefixes (Semantics.Tree.node a) = PrefixSet.node (nonBottomPrefixes ∘ a) := by
  ext w
  cases w with
  | nil => simp [Semantics.Tree.HasLabel]
  | cons i w =>
      simp [Semantics.Tree.hasLabel_node_cons _ _ _ Sym.bot (by decide)]

theorem mem_nonBottomPrefixes_of_hasTopPrefix (t : Semantics.Tree n) (w : List (Fin n)) :
    HasTopPrefix t w → w ∈ (nonBottomPrefixes t).carrier := by
  intro ha hc
  have ht := (Semantics.Tree.trace_eq_top_iff _ _).mpr ha
  have hb := (Semantics.Tree.trace_eq_bot_iff _ _).mpr hc
  exact Tree.bot_ne_top (hb.symm.trans ht)

theorem hasLabel_dual (t : Semantics.Tree n) (w : List (Fin n)) :
    Semantics.Tree.HasLabel (Tree.dual t) w Sym.bot ↔ Semantics.Tree.HasLabel t w Sym.top := by
  simp only [Semantics.Tree.HasLabel, dual_fn, Option.map_eq_some_iff]
  constructor
  · rintro ⟨v, hv, s, hs, he⟩
    cases s <;> simp_all only [Sym.flip, reduceCtorEq]
    exact ⟨v, hv, hs⟩
  · rintro ⟨v, hv, hs⟩
    exact ⟨v, hv, Sym.top, hs, rfl⟩

theorem mem_nonBottomPrefixes_dual (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ (nonBottomPrefixes (Tree.dual t)).carrier ↔ ¬ HasTopPrefix t w := hasLabel_dual t _ |>.not

/-- A pair of prefix-closed sets of paths covering all paths: the paths along which a tree does not
reach `⊥` and those along which it does not reach `⊤`. -/
structure PrefixPair (n : ℕ) where
  /-- Paths whose prefixes carry no bottom label. -/
  nonBottom : PrefixSet n
  /-- Paths whose prefixes carry no top label. -/
  nonTop : PrefixSet n
  cover : ∀ w, w ∈ nonBottom.carrier ∨ w ∈ nonTop.carrier

/-- The pair of a child: the residuals at the child index. -/
def PrefixPair.child (p : PrefixPair n) (b : Fin n) : PrefixPair n :=
  ⟨p.nonBottom.subtree b, p.nonTop.subtree b, fun w => p.cover (b :: w)⟩

attribute [local instance] Classical.propDecidable

/-- The labeling represented by a pair of compatible prefix observations. -/
noncomputable def pairFn (p : PrefixPair n) : List (Fin n) → Option Semantics.Sym
  | [] => if [] ∉ p.nonBottom.carrier then some Sym.bot else
      if [] ∉ p.nonTop.carrier then some Sym.top else some Sym.f
  | b :: w =>
      if [] ∈ p.nonBottom.carrier ∧ [] ∈ p.nonTop.carrier then pairFn (p.child b) w else none

private theorem pairFn_child (p : PrefixPair n) (w : List (Fin n)) (b : Fin n) :
    (pairFn p (w ++ [b])).isSome ↔ pairFn p w = some Sym.f := by
  classical
  induction w generalizing p with
  | nil => simp only [List.nil_append, pairFn]; split_ifs <;> simp_all
  | cons a w ih =>
    simp only [List.cons_append, pairFn]
    split_ifs <;> simp_all

/-- The tree with the given observations: `⊥` where the empty path is outside `nonBottom`, `⊤` where
it is outside `nonTop`, and the constructor with the realizations of the children otherwise. -/
noncomputable def PrefixPair.realize (p : PrefixPair n) : Semantics.Tree n where
  fn := pairFn p
  wf := by
    constructor
    · classical
      simp only [pairFn]
      split_ifs <;> simp
    · exact pairFn_child p

theorem PrefixPair.realize_bot (p : PrefixPair n) (h : [] ∉ p.nonBottom.carrier) :
    PrefixPair.realize p = Tree.bot := by
  classical
  apply (Tree.root_eq_bot_iff _).mp
  simp [PrefixPair.realize, pairFn, h]

theorem PrefixPair.realize_top (p : PrefixPair n) (h : [] ∉ p.nonTop.carrier) :
    PrefixPair.realize p = Tree.top := by
  classical
  have hc : [] ∈ p.nonBottom.carrier := (p.cover []).resolve_right h
  apply (Tree.root_eq_top_iff _).mp
  simp [PrefixPair.realize, pairFn, h, hc]

theorem PrefixPair.realize_node (p : PrefixPair n) (hc : [] ∈ p.nonBottom.carrier)
    (hn : [] ∈ p.nonTop.carrier) :
    PrefixPair.realize p = Semantics.Tree.node (fun i => PrefixPair.realize (p.child i)) := by
  classical
  apply Tree.ext
  funext w
  cases w with
  | nil => simp [PrefixPair.realize, pairFn, hc, hn]
  | cons i w => simp [PrefixPair.realize, pairFn, hc, hn]

theorem PrefixPair.realize_observations (p : PrefixPair n) (w : List (Fin n)) :
    (w ∈ (nonBottomPrefixes (PrefixPair.realize p)).carrier ↔ w ∈ p.nonBottom.carrier) ∧
    (HasTopPrefix (PrefixPair.realize p) w ↔ w ∉ p.nonTop.carrier) := by
  classical
  induction w generalizing p with
  | nil =>
    by_cases hc : [] ∈ p.nonBottom.carrier
    · by_cases hn : [] ∈ p.nonTop.carrier
      · rw [PrefixPair.realize_node p hc hn]
        simp [HasTopPrefix, hc, hn]
      · rw [PrefixPair.realize_top p hn]; simp [hc, hn]
    · have hn := (p.cover []).resolve_left hc
      rw [PrefixPair.realize_bot p hc]; simp [hc, hn]
  | cons b w ih =>
    by_cases hc : [] ∈ p.nonBottom.carrier
    · by_cases hn : [] ∈ p.nonTop.carrier
      · rw [PrefixPair.realize_node p hc hn]
        have hh := ih (p.child b)
        simpa [nonBottomPrefixes_node, HasTopPrefix,
          Semantics.Tree.hasLabel_node_cons _ _ _ Sym.bot (by decide),
        Semantics.Tree.hasLabel_node_cons _ _ _ Sym.top (by decide), PrefixPair.child,
          PrefixSet.subtree, PrefixSet.residual] using hh
      · have hn' : b :: w ∉ p.nonTop.carrier := fun h => hn (p.nonTop.prefix_closed [] _ h)
        have hc' := (p.cover (b :: w)).resolve_right hn'
        rw [PrefixPair.realize_top p hn]; simp [hc', hn']
    · have hc' : b :: w ∉ p.nonBottom.carrier := fun h => hc (p.nonBottom.prefix_closed [] _ h)
      have hn' := (p.cover (b :: w)).resolve_left hc'
      rw [PrefixPair.realize_bot p hc]; simp [hc', hn']

@[simp] theorem PrefixPair.nonBottomPrefixes_realize (p : PrefixPair n) :
    nonBottomPrefixes (PrefixPair.realize p) = p.nonBottom := by
  ext w; exact (PrefixPair.realize_observations p w).1

end DeciSigma1.Full.Models

namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics

variable {n : ℕ}

/-- An observation of the variable `var` at the path `word`: whether the path lies in the non-bottom
set of the value (`dual = false`) or of its dual (`dual = true`), asserted when `value = true` and
negated otherwise. -/
structure Observation (n : ℕ) (X : Type*) where
  /-- Whether to observe the dual of the selected tree. -/
  dual : Bool
  /-- Variable whose tree is observed. -/
  var : X
  /-- Path at which the leaf observation is made. -/
  word : List (Fin n)
  /-- Required Boolean leaf label. -/
  value : Bool

/-- Truth of an observation for an assignment. -/
def Observation.Holds {X : Type*} (ρ : X → Semantics.Tree n) (o : Observation n X) : Prop :=
  let t := if o.dual then Tree.dual (ρ o.var) else ρ o.var
  if o.value then o.word ∈ (nonBottomPrefixes t).carrier else o.word ∉ (nonBottomPrefixes t).carrier

/-- A bound `tree ≤ var` (`lower = true`) or `var ≤ tree` by a finite tree. -/
structure GroundBound (n : ℕ) (V : Type*) where
  /-- Variable constrained by the finite tree. -/
  var : V
  /-- True for a lower bound; false for an upper bound. -/
  lower : Bool
  /-- Finite tree giving the bound. -/
  tree : FTree n

/-- Truth of a ground bound for an assignment, in the covariant order. -/
def GroundBound.Holds {V : Type*} (ρ : V → Semantics.Tree n) (b : GroundBound n V) : Prop :=
  if b.lower then b.tree.toTree ≤ ρ b.var else ρ b.var ≤ b.tree.toTree

end DeciSigma1.Full.Models

namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics

variable {n : ℕ}

/-- The finite tree with `g` at the path `w` and `⊥` at every other child along `w`. -/
def pathBound : List (Fin n) → FTree n → FTree n
  | [], g => g
  | i :: w, g => .node (fun j => if j = i then pathBound w g else .bot)

theorem pathBound_le_iff (w : List (Fin n)) (g : FTree n) (hg : g.toTree ≠ Tree.bot)
    (t : Semantics.Tree n) :
    (pathBound w g).toTree ≤ t ↔ g.toTree ≤ Semantics.Tree.trace t w := by
  induction w generalizing t with
  | nil => rfl
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [pathBound, hg]
    · simp [pathBound]
    · simp only [pathBound, FTree.toTree_node, Tree.node_le_node_iff,
        Semantics.Tree.trace_cons, Semantics.Tree.descend_node]
      rw [← ih]
      constructor
      · intro h
        simpa using h i
      · intro h j
        by_cases hj : j = i <;> simp [hj, h]

theorem node_bot_le_iff (t : Semantics.Tree n) :
    Semantics.Tree.node (fun _ => Tree.bot) ≤ t ↔ t ≠ Tree.bot := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;>
    simp [Tree.node_le_node_iff]

theorem pathBound_le_iff_mem_nonBottomPrefixes (t : Semantics.Tree n) (w : List (Fin n)) :
    (pathBound w (.node (fun _ => .bot))).toTree ≤ t ↔ w ∈ (nonBottomPrefixes t).carrier := by
  rw [pathBound_le_iff w _ (by simp), FTree.toTree_node, FTree.toTree_bot,
    node_bot_le_iff]
  simp only [ne_eq, Semantics.Tree.trace_eq_bot_iff]
  rfl

theorem pathBound_top_le_iff_hasTopPrefix (t : Semantics.Tree n) (w : List (Fin n)) :
    (pathBound w .top).toTree ≤ t ↔ HasTopPrefix t w := by
  rw [pathBound_le_iff w _ (by simp), FTree.toTree_top, Tree.top_le_iff,
    Semantics.Tree.trace_eq_top_iff]
  rfl

theorem le_dual_iff (t : Semantics.Tree n) (g : FTree n) :
    t ≤ g.dual.toTree ↔ g.toTree ≤ Tree.dual t := by
  rw [FTree.toTree_dual, ← dual_le_iff, dual_involutive]

/-- The ground bound with its variable renamed along `f`. -/
def GroundBound.map {V W : Type*} (f : V → W) (b : GroundBound n V) : GroundBound n W :=
  ⟨f b.var, b.lower, b.tree⟩

@[simp] theorem GroundBound.holds_map {V W : Type*} (f : V → W)
    (b : GroundBound n V) (ρ : W → Semantics.Tree n) :
    (b.map f).Holds ρ ↔ b.Holds (ρ ∘ f) := Iff.rfl

/-- The ground bound equivalent to an observation. -/
def Observation.bound {V : Type*} (o : Observation n V) : GroundBound n V :=
  match o.dual, o.value with
  | false, true => ⟨o.var, true, pathBound o.word (.node (fun _ => .bot))⟩
  | false, false => ⟨o.var, false, (pathBound o.word .top).dual⟩
  | true, true => ⟨o.var, false, (pathBound o.word (.node (fun _ => .bot))).dual⟩
  | true, false => ⟨o.var, true, pathBound o.word .top⟩

/-- An observation holds exactly when its ground bound holds. -/
theorem observation_bound {V : Type*} (ρ : V → Semantics.Tree n) (o : Observation n V) :
    o.bound.Holds ρ ↔ o.Holds ρ := by
  classical
  obtain ⟨s,v,w,b⟩ := o
  cases s <;> cases b <;>
    simp only [Observation.bound, GroundBound.Holds, Observation.Holds,
      Bool.false_eq_true, ite_false, ite_true]
  · rw [le_dual_iff, pathBound_top_le_iff_hasTopPrefix]
    have hh := mem_nonBottomPrefixes_dual (Tree.dual (ρ v)) w
    simpa only [dual_involutive, not_not] using hh.not.symm
  · exact pathBound_le_iff_mem_nonBottomPrefixes _ _
  · rw [mem_nonBottomPrefixes_dual, not_not]
    exact pathBound_top_le_iff_hasTopPrefix _ _
  · rw [le_dual_iff]
    exact pathBound_le_iff_mem_nonBottomPrefixes _ _

end DeciSigma1.Full.Models

namespace DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics

variable {n : ℕ}

/-- A regular tree has finitely many distinct subtrees. -/
def RegularTop (t : Semantics.Tree n) : Prop := (Characterization.subtrees t).Finite
/-- A finite tree: the tree of a finite term. -/
def FiniteTop (t : Semantics.Tree n) : Prop := ∃ g : FTree n, g.toTree = t

/-- `Γ` has a solution with variance `c` whose values lie in the class `C`. -/
def SatisfiableIn {V : Type*} (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) : Prop :=
  ∃ ρ, (∀ v, C (ρ v)) ∧ SatT c ρ Γ

/-- A flat constraint has a finite solution with variance `c`. -/
abbrev SatFin {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) : Prop :=
  SatisfiableIn FiniteTop c Γ

/-- Finite satisfiability can be witnessed by an assignment of finite trees. -/
theorem satFin_iff_finite_assignment {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) :
    SatFin c Γ ↔ ∃ σ : V → FTree n, SatT c (FTree.toTree ∘ σ) Γ := by
  constructor
  · rintro ⟨ρ, hf, hs⟩
    choose σ hσ using hf
    exact ⟨σ, (show FTree.toTree ∘ σ = ρ from funext hσ).symm ▸ hs⟩
  · rintro ⟨σ, hs⟩
    exact ⟨FTree.toTree ∘ σ, fun v => ⟨σ v, rfl⟩, hs⟩

/-- Finitely many ground bounds that hold together in some covariant solution of `Γ` hold together
in a finite covariant solution, provided `Γ` has a finite covariant solution. -/
def FiniteBoundPinning {V : Type*} (Γ : List (LitT n V)) : Prop :=
  SatisfiableIn FiniteTop (fun _ => false) Γ →
    ∀ B : List (GroundBound n V),
      (∃ ρ, SatT (fun _ => false) ρ Γ ∧ ∀ b ∈ B, b.Holds ρ) →
      ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ Γ ∧
        ∀ b ∈ B, b.Holds τ

end DeciSigma1.Full.Models
