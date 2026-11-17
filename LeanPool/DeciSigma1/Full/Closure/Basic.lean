/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Models.Observations

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Solutions over `{⊥, f, ⊤}` as Horn-closed sets of signed configurations

A tree `t` with variance `c` is represented by two extension-closed sets of paths, its leaf cones:
`leaf c t false`, the paths along which the normalization of `t` reaches `⊤`, and `leaf c t true`,
the paths along which it reaches `⊥` (`treeLe_iff_leaf`: `t ≤ u` exactly when the `⊤`-cone of `t` is
contained in that of `u` and the `⊥`-cone of `u` in that of `t`). An assignment becomes a set of
signed configurations `(v, s, w)`: the path `w` lies in the cone of sign `s` of `v`. It satisfies
`Γ` exactly when this set is closed under the clauses of `Γ` (moves along literals and extension of
the path), contains the facts (`x = ⊥`, `x = ⊤`), avoids the negative facts (the roots excluded by
constructor bounds) and is consistent (no path in both cones of a variable) (`sat_iff_isSolution`).

The least closure of the facts (`leastClosure`), the closure of the facts and a seed
(`seedClosure`) and the derivations between configurations (`Reach`) describe satisfiability
(`sat_iff_leastClosure`) and liveness of configurations (`live_iff`, `dead_iff`). Moves come in
pairs reversed by exchanging the signs (`moves_dual`). Clause and move derivations use
`Relation.ReflTransGen`.

## Main declarations

- `Closure.leaf`, `Closure.treeLe_iff_leaf`: the leaf cones of a tree and the order.
- `Closure.LeafPair`, `Closure.decode`: trees from pairs of cones.
- `Closure.Config`, `Closure.configSet`, `Closure.assignmentOf`: assignments as sets of signed
  configurations.
- `Closure.Move`, `Closure.Clause`, `Closure.Reach`, `Closure.moves_dual`: clauses and derivations.
- `Closure.IsSolution`, `Closure.sat_iff_isSolution`: solutions as closed consistent sets.
- `Closure.leastClosure`, `Closure.seedClosure`, `Closure.sat_iff_leastClosure`, `Closure.live_iff`,
  `Closure.dead_iff`: least closures, satisfiability and liveness.
-/

@[expose] public section


namespace DeciSigma1.Full.Closure
open DeciSigma1.Full.Models DeciSigma1.Semantics

variable {n : ℕ}

/-- The leaf cone of sign `s` of `t`: the paths along which the normalization of `t` reaches `⊤`
(`s = false`) or `⊥` (`s = true`). -/
def leaf (c : Fin n → Bool) (t : Semantics.Tree n) (s : Bool) : Set (List (Fin n)) :=
  {w | HasTopPrefix (Tree.normalize c s t) w}

theorem leaf_minus (c : Fin n → Bool) (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ leaf c t true ↔ w ∉ (nonBottomPrefixes (Tree.normalize c false t)).carrier := by
  classical
  rw [leaf, Set.mem_ofPred, normalize_true]
  have h := mem_nonBottomPrefixes_dual (Tree.dual (Tree.normalize c false t)) w
  simpa using h.not.symm

/-- A set of paths closed under extension. -/
def ExtensionClosed (A : Set (List (Fin n))) : Prop := ∀ u v, u ∈ A → u ++ v ∈ A

/-- A pair of disjoint extension-closed sets of paths, the possible leaf cones of a tree. -/
structure LeafPair (n : ℕ) where
  /-- Extension-closed paths for each of the two leaf labels. -/
  cone : Bool → Set (List (Fin n))
  extension : ∀ s, ExtensionClosed (cone s)
  disjoint : ∀ w, w ∈ cone false → w ∈ cone true → False

theorem leaf_extension (c : Fin n → Bool) (t : Semantics.Tree n) (s : Bool) :
    ExtensionClosed (leaf c t s) := by
  intro u v h
  obtain ⟨p, ⟨z, hz⟩, hp⟩ := h
  exact ⟨p, ⟨z ++ v, by
      simpa [List.append_assoc] using congrArg (fun q => q ++ v) hz⟩, hp⟩

theorem leaf_disjoint (c : Fin n → Bool) (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ leaf c t false → w ∈ leaf c t true → False := by
  intro hp hm
  exact (leaf_minus c t w).mp hm (mem_nonBottomPrefixes_of_hasTopPrefix _ _ hp)

/-- The prefix pair of a pair of cones: the complements of the `⊥`-cone and of the `⊤`-cone. -/
def LeafPair.toPrefixPair (p : LeafPair n) : PrefixPair n where
  nonBottom := ⟨(p.cone true)ᶜ, fun u v h hu => h (p.extension true u v hu)⟩
  nonTop := ⟨(p.cone false)ᶜ, fun u v h hu => h (p.extension false u v hu)⟩
  cover w := by
    classical
    by_cases hp : w ∈ p.cone false
    · exact Or.inl (fun hm => p.disjoint w hp hm)
    · exact Or.inr hp

/-- The tree with the given leaf cones. -/
noncomputable def decode (c : Fin n → Bool) (p : LeafPair n) : Semantics.Tree n :=
  Tree.normalize c false (PrefixPair.realize p.toPrefixPair)

@[simp] theorem leaf_decode (c : Fin n → Bool) (p : LeafPair n) (s : Bool) :
    leaf c (decode c p) s = p.cone s := by
  classical
  ext w
  cases s with
  | false =>
    change HasTopPrefix (Tree.normalize c false (Tree.normalize c false _)) w ↔ _
    rw [normalize_involutive, (PrefixPair.realize_observations p.toPrefixPair w).2]
    simp [LeafPair.toPrefixPair]
  | true =>
    rw [leaf_minus]
    simp [decode, LeafPair.toPrefixPair]

/-- `t ≤ u` with variance `c` exactly when the `⊤`-cone of `t` is contained in that of `u` and the
`⊥`-cone of `u` in that of `t`. -/
theorem treeLe_iff_leaf (c : Fin n → Bool) (t u : Semantics.Tree n) :
    Tree.Le c t u ↔ leaf c t false ⊆ leaf c u false ∧
      leaf c u true ⊆ leaf c t true := by
  rw [treeLe_iff_normalize, le_iff_forall_hasLabel]
  constructor
  · intro h
    constructor
    · intro w hw; exact (h w).1 hw
    · intro w hw
      have hm : ∀ t, w ∈ leaf c t true ↔
          Semantics.Tree.HasLabel (Tree.normalize c false t) w Sym.bot :=
        fun t => by
          classical
          simpa [nonBottomPrefixes] using leaf_minus c t w
      exact (hm t).mpr ((h w).2 ((hm u).mp hw))
  · rintro ⟨hp, hm⟩ w
    constructor
    · exact hp (a := w)
    · classical
      simpa only [leaf_minus, mem_nonBottomPrefixes, not_not] using hm (a := w)

@[simp] theorem leaf_node_nil (c : Fin n → Bool) (a : Fin n → Semantics.Tree n) (s : Bool) :
    [] ∉ leaf c (Semantics.Tree.node a) s := by
  simp [leaf, HasTopPrefix]

@[simp] theorem leaf_node_cons (c : Fin n → Bool) (a : Fin n → Semantics.Tree n)
    (s : Bool) (i : Fin n) (w : List (Fin n)) :
    i :: w ∈ leaf c (Semantics.Tree.node a) s ↔
      w ∈ leaf c (a i) (Bool.xor s (c i)) := by
  simp only [leaf, Set.mem_ofPred_eq, HasTopPrefix, normalize_node,
    Semantics.Tree.hasLabel_node_cons _ _ _ Sym.top (by decide)]

@[simp] theorem leaf_root_minus (c : Fin n → Bool) (t : Semantics.Tree n) :
    [] ∈ leaf c t true ↔ t = Tree.bot := by
  classical
  rw [leaf_minus]
  simp [nonBottomPrefixes]

@[simp] theorem leaf_root_plus (c : Fin n → Bool) (t : Semantics.Tree n) :
    [] ∈ leaf c t false ↔ t = Tree.top := by
  simp [leaf, HasTopPrefix]

end DeciSigma1.Full.Closure

namespace DeciSigma1.Full.Closure
open DeciSigma1.Semantics
open DeciSigma1.Constraints

variable {n : ℕ}

/-- A signed configuration `(v, s, w)`: the path `w` in the cone of sign `s` of `v`. -/
abbrev Config (n : ℕ) (V : Type*) := V × Bool × List (Fin n)

/-- The signed configurations of an assignment. -/
def configSet {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n) : Set (Config n V) :=
  {p | p.2.2 ∈ leaf c (ρ p.1) p.2.1}

/-- The moves along literals: a variable inequality copies a configuration (forward on the
`⊤`-cones and backward on the `⊥`-cones), and a constructor bound pushes or pops a child index,
with the sign shifted by the variance of the child. -/
inductive Move {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) :
    Config n V → Config n V → Prop
  | copyPlus {u v w} : LitT.le u v ∈ Γ → Move c Γ (u, false, w) (v, false, w)
  | copyMinus {u v w} : LitT.le u v ∈ Γ → Move c Γ (v, true, w) (u, true, w)
  | fLePush {a u w} (i : Fin n) : LitT.fLe a u ∈ Γ →
      Move c Γ (a i, c i, w) (u, false, i :: w)
  | fLePop {a u w} (i : Fin n) : LitT.fLe a u ∈ Γ →
      Move c Γ (u, true, i :: w) (a i, !(c i), w)
  | leFPop {u a w} (i : Fin n) : LitT.leF u a ∈ Γ →
      Move c Γ (u, false, i :: w) (a i, c i, w)
  | leFPush {u a w} (i : Fin n) : LitT.leF u a ∈ Γ →
      Move c Γ (a i, !(c i), w) (u, true, i :: w)

/-- The clauses: moves, and extension of the path. -/
inductive Clause {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) :
    Config n V → Config n V → Prop
  | move {p q} : Move c Γ p q → Clause c Γ p q
  | extend (v : V) (s : Bool) (w : List (Fin n)) (i : Fin n) :
      Clause c Γ (v, s, w) (v, s, w ++ [i])

/-- The facts: `x = ⊥` puts the empty path in the `⊥`-cone of `x`, and `x = ⊤` in its `⊤`-cone. -/
inductive Fact {V : Type*} (Γ : List (LitT n V)) : Config n V → Prop
  | bot {v} : LitT.eqBot v ∈ Γ → Fact Γ (v, true, [])
  | top {v} : LitT.eqTop v ∈ Γ → Fact Γ (v, false, [])

/-- The negative facts: a lower constructor bound `f(a) ≤ u` excludes the empty path from the
`⊥`-cone of `u`, and an upper bound `u ≤ f(a)` excludes it from the `⊤`-cone. -/
inductive Neg {V : Type*} (Γ : List (LitT n V)) : Config n V → Prop
  | fLe {a u} : LitT.fLe a u ∈ Γ → Neg Γ (u, true, [])
  | leF {u a} : LitT.leF u a ∈ Γ → Neg Γ (u, false, [])

/-- The excluded pairs: the two signs of one path of one variable, which a consistent set never
contains together. -/
inductive OppositeSigns {V : Type*} : Config n V → Config n V → Prop
  | pair (v : V) (w : List (Fin n)) : OppositeSigns (v, false, w) (v, true, w)

/-- A set of configurations closed under the clauses. -/
def Closed {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V))
    (S : Set (Config n V)) : Prop := ∀ ⦃p q⦄, Clause c Γ p q → p ∈ S → q ∈ S

/-- A set of configurations containing no negative fact. -/
def Avoids {V : Type*} (Γ : List (LitT n V)) (S : Set (Config n V)) : Prop :=
  ∀ ⦃p⦄, p ∈ S → ¬ Neg Γ p

/-- A set of configurations containing no excluded pair. -/
def Consistent {V : Type*} (S : Set (Config n V)) : Prop :=
  ∀ ⦃p q⦄, OppositeSigns p q → p ∈ S → q ∈ S → False

/-- A solution as a set of signed configurations: closed under the clauses, containing the facts,
avoiding the negative facts and consistent. -/
structure IsSolution {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V))
    (S : Set (Config n V)) : Prop where
  closed : Closed c Γ S
  facts : ∀ ⦃p⦄, Fact Γ p → p ∈ S
  avoids : Avoids Γ S
  consistent : Consistent S

variable {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem configSet_consistent (ρ : V → Semantics.Tree n) : Consistent (configSet c ρ) := by
  intro p q h hp hq
  cases h with
  | pair v w => exact leaf_disjoint c (ρ v) w hp hq

/-- An assignment satisfies `Γ` exactly when its set of signed configurations is a solution. -/
theorem sat_iff_isSolution (ρ : V → Semantics.Tree n) :
    SatT c ρ Γ ↔ IsSolution c Γ (configSet c ρ) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, configSet_consistent ρ⟩
    · intro p q hpq hp
      cases hpq with
      | extend v s w i => exact leaf_extension c (ρ v) s w [i] hp
      | move hm =>
        cases hm with
        | copyPlus hl => exact ((treeLe_iff_leaf _ _ _).mp (h _ hl)).1 hp
        | copyMinus hl => exact ((treeLe_iff_leaf _ _ _).mp (h _ hl)).2 hp
        | fLePush i hl =>
          apply ((treeLe_iff_leaf _ _ _).mp (h _ hl)).1
          simpa [configSet] using hp
        | fLePop i hl =>
          have hh := ((treeLe_iff_leaf _ _ _).mp (h _ hl)).2 hp
          simpa [configSet] using hh
        | leFPop i hl =>
          have hh := ((treeLe_iff_leaf _ _ _).mp (h _ hl)).1 hp
          simpa [configSet] using hh
        | leFPush i hl =>
          apply ((treeLe_iff_leaf _ _ _).mp (h _ hl)).2
          simpa [configSet] using hp
    · intro p hp
      cases hp with
      | bot hl => exact (leaf_root_minus c _).mpr (h _ hl)
      | top hl => exact (leaf_root_plus c _).mpr (h _ hl)
    · intro p hp hn
      cases hn with
      | fLe hl =>
          exact leaf_node_nil c _ true (((treeLe_iff_leaf _ _ _).mp (h _ hl)).2 hp)
      | leF hl =>
          exact leaf_node_nil c _ false (((treeLe_iff_leaf _ _ _).mp (h _ hl)).1 hp)
  · intro h l hl
    cases l with
    | le u v =>
      exact (treeLe_iff_leaf _ _ _).mpr
        ⟨fun _ hw => h.closed (.move (.copyPlus hl)) hw,
         fun _ hw => h.closed (.move (.copyMinus hl)) hw⟩
    | fLe a u =>
      apply (treeLe_iff_leaf _ _ _).mpr
      constructor
      · intro w hw
        cases w with
        | nil => exact (leaf_node_nil c _ false hw).elim
        | cons i w =>
          apply h.closed (.move (.fLePush i hl))
          simpa [configSet] using hw
      · intro w hw
        cases w with
        | nil => exact (h.avoids hw (.fLe hl)).elim
        | cons i w =>
          have hh := h.closed (.move (.fLePop i hl)) hw
          simpa [configSet] using hh
    | leF u a =>
      apply (treeLe_iff_leaf _ _ _).mpr
      constructor
      · intro w hw
        cases w with
        | nil => exact (h.avoids hw (.leF hl)).elim
        | cons i w =>
          have hh := h.closed (.move (.leFPop i hl)) hw
          simpa [configSet] using hh
      · intro w hw
        cases w with
        | nil => exact (leaf_node_nil c _ true hw).elim
        | cons i w =>
          apply h.closed (.move (.leFPush i hl))
          simpa [configSet] using hw
    | eqBot u => exact (leaf_root_minus c _).mp (h.facts (.bot hl))
    | eqTop u => exact (leaf_root_plus c _).mp (h.facts (.top hl))

theorem Closed.extension {S : Set (Config n V)} (h : Closed c Γ S)
    (v : V) (s : Bool) : ExtensionClosed {w | (v, s, w) ∈ S} := by
  intro u w hu
  induction w using List.reverseRecOn with
  | nil => simpa using hu
  | append_singleton w i ih =>
    simpa [List.append_assoc] using h (.extend v s (u ++ w) i) ih

/-- The assignment of a closed consistent set of signed configurations. -/
noncomputable def assignmentOf (S : Set (Config n V)) (hc : Closed c Γ S)
    (hd : Consistent S) : V → Semantics.Tree n := fun v =>
  decode c ⟨fun s => {w | (v, s, w) ∈ S}, hc.extension v,
    fun w hp hm => hd (.pair v w) hp hm⟩

@[simp] theorem configSet_assignmentOf (S : Set (Config n V))
    (hc : Closed c Γ S) (hd : Consistent S) :
    configSet c (assignmentOf S hc hd) = S := by
  ext ⟨v, s, w⟩
  exact Set.ext_iff.mp (leaf_decode c _ s) w

theorem isSolution_iff_assignment {S : Set (Config n V)} :
    IsSolution c Γ S ↔ ∃ ρ, SatT c ρ Γ ∧ configSet c ρ = S := by
  constructor
  · intro h
    refine ⟨assignmentOf S h.closed h.consistent, ?_, configSet_assignmentOf ..⟩
    apply (sat_iff_isSolution _).mpr
    simpa using h
  · rintro ⟨ρ, h, rfl⟩; exact (sat_iff_isSolution ρ).mp h

/-- Derivations by finitely many clauses. -/
abbrev Reach (c : Fin n → Bool) (Γ : List (LitT n V)) :=
  Relation.ReflTransGen (Clause c Γ)

/-- The configurations derivable from the facts and the seeds `A`. -/
def hull (c : Fin n → Bool) (Γ : List (LitT n V)) (A : Set (Config n V)) : Set (Config n V) :=
  {b | ∃ a, (Fact Γ a ∨ a ∈ A) ∧ Reach c Γ a b}

theorem Reach.mem_of_closed {a b : Config n V} {S : Set (Config n V)}
    (h : Reach c Γ a b) (hc : Closed c Γ S) (ha : a ∈ S) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hs ih => exact hc hs ih

theorem hull_closed (A : Set (Config n V)) : Closed c Γ (hull c Γ A) := by
  rintro a b h ⟨s, hs, hr⟩
  exact ⟨s, hs, .tail hr h⟩

theorem hull_facts (A : Set (Config n V)) {p : Config n V} (hp : Fact Γ p) :
    p ∈ hull c Γ A := ⟨p, Or.inl hp, .refl⟩

theorem subset_hull (A : Set (Config n V)) : A ⊆ hull c Γ A :=
  fun p hp => ⟨p, Or.inr hp, .refl⟩

theorem hull_least {A S : Set (Config n V)} (hc : Closed c Γ S)
    (hf : ∀ ⦃p⦄, Fact Γ p → p ∈ S) (ha : A ⊆ S) : hull c Γ A ⊆ S := by
  rintro b ⟨a, hf' | ha', hr⟩
  · exact hr.mem_of_closed hc (hf hf')
  · exact hr.mem_of_closed hc (ha ha')

end DeciSigma1.Full.Closure

namespace DeciSigma1.Full.Closure
open DeciSigma1.Constraints

variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

/-- Derivations by moves only. -/
abbrev Moves (c : Fin n → Bool) (Γ : List (LitT n V)) :=
  Relation.ReflTransGen (Move c Γ)

/-- The configuration with the opposite sign. -/
def flipC (p : Config n V) : Config n V := (p.1, !p.2.1, p.2.2)

/-- Moves come in pairs: exchanging the signs reverses a move. -/
theorem move_dual {p q : Config n V} (h : Move c Γ p q) :
    Move c Γ (flipC q) (flipC p) := by
  cases h with
  | copyPlus hl => exact .copyMinus hl
  | copyMinus hl => exact .copyPlus hl
  | fLePush i hl => exact .fLePop i hl
  | fLePop i hl => simpa [flipC] using Move.fLePush (c := c) i hl
  | leFPop i hl => exact .leFPush i hl
  | leFPush i hl => simpa [flipC] using Move.leFPop (c := c) i hl

/-- Exchanging the signs reverses a move derivation. -/
theorem moves_dual {p q : Config n V} (h : Moves c Γ p q) :
    Moves c Γ (flipC q) (flipC p) := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact ih.head (move_dual hm)

theorem move_append (σ : List (Fin n)) {p q : Config n V} (h : Move c Γ p q) :
    Move c Γ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ) := by
  cases h with
  | copyPlus hl => exact .copyPlus hl
  | copyMinus hl => exact .copyMinus hl
  | fLePush i hl => exact .fLePush i hl
  | fLePop i hl => exact .fLePop i hl
  | leFPop i hl => exact .leFPop i hl
  | leFPush i hl => exact .leFPush i hl

/-- Move derivations act at the head of the path and are unaffected by a common suffix. -/
theorem moves_append (σ : List (Fin n)) {p q : Config n V} (h : Moves c Γ p q) :
    Moves c Γ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ) := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail (move_append σ hm)

theorem moves_reach {a b : Config n V} (h : Moves c Γ a b) : Reach c Γ a b := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact .tail ih (.move hm)

theorem reach_extend (v : V) (s : Bool) (u α : List (Fin n)) :
    Reach c Γ (v, s, u) (v, s, u ++ α) := by
  induction α using List.reverseRecOn with
  | nil => simpa using (Relation.ReflTransGen.refl : Reach c Γ (v, s, u) (v, s, u))
  | append_singleton α i ih =>
    simpa [List.append_assoc] using Relation.ReflTransGen.tail ih (.extend v s (u ++ α) i)

/-- A derivation is a move derivation from an extension of its start. -/
theorem reach_iff_moves {v : V} {s : Bool} {u : List (Fin n)} {b : Config n V} :
    Reach c Γ (v, s, u) b ↔ ∃ α, Moves c Γ (v, s, u ++ α) b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], by simpa using (Relation.ReflTransGen.refl)⟩
    | tail _ hs ih =>
      obtain ⟨α, hα⟩ := ih
      cases hs with
      | move hm => exact ⟨α, hα.tail hm⟩
      | extend v' s' w i =>
        exact ⟨α ++ [i], by simpa [List.append_assoc] using moves_append [i] hα⟩
  · rintro ⟨α, hα⟩
    exact (reach_extend v s u α).trans (moves_reach hα)

/-- The least closure: the configurations derivable from the facts. -/
def leastClosure (c : Fin n → Bool) (Γ : List (LitT n V)) : Set (Config n V) := hull c Γ ∅

/-- The configurations derivable from the facts and the seed `a`. -/
def seedClosure (c : Fin n → Bool) (Γ : List (LitT n V)) (a : Config n V) : Set (Config n V) :=
  hull c Γ {a}

/-- A configuration is live when it belongs to some solution. -/
def Live (c : Fin n → Bool) (Γ : List (LitT n V)) (a : Config n V) : Prop :=
  ∃ S, IsSolution c Γ S ∧ a ∈ S

theorem mem_leastClosure {b : Config n V} :
    b ∈ leastClosure c Γ ↔ ∃ a, Fact Γ a ∧ Reach c Γ a b := by
  simp [leastClosure, hull]

theorem mem_seedClosure {a b : Config n V} :
    b ∈ seedClosure c Γ a ↔ b ∈ leastClosure c Γ ∨ Reach c Γ a b := by
  simp [seedClosure, leastClosure, hull, or_and_right, exists_or]

theorem leastClosure_subset {S : Set (Config n V)} (hS : IsSolution c Γ S) : leastClosure c Γ ⊆ S :=
  hull_least hS.closed hS.facts (Set.empty_subset _)

theorem seedClosure_subset {S : Set (Config n V)} {a : Config n V}
    (hS : IsSolution c Γ S) (ha : a ∈ S) : seedClosure c Γ a ⊆ S :=
  hull_least hS.closed hS.facts (Set.singleton_subset_iff.mpr ha)

/-- A configuration is live exactly when the configurations derivable from the facts and it avoid
the negative facts and are consistent. -/
theorem live_iff {a : Config n V} :
    Live c Γ a ↔ Avoids Γ (seedClosure c Γ a) ∧ Consistent (seedClosure c Γ a) := by
  constructor
  · rintro ⟨S, hS, ha⟩
    have hsub := seedClosure_subset hS ha
    exact ⟨fun {_} hp => hS.avoids (hsub hp),
      fun {_ _} h hp hq => hS.consistent h (hsub hp) (hsub hq)⟩
  · rintro ⟨hn, hd⟩
    exact ⟨seedClosure c Γ a, ⟨hull_closed _, (fun {_} => hull_facts _), hn, hd⟩,
      subset_hull _ (Set.mem_singleton a)⟩

/-- A flat constraint is satisfiable exactly when its least closure avoids the negative facts and
is consistent. -/
theorem sat_iff_leastClosure :
    (∃ ρ, SatT c ρ Γ) ↔ Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    have hS := (sat_iff_isSolution ρ).mp hρ
    have hsub := leastClosure_subset hS
    exact ⟨fun {_} hp => hS.avoids (hsub hp),
      fun {_ _} h hp hq => hS.consistent h (hsub hp) (hsub hq)⟩
  · rintro ⟨hn, hd⟩
    obtain ⟨ρ, hρ, _⟩ := isSolution_iff_assignment.mp
      (show IsSolution c Γ (leastClosure c Γ) from
        ⟨hull_closed _, (fun {_} => hull_facts _), hn, hd⟩)
    exact ⟨ρ, hρ⟩

/-- If `a` and a seed derive the two signs of one configuration, then `a` derives the opposite sign
of an extension of the seed. -/
theorem collision_return {a : Config n V} {h q : V} {s s' : Bool} {w v : List (Fin n)}
    (h₁ : Reach c Γ a (h, s, w)) (h₂ : Reach c Γ (q, s', v) (h, !s, w)) :
    ∃ δ, Reach c Γ a (q, !s', v ++ δ) := by
  obtain ⟨δ, hd⟩ := reach_iff_moves.mp h₂
  refine ⟨δ, h₁.trans (moves_reach ?_)⟩
  simpa [flipC] using moves_dual hd

/-- A consistent set does not contain a configuration together with its opposite sign. -/
theorem Consistent.not_flip {S : Set (Config n V)} (hc : Consistent S)
    {v : V} {s : Bool} {w : List (Fin n)} (hp : (v, s, w) ∈ S) : (v, !s, w) ∉ S := by
  intro hm
  cases s with
  | false => exact hc (.pair v w) hp hm
  | true => exact hc (.pair v w) hm hp

/-- For a satisfiable constraint, a configuration is not live exactly when it derives a negative
fact, its opposite sign at an extension lies in the least closure, or it derives its own opposite
sign at an extension. -/
theorem dead_iff (hsat : Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ))
    {p : V} {s : Bool} {u : List (Fin n)} :
    ¬ Live c Γ (p, s, u) ↔
      (∃ n, Neg Γ n ∧ Reach c Γ (p, s, u) n) ∨
      (∃ δ, (p, !s, u ++ δ) ∈ leastClosure c Γ) ∨
      (∃ δ, Reach c Γ (p, s, u) (p, !s, u ++ δ)) := by
  classical
  constructor
  · intro hdead
    by_cases hn : Avoids Γ (seedClosure c Γ (p, s, u))
    · have hd : ¬ Consistent (seedClosure c Γ (p, s, u)) :=
        fun hd => hdead (live_iff.mpr ⟨hn, hd⟩)
      simp only [Consistent, not_forall] at hd
      obtain ⟨a, b, hab, ha, hb, _⟩ := hd
      cases hab with
      | pair v w =>
        rcases mem_seedClosure.mp ha with hma | hra <;> rcases mem_seedClosure.mp hb with hmb | hrb
        · exact (hsat.2 (.pair v w) hma hmb).elim
        · obtain ⟨f, hf, hfa⟩ := mem_leastClosure.mp hma
          obtain ⟨δ, hδ⟩ := collision_return hfa hrb
          exact Or.inr (Or.inl ⟨δ, mem_leastClosure.mpr ⟨f, hf, hδ⟩⟩)
        · obtain ⟨f, hf, hfb⟩ := mem_leastClosure.mp hmb
          obtain ⟨δ, hδ⟩ := collision_return hfb hra
          exact Or.inr (Or.inl ⟨δ, mem_leastClosure.mpr ⟨f, hf, hδ⟩⟩)
        · exact Or.inr (Or.inr (collision_return hra hrb))
    · simp only [Avoids, not_forall, not_not] at hn
      obtain ⟨n, hnc, hneg⟩ := hn
      rcases mem_seedClosure.mp hnc with hm | hr
      · exact (hsat.1 hm hneg).elim
      · exact Or.inl ⟨n, hneg, hr⟩
  · intro h hlive
    obtain ⟨S, hS, ha⟩ := hlive
    rcases h with ⟨n, hn, hr⟩ | ⟨δ, hm⟩ | ⟨δ, hr⟩
    · exact hS.avoids (hr.mem_of_closed hS.closed ha) hn
    · exact hS.consistent.not_flip
        ((reach_extend p s u δ).mem_of_closed hS.closed ha) (leastClosure_subset hS hm)
    · exact hS.consistent.not_flip
        ((reach_extend p s u δ).mem_of_closed hS.closed ha)
        (hr.mem_of_closed hS.closed ha)

end DeciSigma1.Full.Closure
