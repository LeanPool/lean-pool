/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import Mathlib.Data.Fin.VecNotation
public import LeanPool.DeciSigma1.Full.Basic
public import LeanPool.DeciSigma1.Entailment.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Examples of disjunctive entailment

A disjunctive entailment `Γ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` can hold although no single disjunct
is entailed. The examples below exhibit this with `k = 2`, over `{⊥, f}` with `f` covariant
and over `{⊥, f, ⊤}` with a contravariant argument, next to entailments of the same shape that
fail. All proofs are semantic; no decision procedure is evaluated.

## Main declarations

- `unary_comparable`, `not_unary_comparable_single`: over unary trees `x ≤ y ∨ y ≤ x` holds,
  although neither `x ≤ y` nor `y ≤ x` is entailed.
- `binary_not_comparable`: over binary trees `x ≤ y ∨ y ≤ x` fails.
- `arrow_least`, `not_arrow_least_single`: with `f` contravariant in its first argument and
  covariant in its second, `f(⊤, ⊥)` is the least constructor tree, so
  `x ≤ ⊥ ∨ f(⊤, ⊥) ≤ x` holds, although neither disjunct is entailed.
- `arrow_not_least`: `x ≤ ⊥ ∨ f(⊥, ⊥) ≤ x` fails for the same variance, and
  `covariant_least` shows that it holds when both arguments are covariant.
-/

@[expose] public section


namespace DeciSigma1.Examples

open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics DeciSigma1.Constraints

/-! ## Signature `{⊥, f}` -/

/-- Over a unary constructor a word is determined by its length, so a tree containing a
position contains every shorter one. -/
theorem unary_mem_of_length_le (t : PrefixSet 1) {u v : List (Fin 1)}
    (h : u.length ≤ v.length) (hv : v ∈ t.carrier) : u ∈ t.carrier := by
  have hu : u = v.take u.length :=
    List.ext_getElem (by simp [h]) (fun _ _ _ => Subsingleton.elim _ _)
  rw [hu]
  exact t.prefix_closed _ (v.drop u.length) (by rwa [List.take_append_drop])

/-- Unary trees `⊥ < f(⊥) < f(f(⊥)) < … < f(f(…))` form a chain. -/
theorem unary_le_total (t u : PrefixSet 1) : t ≤ u ∨ u ≤ t := by
  by_contra h
  obtain ⟨h₁, h₂⟩ := not_or.mp h
  have h₁' : ¬ t.carrier ⊆ u.carrier := h₁
  have h₂' : ¬ u.carrier ⊆ t.carrier := h₂
  obtain ⟨w, hwt, hwu⟩ := Set.not_subset.mp h₁'
  obtain ⟨v, hvu, hvt⟩ := Set.not_subset.mp h₂'
  rcases le_total w.length v.length with hl | hl
  · exact hwu (unary_mem_of_length_le u hl hvu)
  · exact hvt (unary_mem_of_length_le t hl hwt)

/-- The queries `x ≤ y` and `y ≤ x` on the variables `x = 0` and `y = 1`. -/
def swapQueries : Fin 2 → Fin 2 × Fin 2 := ![(0, 1), (1, 0)]

/-- Over unary trees, the empty constraint entails `x ≤ y ∨ y ≤ x`. -/
theorem unary_comparable :
    Entailment.DisjEntailsIn (fun _ => True) ([] : List (TopFree.Lit 1 (Fin 2))) swapQueries := by
  intro ρ _ _
  rcases unary_le_total (ρ 0) (ρ 1) with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- Neither disjunct of `unary_comparable` is entailed on its own. -/
theorem not_unary_comparable_single (i : Fin 2) :
    ¬ Entailment.DisjEntailsIn (fun _ => True)
        ([] : List (TopFree.Lit 1 (Fin 2))) ![swapQueries i] := by
  intro h
  let ρ : Fin 2 → PrefixSet 1 :=
    fun v => if v = (swapQueries i).1 then .node (fun _ => .bot) else .bot
  obtain ⟨j, hj⟩ := h ρ (fun _ => trivial) (by simp [TopFree.Sat])
  fin_cases i <;> fin_cases j <;> exact PrefixSet.not_node_le_bot _ hj

/-- Over binary trees, `x ≤ y ∨ y ≤ x` is not entailed: `f(f(⊥, ⊥), ⊥)` and
`f(⊥, f(⊥, ⊥))` are incomparable. -/
theorem binary_not_comparable :
    ¬ Entailment.DisjEntailsIn (fun _ => True) ([] : List (TopFree.Lit 2 (Fin 2))) swapQueries := by
  intro h
  let leaf : PrefixSet 2 := .node (fun _ => .bot)
  obtain ⟨j, hj⟩ := h ![.node ![leaf, .bot], .node ![.bot, leaf]] (fun _ => trivial)
    (by simp [TopFree.Sat])
  fin_cases j
  · exact PrefixSet.not_node_le_bot _ ((PrefixSet.node_le_node _ _).mp hj 0)
  · exact PrefixSet.not_node_le_bot _ ((PrefixSet.node_le_node _ _).mp hj 1)

/-! ## Signature `{⊥, f, ⊤}` with a contravariant argument

The binary constructor `f` below is contravariant in its first argument and covariant in its
second, like the function type constructor. The variables are `x = 0`, `b = 1`, `t = 2` and
`u = 3`; the constraint fixes `b = ⊥`, `t = ⊤` and `u = f(s₀, s₁)`. -/

/-- Variance of a function type constructor: the first argument is contravariant. -/
def arrow : Fin 2 → Bool := ![true, false]

/-- The constraint `b = ⊥ ∧ t = ⊤ ∧ u = f(s₀, s₁)`. -/
def pinned (s : Fin 2 → Fin 4) : List (LitT 2 (Fin 4)) :=
  [.eqBot 1, .eqTop 2, .fLe s 3, .leF 3 s]

/-- The queries `x ≤ b` and `u ≤ x`. -/
def leastQueries : Fin 2 → Fin 4 × Fin 4 := ![(0, 1), (3, 0)]

theorem pinned_sat {c : Fin 2 → Bool} {s : Fin 2 → Fin 4} {ρ : Fin 4 → Semantics.Tree 2}
    (h : SatT c ρ (pinned s)) :
    ρ 1 = Tree.bot ∧ ρ 2 = Tree.top ∧ ρ 3 = Semantics.Tree.node (ρ ∘ s) :=
  ⟨h (.eqBot 1) (by simp [pinned]), h (.eqTop 2) (by simp [pinned]),
    treeLe_antisymm (h (.leF 3 s) (by simp [pinned])) (h (.fLe s 3) (by simp [pinned]))⟩

/-- `f(⊤, ⊥)` lies below every constructor tree, so `x ≤ ⊥ ∨ f(⊤, ⊥) ≤ x` holds. -/
theorem arrow_least :
    DeciSigma1.Full.DisjEntailsIn (fun _ => True) arrow (pinned ![2, 1]) leastQueries := by
  intro ρ _ hs
  obtain ⟨hb, ht, hu⟩ := pinned_sat hs
  rcases (ρ 0).eq_bot_or_eq_top_or_node with h0 | h0 | ⟨a, h0⟩
  · exact ⟨0, show Tree.Le arrow (ρ 0) (ρ 1) by rw [h0]; exact bot_treeLe _ _⟩
  · exact ⟨1, show Tree.Le arrow (ρ 3) (ρ 0) by rw [h0]; exact treeLe_top _ _⟩
  · refine ⟨1, show Tree.Le arrow (ρ 3) (ρ 0) from ?_⟩
    rw [hu, h0, node_treeLe_node_iff]
    intro i
    fin_cases i <;> simp [arrow, ht, hb]

/-- Neither disjunct of `arrow_least` is entailed on its own. -/
theorem not_arrow_least_single (i : Fin 2) :
    ¬ DeciSigma1.Full.DisjEntailsIn (fun _ => True) arrow (pinned ![2, 1]) ![leastQueries i] := by
  intro h
  let least : Semantics.Tree 2 := .node ![.top, .bot]
  let ρ : Fin 4 → Semantics.Tree 2 := ![if i = 0 then least else .bot, .bot, .top, least]
  have hs : SatT arrow ρ (pinned ![2, 1]) := by
    have he : ρ ∘ ![2, 1] = ![.top, .bot] := by
      funext j; fin_cases j <;> rfl
    intro l hl
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [HoldsT, ρ, he, least, treeLe_refl]
  obtain ⟨j, hj⟩ := h ρ (fun _ => trivial) hs
  fin_cases i <;> fin_cases j
  · exact Tree.node_ne_bot _ ((treeLe_bot_iff _ _).mp hj)
  · exact Tree.node_ne_bot _ ((treeLe_bot_iff _ _).mp hj)

/-- With the same variance, `x ≤ ⊥ ∨ f(⊥, ⊥) ≤ x` is not entailed: `x = f(⊤, ⊥)` refutes
both disjuncts, since `f(⊥, ⊥) ≤ f(⊤, ⊥)` would need `⊤ ≤ ⊥`. -/
theorem arrow_not_least :
    ¬ DeciSigma1.Full.DisjEntailsIn (fun _ => True) arrow (pinned ![1, 1]) leastQueries := by
  intro h
  let ρ : Fin 4 → Semantics.Tree 2 := ![.node ![.top, .bot], .bot, .top, .node ![.bot, .bot]]
  have hs : SatT arrow ρ (pinned ![1, 1]) := by
    have he : ρ ∘ ![1, 1] = ![.bot, .bot] := by
      funext j; fin_cases j <;> rfl
    intro l hl
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [HoldsT, ρ, he, treeLe_refl]
  obtain ⟨j, hj⟩ := h ρ (fun _ => trivial) hs
  fin_cases j
  · exact Tree.node_ne_bot _ ((treeLe_bot_iff _ _).mp hj)
  · have h0 := (node_treeLe_node_iff _ _ _).mp hj 0
    simp only [arrow] at h0
    exact Tree.bot_ne_top ((top_treeLe_iff _ _).mp h0)

/-- When both arguments are covariant, `x ≤ ⊥ ∨ f(⊥, ⊥) ≤ x` holds. -/
theorem covariant_least :
    DeciSigma1.Full.DisjEntailsIn (fun _ => True) (fun _ => false)
        (pinned ![1, 1]) leastQueries := by
  intro ρ _ hs
  obtain ⟨hb, -, hu⟩ := pinned_sat hs
  rcases (ρ 0).eq_bot_or_eq_top_or_node with h0 | h0 | ⟨a, h0⟩
  · exact ⟨0, show Tree.Le _ (ρ 0) (ρ 1) by rw [h0]; exact bot_treeLe _ _⟩
  · exact ⟨1, show Tree.Le _ (ρ 3) (ρ 0) by rw [h0]; exact treeLe_top _ _⟩
  · refine ⟨1, show Tree.Le _ (ρ 3) (ρ 0) from ?_⟩
    rw [hu, h0, node_treeLe_node_iff]
    intro i
    fin_cases i <;> simp [hb]

end DeciSigma1.Examples
