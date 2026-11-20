/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SplitIfs

/-!
# Word-representability, wheels and Mycielskian graphs

A word represents a graph if every vertex occurs in it and distinct vertices are
adjacent exactly when their occurrences alternate. The graph constructions use
the conventions of Alshammari, arXiv:2609.20881v1.
-/

@[expose] public section

namespace WordRepTensor

open SimpleGraph

/-! ## 1. Words and word-representability -/

/-- `noRepeat u = true` iff no two consecutive entries of `u` are equal. -/
def noRepeat {V : Type*} [DecidableEq V] : List V → Bool
  | a :: b :: t => (a != b) && noRepeat (b :: t)
  | _ => true

/-- `x` and `y` alternate in `w`: deleting all other letters leaves `xyxy⋯` or `yxyx⋯`. -/
def Alternate {V : Type*} [DecidableEq V] (w : List V) (x y : V) : Prop :=
  noRepeat (w.filter (fun z => z == x || z == y)) = true

/-- The word `w` represents the graph `G`. -/
def Represents {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : List V) : Prop :=
  (∀ v : V, v ∈ w) ∧ ∀ x y : V, x ≠ y → (G.Adj x y ↔ Alternate w x y)

/-- `G` is word-representable. -/
def WordRepresentable {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ w : List V, Represents G w

instance {V : Type*} [DecidableEq V] (w : List V) (x y : V) : Decidable (Alternate w x y) :=
  inferInstanceAs (Decidable (noRepeat (w.filter (fun z => z == x || z == y)) = true))

instance {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : List V) : Decidable (Represents G w) :=
  inferInstanceAs (Decidable ((∀ v : V, v ∈ w) ∧ ∀ x y : V, x ≠ y → (G.Adj x y ↔ Alternate w x y)))

/-! ## 2. Graphs -/

/-- Two vertices are adjacent when both coordinate pairs are adjacent. -/
def tensorProd {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj p q := G.Adj p.1 q.1 ∧ H.Adj p.2 q.2
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl p h := G.loopless.irrefl p.1 h.1

instance {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (tensorProd G H).Adj :=
  fun p q => inferInstanceAs (Decidable (G.Adj p.1 q.1 ∧ H.Adj p.2 q.2))

/-- Edge types of the wheel: rim–rim along the cycle, hub–rim. -/
def wheelRel (n : ℕ) : Fin n ⊕ Unit → Fin n ⊕ Unit → Bool
  | .inl i, .inl j => decide ((cycleGraph n).Adj i j)
  | .inr _, .inl _ => true
  | _, _ => false

/-- The wheel `W_n`: the cycle `C_n` on `inl 0, …, inl (n-1)` plus the hub `inr ()`. -/
def wheel (n : ℕ) : SimpleGraph (Fin n ⊕ Unit) :=
  SimpleGraph.fromRel fun a b => wheelRel n a b = true

instance (n : ℕ) : DecidableRel (wheel n).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (wheelRel n a b = true ∨ wheelRel n b a = true)))

/-- Edge types of the Mycielskian: top–top (`a ~ b`), top `a`–shadow `b` (`a ~ b`),
shadow–root. -/
def mycRel {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    V ⊕ V ⊕ Unit → V ⊕ V ⊕ Unit → Bool
  | .inl a, .inl b => decide (G.Adj a b)
  | .inl a, .inr (.inl b) => decide (G.Adj a b)
  | .inr (.inl _), .inr (.inr _) => true
  | _, _ => false

/-- The Mycielskian `μ(G)` (top row `inl`, shadows `inr ∘ inl`, root `inr (inr ())`). -/
def mycielskian {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph (V ⊕ V ⊕ Unit) :=
  SimpleGraph.fromRel fun a b => mycRel G a b = true

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (mycielskian G).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (mycRel G a b = true ∨ mycRel G b a = true)))

/-- Edge types of the extended Mycielskian: as `mycRel`, but top `a`–shadow `b` iff `a ≠ b`. -/
def extMycRel {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    V ⊕ V ⊕ Unit → V ⊕ V ⊕ Unit → Bool
  | .inl a, .inl b => decide (G.Adj a b)
  | .inl a, .inr (.inl b) => decide (a ≠ b)
  | .inr (.inl _), .inr (.inr _) => true
  | _, _ => false

/-- The extended Mycielskian `μ'(G)`. -/
def extMycielskian {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph (V ⊕ V ⊕ Unit) :=
  SimpleGraph.fromRel fun a b => extMycRel G a b = true

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (extMycielskian G).Adj :=
  fun a b => inferInstanceAs
    (Decidable (a ≠ b ∧ (extMycRel G a b = true ∨ extMycRel G b a = true)))

/-- `μ_n = μ(C_n)` in the notation of [A]. -/
abbrev mu (n : ℕ) : SimpleGraph (Fin n ⊕ Fin n ⊕ Unit) := mycielskian (cycleGraph n)

/-- `μ'_n = μ'(C_n)` in the notation of [A]. -/
abbrev muExt (n : ℕ) : SimpleGraph (Fin n ⊕ Fin n ⊕ Unit) := extMycielskian (cycleGraph n)

end WordRepTensor
