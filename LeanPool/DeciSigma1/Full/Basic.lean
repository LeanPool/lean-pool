/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Closure.Basic

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Disjunctive entailment over `{⊥, f, ⊤}`

A conjunction `Γ` of flat constraints over `{⊥, f, ⊤}` with variance `c` entails the disjunction
`x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` over a class `C` of trees when every solution of `Γ` with values in `C`
satisfies one of the inequalities; otherwise a countermodel refutes all of them. In the leaf
representation of `DeciSigma1.Full.Closure`, an inequality `x ≤ y` fails in one of two modes: some
path reaches `⊤` in (the normalization of) `x` but not in `y`, or reaches `⊥` in `y` but not in `x`.
A mode `m` and a path `w` give the seed configuration that must belong to the solution and the
exclusion configuration that must not (`failures_iff_exists_leaf_witnesses`).

## Main declarations

- `Full.DisjEntailsIn`, `Full.HasCountermodelIn`, `Full.not_disjEntailsIn_iff`: disjunctive
  entailment and its countermodels.
- `Full.seed`, `Full.exclusion`: the two configurations witnessing a failed inequality.
- `Full.failures_iff_exists_leaf_witnesses`: simultaneous failure of all queries through seeds and
  exclusions.
-/

@[expose] public section


namespace DeciSigma1.Full
open DeciSigma1.Semantics
open DeciSigma1.Constraints

variable {n k : Nat} {V : Type}

/-- The seed of a failure of `q = (x, y)` in mode `m` at the path `w`: the normalization of `x`
reaches `⊤` along `w` (mode `false`), or that of `y` reaches `⊥` along `w` (mode `true`). -/
def seed (q : V × V) (m : Bool) (w : List (Fin n)) : Closure.Config n V :=
  (if m then q.2 else q.1, m, w)

/-- The exclusion paired with `seed q m w`: the normalization of `y` reaches `⊤` along `w`
(mode `false`), or that of `x` reaches `⊥` along `w` (mode `true`). -/
def exclusion (q : V × V) (m : Bool) (w : List (Fin n)) : Closure.Config n V :=
  (if m then q.1 else q.2, m, w)

/-- A countermodel in the class `C`: a solution of `Γ` with values in `C` that refutes every
inequality `x_i ≤ y_i`. -/
def HasCountermodelIn (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) (q : Fin k → V × V) : Prop :=
  ∃ ρ, (∀ v, C (ρ v)) ∧ SatT c ρ Γ ∧
    ∀ i, ¬ Tree.Le c (ρ (q i).1) (ρ (q i).2)

/-- Disjunctive entailment over the class `C`: every solution of `Γ` with values in `C` satisfies
one of the inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`, ordered with variance `c`. -/
def DisjEntailsIn (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) (q : Fin k → V × V) : Prop :=
  ∀ ρ, (∀ v, C (ρ v)) → SatT c ρ Γ →
    ∃ i, Tree.Le c (ρ (q i).1) (ρ (q i).2)

/-- A disjunctive entailment fails exactly when it has a countermodel in the class. -/
theorem not_disjEntailsIn_iff (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) (q : Fin k → V × V) :
    ¬ DisjEntailsIn C c Γ q ↔ HasCountermodelIn C c Γ q := by
  classical
  simp only [DisjEntailsIn, HasCountermodelIn, not_forall, not_exists, exists_prop]

/-- An inequality fails exactly when, for some mode and path, its seed belongs to the solution and
its exclusion does not. -/
theorem failure_iff_exists_leaf_witness (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (q : V × V) :
    ¬ Tree.Le c (ρ q.1) (ρ q.2) ↔ ∃ m w,
      seed q m w ∈ Closure.configSet c ρ ∧ exclusion q m w ∉ Closure.configSet c ρ := by
  classical
  rw [Closure.treeLe_iff_leaf]
  simp only [Set.subset_def, not_and_or, not_forall]
  constructor
  · rintro (⟨w, hw, hn⟩ | ⟨w, hw, hn⟩)
    · exact ⟨false, w, hw, hn⟩
    · exact ⟨true, w, hw, hn⟩
  · rintro ⟨m, w, hw, hn⟩
    cases m
    · exact Or.inl ⟨w, hw, hn⟩
    · exact Or.inr ⟨w, hw, hn⟩

/-- All inequalities fail exactly when a mode and a path for each query give seeds in the solution
and exclusions outside it. -/
theorem failures_iff_exists_leaf_witnesses (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (q : Fin k → V × V) :
    (∀ i, ¬ Tree.Le c (ρ (q i).1) (ρ (q i).2)) ↔
      ∃ (m : Fin k → Bool) (W : Fin k → List (Fin n)), ∀ i,
        seed (q i) (m i) (W i) ∈ Closure.configSet c ρ ∧
        exclusion (q i) (m i) (W i) ∉ Closure.configSet c ρ := by
  classical
  simp only [failure_iff_exists_leaf_witness]
  exact ⟨fun h => by choose m W h using h; exact ⟨m, W, h⟩,
    fun ⟨m, W, h⟩ i => ⟨m i, W i, h i⟩⟩

end DeciSigma1.Full
