/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ComparisonTreeInsertion
public import LeanPool.ShellsortMean.ComparisonTranscriptBound

/-! On one fixed comparison tree a complete run ends at a leaf. If such a
run prefixes another complete run, both the output and the entire trace agree. -/
@[expose] public section

namespace Shellsort.ComparisonAudit

theorem run_eq_of_prefix {n : ℕ} {α : Type} (t : Tree n α) (p q : RankPlacement n)
    (h : List.IsPrefix (t.run p).2 (t.run q).2) : t.run p = t.run q := by
  induction t with
  | leaf a => rfl
  | ask i j yes no hyes hno =>
    by_cases hp : p.symm i < p.symm j <;> by_cases hq : q.symm i < q.symm j
    · have same := hyes (by simpa [Tree.run, hp, hq, List.cons_prefix_cons] using h)
      simp [Tree.run, hp, hq, same]
    · simp [Tree.run, hp, hq, List.cons_prefix_cons] at h
    · simp [Tree.run, hp, hq, List.cons_prefix_cons] at h
    · have same := hno (by simpa [Tree.run, hp, hq, List.cons_prefix_cons] using h)
      simp [Tree.run, hp, hq, same]

theorem separates_of_injective_output {n : ℕ} {α : Type} (t : Tree n α)
    (inj : Function.Injective (fun p : RankPlacement n => (t.run p).1)) :
    ComparisonTranscriptBound.Separates (fun p => (t.run p).2) :=
  fun p q h => inj (congrArg Prod.fst (run_eq_of_prefix t p q h))

theorem tree_uniform_lower {n : ℕ} {α : Type} (t : Tree n α)
    (inj : Function.Injective (fun p : RankPlacement n => (t.run p).1))
    (cost : RankPlacement n → ℕ) (len : ∀ p, (t.run p).2.length ≤ cost p) :
    Real.logb 2 (n.factorial : ℝ) ≤ uniformAverage (fun p => (cost p : ℝ)) :=
  ComparisonTranscriptBound.uniform_cost_lower _ cost (separates_of_injective_output t inj) len


end Shellsort.ComparisonAudit
