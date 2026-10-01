/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# The closing arithmetic in Dross's fractional triangle-decomposition argument

At the exact one-tenth deficiency, the two inequalities from the deficient-cut analysis
contradict `n ≥ 20`. This is an internal leaf of the full graph-theoretic proof; the
inequalities are hypotheses here, not conclusions of this module.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

public theorem dross_final_contradiction (n : ℕ) (m : ℝ) (hn : (20 : ℝ) ≤ (n : ℝ))
    (h8 : (2 - 12 * (1 / 10 : ℝ) + 12 * (1 / 10 : ℝ) ^ 2) * (n : ℝ) ^ 2
            < 2 * m - 6 * (1 / 10 : ℝ) * (n : ℝ))
    (hcap : 2 * m ≤ (1 - (1 / 10 : ℝ) + 2 * (1 / 10 : ℝ) ^ 2) * (n : ℝ) ^ 2
                      + 4 + (n : ℝ) - 6 * (1 / 10 : ℝ) * (n : ℝ)) :
    False := by
  nlinarith [hn, h8, hcap]

end LeanPool.DrossFractionalTriangleDecomposition
