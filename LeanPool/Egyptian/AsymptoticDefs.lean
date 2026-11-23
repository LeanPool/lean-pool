/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Infinite denominator expansions and the rigidity statement

The sequence index `k` corresponds to index `k + 1` in the paper.
-/

@[expose] public section

namespace Egyptian

/-- The assumptions on competitor sequences in Theorem 4, with ordinary real series convergence. -/
def Expansion (q : ℚ) (a : ℕ → ℕ) : Prop :=
  (∀ k, 2 ≤ a k) ∧ Monotone a ∧ HasSum (fun k => 1 / (a k : ℝ)) (q : ℝ)

/-- The construction preceding Corollary 3: an optimizing prefix of length
N ≥ 1, a unit remainder with denominator T ≥ 2, and its prescribed greedy
continuation, with every prefix from N onward maximizing in the weak convention. -/
def Benchmark (q : ℚ) (b : ℕ → ℕ) : Prop :=
  Expansion q b ∧ ∃ N T : ℕ, 1 ≤ N ∧ 2 ≤ T ∧
    q = recipSum (prefixTuple b N) + unit T ∧
    (∀ j, b (N + j) = unitIter T j + 1) ∧
    ∀ n, N ≤ n → IsBest .weak q n (prefixTuple b n)

/-- The real growth term a_n^(2^(-n)), n=k+1 in the paper. -/
noncomputable def growth (a : ℕ → ℕ) (k : ℕ) : ℝ :=
  (a k : ℝ) ^ ((2 : ℝ) ^ (k + 1))⁻¹

/-- Extended-real liminf. This also handles competitors for which boundedness
of the sequence of growth terms has not yet been proved. -/
noncomputable def lowerGrowth (a : ℕ → ℕ) : EReal :=
  Filter.liminf (fun k => (growth a k : EReal)) Filter.atTop

/-- Theorem 4 together with the existence and finite positive limiting growth
of the benchmark specified directly before Corollary 3. Quantifying over all
such benchmarks makes the possibly nonunique choice of a maximizing prefix
immaterial. -/
def AsymptoticRigidity : Prop :=
  ∀ q : ℚ, 0 < q →
    (∃ b, Benchmark q b) ∧
    ∀ b, Benchmark q b →
      ∃ L : ℝ, 0 < L ∧ Filter.Tendsto (growth b) Filter.atTop (nhds L) ∧
        ∀ a, Expansion q a →
          lowerGrowth a < (L : EReal) ∨ ∃ K : ℕ, ∀ k, K ≤ k → a k = b k

end Egyptian
