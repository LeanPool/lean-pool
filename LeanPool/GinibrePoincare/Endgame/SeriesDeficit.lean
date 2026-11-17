/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/SeriesDeficit.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# The series arithmetic in the proof of Theorem 1.9

This file formalizes the exact algebraic endgame of the Hermite proof of the
Poincaré deficit formula in http://arxiv.org/abs/2608.19358v2.

The sequence `a` is deliberately shifted by one index:

* `a k` represents `‖g_{k+1}‖²`;
* `modeMass a = ∑ k, ‖g_{k+1}‖²`;
* `modeTail a = ∑ k, k ‖g_{k+1}‖²`, which is
  `∑_{m ≥ 2} (m - 1) ‖g_m‖²`;
* `modeEnergy a = ∑ k, (k + 1) ‖g_{k+1}‖²`, which is
  `∑_{m ≥ 1} m ‖g_m‖²`.

Every theorem in this file has an explicit proof term.
-/


@[expose] public section


open scoped BigOperators

namespace GinibrePoincare

noncomputable section

/-- The unweighted mass of the strictly positive Hermite modes. -/
def modeMass (a : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, a k

/-- The shifted Poincaré-deficit tail. -/
def modeTail (a : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * a k

/-- The weighted Hermite energy, with `a k = ‖g_{k+1}‖²`. -/
def modeEnergy (a : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * a k

/-- The elementary decomposition `(k + 1) a_k = a_k + k a_k`, summed over `k`. -/
theorem modeEnergy_eq_modeMass_add_modeTail
    (a : ℕ → ℝ)
    (ha : Summable a)
    (ht : Summable fun k : ℕ => (k : ℝ) * a k) :
    modeEnergy a = modeMass a + modeTail a := by
  unfold modeEnergy modeMass modeTail
  calc
    (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * a k)
        = ∑' k : ℕ, (a k + (k : ℝ) * a k) := by
            apply tsum_congr
            intro k
            simp only [Nat.cast_add, Nat.cast_one]
            ring
    _ = (∑' k : ℕ, a k) + ∑' k : ℕ, (k : ℝ) * a k :=
      ha.tsum_add ht

/-- Nonnegativity of the shifted tail. -/
theorem modeTail_nonneg
    (a : ℕ → ℝ)
    (ha : ∀ k : ℕ, 0 ≤ a k) :
    0 ≤ modeTail a := by
  unfold modeTail
  exact tsum_nonneg fun k : ℕ => mul_nonneg (Nat.cast_nonneg k) (ha k)

/--
The exact infinite-series deficit identity.

The hypotheses encode, respectively, Parseval, the three-term zero-mode
geometry, and the Hermite energy expansion.
-/
theorem infinite_deficit_identity
    (a : ℕ → ℝ)
    (ha : Summable a)
    (ht : Summable fun k : ℕ => (k : ℝ) * a k)
    (variance holomorphicSq remainderSq energy : ℝ)
    (hParseval : variance = holomorphicSq + modeMass a)
    (hGeometry : variance = 2 * holomorphicSq + remainderSq)
    (hEnergy : energy = 4 * modeEnergy a) :
    energy - 2 * variance = 2 * remainderSq + 4 * modeTail a := by
  rw [hEnergy, modeEnergy_eq_modeMass_add_modeTail a ha ht]
  linarith [hParseval, hGeometry]

/-- The Poincaré inequality obtained from the exact deficit identity. -/
theorem infinite_poincare_from_deficit
    (a : ℕ → ℝ)
    (ha : Summable a)
    (ht : Summable fun k : ℕ => (k : ℝ) * a k)
    (variance holomorphicSq remainderSq energy : ℝ)
    (hParseval : variance = holomorphicSq + modeMass a)
    (hGeometry : variance = 2 * holomorphicSq + remainderSq)
    (hEnergy : energy = 4 * modeEnergy a)
    (hRemainder : 0 ≤ remainderSq)
    (hMode : ∀ k : ℕ, 0 ≤ a k) :
    2 * variance ≤ energy := by
  have hDeficit := infinite_deficit_identity a ha ht variance holomorphicSq
    remainderSq energy hParseval hGeometry hEnergy
  have hTail := modeTail_nonneg a hMode
  linarith

/-- The conventional form `variance ≤ energy / 2`. -/
theorem infinite_poincare_half
    (a : ℕ → ℝ)
    (ha : Summable a)
    (ht : Summable fun k : ℕ => (k : ℝ) * a k)
    (variance holomorphicSq remainderSq energy : ℝ)
    (hParseval : variance = holomorphicSq + modeMass a)
    (hGeometry : variance = 2 * holomorphicSq + remainderSq)
    (hEnergy : energy = 4 * modeEnergy a)
    (hRemainder : 0 ≤ remainderSq)
    (hMode : ∀ k : ℕ, 0 ≤ a k) :
    variance ≤ energy / 2 := by
  have h := infinite_poincare_from_deficit a ha ht variance holomorphicSq
    remainderSq energy hParseval hGeometry hEnergy hRemainder hMode
  linarith

/-- Equality forces both nonnegative pieces of the Poincaré deficit to vanish. -/
theorem infinite_equality_forces_remainder_and_tail_zero
    (a : ℕ → ℝ)
    (ha : Summable a)
    (ht : Summable fun k : ℕ => (k : ℝ) * a k)
    (variance holomorphicSq remainderSq energy : ℝ)
    (hParseval : variance = holomorphicSq + modeMass a)
    (hGeometry : variance = 2 * holomorphicSq + remainderSq)
    (hEnergy : energy = 4 * modeEnergy a)
    (hRemainder : 0 ≤ remainderSq)
    (hMode : ∀ k : ℕ, 0 ≤ a k)
    (hEquality : energy = 2 * variance) :
    remainderSq = 0 ∧ modeTail a = 0 := by
  have hDeficit := infinite_deficit_identity a ha ht variance holomorphicSq
    remainderSq energy hParseval hGeometry hEnergy
  have hTail := modeTail_nonneg a hMode
  constructor <;> linarith

/-- Vanishing of the two pieces is sufficient for equality. -/
theorem infinite_equality_of_remainder_and_tail_zero
    (a : ℕ → ℝ)
    (ha : Summable a)
    (ht : Summable fun k : ℕ => (k : ℝ) * a k)
    (variance holomorphicSq remainderSq energy : ℝ)
    (hParseval : variance = holomorphicSq + modeMass a)
    (hGeometry : variance = 2 * holomorphicSq + remainderSq)
    (hEnergy : energy = 4 * modeEnergy a)
    (hRemainderZero : remainderSq = 0)
    (hTailZero : modeTail a = 0) :
    energy = 2 * variance := by
  have hDeficit := infinite_deficit_identity a ha ht variance holomorphicSq
    remainderSq energy hParseval hGeometry hEnergy
  linarith

section Finite

/-- Finite-mode analogue of `modeMass`. -/
def finiteModeMass (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  (Finset.range N).sum a

/-- Finite-mode analogue of `modeTail`. -/
def finiteModeTail (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  (Finset.range N).sum (fun k : ℕ => (k : ℝ) * a k)

/-- Finite-mode analogue of `modeEnergy`. -/
def finiteModeEnergy (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  (Finset.range N).sum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * a k)

/-- Finite-sum version of `(k + 1) a_k = a_k + k a_k`. -/
theorem finiteModeEnergy_eq_finiteModeMass_add_finiteModeTail
    (N : ℕ) (a : ℕ → ℝ) :
    finiteModeEnergy N a = finiteModeMass N a + finiteModeTail N a := by
  unfold finiteModeEnergy finiteModeMass finiteModeTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Nonnegativity of the finite shifted tail. -/
theorem finiteModeTail_nonneg
    (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ k : ℕ, 0 ≤ a k) :
    0 ≤ finiteModeTail N a := by
  unfold finiteModeTail
  refine Finset.sum_nonneg ?_
  intro k hk
  exact mul_nonneg (Nat.cast_nonneg k) (ha k)

/-- Exact finite-Hermite-expansion deficit identity. -/
theorem finite_deficit_identity
    (N : ℕ) (a : ℕ → ℝ)
    (variance holomorphicSq remainderSq energy : ℝ)
    (hParseval : variance = holomorphicSq + finiteModeMass N a)
    (hGeometry : variance = 2 * holomorphicSq + remainderSq)
    (hEnergy : energy = 4 * finiteModeEnergy N a) :
    energy - 2 * variance = 2 * remainderSq + 4 * finiteModeTail N a := by
  rw [hEnergy, finiteModeEnergy_eq_finiteModeMass_add_finiteModeTail N a]
  linarith [hParseval, hGeometry]

/-- Poincaré inequality for a finite Hermite expansion. -/
theorem finite_poincare_from_deficit
    (N : ℕ) (a : ℕ → ℝ)
    (variance holomorphicSq remainderSq energy : ℝ)
    (hParseval : variance = holomorphicSq + finiteModeMass N a)
    (hGeometry : variance = 2 * holomorphicSq + remainderSq)
    (hEnergy : energy = 4 * finiteModeEnergy N a)
    (hRemainder : 0 ≤ remainderSq)
    (hMode : ∀ k : ℕ, 0 ≤ a k) :
    2 * variance ≤ energy := by
  have hDeficit := finite_deficit_identity N a variance holomorphicSq
    remainderSq energy hParseval hGeometry hEnergy
  have hTail := finiteModeTail_nonneg N a hMode
  linarith

end Finite

end

end GinibrePoincare
