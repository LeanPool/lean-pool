/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDynamicsDrift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EquilibriumFactorization
public import LeanPool.GinibrePoincare.Concrete.GroundState
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-! # Exact deterministic drift factorization at arbitrary paper speed

The Coulomb interaction is translation invariant and has zero coordinate sum.
Consequently the Langevin drift splits into the center Ornstein–Uhlenbeck drift
and an autonomous recentered drift, with the paper's arbitrary speed retained.
These are coefficient identities, not stochastic process or semigroup claims.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The planar Coulomb interaction; the diagonal term is identically zero. -/
def ginibreCoulombInteraction (n : ℕ) (z : Configuration n) : Configuration n :=
  fun j => ∑ k : Fin n, (z j - z k) / (Complex.normSq (z j - z k) : ℂ)

/-- The exact Langevin drift for inverse temperature `n²` and arbitrary speed `α`. -/
def ginibreLangevinDrift (n : ℕ) (α : ℝ) (z : Configuration n) : Configuration n :=
  fun j => -(2 * α / (n : ℝ)) • z j +
    (2 * α / (n : ℝ) ^ 2) • ginibreCoulombInteraction n z j

/-- Translation leaves the actual interaction unchanged, even under the total
convention for division on collisions. -/
theorem ginibreCoulombInteraction_translate (n : ℕ) (z : Configuration n) (c : ℂ) :
    ginibreCoulombInteraction n (fun i => z i + c) = ginibreCoulombInteraction n z := by
  funext j
  unfold ginibreCoulombInteraction
  congr 1
  funext k
  rw [add_sub_add_right_eq_sub]

/-- The total interaction has zero center component. -/
theorem coordinateSum_ginibreCoulombInteraction (n : ℕ) (z : Configuration n) :
    coordinateSum (ginibreCoulombInteraction n z) = 0 := by
  let F (j k : Fin n) := (z j - z k) / (Complex.normSq (z j - z k) : ℂ)
  have ha (j k : Fin n) : F j k = -F k j := by
    dsimp [F]
    rw [show z j - z k = -(z k - z j) by ring, Complex.normSq_neg, neg_div]
  have hs : (∑ j : Fin n, ∑ k : Fin n, F j k) = -(∑ j : Fin n, ∑ k : Fin n, F j k) := by
    calc
      _ = ∑ k : Fin n, ∑ j : Fin n, F j k := Finset.sum_comm
      _ = _ := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        exact ha j k
  have ht : (2 : ℂ) * (∑ j : Fin n, ∑ k : Fin n, F j k) = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

/-- Recentering leaves the actual Coulomb interaction unchanged. -/
theorem ginibreCoulombInteraction_recentered (n : ℕ) (z : Configuration n) :
    ginibreCoulombInteraction n (recenteredConfiguration n z) = ginibreCoulombInteraction n z := by
  change ginibreCoulombInteraction n (fun i => z i - coordinateSum z / (n : ℂ)) = _
  simpa only [sub_eq_add_neg] using
    ginibreCoulombInteraction_translate n z (-(coordinateSum z / (n : ℂ)))

/-- Summing the drift gives the autonomous center Ornstein–Uhlenbeck drift. -/
theorem coordinateSum_ginibreLangevinDrift (n : ℕ) (α : ℝ) (z : Configuration n) :
    coordinateSum (ginibreLangevinDrift n α z) = -(2 * α / (n : ℝ)) • coordinateSum z := by
  unfold ginibreLangevinDrift coordinateSum
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  rw [show (∑ j, ginibreCoulombInteraction n z j) = 0 from
    coordinateSum_ginibreCoulombInteraction n z]
  simp

/-- Orthogonal projection of the drift is the same autonomous drift evaluated
at the recentered configuration, with no center-dependent interaction. -/
theorem recentered_ginibreLangevinDrift (n : ℕ) (α : ℝ) (z : Configuration n) :
    recenteredConfiguration n (ginibreLangevinDrift n α z) =
      ginibreLangevinDrift n α (recenteredConfiguration n z) := by
  funext j
  change ginibreLangevinDrift n α z j -
      coordinateSum (ginibreLangevinDrift n α z) / (n : ℂ) = _
  rw [coordinateSum_ginibreLangevinDrift]
  change ginibreLangevinDrift n α z j - _ =
    -(2 * α / (n : ℝ)) • recenteredConfiguration n z j +
      (2 * α / (n : ℝ) ^ 2) • ginibreCoulombInteraction n (recenteredConfiguration n z) j
  rw [ginibreCoulombInteraction_recentered]
  simp only [ginibreLangevinDrift, recenteredConfiguration, projectToOrthogonal, Complex.real_smul]
  ring

end
end GinibrePoincare
