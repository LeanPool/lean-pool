/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityWeakLinear.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakVariational

/-!
# Ginibre Equality Weak Linear
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory

/-- Sharp equality pairs form a genuine linear subspace of the actual weak domain. -/
def ginibreFullWeakEqualitySpace (n : ℕ) (hn : 0 < n) : Submodule ℝ (ginibreFullWeakSpace n hn)
  where
  carrier := {p | ∀ q : ginibreFullWeakSpace n hn,
    (1 / (n : ℝ)) * inner ℝ p.val.2 q.val.2 =
      2 * inner ℝ (ginibreFullCenter n hn p.val.1) (ginibreFullCenter n hn q.val.1)}
  zero_mem' := by intro q; simp
  add_mem' := by
    intro p r hp hr q
    change (1 / (n : ℝ)) * inner ℝ (p.val.2+r.val.2) q.val.2 =
      2 * inner ℝ (ginibreFullCenter n hn (p.val.1+r.val.1)) (ginibreFullCenter n hn q.val.1)
    rw [map_add, inner_add_left, inner_add_left]
    linarith [hp q, hr q]
  smul_mem' := by
    intro c p hp q
    change (1 / (n : ℝ)) * inner ℝ (c • p.val.2) q.val.2 =
      2 * inner ℝ (ginibreFullCenter n hn (c • p.val.1)) (ginibreFullCenter n hn q.val.1)
    rw [map_smul, real_inner_smul_left, real_inner_smul_left]
    calc
      _ = c * ((1 / (n : ℝ)) * inner ℝ p.val.2 q.val.2) := by ring
      _ = c * (2 * inner ℝ (ginibreFullCenter n hn p.val.1) (ginibreFullCenter n hn q.val.1)) :=
        congrArg (c * ·) (hp q)
      _ = _ := by ring

theorem ginibreFullWeakEqualitySpace_mem_iff (n : ℕ) (hn : 0 < n)
    (p : ginibreFullWeakSpace n hn) :
    p ∈ ginibreFullWeakEqualitySpace n hn ↔
      ginibreWeakEnergy n p.val.2 = 2 * ginibreL2Variance n hn p.val.1 :=
  (ginibreEquality_weak_variational_iff n hn p).symm

/-- Equality extends across every actual real weak-domain affine line. -/
theorem ginibreEquality_weak_linear_combination {n : ℕ} (hn : 0 < n)
    (p q : ginibreFullWeakSpace n hn) (a b : ℝ)
    (hp : ginibreWeakEnergy n p.val.2 = 2 * ginibreL2Variance n hn p.val.1)
    (hq : ginibreWeakEnergy n q.val.2 = 2 * ginibreL2Variance n hn q.val.1) :
    ginibreWeakEnergy n (a•p+b•q).val.2 =
      2 * ginibreL2Variance n hn (a•p+b•q).val.1 := by
  apply (ginibreFullWeakEqualitySpace_mem_iff n hn _).mp
  exact (ginibreFullWeakEqualitySpace n hn).add_mem
    ((ginibreFullWeakEqualitySpace n hn).smul_mem a ((ginibreFullWeakEqualitySpace_mem_iff n hn
      p).mpr hp))
    ((ginibreFullWeakEqualitySpace n hn).smul_mem b ((ginibreFullWeakEqualitySpace_mem_iff n hn
      q).mpr hq))

end GinibrePoincare
