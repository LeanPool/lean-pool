/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralApproximationTransfer.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedApproximation

/-! A two-stage approximation principle for genuine nonnegative errors. -/

@[expose] public section
open Filter MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem nonnegative_error_tendsto_of_approximation
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hu : ∀ k, 0 ≤ u k) (hbound : ∀ n k, u k ≤ v n k)
    (hv : ∀ n, Tendsto (v n) atTop (𝓝 (a n)))
    (ha : Tendsto a atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun k => hb.trans_le (hu k)
  · intro b hb
    obtain ⟨n, hn⟩ := (ha.eventually (eventually_lt_nhds hb)).exists
    filter_upwards [(hv n).eventually (eventually_lt_nhds hn)] with k hk
    exact (hbound n k).trans_lt hk

theorem actualMeanSquareLimit_initial_cutoff_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → Ω → ℝ) (A : ℕ → ℕ → Ω → ℝ)
    (M : ℕ → Ω → ℝ) (I : Ω → ℝ)
    (hS : ∀ k, MemLp (S k) 2 P) (hA : ∀ n k, MemLp (A n k) 2 P)
    (hM : ∀ n, MemLp (M n) 2 P) (hI : MemLp I 2 P)
    (e d : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (hd : Tendsto d atTop (𝓝 0))
    (hb : ∀ n k, (∫ ω, (S k ω - A n k ω) ^ 2 ∂P) ≤ e n + d k)
    (hlim : ∀ n, Tendsto (fun k => ∫ ω, (A n k ω - M n ω) ^ 2 ∂P) atTop (𝓝 0))
    (hm : Tendsto (fun n => ∫ ω, (M n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (S k ω-I ω)^2 ∂P) atTop (𝓝 0) := by
  let v := fun n k => 4*(e n+d k+(∫ ω, (A n k ω-M n ω)^2 ∂P)+
    (∫ ω, (M n ω-I ω)^2 ∂P))
  let a := fun n => 4*(e n+(∫ ω, (M n ω-I ω)^2 ∂P))
  apply nonnegative_error_tendsto_of_approximation _ v a
    (fun k => integral_nonneg fun ω => sq_nonneg _)
  · intro n k
    have hh := actualMeanSquare_difference_le_four_errors P (S k) (A n k) (M n) I I
      (hS k) (hA n k) (hM n) hI hI
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero, add_zero] at hh
    exact hh.trans (by dsimp only [v]; gcongr; exact hb n k)
  · intro n
    have hh := (((hd.const_add (e n)).add (hlim n)).add_const
      (∫ ω, (M n ω-I ω)^2 ∂P)).const_mul 4
    simpa only [v, a, add_zero] using hh
  · have hh := (he.add hm).const_mul 4
    simpa only [a, add_zero, mul_zero] using hh

end
end GinibrePoincare
