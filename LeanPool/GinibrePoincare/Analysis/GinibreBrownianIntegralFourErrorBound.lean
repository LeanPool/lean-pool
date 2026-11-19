/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralFourErrorBound.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralInitialCutoff

/-! Genuine L² error estimates used to pass initial-time-cutoff stochastic
integrals to a continuous martingale limit. -/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem actualMeanSquare_difference_le_four_errors {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I S A T J : Ω → ℝ)
    (hI : MemLp I 2 P) (hS : MemLp S 2 P) (hA : MemLp A 2 P)
    (hT : MemLp T 2 P) (hJ : MemLp J 2 P) :
    (∫ ω, (I ω-J ω)^2 ∂P) ≤ 4*((∫ ω, (I ω-S ω)^2 ∂P)+
      (∫ ω, (S ω-A ω)^2 ∂P)+(∫ ω, (A ω-T ω)^2 ∂P)+
      (∫ ω, (T ω-J ω)^2 ∂P)) := by
  have hIS := (hI.sub hS).integrable_sq
  have hSA := (hS.sub hA).integrable_sq
  have hAT := (hA.sub hT).integrable_sq
  have hTJ := (hT.sub hJ).integrable_sq
  have hbound (ω : Ω) : (I ω-J ω)^2 ≤
      4*((I ω-S ω)^2+(S ω-A ω)^2+(A ω-T ω)^2+(T ω-J ω)^2) := by
    nlinarith [sq_nonneg ((I ω-S ω)-(S ω-A ω)),
      sq_nonneg ((I ω-S ω)-(A ω-T ω)), sq_nonneg ((I ω-S ω)-(T ω-J ω)),
      sq_nonneg ((S ω-A ω)-(A ω-T ω)), sq_nonneg ((S ω-A ω)-(T ω-J ω)),
      sq_nonneg ((A ω-T ω)-(T ω-J ω))]
  have hh := integral_mono (hI.sub hJ).integrable_sq
    (((hIS.add hSA).add hAT).add hTJ |>.const_mul 4) hbound
  simp only [Pi.sub_apply] at hIS hSA hAT hTJ hh
  rw [integral_const_mul] at hh
  have he1 := integral_add ((hIS.add hSA).add hAT) hTJ
  have he2 := integral_add (hIS.add hSA) hAT
  have he3 := integral_add hIS hSA
  simp only [Pi.add_apply] at hh he1 he2 he3
  rw [he1, he2, he3] at hh
  exact hh

end
end GinibrePoincare
