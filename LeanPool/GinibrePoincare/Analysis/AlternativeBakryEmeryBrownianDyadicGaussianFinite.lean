/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicGaussianFinite.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicCoordinates
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Basic
/-!
# Alternative Bakry Emery Brownian dyadic Gaussian finite

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianFiniteDyadic_evaluations_gaussian`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The truncated dyadic index set: the linear coordinate (`none`) together with the tents of
the levels `n < N`. -/
abbrev BakryBrownianFiniteDyadicIndex (N : ℕ) := Option (Σ n : Fin N, Fin (2^n.val))

/-- The inclusion of the truncated index set `BakryBrownianFiniteDyadicIndex N` into
`BakryBrownianDyadicIndex`. -/
def bakryBrownianFiniteDyadicEmbed (N : ℕ) : BakryBrownianFiniteDyadicIndex N →
    BakryBrownianDyadicIndex
  | none => none
  | some ⟨n, k⟩ => some ⟨n.val, k⟩

theorem bakryBrownianFiniteDyadicEmbed_injective (N : ℕ) :
    Function.Injective (bakryBrownianFiniteDyadicEmbed N) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => simp [bakryBrownianFiniteDyadicEmbed] at h
  | some i =>
    cases j with
    | none => simp [bakryBrownianFiniteDyadicEmbed] at h
    | some j =>
      cases i with
      | mk n k =>
        cases j with
        | mk m l =>
          have hnm : n.val = m.val := congrArg (fun x : BakryBrownianDyadicIndex =>
            match x with | none => 0 | some p => p.1) h
          have he : n = m := Fin.ext hnm
          cases he
          have hkl : k = l := by simpa [bakryBrownianFiniteDyadicEmbed] using h
          cases hkl
          rfl

/-- Genuine finite coefficient Gaussian law extracted from the internally
constructed countable independent Gaussian product. -/
theorem bakryBrownianFiniteDyadic_coordinates_gaussian (N : ℕ) :
    HasGaussianLaw (fun sample : BakryBrownianDyadicSample => fun i : BakryBrownianFiniteDyadicIndex
        N =>
      sample (bakryBrownianFiniteDyadicEmbed N i)) bakryBrownianDyadicMeasure := by
  apply iIndepFun.hasGaussianLaw
  · intro i
    exact (bakryBrownianDyadic_coordinate_law _).hasGaussianLaw
  · exact bakryBrownianDyadic_coordinates_independent.precomp
      (bakryBrownianFiniteDyadicEmbed_injective N)

/-- The literal finite Faber–Schauder evaluation is a concrete continuous
linear form of the finite product coefficients. -/
def bakryBrownianFiniteDyadicEvaluation (N : ℕ) (t : Icc (0 : ℝ) 1) :
    (BakryBrownianFiniteDyadicIndex N → ℝ) →L[ℝ] ℝ :=
  t.val • ContinuousLinearMap.proj none + ∑ n : Fin N, ∑ k : Fin (2^n.val),
    ((1/Real.sqrt 2)^n.val * bakryBrownianDyadicTent n.val k t) •
      ContinuousLinearMap.proj (some ⟨n, k⟩)

theorem bakryBrownianFiniteDyadicEvaluation_apply (N : ℕ) (t : Icc (0 : ℝ) 1)
    (x : BakryBrownianFiniteDyadicIndex N → ℝ) :
    bakryBrownianFiniteDyadicEvaluation N t x = x none*t.val +
      ∑ n : Fin N, (1/Real.sqrt 2)^n.val * ∑ k : Fin (2^n.val), x (some ⟨n, k⟩) *
        bakryBrownianDyadicTent n.val k t := by
  simp only [bakryBrownianFiniteDyadicEvaluation, add_apply,
    smul_apply, ContinuousLinearMap.proj_apply,
    sum_apply, smul_eq_mul]
  rw [mul_comm t.val]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Every finite vector of actual partial-series evaluations is jointly
Gaussian; shared coefficients are handled by one concrete linear map. -/
theorem bakryBrownianFiniteDyadic_evaluations_gaussian {ι : Type*} [Finite ι]
    (N : ℕ) (t : ι → Icc (0 : ℝ) 1) :
    HasGaussianLaw (fun sample : BakryBrownianDyadicSample => fun a : ι =>
      sample none*(t a).val + ∑ n : Fin N, (1/Real.sqrt 2)^n.val *
        ∑ k : Fin (2^n.val), sample (some ⟨n.val, k⟩)*bakryBrownianDyadicTent n.val k (t a))
      bakryBrownianDyadicMeasure := by
  have := Fintype.ofFinite ι
  let L : (BakryBrownianFiniteDyadicIndex N → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (fun a => bakryBrownianFiniteDyadicEvaluation N (t a))
  have h := (bakryBrownianFiniteDyadic_coordinates_gaussian N).map_fun L
  convert h using 1
  funext sample a
  simp only [L, ContinuousLinearMap.pi_apply, bakryBrownianFiniteDyadicEvaluation_apply,
    bakryBrownianFiniteDyadicEmbed]

end
end GinibrePoincare
