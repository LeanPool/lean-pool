/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BernoulliBinomialBridge.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BernoulliCubeExpectations
public import Mathlib.Probability.Independence.Integration

/-!
# Bernoulli binomial bridge

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `bernoulliCubeAverage_eq_rademacherSum_integral`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section

/-- The unnormalized sum on the concrete independent-sign probability space. -/
def rademacherSum (n : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range n, ω k

/-- Adding a fair sign averages the two translated tests. -/
def bernoulliAverageStep (F : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  (1 / 2 : ℝ) • (F.compContinuous ⟨fun x => x + 1, by fun_prop⟩ +
    F.compContinuous ⟨fun x => x - 1, by fun_prop⟩)

/-- Independence gives the concrete two-translation expectation recursion. -/
theorem rademacherSum_integral_succ (n : ℕ) (F : ℝ →ᵇ ℝ) :
    (∫ ω, F (rademacherSum (n + 1) ω) ∂rademacherProduct) =
      ∫ ω, bernoulliAverageStep F (rademacherSum n ω) ∂rademacherProduct := by
  have hs : Measurable (rademacherSum n) := by unfold rademacherSum; fun_prop
  have hn : Measurable (fun ω : ℕ → ℝ => ω n) := by fun_prop
  have hi : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) rademacherProduct :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (by fun_prop)
  have hind := hi.indepFun_finsetSum_of_notMem (by fun_prop) (s := Finset.range n) (i := n) (by
      simp)
  have hind' : IndepFun (rademacherSum n) (fun ω : ℕ → ℝ => ω n) rademacherProduct := by
    convert! hind using 1
    funext ω
    simp [rademacherSum, Finset.sum_apply]
  let μ := rademacherProduct.map (rademacherSum n)
  have : IsProbabilityMeasure μ := (by infer_instance)
  let J : (ℝ × ℝ) →ᵇ ℝ := F.compContinuous ⟨fun p => p.1 + p.2, by fun_prop⟩
  have hj : HasLaw (fun ω : ℕ → ℝ => (rademacherSum n ω, ω n))
      (μ.prod rademacherMeasure) rademacherProduct := by
    refine ⟨(hs.prodMk hn).aemeasurable, ?_⟩
    rw [IndepFun.map_prod_eq_prod_map_map hs.aemeasurable hn.aemeasurable hind',
      (rademacherCoordinate_hasLaw n).map_eq]
  have he := hj.integral_comp J.continuous.aestronglyMeasurable
  change (∫ ω, J (rademacherSum n ω, ω n) ∂rademacherProduct) = _ at he
  have hl : (∫ ω, F (rademacherSum (n + 1) ω) ∂rademacherProduct) =
      ∫ ω, J (rademacherSum n ω, ω n) ∂rademacherProduct := by
    apply integral_congr_ae
    apply ae_of_all
    intro ω
    simp [rademacherSum, Finset.sum_range_succ, J]
  rw [hl, he, integral_prod _ (J.integrable _)]
  have hinner (x : ℝ) : (∫ y, J (x, y) ∂rademacherMeasure) = bernoulliAverageStep F x := by
    unfold rademacherMeasure
    rw [integral_bernoulliMeasure]
    change (1 / 2 : ℝ) * F (x + 1) + (1 - (1 / 2 : ℝ)) * F (x + -1) =
      (1 / 2 : ℝ) * (F (x + 1) + F (x - 1))
    rw [sub_eq_add_neg]
    ring_nf
  simp_rw [hinner]
  exact integral_map hs.aemeasurable (bernoulliAverageStep F).continuous.aestronglyMeasurable

/-- Uniform finite-cube averages are the actual binomial expectations. -/
theorem bernoulliCubeAverage_eq_rademacherSum_integral (n : ℕ) (F : ℝ →ᵇ ℝ) :
    bernoulliCubeAverage n (fun x => F (bernoulliCubeSum n x)) =
      ∫ ω, F (rademacherSum n ω) ∂rademacherProduct := by
  induction n generalizing F with
  | zero =>
      unfold bernoulliCubeAverage
      change (∑ x : Unit, F (bernoulliCubeSum 0 x)) / Fintype.card Unit = _
      simp [bernoulliCubeSum, rademacherSum, Fintype.card_unique]
  | succ n ih =>
      rw [rademacherSum_integral_succ, ← ih, bernoulliCubeAverage_succ]
      simp only [bernoulliCubeSum, bernoulliAverageStep, BoundedContinuousFunction.smul_apply,
        BoundedContinuousFunction.add_apply, BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk, smul_eq_mul, Bool.false_eq_true, ite_true, ite_false]
      unfold bernoulliCubeAverage
      simp only [sub_eq_add_neg]
      ring_nf
      simp only [Finset.sum_add_distrib, Finset.sum_mul]
      simp only [← Finset.sum_mul]
      ring

end
end GinibrePoincare
