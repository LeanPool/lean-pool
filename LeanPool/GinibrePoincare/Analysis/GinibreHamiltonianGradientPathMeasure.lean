/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGradientPathMeasure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGradientPathWeight
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.Prod

/-! Borel measurability of the genuine Hamiltonian action on continuous paths. -/

@[expose] public section
open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance instBorelGinibreHamiltonianGradientPathMeasure1 (n : ℕ) : MeasurableSpace C(ℝ,
    Configuration n) := borel _
local instance instBorelGinibreHamiltonianGradientPathMeasure2 (n : ℕ) : BorelSpace C(ℝ,
    Configuration n) := ⟨rfl⟩

theorem ginibreHamiltonian_action_measurable (n : ℕ) : Measurable (ginibreHamiltonian n) := by
  unfold ginibreHamiltonian
  exact (measurable_const.mul (contDiff_configurationNormSq (n := n)).continuous.measurable).sub
    (Real.measurable_log.comp (contDiff_vandermondeWeight n).continuous.measurable)

theorem ginibreHamiltonianGradientNormSq_measurable (n : ℕ) :
    Measurable (ginibreHamiltonianGradientNormSq n) := by
  unfold ginibreHamiltonianGradientNormSq
  apply Finset.measurable_sum
  intro j hj
  exact ((measurable_fderiv_apply_const ℝ (ginibreHamiltonian n)
    (realCoordinateDirection j)).pow_const 2).add
    ((measurable_fderiv_apply_const ℝ (ginibreHamiltonian n)
      (imaginaryCoordinateDirection j)).pow_const 2)

theorem ginibreHamiltonianPathEnergy_measurable (n : ℕ) (α T : ℝ) :
    Measurable (fun x : C(ℝ, Configuration n) => ginibreHamiltonianPathEnergy n α T x) := by
  have hm : Measurable (fun p : C(ℝ, Configuration n) × ℝ =>
      ginibreHamiltonianGradientNormSq n (p.1 p.2)) :=
    (ginibreHamiltonianGradientNormSq_measurable n).comp continuous_eval.measurable
  have hi (s : Set ℝ) : Measurable (fun x : C(ℝ, Configuration n) =>
      ∫ t in s, ginibreHamiltonianGradientNormSq n (x t)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  unfold ginibreHamiltonianPathEnergy intervalIntegral
  exact measurable_const.mul ((hi (Ioc 0 T)).sub (hi (Ioc T 0)))

theorem ginibreHamiltonianGradientPathWeight_measurable (n : ℕ) (α T : ℝ) :
    Measurable (fun x : C(ℝ, Configuration n) =>
      ginibreHamiltonianGradientPathWeight n α T x) := by
  unfold ginibreHamiltonianGradientPathWeight
  have h0 : Measurable (fun x : C(ℝ, Configuration n) => ginibreHamiltonian n (x 0)) :=
      (ginibreHamiltonian_action_measurable n).comp (continuous_eval_const (0 : ℝ)).measurable
  have hT : Measurable (fun x : C(ℝ, Configuration n) => ginibreHamiltonian n (x T)) :=
      (ginibreHamiltonian_action_measurable n).comp (continuous_eval_const T).measurable
  exact Real.measurable_exp.comp
    ((((h0.add hT).neg.div_const 2).add_const (2*α*T)).sub
      (ginibreHamiltonianPathEnergy_measurable n α T))

end
end GinibrePoincare
