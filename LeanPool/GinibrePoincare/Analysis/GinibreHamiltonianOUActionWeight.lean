/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOUActionWeight.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianConfigurationOUReference

/-! The correct stationary-OU reference action is a quotient by the quadratic
Hamiltonian action. Its identification as the original SDE Radon–Nikodym law
still requires the continuous Girsanov and Itô theorems. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance GinibreHamiltonianOUActionWeightRealMeasurable (n : ℕ) : MeasurableSpace C(ℝ,
    Configuration n) := borel _
local instance GinibreHamiltonianOUActionWeight_realBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n)
    := ⟨rfl⟩
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance GinibreHamiltonianOUActionWeightCompactMeasurable (n : ℕ) (T : ℝ) : MeasurableSpace
    C(Icc (0 : ℝ) T, Configuration n) := borel _
local instance GinibreHamiltonianOUActionWeight_compactBorel (n : ℕ) (T : ℝ) : BorelSpace C(Icc (0 :
    ℝ) T, Configuration n) := ⟨rfl⟩

/-- The quadratic (Ornstein–Uhlenbeck) path weight
`exp (-(n ‖x 0‖² + n ‖x T‖²) / 2 + 2αT - α ∫ s in 0..T, ‖x s‖²)`. -/
def ginibreQuadraticGradientPathWeight (n : ℕ) (α T : ℝ) (x : ℝ → Configuration n) : ℝ :=
  Real.exp (-((n : ℝ)*configurationNormSq (x 0)+(n : ℝ)*configurationNormSq (x T))/2 +
    2*α*T - α*(∫ s in (0 : ℝ)..T, configurationNormSq (x s)))

/-- The ratio of the compact Hamiltonian path weight to the quadratic path weight
`ginibreQuadraticGradientPathWeight` of the extended path. -/
def ginibreHamiltonianOUActionWeight (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T, Configuration n)) : ℝ :=
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  ginibreHamiltonianCompactPathWeight n α T hT x /
    ginibreQuadraticGradientPathWeight n α T (ContinuousMap.IccExtendCM x)

theorem ginibreQuadraticGradientPathWeight_reverse (n : ℕ) (α T : ℝ)
    (x : ℝ → Configuration n) :
    ginibreQuadraticGradientPathWeight n α T (fun s => x (T-s)) =
    ginibreQuadraticGradientPathWeight n α T x := by
  unfold ginibreQuadraticGradientPathWeight
  have hi := intervalIntegral.integral_comp_sub_left
    (fun s => configurationNormSq (x s)) (a := 0) (b := T) T
  simp only [sub_zero, sub_self] at hi ⊢
  rw [hi]
  congr 1
  ring

theorem ginibreQuadraticGradientPathWeight_measurable (n : ℕ) (α T : ℝ) :
    Measurable (fun x : C(ℝ, Configuration n) => ginibreQuadraticGradientPathWeight n α T x) := by
  have hnorm : Measurable (configurationNormSq : Configuration n → ℝ) :=
    (contDiff_configurationNormSq (n := n)).continuous.measurable
  have hm : Measurable (fun p : C(ℝ, Configuration n) × ℝ => configurationNormSq (p.1 p.2)) :=
    hnorm.comp continuous_eval.measurable
  have hi (s : Set ℝ) : Measurable (fun x : C(ℝ, Configuration n) => ∫ t in s, configurationNormSq
      (x t)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have he : Measurable (fun x : C(ℝ, Configuration n) => ∫ t in (0 : ℝ)..T, configurationNormSq (x
      t)) := by
    unfold intervalIntegral
    exact (hi _).sub (hi _)
  have h0 : Measurable (fun x : C(ℝ, Configuration n) => configurationNormSq (x 0)) :=
    hnorm.comp (continuous_eval_const (0 : ℝ)).measurable
  have hT : Measurable (fun x : C(ℝ, Configuration n) => configurationNormSq (x T)) :=
    hnorm.comp (continuous_eval_const T).measurable
  unfold ginibreQuadraticGradientPathWeight
  exact Real.measurable_exp.comp
    (((((measurable_const.mul h0).add (measurable_const.mul hT)).neg.div_const 2).add_const _).sub
      (measurable_const.mul he))

theorem ginibreHamiltonianOUActionWeight_measurable (n : ℕ) (α T : ℝ) (hT : 0 ≤ T) :
    Measurable (ginibreHamiltonianOUActionWeight n α T hT) := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  exact (ginibreHamiltonianCompactPathWeight_measurable n α T hT).div
    ((ginibreQuadraticGradientPathWeight_measurable n α T).comp
      (ContinuousMap.IccExtendCM : C(C(Icc (0 : ℝ) T, Configuration n), C(ℝ, Configuration
          n))).continuous.measurable)

theorem ginibreHamiltonianOUActionWeight_reverse (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T, Configuration n)) :
    ginibreHamiltonianOUActionWeight n α T hT
      (x.comp (ginibreHamiltonianCompactReverseTime T hT)) =
    ginibreHamiltonianOUActionWeight n α T hT x := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  unfold ginibreHamiltonianOUActionWeight
  rw [ginibreHamiltonianCompactPathWeight_reverse]
  congr 1
  change ginibreQuadraticGradientPathWeight n α T
    (fun s => ContinuousMap.IccExtendCM (x.comp (ginibreHamiltonianCompactReverseTime T hT)) s) = _
  rw [ginibreHamiltonianCompactExtend_reverse, ginibreQuadraticGradientPathWeight_reverse]

/-- The actual stationary original-Brownian OU product law, reweighted by the
correct Hamiltonian/quadratic action quotient, is time-reversal invariant.
This is a genuine measure identity; equality with the singular-SDE law remains
a separate stochastic identification, and is not assumed here. -/
theorem ginibreHamiltonianOUActionMeasure_reverse {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1 / 2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (α : ℝ) (T : ℝ≥0) :
    ((ginibreConfigurationOUReferenceLaw n B P Z (2*α/(n : ℝ)).toNNReal T).withDensity
      (fun x => ENNReal.ofReal (ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property x))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    (ginibreConfigurationOUReferenceLaw n B P Z (2*α/(n : ℝ)).toNNReal T).withDensity
      (fun x => ENNReal.ofReal (ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property x)) := by
  exact invariant_measure_withDensity_of_invariant_weight _ _
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime (T : ℝ)
        T.property)).measurable
    (ginibreConfigurationOUReferenceLaw_reverse n B P hB Z hZ hind _ T) _
    (ENNReal.measurable_ofReal.comp (ginibreHamiltonianOUActionWeight_measurable n α (T : ℝ)
        T.property))
    (fun x => congrArg ENNReal.ofReal (ginibreHamiltonianOUActionWeight_reverse n α (T : ℝ)
        T.property x))

end
end GinibrePoincare
