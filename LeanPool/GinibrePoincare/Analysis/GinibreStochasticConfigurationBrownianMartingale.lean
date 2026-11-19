/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticConfigurationBrownianMartingale.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyMartingale
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticConfigurationBrownianIncrement

/-! The actual normalized n-particle noise is adapted and has martingale coordinates. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreConfigurationBrownianNoise_real_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (j : Fin n) :
    Martingale (fun (t : ℝ≥0) ω => (ginibreConfigurationBrownianNoise n B α ω t j).re)
      (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_coordinate_martingale B P hB hind (j, 0)).smul
    (Real.sqrt (2*α/(n : ℝ)^2))
  convert! h using 1
  funext t ω
  simp [ginibreConfigurationBrownianNoise, Pi.smul_apply, smul_eq_mul, Complex.mul_re]

theorem ginibreConfigurationBrownianNoise_imag_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (j : Fin n) :
    Martingale (fun (t : ℝ≥0) ω => (ginibreConfigurationBrownianNoise n B α ω t j).im)
      (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_coordinate_martingale B P hB hind (j, 1)).smul
    (Real.sqrt (2*α/(n : ℝ)^2))
  convert! h using 1
  funext t ω
  simp [ginibreConfigurationBrownianNoise, Pi.smul_apply, smul_eq_mul, Complex.mul_im]

theorem ginibreConfigurationBrownianNoise_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (α : ℝ) :
    StronglyAdapted (ginibreBrownianFamilyFiltration B P hB)
      (fun t ω => ginibreConfigurationBrownianNoise n B α ω t) := by
  intro s
  have hPast : @Measurable Ω ((Fin n × Fin 2) × Set.Iic s → ℝ)
      (ginibreBrownianFamilyPastSpace B s) inferInstance
      (fun ω p => B p.1 p.2 ω) := Measurable.of_comap_le le_rfl
  have hEval : Measurable (fun p : (Fin n × Fin 2) × Set.Iic s → ℝ =>
      fun i => p (i, ⟨s, by change s ≤ s; exact le_rfl⟩)) := by fun_prop
  have h := ((ginibreConfigurationBrownianEmbedding_measurable n α).comp hEval).comp hPast
  apply Measurable.stronglyMeasurable
  convert! h using 1
  funext ω j
  simp only [Function.comp_apply, ginibreConfigurationBrownianNoise,
    ginibreConfigurationBrownianEmbedding, Real.toNNReal_coe]

end
end GinibrePoincare
