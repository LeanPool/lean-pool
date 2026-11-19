/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticConfigurationBrownianIncrement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyPast
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalExistence

/-! The actual general-particle Brownian noise has fresh Gaussian independent increments. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The map sending real coordinates `v` to the configuration
`j ↦ √(2α / n²) (v (j, 0) + i v (j, 1))`. -/
def ginibreConfigurationBrownianEmbedding (n : ℕ) (α : ℝ) :
    ((Fin n × Fin 2) → ℝ) → Configuration n := fun v j =>
  Real.sqrt (2*α/(n : ℝ)^2) • ((v (j, 0) : ℂ)+Complex.I*(v (j, 1) : ℂ))

theorem ginibreConfigurationBrownianEmbedding_measurable (n : ℕ) (α : ℝ) :
    Measurable (ginibreConfigurationBrownianEmbedding n α) := by
  unfold ginibreConfigurationBrownianEmbedding
  fun_prop

/-- The law of a configuration Brownian increment over time `t`: the image under
`ginibreConfigurationBrownianEmbedding n α` of independent centred Gaussians of variance `t`. -/
def ginibreConfigurationBrownianIncrementLaw (n : ℕ) (α : ℝ) (t : ℝ≥0) : Measure (Configuration n)
    :=
  (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 t)).map
      (ginibreConfigurationBrownianEmbedding n α)

instance ginibreConfigurationBrownianIncrementLaw_isProbabilityMeasure (n : ℕ) (α : ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (ginibreConfigurationBrownianIncrementLaw n α t) :=
  (by unfold ginibreConfigurationBrownianIncrementLaw; infer_instance)

theorem ginibreConfigurationBrownianNoise_increment_eq {Ω : Type*}
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (s t : ℝ≥0) (ω : Ω) :
    ginibreConfigurationBrownianNoise n B α ω (s+t)-ginibreConfigurationBrownianNoise n B α ω s =
      ginibreConfigurationBrownianEmbedding n α (fun i => B i (s+t) ω-B i s ω) := by
  ext j
  simp only [ginibreConfigurationBrownianNoise, ginibreConfigurationBrownianEmbedding,
    ← NNReal.coe_add, Real.toNNReal_coe, Pi.sub_apply, Complex.ofReal_sub]
  rw [← smul_sub]
  congr 1
  ring

theorem ginibreConfigurationBrownianNoise_increment_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (s t : ℝ≥0) :
    HasLaw (fun ω => ginibreConfigurationBrownianNoise n B α ω
        (s+t)-ginibreConfigurationBrownianNoise n B α ω s)
      (ginibreConfigurationBrownianIncrementLaw n α t) P := by
  have hE : HasLaw (ginibreConfigurationBrownianEmbedding n α)
      (ginibreConfigurationBrownianIncrementLaw n α t) (Measure.pi (fun _ : Fin n × Fin 2 =>
          gaussianReal 0 t)) :=
    ⟨(ginibreConfigurationBrownianEmbedding_measurable n α).aemeasurable, rfl⟩
  have h := hE.comp (ginibreBrownian_family_increment_hasLaw B P hB hind s t)
  simpa only [Function.comp_def, id_eq, ginibreConfigurationBrownianNoise_increment_eq] using h

theorem ginibreConfigurationBrownianNoise_increment_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (s t : ℝ≥0) :
    IndepFun (fun ω => ginibreConfigurationBrownianNoise n B α ω
        (s+t)-ginibreConfigurationBrownianNoise n B α ω s)
      (fun ω (p : (Fin n × Fin 2) × Set.Iic s) => B p.1 p.2 ω) P := by
  have h := (ginibreBrownian_family_increment_independent_past B P hB hind s t).comp
    (ginibreConfigurationBrownianEmbedding_measurable n α) measurable_id
  simpa only [Function.comp_def, id_eq, ginibreConfigurationBrownianNoise_increment_eq] using h

end
end GinibrePoincare
