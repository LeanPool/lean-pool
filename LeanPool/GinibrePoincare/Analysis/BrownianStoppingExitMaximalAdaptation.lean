/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitMaximalAdaptation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitPastNoisePath

/-! The actual canonical maximal Brownian-driven solution is strongly adapted. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The value at time `t` of the maximal solution of the Ginibre Langevin equation started at
`z` and driven by the continuous Brownian noise of the sample `ω`. -/
def ginibreBrownianMaximalProcess {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : Configuration n :=
  ginibreDrivenMaximalValue n α (ginibreBrownianFullContinuousNoise n B α ω).val z t

/-- The maximal lifetime of the Ginibre Langevin solution started at `z` and driven by the
continuous Brownian noise of the sample `ω`. -/
def ginibreBrownianMaximalLifetime {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α ω).val z

theorem ginibreBrownianMaximalLifetime_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (ginibreBrownianMaximalLifetime n α z B) :=
  (ginibreDrivenMaximalLifetime_measurable hn α z).comp
    (ginibreBrownianFullContinuousNoise_measurable n B P hB α)

theorem ginibreBrownianMaximalProcess_stronglyAdapted {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreBrownianMaximalProcess n α z B) := by
  intro s
  have hAE₁ := ginibreBrownianFullContinuousNoise_ae n B P hB α
  have hAE₂ := ginibreBrownianFullPastContinuousNoise_ae n B P hB α s
  have hm := ginibreBrownianFamilyPastSpace_le B P (fun i => (hB i).toIsPreBrownianReal) s
  let mPast := ginibreBrownianFamilyPastSpace B s
  let mAug := ginibreNullAugmentation (mAmbient := mAmbient) P mPast
  have hAug := ginibreNullAugmentation_le (mAmbient := mAmbient) P mPast hm
  let μ := P.trim hAug
  have : μ.IsComplete := ginibreNullAugmentation_trim_complete (mAmbient := mAmbient) P mPast hm
  have hPast : @Measurable Ω (Configuration n) mAug _ (fun ω =>
      ginibreDrivenMaximalValue n α (ginibreBrownianFullPastContinuousNoise n B α s ω).val z s) :=
    (ginibreDrivenMaximalValue_measurable hn α z s).comp
      (ginibreBrownianFullPastContinuousNoise_measurable (mAmbient := mAmbient) n B P hB α s)
  have hAE := ginibreNullAugmentation_ae_transfer (mAmbient := mAmbient) P mPast hm _
    (hAE₁.and hAE₂)
  have heq : (fun ω => ginibreDrivenMaximalValue n α
      (ginibreBrownianFullPastContinuousNoise n B α s ω).val z s) =ᵐ[μ]
      ginibreBrownianMaximalProcess n α z B s := by
    filter_upwards [hAE] with ω hω
    let A := ginibreBrownianFullPastContinuousNoise n B α s ω
    let C := ginibreBrownianFullContinuousNoise n B α ω
    apply ginibreDrivenMaximalValue_past_invariant A.val.continuous A.property C.val.continuous
        C.property s
    intro u hu
    rw [hω.2 u, hω.1 u, min_eq_left hu.2]
  exact ((aemeasurable_iff_measurable (μ := μ)).mp
    (hPast.aemeasurable.congr heq)).stronglyMeasurable

end
end GinibrePoincare
