/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticItoUntilStopping.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTestCompensator

/-! Actual local Itô identities hold simultaneously through an actual bounded stopping time. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCompactVolterra_compensator_eq_gradient_process_until
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0)
    (b : ℝ → Ω → Configuration n) (hb : ∀ ω, Continuous (fun s => b s ω))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ ω, ‖b s ω‖ ≤ M)
    (θ : Ω → ℝ≥0) (hθ : Measurable θ) (hθT : ∀ ω, θ ω ≤ T)
    (hVolterra : ∀ᵐ ω ∂P, ∀ t ≤ θ ω, X t ω = X 0 ω +
      (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω 0) +
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω)
    (J : ℝ≥0 → Ω → ℝ) (hJC : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (hJL : ∀ t ≤ T, TendstoInMeasure P (ginibreConfigurationBrownianGradientSum n B α X f t)
      atTop (J t)) :
    ∀ᵐ ω ∂P, ∀ t ≤ θ ω, ginibreConfigurationTestCompensator n α X f b t ω=J t ω := by
  apply ginibre_ae_continuous_identity_until P _ J θ
    (Filter.Eventually.of_forall (fun ω => ginibreConfigurationTestCompensator_continuous
      n α X hCont f U K hU hf hKU hRange b hb ω)) hJC
  intro t
  by_cases ht : t ≤ T
  · have hVE : ∀ᵐ ω ∂P, ω ∈ {ω | t ≤ θ ω} → ∀ r ∈ Icc 0 t,
        X r ω=X 0 ω+
          (ginibreConfigurationBrownianNoise n B α ω r-ginibreConfigurationBrownianNoise n B α ω 0)+
          ∫ s in (0 : ℝ)..(r : ℝ), b s ω := by
      filter_upwards [hVolterra] with ω hω
      intro he r hr
      exact hω r (hr.2.trans he)
    have heq := ginibreCompactVolterra_restricted_ito_identify n B P hB hind α X hX hCont
      f U K hU hf hK hKU hRange t b (fun ω => (hb ω).continuousOn) M hM
      (fun s hs ω => hbound s ⟨hs.1, hs.2.trans ht⟩ ω)
      {ω | t ≤ θ ω} (measurableSet_le measurable_const hθ) hVE (J t) (hJL t ht)
    filter_upwards [heq] with ω hω
    intro hwt
    have hh := hω hwt
    dsimp [ginibreConfigurationTestCompensator]
    linarith
  · exact Filter.Eventually.of_forall (fun ω hw => False.elim (ht (hw.trans (hθT ω))))
end
end GinibrePoincare
