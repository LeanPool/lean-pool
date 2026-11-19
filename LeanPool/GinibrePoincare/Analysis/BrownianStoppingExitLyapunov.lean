/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitLyapunov.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitContinuous

/-! Lyapunov exit bounds derived from an actual stopped martingale decomposition. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem continuous_stopped_lyapunov_exit_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N ℱ μ) (hcont : ∀ᵐ ω ∂μ, Continuous (fun t => N t ω))
    (hN0 : N 0 =ᵐ[μ] 0)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    {Y A : Ω → ℝ} {H₀ M c R : ℝ} (hA : Integrable A μ)
    (hdecomp : Y =ᵐ[μ] fun ω => H₀ + (fun ω => N (τ ω) ω) ω + A ω)
    (hupper : A ≤ᵐ[μ] fun _ => c * (T : ℝ))
    (hlower : (fun _ => M) ≤ᵐ[μ] Y) (hR : M < R) :
    μ.real {ω | R ≤ Y ω} ≤ (H₀-M+c*(T : ℝ))/(R-M) := by
  have hop := continuous_martingale_bounded_stopping_integral hN hcont hτ hτT
  have hstop := hop.1
  have hY : Integrable Y μ :=
    ((integrable_const H₀).add hstop |>.add hA).congr hdecomp.symm
  have hmean : ∫ ω, (fun ω => N (τ ω) ω) ω ∂μ = 0 := by
    rw [hop.2,
      integral_congr_ae hN0]
    simp
  have hAY : ∫ ω, A ω ∂μ ≤ c*(T : ℝ) := by
    simpa using integral_mono_ae hA (integrable_const (c*(T : ℝ))) hupper
  have hEY : ∫ ω, Y ω ∂μ ≤ H₀+c*(T : ℝ) := by
    rw [integral_congr_ae hdecomp,
      integral_add (f := fun ω => H₀ + (fun ω => N (τ ω) ω) ω) (g := A)
        ((integrable_const H₀).add hstop) hA,
      integral_add (f := fun _ : Ω => H₀) (g := (fun ω => N (τ ω) ω))
        (integrable_const H₀) hstop, hmean]
    simpa using hAY
  have hnonneg : 0 ≤ᵐ[μ] (fun ω => Y ω-M) := hlower.mono (fun ω h => sub_nonneg.mpr h)
  have hm := mul_meas_ge_le_integral_of_nonneg hnonneg (hY.sub (integrable_const M)) (R-M)
  have heq : {ω | R-M ≤ Y ω-M} = {ω | R ≤ Y ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sub_le_sub_iff_right]
  rw [heq, integral_sub hY (integrable_const M)] at hm
  have hi : (∫ _ : Ω, M ∂μ) = M := by simp
  rw [hi] at hm
  apply (le_div_iff₀ (sub_pos.mpr hR)).mpr
  nlinarith

end
end GinibrePoincare
