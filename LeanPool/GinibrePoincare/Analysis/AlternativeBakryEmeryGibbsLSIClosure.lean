/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsLSIClosure.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSIObservables
/-!
# Alternative Bakry Emery Gibbs LSI closure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_stationaryCoupling_square_lsi_limit`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
lemma bakryEmery_compactObservable_bound (g : E → ℝ) (hg : Continuous g)
    (hs : HasCompactSupport g) : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := (hs.isCompact_range hg).exists_bound_of_continuousOn continuous_id.continuousOn
  exact ⟨C, fun x => by simpa only [id_eq, Real.norm_eq_abs] using hC (g x) (mem_range_self x)⟩

omit [FiniteDimensional ℝ E] in
/-- Equilibrium closure for a concrete synchronous coupling. This is the
limit lemma; the stationary marginal and finite-time inequalities are supplied
by the separately constructed stochastic laws, and are not assumed in the
final Gibbs theorem. -/
theorem bakryEmery_stationaryCoupling_square_lsi_limit
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f)
    (X Y : ℕ → Ω → E) (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n, HasLaw (Y n) ν P)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => dist (X n ω) (Y n ω)) atTop (nhds 0))
    (c : ℝ) (hineq : ∀ n, squareEntropy P (fun ω => f (X n ω)) ≤
      c * ∫ ω, ‖gradient f (X n ω)‖ ^ 2 ∂P) :
    squareEntropy ν f ≤ c * ∫ x, ‖gradient f x‖^2 ∂ν := by
  have hgrad : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgs : HasCompactSupport (gradient f) :=
    (hs.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (map_zero _)
  have hs2 := hs.comp_left (g := fun x : ℝ => x^2) (by simp)
  have hsl := hs.comp_left (g := fun x : ℝ => x^2*Real.log (x^2)) (by simp)
  have hse := hgs.comp_left (g := fun x : E => ‖x‖^2) (by simp)
  obtain ⟨Cs, hCs⟩ := bakryEmery_compactObservable_bound (fun x => f x^2) (hf.continuous.pow 2) hs2
  obtain ⟨Cl, hCl⟩ := bakryEmery_compactObservable_bound (fun x => f x^2*Real.log (f x^2))
    (continuous_square_mul_log hf.continuous) hsl
  obtain ⟨Ce, hCe⟩ := bakryEmery_compactObservable_bound (fun x => ‖gradient f x‖^2)
    (hgrad.norm.pow 2) hse
  have huc := bakryEmery_compactSquareEntropy_uniformContinuous f hf.continuous hs
  have hmass := bakryEmery_stationaryCoupling_expectation_tendsto P ν
    (fun x => f x^2) huc.1 Cs hCs X Y hX hY hXY
  have hlog := bakryEmery_stationaryCoupling_expectation_tendsto P ν
    (fun x => f x^2*Real.log (f x^2)) huc.2 Cl hCl X Y hX hY hXY
  have henergy := bakryEmery_stationaryCoupling_expectation_tendsto P ν
    (fun x => ‖gradient f x‖^2) (bakryEmery_compactGradientEnergy_uniformContinuous f hf hs)
    Ce hCe X Y hX hY hXY
  have hent : Tendsto (fun n => squareEntropy P (fun ω => f (X n ω))) atTop
      (nhds (squareEntropy ν f)) := by
    exact hlog.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hmass)
  exact le_of_tendsto_of_tendsto' hent (henergy.const_mul c) hineq

end
end GinibrePoincare
