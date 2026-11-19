/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/EntropyL2Closure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreL2Norm
public import LeanPool.GinibrePoincare.Analysis.EntropyLimitStability
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences

/-!
# Entropy L 2 closure

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `entropy_bound_on_closure`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Strong L² convergence and convergent energy bounds imply the limiting
entropy inequality, including integrability of its logarithmic moment. -/
theorem squareEntropy_le_of_L2_tendsto {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ) (E : ℕ → ℝ) (e : ℝ)
    (hf : Tendsto f atTop (𝓝 g)) (hE : Tendsto E atTop (𝓝 e))
    (hlog : ∀ m, Integrable (fun x => f m x ^ 2 * Real.log (f m x ^ 2)) μ)
    (hineq : ∀ m, squareEntropy μ (f m) ≤ E m) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ ∧ squareEntropy μ g ≤ e := by
  obtain ⟨s, hs, ha⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  have hmass : Tendsto (fun m => ∫ x, f m x ^ 2 ∂μ) atTop (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
    simp_rw [integral_square_eq_L2_norm_sq]
    exact hf.norm.pow 2
  exact squareEntropy_le_of_ae_tendsto μ (fun m => f (s m)) g (E ∘ s) e
    (fun m => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (fun m => hlog _) ha (hmass.comp hs.tendsto_atTop) (hE.comp hs.tendsto_atTop)
    (fun m => hineq _)

/-- The entropy-energy inequality defines a closed subset of the product of
an L² value space and an L² gradient space. This is the analytic closure step;
it does not assume or prove a Gaussian or Ginibre core inequality. -/
theorem isClosed_entropy_energy_pairs {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V]
    (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    IsClosed {p : Lp ℝ 2 μ × Lp V 2 μ |
      Integrable (fun x => p.1 x ^ 2 * Real.log (p.1 x ^ 2)) μ ∧
        squareEntropy μ p.1 ≤ c * ‖p.2‖ ^ 2} := by
  apply IsSeqClosed.isClosed
  intro p q hp hq
  exact squareEntropy_le_of_L2_tendsto μ (fun m => (p m).1) q.1
    (fun m => c * ‖(p m).2‖ ^ 2) (c * ‖q.2‖ ^ 2)
    (continuous_fst.tendsto q |>.comp hq)
    ((continuous_snd.tendsto q |>.comp hq).norm.pow 2 |>.const_mul c)
    (fun m => (hp m).1) (fun m => (hp m).2)

/-- Any verified core entropy bound extends to the closure of its value-gradient
pairs in the actual L² product topology. -/
theorem entropy_bound_on_closure {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V]
    (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ)
    (S : Set (Lp ℝ 2 μ × Lp V 2 μ))
    (hS : ∀ p ∈ S,
      Integrable (fun x => p.1 x ^ 2 * Real.log (p.1 x ^ 2)) μ ∧
        squareEntropy μ p.1 ≤ c * ‖p.2‖ ^ 2) :
    ∀ p ∈ closure S,
      Integrable (fun x => p.1 x ^ 2 * Real.log (p.1 x ^ 2)) μ ∧
        squareEntropy μ p.1 ≤ c * ‖p.2‖ ^ 2 := by
  exact closure_minimal hS (isClosed_entropy_energy_pairs μ c)

end
end GinibrePoincare
