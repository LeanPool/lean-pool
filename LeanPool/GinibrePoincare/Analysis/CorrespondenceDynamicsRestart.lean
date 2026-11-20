/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsRestart.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsNoiseShift
/-!
# Correspondence dynamics restart

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondence_ginibre_restart_all_times`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- Original-process restart holds simultaneously at all times, hence at any
finite random time, using the actual continuous shifted noise path. -/
theorem correspondence_ginibre_restart_all_times
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      ginibreDrivenMaximalLifetime n α
        (correspondenceNoiseShift n s (ginibreBrownianFullContinuousNoise n B α ω)).val
        (ginibreBrownianMaximalProcess n α z B s ω) = ⊤ ∧
      ∀ t : ℝ≥0, ginibreDrivenMaximalValue n α
        (correspondenceNoiseShift n s (ginibreBrownianFullContinuousNoise n B α ω)).val
        (ginibreBrownianMaximalProcess n α z B s ω) t =
          ginibreBrownianMaximalProcess n α z B (s+t) ω := by
  filter_upwards [(ginibreBrownianMaximalProcess_global_original_solution hn α z hz B P hB hind).2,
    ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hω hNoise
  intro s
  let X : ℝ → Configuration n := fun t => ginibreBrownianMaximalProcess n α z B t.toNNReal ω
  let N := (correspondenceNoiseShift n s (ginibreBrownianFullContinuousNoise n B α ω)).val
  have he : IsGinibreDrivenPath n α N (fun t => X (s+t)) := by
    have hShift := ginibreDrivenPath_shift n α _ _ hω.2.2.2 s s.property
    refine ⟨hShift.1,?_⟩
    intro t ht
    have heq : N t = ginibreConfigurationBrownianNoise n B α ω (s+t) -
        ginibreConfigurationBrownianNoise n B α ω s := by
      change (ginibreBrownianFullContinuousNoise n B α ω).val ((s : ℝ)+max t 0) -
        (ginibreBrownianFullContinuousNoise n B α ω).val s = _
      rw [max_eq_left ht, hNoise, hNoise]
    rw [heq]
    exact hShift.2 t ht
  have h := ginibreDrivenPath_canonical_global
    (hω.1.comp (continuous_const.add continuous_id))
    (fun t ht => hω.2.2.1 (s+t) (add_nonneg s.property ht)) he
  simpa only [X, N, Function.comp_def, Pi.add_apply, id_eq, add_zero, Real.toNNReal_coe,
    ← NNReal.coe_add] using h

end
end GinibrePoincare
