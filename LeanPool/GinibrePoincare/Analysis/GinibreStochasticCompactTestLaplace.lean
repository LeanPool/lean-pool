/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCompactTestLaplace.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactTestDynkin
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionWeightedLaplace

/-!
# Ginibre stochastic compact test Laplace

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_compact_test_transition_weighted_laplace_identity`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance actualCompactTestFullPathMeasurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration n)
    := borel _
local instance actualCompactTestFullPathBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

theorem ginibreBrownian_compact_test_transition_duhamel {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : Configuration n → ℝ) (hf : IsGinibreCollisionFreeCompactTest f) :
    (∫ ω, f (ginibreBrownianMaximalProcess n α z B T ω) ∂P)=f z+
      ∫ s in (0 : ℝ)..(T : ℝ), (∫ ω, ginibreRealPaperSpeedGenerator n α f
        (ginibreBrownianMaximalProcess n α z B s.toNNReal ω) ∂P) := by
  let L := ginibreRealPaperSpeedGenerator n α f
  let X := fun ω => ginibreDrivenGlobalPathElement α (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n
      B α ω)
  have hXm : Measurable X := (ginibreDrivenGlobalPathElement_measurable hn α).comp
    (measurable_const.prodMk (ginibreBrownianFullContinuousNoise_measurable n B P hB α))
  have hLc : Continuous L := (continuous_ginibrePregenerator_of_compact_test hf).const_mul _
  have hLs : HasCompactSupport L := by
    change HasCompactSupport ((fun _ => (α : ℝ)/(n : ℝ))*ginibrePregenerator n f)
    exact (hasCompactSupport_ginibrePregenerator hf.2.1).mul_left
  obtain ⟨D, hD⟩ := hLs.exists_bound_of_continuous hLc
  let ν := volume.restrict (Ioc (0 : ℝ) (T : ℝ))
  have hjm : Measurable (fun p : ℝ × Ω => L (X p.2 p.1)) := hLc.measurable.comp
    (continuous_eval.measurable.comp ((hXm.comp measurable_snd).prodMk measurable_fst))
  have hji : Integrable (fun p : ℝ × Ω => L (X p.2 p.1)) (ν.prod P) :=
    (integrable_const D).mono' hjm.aestronglyMeasurable (ae_of_all _ (fun p => hD _))
  have hSwap := integral_integral_swap (f := fun s ω => L (X ω s)) hji
  have htop := ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind
  have hEq : ∀ᵐ ω ∂P, ∀ s, L (X ω s)=L (ginibreBrownianMaximalProcess n α z B s.toNNReal ω) := by
    filter_upwards [htop] with ω hω
    intro s
    have hd : ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α ω).val z=⊤
        := hω
    simp only [X, ginibreDrivenGlobalPathElement, dite_eq_left hd, ContinuousMap.coe_mk,
      ginibreBrownianMaximalProcess]
  have hLeft : (∫ ω, (∫ s in (0 : ℝ)..(T : ℝ), L (ginibreBrownianMaximalProcess n α z B s.toNNReal
      ω)) ∂P)=
      ∫ ω, (∫ s in (0 : ℝ)..(T : ℝ), L (X ω s)) ∂P := by
    apply integral_congr_ae
    filter_upwards [hEq] with ω hω
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hω s).symm
  have hRight : (∫ s in (0 : ℝ)..(T : ℝ), (∫ ω, L (X ω s) ∂P))=
      ∫ s in (0 : ℝ)..(T : ℝ), (∫ ω, L (ginibreBrownianMaximalProcess n α z B s.toNNReal ω) ∂P) :=
          by
    apply intervalIntegral.integral_congr
    intro s hs
    apply integral_congr_ae
    exact hEq.mono (fun ω hω => hω s)
  rw [ginibreBrownian_compact_test_expectation hn α z hz B P hB hind T f hf, hLeft]
  congr 1
  have heSwap : (∫ ω, (∫ s in (0 : ℝ)..(T : ℝ), L (X ω s)) ∂P)=
      ∫ s in (0 : ℝ)..(T : ℝ), (∫ ω, L (X ω s) ∂P) := by
    simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ)≤(T : ℝ) from T.property)]
    exact hSwap.symm
  exact heSwap.trans hRight

theorem ginibreBrownian_compact_test_transition_weighted_laplace_identity {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n → ℝ) (hf : IsGinibreCollisionFreeCompactTest f) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-ℓ*t)*
      (ℓ*(∫ ω, f (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P)-
       (∫ ω, ginibreRealPaperSpeedGenerator n α f
         (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P)))=f z := by
  let L := ginibreRealPaperSpeedGenerator n α f
  have hLc : Continuous L := (continuous_ginibrePregenerator_of_compact_test hf).const_mul _
  have hLs : HasCompactSupport L := by
    change HasCompactSupport ((fun _ => (α : ℝ)/(n : ℝ))*ginibrePregenerator n f)
    exact (hasCompactSupport_ginibrePregenerator hf.2.1).mul_left
  obtain ⟨C, hC⟩ := hf.2.1.exists_bound_of_continuous hf.1.continuous
  obtain ⟨D, hD⟩ := hLs.exists_bound_of_continuous hLc
  let a := fun t : ℝ => ∫ ω, f (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P
  let b := fun t : ℝ => ∫ ω, L (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P
  have ha := ginibreBrownian_bounded_continuous_transition_mean_continuous hn α z hz B P hB hind f
      hf.1.continuous C hC
  have hb := ginibreBrownian_bounded_continuous_transition_mean_continuous hn α z hz B P hB hind L
      hLc D hD
  have hAm : ∀ t≥0, ‖a t‖≤C := by
    intro t ht
    simpa [a] using norm_integral_le_of_norm_le_const (μ := P) (ae_of_all P (fun ω => hC _))
  have hBm : ∀ t≥0, ‖b t‖≤D := by
    intro t ht
    simpa [b] using norm_integral_le_of_norm_le_const (μ := P) (ae_of_all P (fun ω => hD _))
  have hA0 : a 0=f z := by
    simpa [a] using ginibreBrownian_compact_test_transition_duhamel hn α z hz B P hB hind 0 f hf
  have he : ∀ t≥0, a t=a 0+∫ s in (0 : ℝ)..t, b s := by
    intro t ht
    simpa only [a, b, hA0, Real.coe_toNNReal t ht] using
      ginibreBrownian_compact_test_transition_duhamel hn α z hz B P hB hind t.toNNReal f hf
  exact (boundedDuhamel_weighted_laplace_core a b ℓ hℓ ha hb C D hAm hBm he).trans hA0

end
end GinibrePoincare
