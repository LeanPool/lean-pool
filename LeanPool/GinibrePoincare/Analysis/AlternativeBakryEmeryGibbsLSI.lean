/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSIDriverIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCompletedProductBrownian
/-!
# Alternative Bakry Emery Gibbs LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryConfigurationGibbs_square_lsi_of_Brownian`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Actual normalized strongly convex Gibbs LSI via the constructed Langevin
flow and internally proved Gibbs invariance. Brownian existence remains an
explicit process input in this stochastic theorem. -/
theorem bakryEmeryConfigurationGibbs_square_lsi_of_Brownian
    (n : ℕ) (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n×Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (B : (Fin n×Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm)) f ≤
      (2/κ)*∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (W ∘ (configurationEuclideanEquiv n).symm) := by
  let μ := bakryEmeryNormalizedGibbs volume W
  let ν := bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm)
  have : IsProbabilityMeasure μ := bakryEmeryConfiguration_gibbs_probability n W κ hκ hW hc
  let Q := (μ.prod P).completion
  let Ωc := NullMeasurableSpace (Configuration n×Ω) (μ.prod P)
  have : IsProbabilityMeasure Q := ginibre_completion_isProbabilityMeasure (μ.prod P)
  have : Nonempty (Fin n×Fin 2) := ⟨(⟨0, hn⟩, 0)⟩
  let Bc : (Fin n×Fin 2) → ℝ≥0 → Ωc → ℝ := fun i t p => B i t p.2
  let Z : Ωc → EuclideanSpace ℝ (Fin n×Fin 2) := fun p => configurationEuclideanEquiv n p.1
  have hBc : ∀ i, IsBrownianReal (Bc i) Q :=
    ginibreBrownian_completed_initial_noise_product μ P B hB
  have hiBc : iIndepFun (fun i p t => Bc i t p) Q :=
    ginibreBrownian_completed_product_independent_coordinates μ P B hB hind
  apply bakryEmeryBrownianEndpoint_stationary_square_lsi
    (W ∘ (configurationEuclideanEquiv n).symm) κ hκ
    (hW.comp (configurationEuclideanEquiv n).symm.contDiff) hc 0 Z Bc Q hBc hiBc ν ?_ f hf hs
  intro m
  let T : ℝ≥0 := ⟨m+1, by positivity⟩
  let E : Configuration n×Ω → EuclideanSpace ℝ (Fin n×Fin 2) :=
    fun p => configurationEuclideanEquiv n (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B p)
  have hE : Measurable E := (configurationEuclideanEquiv n).continuous.measurable.comp
    (bakryEmeryGibbsActualEndpoint_measurable W hW κ hκ hc T B P hB)
  have hLaw : HasLaw (fun p : Ωc => E p) ν Q := by
    refine ⟨hE.nullMeasurable.measurable'.aemeasurable,?_⟩
    rw [ginibre_map_completion (μ.prod P) E hE]
    exact bakryEmeryGibbsActualEndpoint_hilbert_stationary hn W hW κ hκ hc P B hB hind T (by
        change (0 : ℝ) < (m : ℝ)+1; positivity)
  apply hLaw.congr
  have hAE := (ginibreCompletedProduct_snd_preserving μ P).quasiMeasurePreserving.ae
    (bakryEmeryGibbsActualEndpoint_eq_BrownianEndpoint n hn W hW κ hκ hc B P hB T)
  filter_upwards [hAE] with p hp
  exact (hp p.1).symm

end
end GinibrePoincare
