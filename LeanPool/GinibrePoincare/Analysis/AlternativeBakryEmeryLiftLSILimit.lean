/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLiftLSILimit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryConvexGibbsLSI
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryRegularizedEuclidean
public import LeanPool.GinibrePoincare.Analysis.BakryEmeryRegularizationVolume
/-!
# Alternative Bakry Emery lift LSI limit

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryEuclideanLift_square_lsi`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Positive radial regularization preserves the exact curvature constant;
the selected diffusion inequality is applied to the literal regularized density. -/
theorem bakryEmeryRegularizedLift_square_lsi_of_Brownian {Ω : Type*} [MeasurableSpace Ω]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (B : (Fin d × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (ε : ℝ) (hε : 0 < ε) (f : EuclideanSpace ℝ (Fin d × Fin 2) → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (bakryEmeryRegularizedLiftPotential n V ε)) f ≤
      (2/((n : ℝ)*ρ)) * ∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (bakryEmeryRegularizedLiftPotential n V ε) := by
  let W := bakryEmeryRegularizedConfigurationPotential n d V ε
  have hWe := bakryEmeryRegularizedConfigurationPotential_euclidean_contDiff n d V ε hV hε
  have hW : ContDiff ℝ 2 W := by
    have h := hWe.comp (configurationEuclideanEquiv d).contDiff
    simpa [Function.comp_def, W] using h
  have hκ : 0 < (n : ℝ)*ρ := mul_pos (Nat.cast_pos.mpr hn) hρ
  have h := bakryEmeryConfigurationGibbs_square_lsi_of_Brownian d hd W hW _ hκ
    (bakryEmeryRegularizedConfigurationPotential_euclidean_strongConvex n d ρ ε V hrot hc)
    B P hB hind f hf hs
  simpa only [W, bakryEmeryRegularizedConfigurationPotential_euclidean] using h

/-- Passage to the unregularized Euclidean lift. Both entropy and actual
gradient expectations converge under internally proved Gaussian domination. -/
theorem bakryEmeryEuclideanLift_square_lsi_of_Brownian {Ω : Type*} [MeasurableSpace Ω]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (B : (Fin d × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : EuclideanSpace ℝ (Fin d × Fin 2) → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (bakryEmeryEuclideanLiftPotential n V)) f ≤
      (2/((n : ℝ)*ρ)) * ∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (bakryEmeryEuclideanLiftPotential n V) := by
  have he := bakryEmeryRegularizedLift_volume_entropy_tendsto n hn ρ hρ V hV.continuous hrot hc f
      hf.continuous hs
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d × Fin 2))).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgs : HasCompactSupport (fun x => ‖gradient f x‖^2) :=
    ((hs.fderiv ℝ).comp_left
      (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d × Fin 2))).symm) (map_zero
          _)).comp_left
      (g := fun x : EuclideanSpace ℝ (Fin d × Fin 2) => ‖x‖^2) (by simp)
  have hi := bakryEmeryRegularizedLift_volume_expectation_tendsto n hn ρ hρ V hV.continuous hrot hc
    (fun x => ‖gradient f x‖^2) (hg.norm.pow 2) hgs
  let ε : ℕ → ℝ := fun m => 1/(m+1 : ℝ)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact le_of_tendsto_of_tendsto (he.comp hε) ((tendsto_const_nhds.mul hi).comp hε)
    (Eventually.of_forall (fun m => bakryEmeryRegularizedLift_square_lsi_of_Brownian
      n d hn hd ρ hρ V hV hrot hc B P hB hind (ε m) (by dsimp [ε]; positivity) f hf hs))

/-- Concrete unregularized radial lift inequality. The Brownian family and
all analytic completion inputs are proved internally. -/
theorem bakryEmeryEuclideanLift_square_lsi
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : EuclideanSpace ℝ (Fin d × Fin 2) → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (bakryEmeryEuclideanLiftPotential n V)) f ≤
      (2/((n : ℝ)*ρ)) * ∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (bakryEmeryEuclideanLiftPotential n V) := by
  exact bakryEmeryEuclideanLift_square_lsi_of_Brownian n d hn hd ρ hρ V hV hrot hc
    (bakryBrownianCoordinateProcess (Fin d × Fin 2))
    (bakryBrownianCoordinateMeasure (Fin d × Fin 2))
    (bakryBrownianCoordinate_isBrownian (Fin d × Fin 2))
    (bakryBrownianCoordinate_independent (Fin d × Fin 2)) f hf hs

end
end GinibrePoincare
