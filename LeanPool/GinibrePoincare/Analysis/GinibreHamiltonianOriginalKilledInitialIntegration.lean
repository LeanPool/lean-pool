/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOriginalKilledInitialIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianKilledMixtureIntegration
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInitialCollisionNormalization
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltJointCanonicalPath
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCompletedStationaryReference

/-!
# Ginibre Hamiltonian original killed initial integration

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreHamiltonian_original_killed_gaussian_initial_identity`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance ginibreOriginalInitialIntegrationPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance ginibreOriginalInitialIntegration_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- The canonical original path on `[0, T]` started from the collision-free normalization of
the configuration assembled from the real coordinates `x.1`, driven by the noise at `x.2`. -/
def ginibreGaussianInitialOriginalPath {Ω : Type*} (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (x : ((Fin n × Fin 2) → ℝ) × Ω) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ginibreCanonicalJointHorizonPath α T
    (ginibreInitialCollisionNormalize n (ginibreHamiltonianOUCoordinateAssembly n x.1),
      ginibreBrownianFullContinuousNoise n B α x.2)

/-- The Ornstein–Uhlenbeck path on `[0, T]` started from the configuration assembled from the
real coordinates `x.1`, driven by the Brownian noise of `B` at `x.2`. -/
def ginibreGaussianInitialOUPath {Ω : Type*} (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (x : ((Fin n × Fin 2) → ℝ) × Ω) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ginibreHamiltonianOUJointHorizonPath n α T
    (ginibreHamiltonianOUCoordinateAssembly n x.1, ginibreBrownianFullContinuousNoise n B α x.2)

theorem ginibreGaussianInitialOriginalPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (ginibreGaussianInitialOriginalPath n α T B) :=
  (ginibreCanonicalJointHorizonPath_measurable hn α T).comp
    (((ginibreInitialCollisionNormalize_measurable n).comp
      ((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst)).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

theorem ginibreGaussianInitialOUPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (ginibreGaussianInitialOUPath n α T B) :=
  (ginibreHamiltonianOUJointHorizonPath_measurable n α T).comp
    (((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

/-- Actual fixed-initial Girsanov laws integrated against the genuine Gaussian
initial law and Vandermonde weight. No stochastic identity is assumed. -/
theorem ginibreHamiltonian_original_killed_gaussian_initial_identity {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) (R : ℝ) :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    ((((γ.prod P).withDensity (fun x => vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n
        x.1))).map
      (ginibreGaussianInitialOriginalPath n α T B)).restrict (ginibreHamiltonianCompactSurvival n (T
          : ℝ) R)) =
      ((γ.prod P).map (ginibreGaussianInitialOUPath n α T B)).withDensity
        (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property
            x)) := by
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let C := ginibreGaussianInitialOriginalPath n α T B
  let O := ginibreGaussianInitialOUPath n α T B
  let S := ginibreHamiltonianCompactSurvival n (T : ℝ) R
  let a := fun x => ENNReal.ofReal (ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property x)
  let w := fun x => vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x)
  let e := fun x => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n
      (ginibreHamiltonianOUCoordinateAssembly n x)))
  have hC := ginibreGaussianInitialOriginalPath_measurable hn α T B P hB
  have hO := ginibreGaussianInitialOUPath_measurable n α T B P hB
  have hS := ginibreHamiltonianCompactSurvival_measurableSet n (T : ℝ) R
  have ha : Measurable a := ENNReal.measurable_ofReal.comp
    (ginibreHamiltonianOUActionWeight_measurable n α (T : ℝ) T.property)
  have hw : Measurable w := measurable_vandermondeDensity.comp
    (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
  have he : Measurable e := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((Real.measurable_log.comp (contDiff_vandermondeWeight n).continuous.measurable).neg.comp
      (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable))
  have hCancel : ∀ᵐ x ∂γ, w x * e x = 1 := by
    filter_upwards [ginibreGaussian_coordinates_collisionFree_ae hn] with x hx
    change ENNReal.ofReal (vandermondeWeight _) * ENNReal.ofReal (Real.exp
        (ginibreInteractionPotential n _)) = 1
    rw [← ENNReal.ofReal_mul (vandermondeWeight_nonneg _),
        ginibreInteraction_initial_density_cancellation _ hx]
    norm_num
  have hFiber : ∀ᵐ x ∂γ,
      (P.map (fun ω => C (x, ω))).restrict S =
      (P.withDensity (fun ω => e x * S.indicator a (O (x, ω)))).map (fun ω => O (x, ω)) := by
    filter_upwards [ginibreGaussian_coordinates_collisionFree_ae hn] with x hx
    have h := ginibreBrownian_original_joint_killed_compact_path_law_all_initial hn B P hB hiB α
      (ginibreHamiltonianOUCoordinateAssembly n x) hx R T hT
    have hNorm := ginibreInitialCollisionNormalize_of_free (ginibreHamiltonianOUCoordinateAssembly n
        x) hx
    have hDensity : (fun ω => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n
        (ginibreHamiltonianOUCoordinateAssembly n x)) *
        ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property
          (ginibreHamiltonianOUReferenceHorizon n α (ginibreHamiltonianOUCoordinateAssembly n x) B T
              ω))) =
        (fun ω => e x * S.indicator a (O (x, ω))) := by
      funext ω
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      change ENNReal.ofReal (S.indicator (ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property)
          (O (x, ω))) =
        S.indicator a (O (x, ω))
      by_cases hs : O (x, ω) ∈ S
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
        exact ENNReal.ofReal_zero
    rw [hDensity] at h
    have hOE : ginibreHamiltonianOUReferenceHorizon n α (ginibreHamiltonianOUCoordinateAssembly n x)
        B T =
        (fun ω => O (x, ω)) := by funext ω; rfl
    rw [hOE] at h
    simpa only [C, ginibreGaussianInitialOriginalPath, hNorm, O, ginibreGaussianInitialOUPath, S,
      ginibreHamiltonianOUReferenceHorizon] using h
  have hMix := ginibre_killed_product_mixture γ P C O hC hO S hS a ha w e hw he hCancel hFiber
  have hKilled : S.indicator a = (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n
      α (T : ℝ) R T.property x)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [S, a, ginibreHamiltonianKilledOUActionWeight, hx]
  rw [hKilled] at hMix
  exact hMix

end
end GinibrePoincare
