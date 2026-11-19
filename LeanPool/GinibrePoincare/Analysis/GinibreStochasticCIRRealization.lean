/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCIRRealization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRDrivenLocal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialPath

/-! # CIR equation for the relative radius

The observable is `pairwiseRadius` of the original configuration process, with
shape `recenteredGammaShape n`. Its drift is `(4 * α / n) * (shape - radius)`
and its diffusion amplitude is `sqrt ((8 * α / n) * radius)`.

`ginibreBrownianMaximalProcess_CIR_realization_named` exports the same result
through `CIRScalarDriver`, `CIRExhaustingLocalization`, and
`CIRStoppedIntegral`, whose fields can be accessed by mathematical role.
The original endpoint remains available with its existing conjunction layout.

The original conclusion is arranged in three groups: properties of the scalar Brownian
driver `β`; stopping times increasing to infinity and positivity of the radius;
then, for each Hamiltonian level `R` and time cap `T`, a continuous martingale
`J` representing the integral against `β`. The last group records both
mean-square and convergence-in-measure interpretations of the uniform left
sums, followed by the equation up to the stopping time.

Proof route: construct `β` in `GinibreStochasticRadialBrownian`, use
`GinibreStochasticLocalizationExhaustion` for the stops, and apply the local
substitution theorem in `GinibreStochasticCIRDrivenLocal`. The assumption
`2 ≤ n` ensures strict positivity of the relative radius on collision-free
configurations. Completeness of `P` is used by the augmented-filtration
construction. The speed `α` may be zero. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- A scalar Brownian driver relative to the original augmented past.
The named fields replace positional projections into the driver conjunction. -/
structure CIRScalarDriver {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) : Prop where
  /-- Standard scalar Brownian law under `P`. -/
  brownian : IsBrownianReal β P
  /-- Martingale property relative to the original filtration. -/
  martingale : Martingale β F P
  /-- Square integrability at each deterministic time. -/
  squareIntegrable : ∀ t, MemLp (β t) 2 P
  /-- Future increments are independent of every variable measurable in the past. -/
  freshIncrements : ∀ s t (Y : Ω → ℝ), @Measurable Ω ℝ (F s) _ Y →
    IndepFun Y (fun ω => β (s + t) ω - β s ω) P

/-- Increasing stopping-time localizations eventually cover every finite horizon.
The exhaustion is pathwise on a single event of full measure. -/
structure CIRExhaustingLocalization {Ω : Type*} [MeasurableSpace Ω]
    (τ : ℕ → Ω → ℝ≥0) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) : Prop where
  /-- Each member is a stopping time in `F`. -/
  stoppingTime : ∀ k, IsStoppingTime F (fun ω => (τ k ω : WithTop ℝ≥0))
  /-- Stops increase pathwise with the localization index. -/
  monotone : ∀ ω, Monotone (fun k => τ k ω)
  /-- On one full-measure event, every finite horizon is eventually covered. -/
  exhausts : ∀ᵐ ω ∂P, ∀ b : ℝ≥0, ∀ᶠ k : ℕ in atTop, b ≤ τ k ω

/-- A stopped CIR integral specified by uniform Brownian left sums.
`r` is the stopped observable, `a` its diffusion amplitude, and `c * (θ - r)`
its drift. The equation holds only until `σ`, while continuity of `J` is global. -/
structure CIRStoppedIntegral {Ω : Type*} [MeasurableSpace Ω]
    (β a J : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (r : ℝ≥0 → Ω → ℝ) (r₀ c θ : ℝ) : Prop where
  martingale : Martingale J F P
  continuous : ∀ ω, Continuous (fun t => J t ω)
  squareIntegrable : ∀ t, MemLp (J t) 2 P
  initial : J 0 =ᵐ[P] (fun _ => 0)
  /-- Uniform left sums converge in mean square on the deterministic horizon. -/
  meanSquareLimit : ∀ t ≤ T, Tendsto (fun k => ∫ ω,
    (brownianUniformLeftSum β a t (k + 1) ω - J t ω)^2 ∂P) atTop (𝓝 0)
  /-- The same sums converge in measure to the integral process. -/
  probabilityLimit : ∀ t ≤ T,
    TendstoInMeasure P (fun k => brownianUniformLeftSum β a t (k + 1)) atTop (J t)
  /-- One full-measure event supports the CIR equation at every time before `σ`. -/
  equation : ∀ᵐ ω ∂P, ∀ t ≤ σ ω,
    r t ω - r₀ = J t ω + ∫ s in (0 : ℝ)..t, c * (θ - r s.toNNReal ω)

theorem ginibreBrownianMaximalProcess_CIR_realization
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    let τ := fun k : ℕ => ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k
    -- Scalar driver: Brownian law, martingale structure, and fresh increments.
    ∃ β : ℝ≥0 → Ω → ℝ,
      IsBrownianReal β P ∧ Martingale β F P ∧ (∀ t, MemLp (β t) 2 P) ∧
      (∀ s t (Y : Ω → ℝ), @Measurable Ω ℝ (F s) _ Y →
        IndepFun Y (fun ω => β (s+t) ω-β s ω) P) ∧
      -- Hamiltonian localization: stopping times, monotonicity, and exhaustion.
      (∀ k, IsStoppingTime F (fun ω => (τ k ω : WithTop ℝ≥0))) ∧
      (∀ ω, Monotone (fun k => τ k ω)) ∧
      (∀ᵐ ω ∂P, ∀ b : ℝ≥0, ∀ᶠ k : ℕ in atTop, b ≤ τ k ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => pairwiseRadius (ginibreBrownianMaximalProcess n α z B t
          ω)) ∧
        ∀ t, 0 < pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
      -- At each localization, identify the stochastic integral and CIR equation.
      ∀ (R : ℝ), ginibreHamiltonian n z ≤ R → ∀ (T : ℝ≥0),
        let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
        let a := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius (X t ω))
        ∃ J : ℝ≥0 → Ω → ℝ,
          Martingale J F P ∧ (∀ ω, Continuous (fun t => J t ω)) ∧
          (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum β a t (k+1) ω-J t ω)^2 ∂P) atTop (𝓝 0)) ∧
          (∀ t ≤ T, TendstoInMeasure P (fun k => brownianUniformLeftSum β a t (k+1)) atTop (J t)) ∧
          (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
            pairwiseRadius (X t ω)-pairwiseRadius z = J t ω+
              ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
                ((recenteredGammaShape n : ℝ)-pairwiseRadius (X s.toNNReal ω))) := by
  classical
  let i₀ : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  -- Construct the radial driver from the original coordinate Brownian family.
  obtain ⟨β, hβ, hβMartingale, hβSquareIntegrable, hβInitial, hβSumLimit, hβShiftedSumLimit,
      hβFreshIncrements⟩ :=
    ginibreBrownianMaximalProcess_radial_Brownian_exists hn α z hz B P hB hind
  refine ⟨β, hβ, hβMartingale, hβSquareIntegrable, hβFreshIncrements, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ginibreBrownianHamiltonianBoundedStop_isStoppingTime (by omega) α z hz B P hB
      _ (le_add_of_nonneg_right (Nat.cast_nonneg k)) k
  · intro ω
    exact ginibreBrownianHamiltonianBoundedStop_natural_monotone n α z B ω
  · exact ginibreBrownianHamiltonianBoundedStop_exhausts_ae (by omega) α z hz B P hB hind
  · have hh := (ginibreBrownianMaximalProcess_radius_path_properties hn α z hz B P hB hind).2
    filter_upwards [hh] with ω hω
    exact ⟨hω.1, hω.2.1⟩
  · intro R hR T
    exact ginibreBrownianMaximalProcess_local_CIR_Brownian_integral hn α z hz B P hB hind
      e he β hβSquareIntegrable hβSumLimit R hR T

/-- The relative-radius CIR realization with named driver, localization and
integral fields. This is an adapter of the original endpoint, preserving all
of its hypotheses and conclusions while avoiding positional projections. -/
theorem ginibreBrownianMaximalProcess_CIR_realization_named
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    let τ := fun k : ℕ => ginibreBrownianHamiltonianBoundedStop n α z B
      (ginibreHamiltonian n z + k) k
    ∃ β : ℝ≥0 → Ω → ℝ,
      CIRScalarDriver β F P ∧ CIRExhaustingLocalization τ F P ∧
      (∀ᵐ ω ∂P,
        Continuous (fun t : ℝ≥0 => pairwiseRadius
          (ginibreBrownianMaximalProcess n α z B t ω)) ∧
        ∀ t, 0 < pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
      ∀ (R : ℝ), ginibreHamiltonian n z ≤ R → ∀ (T : ℝ≥0),
        let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
        let r := fun t ω => pairwiseRadius (X t ω)
        let a := fun t ω => Real.sqrt ((8 * (α : ℝ) / (n : ℝ)) * r t ω)
        ∃ J : ℝ≥0 → Ω → ℝ,
          CIRStoppedIntegral β a J F P T
            (ginibreBrownianHamiltonianBoundedStop n α z B R T)
            r (pairwiseRadius z) (4 * (α : ℝ) / (n : ℝ)) (recenteredGammaShape n : ℝ) := by
  obtain ⟨β, hBrownian, hMartingale, hSquareIntegrable, hFresh,
    hStopping, hMonotone, hExhausts, hRadius, hIntegrals⟩ :=
    ginibreBrownianMaximalProcess_CIR_realization hn α z hz B P hB hind
  refine ⟨β, ⟨hBrownian, hMartingale, hSquareIntegrable, hFresh⟩,
    ⟨hStopping, hMonotone, hExhausts⟩, hRadius, ?_⟩
  intro R hR T
  obtain ⟨J, hMartingale, hContinuous, hSquareIntegrable, hInitial,
    hMeanSquare, hProbability, hEquation⟩ := hIntegrals R hR T
  exact ⟨J, ⟨hMartingale, hContinuous, hSquareIntegrable, hInitial,
    hMeanSquare, hProbability, hEquation⟩⟩

end
end GinibrePoincare
