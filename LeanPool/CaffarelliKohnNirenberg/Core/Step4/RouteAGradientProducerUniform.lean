/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSymmetricCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAGradientProducerUniformExponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAGradientProducerUniformMorrey
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Route AGradient Producer Uniform

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-! # The pressure-gradient producer at a free velocity exponent

The bootstrap of `prop:bootstrap` runs the velocity through the whole range
`τ ∈ [25/3, 25]` of Morrey exponents, and each round needs the pressure
gradient in `M^{6/5, κ(τ)}` with `1/κ(τ) = 1/τ + 1/τ₃` and `τ₃ = 25/8`, that
is `κ(τ) = (1/τ + 8/25)⁻¹`.  The producer is stated here with `τ` free.
-/

/-- The Route A pressure-gradient producer at a free velocity exponent.  This
is the statement consumed by the regularity provider for every `τ` that the
bootstrap of `prop:bootstrap` visits. -/
def routeAGradientProducerUniform : Prop :=
  ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
      Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
      morreyVecMem 3 τ (Metric.ball z₀ R) u →
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
        (Metric.ball z₀ R) (fun z => Du z i)) →
      ∃ Dp : ParabolicPoint → Vec3,
        (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
          (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
        (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
        morreyVecMem (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
          (Metric.ball z₀ (R / 2)) Dp

end CKN.Core.Step4
