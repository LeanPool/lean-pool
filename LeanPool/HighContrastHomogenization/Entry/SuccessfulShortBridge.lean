/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.ShortBridge

/-!
# High-contrast homogenization: Entry.SuccessfulShortBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The successful short bridge

The exact type of `p.successful.short.bridge`.
All ordinary analytic obligations are discharged in `Annealed.ShortBridge`.
The probability proof is introduced at its position and then installed
as an instance. Unit-range is forwarded in its original position; the ordinary
mathematical proof does not use it.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Entry
open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The short-bridge type, assembled from the ordinary rounded-grid theorem. -/
theorem successful_short_bridge
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ (L₀ : ℕ) (c₀ : ℝ), c₀ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ L : ℕ, (L₀ : ℤ) + ⌈Real.logb 3 σ⁻¹⌉ ≤ (L : ℤ) →
          ∃ B₀ : ℝ, 1 ≤ B₀ ∧
            ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
              (S : CoeffSpace d → ℝ),
              IsProbabilityMeasure P →
              IsStationaryLaw P →
              IsUnitRangeLaw P →
              CoarseEllipticityDagger P γ E Ψ K S →
              ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
                  ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L
                      : ℤ)) ∪
                        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus)
                          (n + (L : ℤ)) ⊆
                      HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                    Real.log (‖m‖ * ‖m⁻¹‖) ≤
                      c₀ / (L : ℝ) *
                        ((k : ℝ) - (jStar : ℝ) -
                          (⌈B₀ * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) →
                    k + 2 * (bigQ d γ : ℤ) ≤ n →
                    projectiveDistance m mPlus ≤ 1 →
                    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
                        detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)) ≤
                      c₀ * σ →
                    BlockMatLoewnerLE
                        (blockScale (1 - σ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) ∧
                      BlockMatLoewnerLE
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                        (blockScale (1 + σ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                            (n + 2 * (L : ℤ)))) := by
  obtain ⟨L₀, c₀, hc₀, Csrc, hCsrc, hbridge⟩ :=
    Annealed.successful_short_bridge_roundedGrid d hd γ hγ
  refine ⟨L₀, c₀, hc₀, Csrc, hCsrc, ?_⟩
  intro σ hσ L hL
  obtain ⟨B₀, hB₀, hbridge⟩ := hbridge σ hσ L hL
  refine ⟨B₀, hB₀, ?_⟩
  intro P E Ψ K S hP hstat _hunit hdag
  let := hP
  exact hbridge P E Ψ K S hstat _hunit hdag

end HCPolySupport.HighContrast.Entry
