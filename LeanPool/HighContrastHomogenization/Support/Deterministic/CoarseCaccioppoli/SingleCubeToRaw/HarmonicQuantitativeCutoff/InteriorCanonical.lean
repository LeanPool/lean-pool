/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicQuantitativeCutoff.BoundaryCanonical

/-!
# Coarse-graining support:
Support.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicQuantitativeCutoff.InteriorCanonical

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

noncomputable section

open scoped ENNReal

/-- Interior coarse Caccioppoli for the actual harmonic family using the
canonical chapter-3 quantitative cube cutoff, with the strict support
hypothesis `ρ₂ < 1` discharged automatically on the deterministic radius
sequence. -/
theorem
    coarseCaccioppoli_interior_qone_of_quantitativeCutoff_of_scalarCutoffControl
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = G₀ ρ₂)
    (hfluxMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (fun x => (w ρ₁ ρ₂).toH1 x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds
        Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  have hs1 : s < 1 := by
    linarith
  refine
    coarseCaccioppoli_interior_qone_of_radiusAgreement_of_heightChoice
      Q a s t C uL2Sq k hC hs ht hst hu hagree hG_nonneg hG_bounded hscale ?_
  intro n
  have hρ₁ := (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hlt : coarseCaccioppoliRadiusSequence n < coarseCaccioppoliRadiusSequence (n + 1) :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ := (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  rcases
    coarseCaccioppoliBoundaryRadiusEnergyAnalyticInputs_at_radiusSequence
      Q a s C G₀ w g Acirc1 AcircS U A1 AS hEll n
      (hlower hρ₁ hlt hρ₂)
      (henergyAvg hρ₁ hlt hρ₂)
      (hfluxMem hρ₁ hlt hρ₂)
      (huMem hρ₁ hlt hρ₂)
      (hgMem hρ₁ hlt hρ₂)
      (hfluxEnergy hρ₁ hlt hρ₂)
      (hscalar hρ₁ hlt hρ₂)
      hC
      (hAcirc1_nonneg hρ₁ hlt hρ₂)
      (hAcircS_nonneg hρ₁ hlt hρ₂)
      (hU hρ₁ hlt hρ₂)
      (hA1 hρ₁ hlt hρ₂)
      (hAS hρ₁ hlt hρ₂) with
    ⟨htest, henergyAvgN, hfluxMemN, huMemN, hgMemN, hξLpN, hfluxEnergyN, hscalarN,
      hB_nonnegN, hAcirc1_nonnegN, hAcircS_nonnegN, hUN, hXiN, hDN, hA1N, hASN⟩
  rcases hrawcoeff hρ₁ hlt hρ₂ with ⟨hconst, hcentered⟩
  refine le_trans htest ?_
  simpa [henergyAvgN] using
    (abs_cubeAverage_vecDot_scalar_smul_le_boundaryRawEstimate_of_canonical_factor_bounds
      (Q := Q) (a := a) (s := s)
      (flux := fun x =>
        matVecMul (a x)
          ((w (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))).toH1.grad x))
      (u := fun x =>
        (w (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1))).toH1 x)
      (g := g (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (ξ := scalarCutoffGradientField
        (QuantitativeCubeCutoff.canonicalFun Q
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1))))
      (energy := fun x =>
        scalarVariationEnergyIntegrand a
          (w (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))) x)
      (Acirc1 := Acirc1 (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (AcircS := AcircS (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (B := coarseCaccioppoliQuantitativeCutoffHessianBound Q
        (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (C := C)
      (U := U (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (Xi := coarseCaccioppoliQuantitativeCutoffGradientBound Q
        (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (D := coarseCaccioppoliQuantitativeCutoffHessianBound Q
        (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (A1 := A1 (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (AS := AS (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (Alpha := coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      (Bcross := coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
      hs hs1 hfluxMemN huMemN hgMemN hξLpN hfluxEnergyN hscalarN
      hAcirc1_nonnegN hAcircS_nonnegN hUN hXiN hDN hA1N hASN hconst hcentered)


end

end HCPolySupport
