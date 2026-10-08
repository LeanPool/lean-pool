/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.RunAssembly

/-!
# High-contrast homogenization: Entry.GlobalSelection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `p.global.selection`

`HCPolySupport.HighContrast.Entry.global_selection` is the type of
`HCPoly/Entry/Statements/GlobalSelection.lean` byte for byte, discharged from
`Multiscale.global_run`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Entry

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Proof of `p.global.selection`: the type of `HCPoly/Entry/Statements/GlobalSelection.lean`
byte for byte. Discharged from `Multiscale.global_run` by unfolding `SelectedOutput`. -/
theorem global_selection
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ H : ℕ, max 4 S.h ≤ H →
          ∃ Cprof : ℝ, 0 < Cprof ∧
            ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
              ∃ C : ℝ, 0 < C ∧
                ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                  (Src : CoeffSpace d → ℝ),
                  IsProbabilityMeasure P →
                  IsStationaryLaw P →
                  IsUnitRangeLaw P →
                  CoarseEllipticityDagger P γ E Ψ K Src →
                  ∀ B : ℝ, S.B0 ε σ ≤ B →
                    ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                      ⌈C * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
                          Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                        ∃ (F : BlockMat d) (s t : ℤ),
                          IsSymmetricBlockMat F ∧
                            Book.Ch02.BlockPosDef F ∧
                            s < t ∧
                            t = s + (H : ℤ) ∧
                            (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s ∧
                            t ≤ (jStar : ℤ) + ⌈(B + C) * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                            HighContrast.adaptedCell
                                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
                              HighContrast.centeredCube d (2 * (jStar : ℤ)) ∧
                            BlockMatLoewnerLE (blockScale (1 - Real.sqrt ε * σ) F)
                              (adaptedMean P
                                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                                  s) ∧
                            BlockMatLoewnerLE
                              (adaptedMean P
                                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
                              (blockScale (1 + Real.sqrt ε * σ) F) ∧
                            (d : ℝ)⁻¹ *
                                detIncrement P
                                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                                    F)) s t < σ ∧
                            max
                                  (max
                                    (profile P γ
                                      (Geometry.explicitRoundedGrid jStar
                                        (explicitCanonicalMetric F)) jStar
                                      s s)
                                    (profile P γ
                                      (Geometry.explicitRoundedGrid jStar
                                        (explicitCanonicalMetric F)) jStar
                                      s t))
                                  (profile P γ
                                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                                      F)) jStar
                                    t t) +
                                determinantDrift P γ
                                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                                    F)) jStar s +
                                determinantDrift P γ
                                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                                    F)) jStar t ≤
                              Cprof * σ ^ ((1 - γ) / 8) ∧
                            (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^
                              ((1 : ℝ) / 2) ≤
                              (2 + aspectRatio E) ^ C  :=
  Multiscale.global_run d hd γ hγ S hS

end

end HCPolySupport.HighContrast.Entry
