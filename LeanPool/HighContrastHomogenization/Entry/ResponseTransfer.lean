/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ResponseTransferSkeleton

/-!
# High-contrast homogenization: Entry.ResponseTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `p.response.transfer`

`HCPolySupport.HighContrast.Entry.response_transfer` is the statement of
`HCPolySupport.HighContrast.response_transfer` (`HCPoly/Entry/Statements/ResponseTransfer.lean`).
Its statement is
the one, character for character; the statement file's body is one `by exact` application
of this theorem to that statement's binders.

The proof is the assembly of `p.response.transfer` over the four kernels and the
bookkeeping lemmas of `HCPoly/Entry/Multiscale/ResponseTransferSkeleton.lean`, which this file
imports.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean annealedContrast aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Entry

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- **Proposition `p.response.transfer`**. In the
the generalized raw-output form, one source constant `Csrc(d,γ)` works for every raw
`ε ∈ (0,ε₀]`; for every `δ ∈ (0,1]` there are `H ≥ max {4,h}` and `σ₀ ∈ (0,ε]`
such that, for every `σ ∈ (0,σ₀]` and raw global constant `Cglob`, there are response
constants `Bresp ≥ 1` and `Cresp < ∞` with: every qualifying global-selection output at
`B ≥ max {B₀,Bresp}` admits a deterministic Euclidean generation `m_ent > t` satisfying
`m_ent - t ≤ ⌈Cresp log₃(2+Π)⌉` and `Θ_{m_ent}-1 ≤ δ`.

Assembly (`p.response.transfer`): `Csrc := max` of the two kernel source constants; tolerances
from `response_tolerances`; `H, σ₀, Bresp₁` from `adapted_response_kernel`; `Bresp₂, Cresp` from
`persistence_transfer_kernel`; `Bresp := max`; unpack the binders into `RawOutput`, weaken by
`RawOutput.mono`; `mEnt := t + ℓ`; widen the sandwich by `blockScale_loewner_mono` and
`loewner_trans`; `canonical_comparison_kernel`, then `euclidean_contrast_bridge_kernel` with
`annealedContrast_eq` and the third tolerance; generation bound by `nat_le_ceil_of_le`. -/
theorem response_transfer
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
      ∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) 1 →
        ∃ H : ℕ, max 4 S.h ≤ H ∧
          ∀ Cprof : ℝ, 0 < Cprof →
            ∃ σ₀ : ℝ, σ₀ ∈ Set.Ioc (0 : ℝ) ε ∧
              ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) σ₀ →
                ∀ Cglob : ℝ, 0 < Cglob →
                  ∃ Bresp : ℝ, 1 ≤ Bresp ∧
                    ∃ Cresp : ℝ, 0 < Cresp ∧
                      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                        (Src : CoeffSpace d → ℝ),
                        IsProbabilityMeasure P →
                        IsStationaryLaw P →
                        IsUnitRangeLaw P →
                        CoarseEllipticityDagger P γ E Ψ K Src →
                        ∀ B : ℝ, max (S.B0 ε σ) Bresp ≤ B →
                          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                            ⌈Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
                                Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                              ∀ (F : BlockMat d) (s t : ℤ),
                                IsSymmetricBlockMat F →
                                Book.Ch02.BlockPosDef F →
                                s < t →
                                t = s + (H : ℤ) →
                                (jStar : ℤ) +
                                    ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s →
                                t ≤ (jStar : ℤ) +
                                    ⌈(B + Cglob) * Real.logb 3 (2 + aspectRatio E)⌉ →
                                HighContrast.adaptedCell
                                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                                      F)) t ⊆
                                  HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                                BlockMatLoewnerLE
                                  (blockScale (1 - Real.sqrt ε * σ) F)
                                  (adaptedMean P
                                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                                      F)) s) →
                                BlockMatLoewnerLE
                                  (adaptedMean P
                                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                                      F)) s)
                                  (blockScale (1 + Real.sqrt ε * σ) F) →
                                (d : ℝ)⁻¹ *
                                    detIncrement P
                                      (Geometry.explicitRoundedGrid jStar
                                        (explicitCanonicalMetric F)) s t < σ →
                                max
                                      (max
                                        (profile P γ
                                          (Geometry.explicitRoundedGrid jStar
                                            (explicitCanonicalMetric F))
                                          jStar s s)
                                        (profile P γ
                                          (Geometry.explicitRoundedGrid jStar
                                            (explicitCanonicalMetric F))
                                          jStar s t))
                                      (profile P γ
                                        (Geometry.explicitRoundedGrid jStar
                                          (explicitCanonicalMetric F))
                                        jStar t t) +
                                    determinantDrift P γ
                                      (Geometry.explicitRoundedGrid jStar
                                        (explicitCanonicalMetric F)) jStar s +
                                    determinantDrift P γ
                                      (Geometry.explicitRoundedGrid jStar
                                        (explicitCanonicalMetric F)) jStar t ≤
                                  Cprof * σ ^ ((1 - γ) / 8) →
                                (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^
                                    ((1 : ℝ) / 2) ≤
                                  (2 + aspectRatio E) ^ Cglob →
                                ∃ mEnt : ℤ,
                                  t < mEnt ∧
                                    mEnt - t ≤
                                      ⌈Cresp * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                                    annealedContrast P mEnt - 1 ≤ δ := by
  obtain ⟨C1, hC1, K1⟩ := Multiscale.adapted_response_kernel d hd γ hγ S hS
  obtain ⟨C2, _hC2, K2⟩ := Multiscale.persistence_transfer_kernel d hd γ hγ S hS
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro ε hε δ hδ
  obtain ⟨ηiso, δad, ηp, ηm, hηiso, hδad, hηp, hηm, hpi, hlow, hthird⟩ :=
    Multiscale.response_tolerances d hd δ hδ
  obtain ⟨H, hH, K1'⟩ := K1 ε hε δad hδad
  refine ⟨H, hH, ?_⟩
  intro Cprof hCprof
  obtain ⟨σ₀, hσ₀, K1''⟩ := K1' Cprof hCprof
  refine ⟨σ₀, hσ₀, ?_⟩
  intro σ hσ Cglob hCglob
  obtain ⟨B1, hB1, K1c⟩ := K1'' σ hσ Cglob hCglob
  have hσε : σ ∈ Set.Ioc (0 : ℝ) ε := ⟨hσ.1, hσ.2.trans hσ₀.2⟩
  obtain ⟨B2, _hB2, Cresp, hCresp, K2c⟩ :=
    K2 ε hε δad hδad ηp hηp ηm hηm H hH Cprof hCprof σ hσε Cglob hCglob
  refine ⟨max B1 B2, le_max_of_le_left hB1, Cresp, hCresp, ?_⟩
  intro P E Ψ K Src hP hstat hunit hell B hB jStar hj hsrc F s t hsymm hpos hst ht hlo hhi
    hcube hclo hchi hdet hprof hecc
  have raw : Multiscale.RawOutput d γ S ε σ Cglob Cprof (max C1 C2) H (max B1 B2)
      P E Ψ K Src B jStar F s t :=
    ⟨hP, hstat, hunit, hell, hB, hj, hsrc, hsymm, hpos, hst, ht, hlo, hhi, hcube, hclo, hchi,
      hdet, hprof, hecc⟩
  obtain ⟨hAs, hApos, himb⟩ :=
    K1c P E Ψ K Src B jStar F s t (raw.mono (le_max_left _ _) (le_max_left _ _))
  obtain ⟨ℓ, hℓ, hℓle, hMs, hlo', hhi'⟩ :=
    K2c P E Ψ K Src B jStar F s t (raw.mono (le_max_right _ _) (le_max_right _ _)) himb
  refine ⟨t + (ℓ : ℤ), by omega, ?_, ?_⟩
  · have hceil := Multiscale.nat_le_ceil_of_le ℓ (Cresp * Real.logb 3 (2 + aspectRatio E)) hℓle
    linarith only [hceil]
  · have hpos1 : (0 : ℝ) < 1 - ηiso := by linarith only [hηiso.2]
    have hloM := Multiscale.loewner_trans
      (Multiscale.blockScale_loewner_mono _ hApos hlow) hlo'
    have hhiM := Multiscale.loewner_trans hhi'
      (Multiscale.blockScale_loewner_mono _ hApos
        (show (1 : ℝ) + ηp ≤ 1 + ηiso by linarith only [hpi]))
    have hMpos := Multiscale.blockPosDef_of_blockScale_le hpos1 hApos hloM
    have hcomp := Multiscale.canonical_comparison_kernel hd _ _ hAs hApos hMs hηiso hδad
      hloM hhiM himb
    have hx0 : (0 : ℝ) ≤ (1 + ηiso) ^ 3 / (1 - ηiso) * (1 + δad) - 1 := by
      have h1 : (1 : ℝ) ≤ (1 + ηiso) ^ 3 / (1 - ηiso) := by
        rw [le_div_iff₀ hpos1]
        nlinarith only [hηiso.1, sq_nonneg ηiso, pow_nonneg hηiso.1.le 3]
      have hd0 : (0 : ℝ) ≤ δad := hδad.1.le
      nlinarith only [h1, hd0]
    have hbridge := Multiscale.euclidean_contrast_bridge_kernel hd _ hMs hMpos hx0
      (by linarith only [hcomp])
    rw [Multiscale.annealedContrast_eq d P (t + (ℓ : ℤ))]
    linarith only [hbridge, hthird]

end HCPolySupport.HighContrast.Entry
