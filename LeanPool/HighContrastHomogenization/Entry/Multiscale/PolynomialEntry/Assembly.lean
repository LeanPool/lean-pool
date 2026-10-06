/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Annealed.ReferenceNormalization
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.PolynomialEntry.Arithmetic
public import LeanPool.HighContrastHomogenization.Entry.GlobalSelection
public import LeanPool.HighContrastHomogenization.Entry.ScaleSelection
public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData

/-!
# High-contrast homogenization: Entry.Multiscale.PolynomialEntry.Assembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Assembly of `t.polynomial.entry`

This module assembles the paper's Theorem `t.polynomial.entry` from the two selection
statements `p.scale.selection` and `p.global.selection` together with an assumed
`p.response.transfer`.  The constants are introduced in the order the paper's proof fixes
them, each from the statement that owns it, so that the constant of the conclusion is
determined before the coefficient law is quantified over.  The bridge from the entry
generation to every larger scale is the monotonicity of the annealed contrast in the scale:
a contrast bound at the entry generation propagates to all scales above it.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean annealedContrast aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The standing coarse-ellipticity assumption carries a growth witness `K > 1`, hence in
particular `K ≥ 1`. -/
private theorem one_le_growth_of_dagger {d : ℕ} {P : Measure (CoeffSpace d)} {γ : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {Src : CoeffSpace d → ℝ}
    (h : CoarseEllipticityDagger P γ E Ψ K Src) : 1 ≤ K :=
  h.one_lt_growthWitness.le

/-- Under the standing coarse-ellipticity assumption at a probability law and `d ≥ 2`, the
aspect ratio `Π` of the reference block is at least one. -/
private theorem one_le_aspectRatio_of_dagger {d : ℕ} (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {γ : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {Src : CoeffSpace d → ℝ}
    (h : CoarseEllipticityDagger P γ E Ψ K Src) : 1 ≤ aspectRatio E := by
  have : NeZero d := ⟨by omega⟩
  exact HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger h

/-- The conclusion of `p.global.selection` after its constants `ε, Csrc, H, Cprof, σ, C`: for
every coefficient law satisfying the standing assumptions, every `B ≥ B₀(ε,σ)`, and every
generation `j_*` above the source scale, it produces a symmetric positive block `F` and two
integer scales `s < t` whose adapted cells, Loewner comparisons, determinant loss and profile
drift all satisfy the printed bounds. -/
@[expose]
public def GlobalSelectionBody (d : ℕ) (γ : ℝ) (S : SelectionData) (ε Csrc : ℝ) (H : ℕ)
    (Cprof σ C : ℝ) : Prop :=
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
                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s) ∧
              BlockMatLoewnerLE
                (adaptedMean P
                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
                (blockScale (1 + Real.sqrt ε * σ) F) ∧
              (d : ℝ)⁻¹ *
                  detIncrement P
                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s t < σ ∧
              max
                    (max
                      (profile P γ
                        (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar
                        s s)
                      (profile P γ
                        (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar
                        s t))
                    (profile P γ
                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar
                      t t) +
                  determinantDrift P γ
                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s +
                  determinantDrift P γ
                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t ≤
                Cprof * σ ^ ((1 - γ) / 8) ∧
              (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^ ((1 : ℝ) / 2) ≤
                (2 + aspectRatio E) ^ C

/-- The conclusion of `p.response.transfer` after its constants
`Csrc, ε, H, Cprof, σ, Cglob, Bresp, Cresp, δ`: given the same coefficient-law data and a
symmetric positive block `F` with scales `s < t` satisfying the entry hypotheses at a
generation above the source scale, it extends the terminal scale to an integer `mEnt > t`
within `⌈Cresp log₃(2+Π)⌉` of `t` at which the annealed contrast has dropped to `1 + δ`. -/
@[expose]
public def ResponseTransferBody (d : ℕ) (γ : ℝ) (S : SelectionData) (ε Csrc : ℝ) (H : ℕ)
    (Cprof σ Cglob Bresp Cresp δ : ℝ) : Prop :=
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
                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
              HighContrast.centeredCube d (2 * (jStar : ℤ)) →
            BlockMatLoewnerLE
              (blockScale (1 - Real.sqrt ε * σ) F)
              (adaptedMean P
                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s) →
            BlockMatLoewnerLE
              (adaptedMean P
                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
              (blockScale (1 + Real.sqrt ε * σ) F) →
            (d : ℝ)⁻¹ *
                detIncrement P
                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s t < σ →
            max
                  (max
                    (profile P γ
                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                      jStar s s)
                    (profile P γ
                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                      jStar s t))
                  (profile P γ
                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                    jStar t t) +
                determinantDrift P γ
                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s +
                determinantDrift P γ
                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t ≤
              Cprof * σ ^ ((1 - γ) / 8) →
            (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^
                ((1 : ℝ) / 2) ≤
              (2 + aspectRatio E) ^ Cglob →
            ∃ mEnt : ℤ,
              t < mEnt ∧
                mEnt - t ≤
                  ⌈Cresp * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                annealedContrast P mEnt - 1 ≤ δ

/-- The law-level assembly of `t.polynomial.entry`: from the global-selection conclusion at
the constants `ε, CsrcG, H, Cprof, τ, Cg` and the response-transfer conclusion at
`ε, CsrcR, H, Cprof, τ, Cg, Bresp, Cresp, δ = σ`, every scale above the entry generation
`⌈entryConst … log₃(2 + Π K)⌉` has annealed contrast at most `1 + σ`. -/
private theorem entry_of_law
    (d : ℕ) (hd : 2 ≤ d) (γ σ : ℝ) (S : SelectionData) (ε CsrcG : ℝ) (hCsrcG : 0 < CsrcG)
    (H : ℕ) (Cprof τ Cg : ℝ) (hCg : 0 < Cg)
    (hGS : GlobalSelectionBody d γ S ε CsrcG H Cprof τ Cg)
    (CsrcR : ℝ) (Bresp : ℝ) (hBresp : 1 ≤ Bresp) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (hRT : ResponseTransferBody d γ S ε CsrcR H Cprof τ Cg Bresp Cresp σ)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ)
    (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P) (hur : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ K Src) :
    ∀ m : ℤ,
      ⌈entryConst (Cg * (max (S.B0 ε τ) Bresp + 1)) (max (S.B0 ε τ) Bresp) Cg Cresp
            (max CsrcG CsrcR) d * Real.logb 3 (2 + aspectRatio E * K)⌉ ≤ m →
        annealedContrast P m ≤ 1 + σ := by
  have := hP
  have hK : (1 : ℝ) ≤ K := one_le_growth_of_dagger hdag
  have hPi : (1 : ℝ) ≤ aspectRatio E := one_le_aspectRatio_of_dagger hd hdag
  have ha : (0 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := logb_two_add_nonneg _ (by linarith only [hPi])
  have hb : (0 : ℝ) ≤ Real.logb 3 (2 * K) := logb_two_mul_nonneg_of_one_le K hK
  have hBm : (1 : ℝ) ≤ max (S.B0 ε τ) Bresp := hBresp.trans (le_max_right _ _)
  have hCs : (0 : ℝ) ≤ max CsrcG CsrcR := le_trans hCsrcG.le (le_max_left _ _)
  have hA : (0 : ℝ) ≤ Cg * (max (S.B0 ε τ) Bresp + 1) := mul_nonneg hCg.le (by linarith only [hBm])
  have hj1 : 2 * d ≤ 3 ^ entryScale (Cg * (max (S.B0 ε τ) Bresp + 1)) (max CsrcG CsrcR)
      (Real.logb 3 (2 + aspectRatio E)) (Real.logb 3 (2 * K)) d :=
    two_mul_le_three_pow_of_le d _ (le_entryScale _ _ _ _ _)
  have hjG := ceil_le_entryScale (Cg * (max (S.B0 ε τ) Bresp + 1)) (max CsrcG CsrcR) CsrcG
    (Real.logb 3 (2 + aspectRatio E)) (Real.logb 3 (2 * K)) d hb (le_max_left _ _)
  have hjR := ceil_le_entryScale (Cg * (max (S.B0 ε τ) Bresp + 1)) (max CsrcG CsrcR) CsrcR
    (Real.logb 3 (2 + aspectRatio E)) (Real.logb 3 (2 * K)) d hb (le_max_right _ _)
  obtain ⟨F, s, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hGS P E Ψ K Src hP hst hur hdag (max (S.B0 ε τ) Bresp) (le_max_left _ _) _ hj1 hjG
  obtain ⟨mEnt, hm1, hm2, hm3⟩ :=
    hRT P E Ψ K Src hP hst hur hdag (max (S.B0 ε τ) Bresp) le_rfl _ hj1 hjR F s t
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  intro m hm
  -- the entry generation is above `j_*`, so the contrast at `m` is at most the contrast there
  have hjm := scale_le_terminal _ s t mEnt (max (S.B0 ε τ) Bresp)
    (Real.logb 3 (2 + aspectRatio E)) (by linarith only [hBm]) ha h5 h3 hm1
  have hjle := entryScale_le (Cg * (max (S.B0 ε τ) Bresp + 1)) (max CsrcG CsrcR)
    (Real.logb 3 (2 + aspectRatio E)) (Real.logb 3 (2 * K)) d
    (add_nonneg (mul_nonneg hA ha) (mul_nonneg hCs hb))
  have hmr := terminal_le_real _ t mEnt (max (S.B0 ε τ) Bresp) Cg Cresp
    (Real.logb 3 (2 + aspectRatio E)) h6 hm2
  push_cast at hmr
  have hmb := entry_bound_int _ _ mEnt
    (entry_bound_real (Cg * (max (S.B0 ε τ) Bresp + 1)) (max (S.B0 ε τ) Bresp) Cg Cresp
      (max CsrcG CsrcR) (Real.logb 3 (2 + aspectRatio E)) (Real.logb 3 (2 * K))
      (Real.logb 3 (2 + aspectRatio E * K)) d ha hb
      (logb_two_add_le_logb_two_add_mul _ K (by linarith only [hPi]) hK)
      (logb_two_mul_le_two_mul_logb _ K hPi hK)
      (logb_two_le_logb_two_add _ (mul_nonneg (by linarith only [hPi]) (by linarith only [hK])))
      hA (by linarith only [hBm]) hCg.le hCresp.le hCs (mEnt : ℝ) (by linarith only [hmr, hjle]))
  have hstep := Annealed.annealedContrast_antitone d hd P γ E Ψ K Src hst hdag _ hj1 mEnt m
    hjm (le_trans hmb hm)
  linarith only [hstep, hm3]

/-- **`t.polynomial.entry` from `p.response.transfer`.**  For every `d ≥ 2`, every
`γ ∈ [0,1)` and every tolerance `σ ∈ (0,1]`, the conclusion of `p.response.transfer` — its
constants chosen in the printed order after those of `p.scale.selection` and
`p.global.selection` — implies the polynomial entry estimate: there is a constant `C > 0`,
fixed before the coefficient law is quantified over and depending only on `d`, `γ` and `σ`,
such that under the standing assumptions on the law the annealed contrast satisfies
`Θ_m ≤ 1 + σ` at every scale `m ≥ ⌈C log₃(2 + Π K)⌉`. -/
theorem polynomial_entry_of_response_transfer
    (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (hRT : ∀ (S : SelectionData), S.Selects d γ →
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
                                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
                                    HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                                  BlockMatLoewnerLE
                                    (blockScale (1 - Real.sqrt ε * σ) F)
                                    (adaptedMean P
                                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s) →
                                  BlockMatLoewnerLE
                                    (adaptedMean P
                                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
                                    (blockScale (1 + Real.sqrt ε * σ) F) →
                                  (d : ℝ)⁻¹ *
                                      detIncrement P
                                        (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s t < σ →
                                  max
                                        (max
                                          (profile P γ
                                            (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                                            jStar s s)
                                          (profile P γ
                                            (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                                            jStar s t))
                                        (profile P γ
                                          (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                                          jStar t t) +
                                      determinantDrift P γ
                                        (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s +
                                      determinantDrift P γ
                                        (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t ≤
                                    Cprof * σ ^ ((1 - γ) / 8) →
                                  (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^
                                      ((1 : ℝ) / 2) ≤
                                    (2 + aspectRatio E) ^ Cglob →
                                  ∃ mEnt : ℤ,
                                    t < mEnt ∧
                                      mEnt - t ≤
                                        ⌈Cresp * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                                      annealedContrast P mEnt - 1 ≤ δ)
    (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ m : ℤ, ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ≤ m →
          annealedContrast P m ≤ 1 + σ := by
  obtain ⟨S, hS⟩ := Entry.scale_selection d hd γ hγ
  obtain ⟨ε, hε, CsrcG, hCsrcG, hGS⟩ := Entry.global_selection d hd γ hγ S hS
  obtain ⟨CsrcR, -, hRT⟩ := hRT S hS
  obtain ⟨H, hH, hRT⟩ := hRT ε hε σ hσ
  obtain ⟨Cprof, hCprof, hGS⟩ := hGS H hH
  obtain ⟨σ₀, hσ₀, hRT⟩ := hRT Cprof hCprof
  obtain ⟨Cg, hCg, hGS⟩ := hGS σ₀ hσ₀
  obtain ⟨Bresp, hBresp, Cresp, hCresp, hRT⟩ := hRT σ₀ ⟨hσ₀.1, le_rfl⟩ Cg hCg
  have hBm : (1 : ℝ) ≤ max (S.B0 ε σ₀) Bresp := hBresp.trans (le_max_right _ _)
  refine ⟨entryConst (Cg * (max (S.B0 ε σ₀) Bresp + 1)) (max (S.B0 ε σ₀) Bresp) Cg Cresp
      (max CsrcG CsrcR) d,
    entryConst_pos _ _ _ _ _ _ (mul_nonneg hCg.le (by linarith only [hBm])) (by linarith only [hBm]) hCg hCresp.le
      (le_trans hCsrcG.le (le_max_left _ _)), ?_⟩
  intro P E Ψ K Src hP hst hur hdag
  exact entry_of_law d hd γ σ S ε CsrcG hCsrcG H Cprof σ₀ Cg hCg hGS CsrcR Bresp hBresp
    Cresp hCresp hRT P E Ψ K Src hP hst hur hdag

end HCPolySupport.HighContrast.Multiscale
